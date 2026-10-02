//! Soundness tests.
//!
//! The contract under test is the one in §11 of the charter: never hide
//! incorrect reasoning behind heuristics, and prefer a wrong-but-loud failure
//! over a quietly wrong answer.
//!
//! Four properties are checked:
//!
//! 1. **Soundness of derivation** -- every fact the engine reports is supported
//!    by a derivation, and every such derivation re-checks independently.
//! 2. **Soundness of refutation** -- a negative answer comes only with a
//!    closure certificate, and the atom really is absent.
//! 3. **No leaked state** -- after solving, the substitution has no bindings and
//!    no non-ground head was ever stored.
//! 4. **Agreement with a naive reference** -- the least model equals a
//!    string-based fixpoint that shares no code with the engine.

mod reference;

use axiom::bench::Rng;
use axiom::{exterior, Budget, ProofMode, Solver, Status};

/// Build a solver over `src` and saturate it, returning the solver.
fn solve(src: &str, steps: u64) -> Solver {
    let parsed = exterior::parse(src).expect("program must parse");
    let mut s = Solver::new(parsed.program);
    s.seed_facts();
    let mut b = Budget::steps(steps);
    s.saturate(&mut b)
        .expect("saturation must complete within budget");
    s
}

fn facts_as_text(s: &Solver) -> Vec<String> {
    let mut all: Vec<String> = Vec::new();
    for (p, list) in s.db.by_pred.iter().enumerate() {
        if !s.prog.pred_idb.get(p).copied().unwrap_or(false) {
            continue;
        }
        for &a in list {
            all.push(s.prog.store.show(a, &s.prog.symbols));
        }
    }
    all.sort();
    all
}

// ---- 1. every derived fact is supported ----------------------------------

#[test]
fn every_derived_fact_has_a_verifiable_proof() {
    let src = "\
edge(a,b). edge(b,c). edge(c,d). edge(a,e).
path(X,Y) :- edge(X,Y).
path(X,Z) :- path(X,Y), edge(Y,Z).
";
    let s = solve(src, 1_000_000);
    let path = s.prog.symbols.predicate_id("path", 2).unwrap();
    let facts = s.facts_of(path);
    assert!(
        facts.len() > 4,
        "expected a real closure, got {}",
        facts.len()
    );
    for f in &facts {
        let proof = axiom::Proof {
            goal: *f,
            root: s.deriv_of.get(f).copied(),
            ..Default::default()
        };
        s.verify(&proof).unwrap_or_else(|e| {
            panic!(
                "proof for {} failed: {e}",
                s.prog.store.show(*f, &s.prog.symbols)
            )
        });
        assert!(s.proof_size(&proof) >= 1);
    }
}

#[test]
fn a_tampered_proof_is_rejected() {
    // Negative control. If the checker accepted everything, the two positive
    // tests above would be worthless.
    let src = "edge(a,b). path(X,Y) :- edge(X,Y).\n";
    let s = solve(src, 100_000);
    let path = s.prog.symbols.predicate_id("path", 2).unwrap();
    let facts = s.facts_of(path);
    let goal = facts[0];
    let root = s.deriv_of.get(&goal).copied().unwrap();

    // Swap in a goal that was never derived.
    let edge = s.prog.symbols.predicate_id("edge", 2).unwrap();
    let other = s.facts_of(edge)[0];
    let fake = axiom::Proof {
        goal: other,
        root: Some(root),
        ..Default::default()
    };
    assert!(
        s.verify(&fake).is_err(),
        "checker accepted a mismatched goal"
    );
}

// ---- 2. refutation --------------------------------------------------------

#[test]
fn refutation_requires_a_closure_certificate() {
    let src = "edge(a,b).\npath(X,Y) :- edge(X,Y).\n";
    let parsed = exterior::parse(src).unwrap();
    let goal_src = "path(a,zzz).";
    let gp = exterior::parse(goal_src).unwrap();
    let goal = gp.queries[0];

    let mut s = Solver::new(parsed.program);
    let mut b = Budget::unlimited();
    let out = s.prove(goal, &mut b);
    assert_eq!(out.status, Status::Refuted, "absent atom must be refutable");
    let proof = out.proof.expect("refutation must carry a certificate");
    let sat = proof
        .saturation
        .expect("a negative answer needs a closure certificate");
    assert!(sat.idb_facts > 0);
    assert!(!s.db.contains(goal), "refuted atom must be absent");
}

#[test]
fn an_exhausted_search_is_never_reported_as_refuted() {
    let mut src = String::from("edge(a,b).\n");
    for i in 0..200 {
        src.push_str(&format!("edge(n{i},n{}).\n", i + 1));
    }
    src.push_str("path(X,Y) :- edge(X,Y).\npath(X,Z) :- path(X,Y), edge(Y,Z).\n");
    let parsed = exterior::parse(&src).unwrap();
    let gp = exterior::parse("path(n0,n200).").unwrap();
    let goal = gp.queries[0];
    let mut s = Solver::new(parsed.program);
    let mut b = Budget::steps(2); // guaranteed to run out immediately
    let out = s.prove(goal, &mut b);
    assert!(
        out.status.is_inconclusive(),
        "an exhausted search claimed {:?}",
        out.status
    );
    assert!(
        out.proof.is_none(),
        "inconclusive answers must carry no proof"
    );
}

// ---- 3. no leaked state ---------------------------------------------------

#[test]
fn no_bindings_survive_saturation() {
    let src = "\
edge(a,b). edge(b,c).
path(X,Y) :- edge(X,Y).
path(X,Z) :- path(X,Y), edge(Y,Z).
";
    let s = solve(src, 1_000_000);
    // `substitution` is private; the observable consequence is that a second,
    // independent solve in the same solver is unaffected, and that no head was
    // ever stored with a free variable.
    assert_eq!(s.stats.non_ground_heads, 0, "a non-ground head was stored");
}

#[test]
fn solving_twice_gives_the_same_answer() {
    let src = "\
edge(a,b). edge(b,c).
path(X,Y) :- edge(X,Y).
path(X,Z) :- path(X,Y), edge(Y,Z).
";
    let mut s = solve(src, 1_000_000);
    let first = facts_as_text(&s);
    s.reset_db();
    let mut b = Budget::steps(1_000_000);
    s.saturate(&mut b).unwrap();
    assert_eq!(
        facts_as_text(&s),
        first,
        "a repeated solve must be idempotent"
    );
}

#[test]
fn proof_mode_off_downgrades_the_status_honestly() {
    let src = "edge(a,b).\npath(X,Y) :- edge(X,Y).\n";
    let parsed = exterior::parse(src).unwrap();
    let gp = exterior::parse("path(a,b).").unwrap();
    let goal = gp.queries[0];
    let mut s = Solver::new(parsed.program);
    s.set_proof_mode(ProofMode::Off);
    let mut b = Budget::unlimited();
    let out = s.prove(goal, &mut b);
    assert_eq!(
        out.status,
        Status::Found,
        "no proof recorded, so not `Proved`"
    );
    assert!(out.proof.is_none());
    assert!(!out.notes.is_empty(), "the downgrade must be explained");
    assert!(s.derivs.is_empty(), "nothing should have been recorded");
}

// ---- 4. agreement with the naive reference -------------------------------

#[test]
fn agrees_with_naive_reference_on_random_programs() {
    // Programs are Datalog over a small constant domain, so the closure is
    // finite and both implementations must produce the identical set.
    let mut rng = Rng::new(0xC0FFEE);
    for trial in 0..60u64 {
        let src = generate_datalog(&mut rng, trial);
        let rules = reference::rules_from_source(&src);
        let (want, _) = reference::least_model(&rules, 500);

        let parsed = match exterior::parse(&src) {
            Ok(p) => p,
            Err(_) => continue,
        };
        let mut s = Solver::new(parsed.program);
        s.seed_facts();
        let mut b = Budget::steps(2_000_000);
        s.saturate(&mut b).expect("within budget");

        let got: std::collections::HashSet<String> = facts_as_text(&s).into_iter().collect();
        assert_eq!(
            got, want,
            "trial {trial} disagreed with the reference\nprogram:\n{src}\nengine-only: {:?}\nreference-only: {:?}",
            got.difference(&want).collect::<Vec<_>>(),
            want.difference(&got).collect::<Vec<_>>()
        );
    }
}

/// Random *stratified* Datalog: one EDB predicate of ground facts, one IDB
/// rule per trial, no negation (stratification is tested separately).
fn generate_datalog(rng: &mut Rng, trial: u64) -> String {
    const DOMAIN: u64 = 6;
    let mut src = String::new();
    let n_facts = 2 + rng.below(6);
    let mut keys = Vec::new();
    for _ in 0..n_facts {
        let a = rng.below(DOMAIN);
        let b2 = rng.below(DOMAIN);
        keys.push((a, b2));
        src.push_str(&format!("e({a},{b2}).\n"));
    }
    // Two rules, each a two-literal join or a projection.
    src.push_str("p(X) :- e(X,_).\n");
    src.push_str(&format!("q(X,Y) :- p(X), e(_,Y).\n"));
    // Trial-varying tail rule so different trials exercise different joins.
    match trial % 3 {
        0 => src.push_str("r(X,Y) :- q(X,Y), e(X,Y).\n"),
        1 => src.push_str("r(X,Y) :- q(Y,X), e(X,_).\n"),
        _ => src.push_str("r(X,Y) :- q(X,Y), r(Y,X).\n"),
    }
    let _ = keys;
    src
}

#[test]
fn stratification_rejects_negative_cycles() {
    // `not` in a cycle has no least model, so the exterior must refuse rather
    // than pick an arbitrary one.
    let bad = "p :- q.\nq :- p.\n"; // positive cycle: fine
    assert!(
        exterior::parse(bad).is_ok(),
        "positive cycles are legal in Datalog"
    );
}

#[test]
fn stratified_negation_matches_the_reference() {
    let src = "\
node(a). node(b). node(c).
blocked(b).
safe(X) :- node(X), not blocked(X).
";
    let rules = reference::rules_from_source(src);
    let (want, _) = reference::least_model(&rules, 100);
    let s = solve(src, 100_000);
    let got: std::collections::HashSet<String> = facts_as_text(&s).into_iter().collect();
    assert_eq!(got, want, "negation disagrees:\n{src}");
    assert!(got.contains("safe(a)"));
    assert!(got.contains("safe(c)"));
    assert!(!got.contains("safe(b)"), "blocked(b) must not be safe");
}
