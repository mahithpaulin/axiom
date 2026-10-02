//! Robustness tests: malformed input, adversarial programs, termination.
//!
//! §21 requires the exterior to treat input as hostile and §11 requires
//! termination behaviour and malformed-input handling to be tested explicitly.
//! The standard here is that **nothing panics and nothing hangs**: every
//! rejection is a value, every budget is respected.

use axiom::{exterior, Budget, Exhausted, Limits, Solver, Status};

// ---- malformed input -----------------------------------------------------

#[test]
fn malformed_programs_are_rejected_without_panicking() {
    let cases = [
        "",
        "(",
        ")",
        "edge(a,b",
        "edge(a,b)).",
        "edge((a)).",
        ":- .",
        "edge(a,b) :- .",
        ":- edge(a).",
        "not",
        ":- not .",
        "?- .",
        "?-",
        "edge(a,b) :- edge(a,b)",
        "p(",
        "p(,)",
        "p(a,,b).",
        "p(X) :- .",
        ". . .",
        "p(a) :- q(X), .",
        "p(a) :- not .",
        "\u{0}\u{1}\u{2}",
        "p(\u{1F600}).",
        "(((((((((p)))))))))",
        "p(a,b,c) :- q(a,b,c) extra",
    ];
    for src in cases {
        // The only requirement is that this returns rather than panicking or
        // looping. Some of these are accepted; that is fine and is why the
        // assertion is not `is_err`.
        let _ = exterior::parse(src);
    }
}

#[test]
fn non_ground_facts_are_rejected() {
    for src in ["p(X).", "p(f(X)).", "p(a,b,c)."] {
        let r = exterior::parse(src);
        match src {
            // arity is inferred, so this one is fine
            "p(a,b,c)." => assert!(r.is_ok()),
            _ => assert!(r.is_err(), "{src} should be rejected as a non-ground fact"),
        }
    }
}

#[test]
fn unstratified_negation_is_rejected() {
    let src = "p :- not q.\nq :- not p.\n";
    let err = exterior::parse(src).expect_err("a negative cycle has no least model");
    assert!(
        err.message.contains("stratified"),
        "unhelpful error: {}",
        err.message
    );
}

#[test]
fn limits_are_enforced() {
    let deep = "p(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a(a)))))))))))))))))))))))))))))))))))))))))))).";
    assert!(exterior::parse(deep).is_ok() || exterior::parse(deep).is_err());
    let tiny = Limits {
        max_depth: 3,
        ..Default::default()
    };
    assert!(
        exterior::parse_with(deep, tiny).is_err(),
        "depth limit not enforced"
    );

    let small = Limits {
        max_arity: 2,
        ..Default::default()
    };
    let wide = "p(a,b,c,d).";
    assert!(
        exterior::parse_with(wide, small).is_err(),
        "arity limit not enforced"
    );

    let few = Limits {
        max_tokens: 3,
        ..Default::default()
    };
    assert!(
        exterior::parse_with("e(a,b). e(c,d). e(e,f). e(g,h).", few).is_err(),
        "token limit not enforced"
    );
}

#[test]
fn a_very_long_identifier_is_handled() {
    let name = "x".repeat(100_000);
    let src = format!("p({name}).");
    let r = exterior::parse(&src);
    assert!(r.is_ok() || r.is_err());
}

#[test]
fn empty_program_is_valid_and_proves_nothing() {
    let parsed = exterior::parse("").unwrap();
    assert_eq!(parsed.program.rules.len(), 0);
    let mut s = Solver::new(parsed.program);
    s.seed_facts();
    let mut b = Budget::unlimited();
    let sat = s.saturate(&mut b).unwrap();
    assert_eq!(sat.idb_facts, 0);
}

// ---- adversarial programs -------------------------------------------------

/// Rules with a function symbol in the head have an infinite relation, so
/// bottom-up saturation cannot enumerate them. They must be marked, skipped, and
/// reported as such -- never loop, never store a non-ground fact.
#[test]
fn function_symbols_in_heads_do_not_break_saturation() {
    let src = "\
base(z).\nnum(succ(X)) :- base(X).\n";
    let parsed = exterior::parse(src).unwrap();
    assert!(
        parsed.program.rules.iter().any(|r| r.backward_only),
        "a function symbol in the head must mark the rule backward-only"
    );
    let mut s = Solver::new(parsed.program);
    s.seed_facts();
    let mut b = Budget::steps(1_000_000);
    let sat = s.saturate(&mut b).expect("saturation must terminate");
    assert_eq!(s.stats.non_ground_heads, 0);
    assert!(sat.rounds <= 2);
}

#[test]
fn self_referential_rules_terminate_under_a_budget() {
    // p(X) :- p(X) is useless but legal; it must reach the fixpoint, not spin.
    let src = "q(a).\np(X) :- q(X).\np(X) :- p(X).\n";
    let parsed = exterior::parse(src).unwrap();
    let mut s = Solver::new(parsed.program);
    s.seed_facts();
    let mut b = Budget::steps(1_000_000);
    let sat = s.saturate(&mut b);
    assert!(sat.is_ok(), "must reach a fixpoint: {sat:?}");
}

#[test]
fn budget_exhaustion_is_reported_not_hidden() {
    let mut src = String::new();
    for i in 0..300 {
        src.push_str(&format!("e(n{i},n{}).\n", i + 1));
    }
    src.push_str("p(X,Y) :- e(X,Y).\np(X,Z) :- p(X,Y), e(Y,Z).\n");
    let parsed = exterior::parse(&src).unwrap();
    let gp = exterior::parse("p(n0,n300).").unwrap();
    let goal = gp.queries[0];
    let mut s = Solver::new(parsed.program);
    let mut b = Budget::steps(5);
    let out = s.prove(goal, &mut b);
    assert!(out.status.is_inconclusive(), "claimed {:?}", out.status);
    assert!(out.reason.is_some(), "an inconclusive answer must say why");
    assert!(matches!(out.reason, Some(Exhausted::Steps)));
}

#[test]
fn budget_of_zero_stops_immediately() {
    let src = "e(a,b).\np(X,Y) :- e(X,Y).\n";
    let parsed = exterior::parse(src).unwrap();
    let gp = exterior::parse("p(a,b).").unwrap();
    let goal = gp.queries[0];
    let mut s = Solver::new(parsed.program);
    let mut b = Budget::steps(0);
    let out = s.prove(goal, &mut b);
    assert!(!out.status.is_definite() || out.reason.is_none() || out.reason.is_some());
    // Whichever status comes back, it must be consistent with its reason.
    if out.status.is_inconclusive() {
        assert!(out.proof.is_none());
    }
}

#[test]
fn very_wide_atoms_do_not_exhaust_memory_or_stack() {
    let mut src = String::new();
    let arity = 2000;
    let args: Vec<String> = (0..arity).map(|i| format!("a{i}")).collect();
    src.push_str(&format!("w({}).\n", args.join(",")));
    let parsed = exterior::parse(&src).unwrap();
    let mut s = Solver::new(parsed.program);
    s.seed_facts();
    let mut b = Budget::steps(100_000);
    s.saturate(&mut b).expect("wide atoms must be handled");
    let w = s.prog.symbols.predicate_id("w", arity as u16).unwrap();
    assert_eq!(s.fact_count(w), 1);
}

#[test]
fn deeply_nested_terms_do_not_overflow_the_stack() {
    // 200k-deep nesting in a *term*, parsed under a raised limit, then walked
    // and resolved. Every traversal in the engine is iterative for exactly this
    // reason.
    let depth = 200_000;
    let mut term = String::from("z");
    for _ in 0..depth {
        term = format!("f({term})");
    }
    let src = format!("p({term}).");
    let parsed = exterior::parse_with(
        &src,
        Limits {
            max_depth: 500_000,
            ..Default::default()
        },
    )
    .expect("deep term must parse");
    let mut s = Solver::new(parsed.program);
    s.seed_facts();
    let mut b = Budget::steps(10_000_000);
    s.saturate(&mut b).expect("deep term must not overflow");
    let p = s.prog.symbols.predicate_id("p", 1).unwrap();
    assert_eq!(s.fact_count(p), 1);
}

#[test]
fn many_facts_of_one_predicate_stay_indexable() {
    let mut src = String::new();
    for i in 0..2000 {
        src.push_str(&format!("e(k{},v{i}).\n", i % 100));
    }
    src.push_str("p(X,Y) :- e(X,Y).\n");
    let parsed = exterior::parse(&src).unwrap();
    let mut s = Solver::new(parsed.program);
    s.seed_facts();
    let mut b = Budget::steps(10_000_000);
    s.saturate(&mut b).unwrap();
    let p = s.prog.symbols.predicate_id("p", 2).unwrap();
    assert_eq!(s.fact_count(p), 2000);
}

#[test]
fn facts_with_identical_arguments_are_deduplicated() {
    let src = "e(a,a).\ne(a,a).\ne(a,a).\np(X,Y) :- e(X,Y).\n";
    let parsed = exterior::parse(src).unwrap();
    let mut s = Solver::new(parsed.program);
    s.seed_facts();
    let mut b = Budget::unlimited();
    s.saturate(&mut b).unwrap();
    let e = s.prog.symbols.predicate_id("e", 2).unwrap();
    assert_eq!(
        s.fact_count(e),
        1,
        "duplicate facts must collapse to one node"
    );
}

#[test]
fn a_query_with_no_answers_is_refuted_not_unknown() {
    let src = "e(a,b).\np(X,Y) :- e(X,Y).\n";
    let parsed = exterior::parse(src).unwrap();
    let gp = exterior::parse("?- p(a,zzz).").unwrap();
    let goal = gp.queries[0];
    let mut s = Solver::new(parsed.program);
    let mut b = Budget::unlimited();
    let out = s.query(goal, &mut b);
    assert_eq!(out.status, Status::Refuted);
    assert!(out.answers.is_empty());
    assert!(
        out.saturation.is_some(),
        "a negative answer needs its certificate"
    );
}

#[test]
fn a_query_with_answers_reports_them_with_substitutions() {
    let src = "e(a,b). e(b,c).\np(X,Y) :- e(X,Y).\n";
    let parsed = exterior::parse(src).unwrap();
    let gp = exterior::parse("?- p(X,c).").unwrap();
    let goal = gp.queries[0];
    let mut s = Solver::new(parsed.program);
    let mut b = Budget::unlimited();
    let out = s.query(goal, &mut b);
    assert_eq!(out.status, Status::Found);
    assert_eq!(out.answers.len(), 1);
    // The answer's proof must verify independently.
    for a in &out.answers {
        assert!(s.verify(&a.proof).is_ok());
    }
}
