//! Determinism tests.
//!
//! §27 asks for reproducible benchmarks; §13 asks for reproducible
//! comparisons. Both rest on the engine being a deterministic function of its
//! input. That is easy to lose by accident -- hash-map iteration order, a
//! `HashSet` driving a join, thread scheduling -- and a flaky benchmark is
//! indistinguishable from a real effect.
//!
//! Every property here is checked by comparing two *separate* solver instances,
//! not by comparing a value to a constant, so the tests keep their value when
//! the implementation changes.

use axiom::bench::Rng;
use axiom::{exterior, Budget, Solver};

fn closure_text(s: &Solver) -> Vec<String> {
    let mut v = Vec::new();
    for (p, list) in s.db.by_pred.iter().enumerate() {
        if !s.prog.pred_idb.get(p).copied().unwrap_or(false) {
            continue;
        }
        for &a in list {
            v.push(s.prog.store.show(a, &s.prog.symbols));
        }
    }
    v
}

const TC: &str = "\
edge(a,b). edge(b,c). edge(c,d). edge(a,e). edge(e,d).
path(X,Y) :- edge(X,Y).
path(X,Z) :- path(X,Y), edge(Y,Z).
";

fn solve_fresh(src: &str, steps: u64) -> Solver {
    let parsed = exterior::parse(src).unwrap();
    let mut s = Solver::new(parsed.program);
    s.seed_facts();
    let mut b = Budget::steps(steps);
    s.saturate(&mut b).expect("within budget");
    s
}

#[test]
fn two_runs_produce_identical_closures_in_identical_order() {
    let a = solve_fresh(TC, 1_000_000);
    let b = solve_fresh(TC, 1_000_000);
    assert_eq!(
        closure_text(&a),
        closure_text(&b),
        "closure differs between runs"
    );
    assert_eq!(
        a.stats.candidates, b.stats.candidates,
        "work counters differ"
    );
    assert_eq!(a.stats.rounds, b.stats.rounds);
    assert_eq!(a.stats.derivations, b.stats.derivations);
}

#[test]
fn closure_fingerprint_is_stable() {
    let a = solve_fresh(TC, 1_000_000);
    let b = solve_fresh(TC, 1_000_000);
    assert_eq!(a.closure_hash(), b.closure_hash());
    // And it must actually depend on the closure: a different program must not
    // share a fingerprint, or the negative-answer certificate is worthless.
    let c = solve_fresh("edge(a,b). path(X,Y) :- edge(X,Y).\n", 1_000_000);
    assert_ne!(a.closure_hash(), c.closure_hash());
}

#[test]
fn results_do_not_depend_on_the_budget_size() {
    // Work is bounded by step counts, so a larger budget can only allow more
    // work -- it must never change a completed answer.
    let tight = solve_fresh(TC, 10_000_000);
    let loose = solve_fresh(TC, 1_000_000_000);
    assert_eq!(closure_text(&tight), closure_text(&loose));
}

#[test]
fn random_programs_are_reproducible() {
    let mut rng = Rng::new(12345);
    for _ in 0..10 {
        let mut src = String::new();
        for _ in 0..8 {
            let a = rng.below(5);
            let b2 = rng.below(5);
            src.push_str(&format!("e({a},{b2}).\n"));
        }
        src.push_str("p(X) :- e(X,_).\nq(X,Y) :- p(X), e(_,Y).\nr(X,Y) :- q(X,Y), q(Y,X).\n");
        let a = solve_fresh(&src, 1_000_000);
        let b = solve_fresh(&src, 1_000_000);
        assert_eq!(
            closure_text(&a),
            closure_text(&b),
            "non-deterministic closure for:\n{src}"
        );
        assert_eq!(a.closure_hash(), b.closure_hash());
    }
}

#[test]
fn proof_shape_is_reproducible() {
    // The proof is a first-class output, so it must be as deterministic as the
    // answer it supports. Node ids are arena positions, so comparing the
    // rendered derivation graph is the right granularity.
    let a = solve_fresh(TC, 1_000_000);
    let b = solve_fresh(TC, 1_000_000);
    assert_eq!(
        a.derivs.len(),
        b.derivs.len(),
        "different derivation counts"
    );
    for (x, y) in a.derivs.iter().zip(b.derivs.iter()) {
        assert_eq!(x.rule, y.rule);
        assert_eq!(x.concl, y.concl);
        assert_eq!(x.body.len(), y.body.len());
        assert_eq!(x.inst.len(), y.inst.len());
    }
}
