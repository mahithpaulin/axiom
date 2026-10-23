use axiom::Budget;
use axiom_core::{Engine, Outcome, Problem, Verdict};
use axiom_smt::SmtEngine;

fn solve(source: &str) -> Outcome {
    let problem = Problem::smt(source);
    let mut budget = Budget::steps(1_000_000);
    let mut engine = SmtEngine::new();
    let outcome = engine.solve(&problem, &mut budget);
    engine
        .verify(&problem, &outcome)
        .expect("every SMT answer must carry checkable evidence");
    outcome
}

#[test]
fn the_integer_gap_in_a_negated_difference_bound_is_exact() {
    let outcome = solve(
        "(declare-fun x () Int) (declare-fun y () Int) \
         (assert (> (- y x) 3)) (assert (< (- y x) 4)) (check-sat)",
    );
    assert_eq!(outcome.verdict, Verdict::Impossible, "{outcome:?}");
}

#[test]
fn disequality_contradicts_equality() {
    let outcome = solve(
        "(declare-fun x () Int) (declare-fun y () Int) \
         (assert (= x y)) (assert (not (= x y))) (check-sat)",
    );
    assert_eq!(outcome.verdict, Verdict::Impossible, "{outcome:?}");
}
