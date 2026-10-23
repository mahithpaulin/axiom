use axiom::Budget;
use axiom_core::{Engine, Outcome, Problem, Verdict};
use axiom_prover::FolEngine;

fn solve(source: &str) -> Outcome {
    let problem = Problem::fol(source);
    let mut budget = Budget::steps(1_000_000);
    let mut engine = FolEngine::new();
    let outcome = engine.solve(&problem, &mut budget);
    if outcome.evidence.is_some() {
        engine
            .verify(&problem, &outcome)
            .expect("a definite answer must carry checkable evidence");
    }
    outcome
}

#[test]
fn an_unrelated_ground_equality_goal_is_never_refuted() {
    let outcome = solve("axiom a = b. goal c = d.");
    assert!(
        matches!(outcome.verdict, Verdict::Unknown | Verdict::ResourceLimit),
        "{outcome:?}"
    );
    assert!(outcome.evidence.is_none());
}

#[test]
fn a_contradicted_ground_equality_goal_is_not_proved() {
    let outcome = solve("axiom a = b. goal not a = b.");
    assert_ne!(outcome.verdict, Verdict::Proved, "{outcome:?}");
    assert!(outcome.evidence.is_none());
}
