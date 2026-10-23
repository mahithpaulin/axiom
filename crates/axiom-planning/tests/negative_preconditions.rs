use axiom::Budget;
use axiom_core::{Engine, Problem, Verdict};
use axiom_planning::PlanningEngine;

const DOMAIN: &str = r#"
(define (domain gate)
  (:requirements :strips :negative-preconditions)
  (:predicates (at ?x) (blocked ?x))
  (:constants item)
  (:action enter
    :parameters ()
    :precondition (not (blocked item))
    :effect (at item)))
"#;

fn solve(problem: &str) -> axiom_core::Outcome {
    let problem = Problem::planning(DOMAIN, problem);
    let mut engine = PlanningEngine::new();
    let outcome = engine.solve(&problem, &mut Budget::steps(1_000_000));
    engine
        .verify(&problem, &outcome)
        .expect("every planning answer must be replayable");
    outcome
}

#[test]
fn a_negative_precondition_is_honoured_and_replayed() {
    let outcome = solve("(define (problem p) (:domain gate) (:init) (:goal (at item)))");
    assert_eq!(outcome.verdict, Verdict::Found, "{outcome:?}");
}

#[test]
fn a_true_negative_precondition_blocks_the_action() {
    let outcome =
        solve("(define (problem p) (:domain gate) (:init (blocked item)) (:goal (at item)))");
    assert_eq!(outcome.verdict, Verdict::Impossible, "{outcome:?}");
}
