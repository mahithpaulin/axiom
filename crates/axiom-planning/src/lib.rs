//! Axiom v4 STRIPS planning engine.
//!
//! The planner grounds a finite untyped STRIPS task and runs deterministic BFS.
//! A found plan is serialised as an action sequence and independently replayed by
//! [`planner::validate_actions`]. Exhausting the finite reachable state space is
//! the only route to `Impossible`; every cap hit is `ResourceLimit`.
//!
//! # Example
//!
//! ```
//! use axiom::Budget;
//! use axiom_planning::{Engine, PlanningEngine, Problem};
//!
//! let domain = r#"
//!   (define (domain d) (:predicates (p))
//!     (:action go :parameters () :precondition (p) :effect (p)))
//! "#;
//! let problem = r#"
//!   (define (problem q) (:domain d) (:objects) (:init (p)) (:goal (p)))
//! "#;
//! let p = Problem::planning(domain, problem);
//! let mut e = PlanningEngine::new();
//! let out = e.solve(&p, &mut Budget::steps(100_000));
//! assert_eq!(out.verdict, axiom_core::Verdict::Found);
//! e.verify(&p, &out).unwrap();
//! ```

pub mod pddl;
pub mod planner;

use axiom::Budget;
use axiom_core::{
    Capabilities, Evidence, Guarantee, Outcome, ProblemKind, Stats, Verdict, VerifyError,
};
use std::time::Instant;

pub use axiom_core::{Engine, Problem};
pub use pddl::{PddlError, PlanningTask};
pub use planner::{GroundAction, Plan, PlanResult, PlanStatus};

const PLAN_KIND: &str = "axiom-plan";
const EXHAUSTED_KIND: &str = "axiom-plan-exhausted";
const VERIFY_STEPS: u64 = 10_000_000;

#[derive(Clone, Copy, Debug, Default)]
pub struct PlanningEngine;

impl PlanningEngine {
    pub fn new() -> Self {
        PlanningEngine
    }

    fn source(problem: &Problem) -> Result<(&str, &str), String> {
        match problem {
            Problem::Planning { domain, problem } => Ok((domain, problem)),
            _ => Err("planning engine received a non-planning problem".into()),
        }
    }

    fn task(&self, problem: &Problem) -> Result<PlanningTask, Outcome> {
        let (domain, source) = Self::source(problem).map_err(Outcome::error)?;
        pddl::parse_task(domain, source).map_err(|e| match e {
            PddlError::Unsupported(m) => Outcome::unsupported(m),
            PddlError::Limit(m) => Outcome::resource_limit(m),
            PddlError::Malformed(m) => Outcome::error(m),
        })
    }
}

impl Engine for PlanningEngine {
    fn capabilities(&self) -> Capabilities {
        Capabilities::new("axiom-strips-bfs", env!("CARGO_PKG_VERSION"))
            .handles(ProblemKind::Planning)
            .fragment("untyped finite STRIPS")
            .fragment("negative preconditions and delete effects")
            .guarantee(Guarantee::Sound)
            .guarantee(Guarantee::Deterministic)
            .guarantee(Guarantee::EvidenceChecked)
            .limit("no typing, equality, numeric fluents, conditional effects, or costs")
            .limit("grounding, state, and expansion caps")
    }

    fn solve(&mut self, problem: &Problem, budget: &mut Budget) -> Outcome {
        let start = Instant::now();
        let task = match self.task(problem) {
            Ok(t) => t,
            Err(o) => return o,
        };
        let result = planner::plan(&task, budget, planner::Limits::default());
        let stats = Stats::new(budget.spent(), start.elapsed().as_millis() as u64)
            .with("expanded", result.expanded)
            .with("states", result.states as u64)
            .with("ground_actions", result.ground_actions as u64);
        match result.status {
            PlanStatus::Found(plan) => {
                let payload = format!(
                    "length={};states={};expanded={};plan={}",
                    plan.actions.len(),
                    result.states,
                    result.expanded,
                    planner::plan_text(&plan)
                );
                Outcome::definite(Verdict::Found, Evidence::new(PLAN_KIND, payload), stats)
            }
            PlanStatus::Impossible => {
                let payload = format!(
                    "states={};expanded={};ground_actions={}",
                    result.states, result.expanded, result.ground_actions
                );
                Outcome::definite(
                    Verdict::Impossible,
                    Evidence::new(EXHAUSTED_KIND, payload),
                    stats,
                )
            }
            PlanStatus::Limit(m) => Outcome::resource_limit(m).with_stats(stats),
        }
    }

    fn verify(&self, problem: &Problem, outcome: &Outcome) -> Result<(), VerifyError> {
        if !outcome.verdict.is_definite() {
            if outcome.evidence.is_some() {
                return Err(VerifyError::InvalidEvidence(
                    "inconclusive planning outcomes must not carry evidence".into(),
                ));
            }
            return Ok(());
        }
        let task = pddl::parse_task(
            Self::source(problem).map_err(VerifyError::Malformed)?.0,
            Self::source(problem).map_err(VerifyError::Malformed)?.1,
        )
        .map_err(|e| VerifyError::Malformed(e.to_string()))?;
        let evidence = outcome
            .evidence
            .as_ref()
            .ok_or(VerifyError::MissingEvidence)?;
        match outcome.verdict {
            Verdict::Found => {
                if evidence.kind != PLAN_KIND {
                    return Err(VerifyError::InvalidEvidence(
                        "wrong plan evidence kind".into(),
                    ));
                }
                let fields = fields(&evidence.payload)?;
                let length: usize = fields
                    .get("length")
                    .ok_or_else(|| VerifyError::InvalidEvidence("missing length".into()))?
                    .parse()
                    .map_err(|_| VerifyError::InvalidEvidence("bad length".into()))?;
                let text = fields
                    .get("plan")
                    .ok_or_else(|| VerifyError::InvalidEvidence("missing plan".into()))?;
                let actions =
                    planner::parse_plan_text(text).map_err(VerifyError::InvalidEvidence)?;
                if actions.len() != length {
                    return Err(VerifyError::Mismatch {
                        expected: length.to_string(),
                        found: actions.len().to_string(),
                    });
                }
                planner::validate_actions(&task, &actions).map_err(VerifyError::InvalidEvidence)?;
                Ok(())
            }
            Verdict::Impossible => {
                if evidence.kind != EXHAUSTED_KIND {
                    return Err(VerifyError::InvalidEvidence(
                        "wrong exhaustion evidence kind".into(),
                    ));
                }
                let mut budget = Budget::steps(VERIFY_STEPS);
                let again = planner::plan(&task, &mut budget, planner::Limits::default());
                match again.status {
                    PlanStatus::Impossible => Ok(()),
                    PlanStatus::Limit(m) => Err(VerifyError::ResourceLimit(m)),
                    PlanStatus::Found(_) => Err(VerifyError::Mismatch {
                        expected: "impossible".into(),
                        found: "found a plan".into(),
                    }),
                }
            }
            _ => Err(VerifyError::Unsupported(
                "planning engine only produces Found and Impossible".into(),
            )),
        }
    }
}

fn fields(payload: &str) -> Result<std::collections::BTreeMap<&str, &str>, VerifyError> {
    let mut out = std::collections::BTreeMap::new();
    for f in payload.split(';') {
        let (k, v) = f
            .split_once('=')
            .ok_or_else(|| VerifyError::InvalidEvidence(format!("bad field {f:?}")))?;
        if out.insert(k, v).is_some() {
            return Err(VerifyError::InvalidEvidence(format!("duplicate field {k}")));
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    const DOMAIN: &str = r#"
        (define (domain move)
          (:predicates (at ?x ?y) (connected ?x ?y))
          (:constants item)
          (:action move
            :parameters (?from ?to)
            :precondition (and (at item ?from) (connected ?from ?to))
            :effect (and (not (at item ?from)) (at item ?to))))
    "#;

    const PROBLEM: &str = r#"
        (define (problem p)
          (:domain move)
          (:objects a b)
          (:init (at item a) (connected a b))
          (:goal (at item b)))
    "#;

    fn p(problem: &str) -> Problem {
        Problem::planning(DOMAIN, problem)
    }

    #[test]
    fn finds_and_verifies_a_plan() {
        let p = p(PROBLEM);
        let mut e = PlanningEngine::new();
        let out = e.solve(&p, &mut Budget::steps(1_000_000));
        assert_eq!(out.verdict, Verdict::Found, "{out:?}");
        e.verify(&p, &out).unwrap();
    }

    #[test]
    fn proves_impossibility_by_exhaustion() {
        let problem = r#"
            (define (problem p) (:domain move) (:objects a b c)
              (:init (at item a) (connected a b)) (:goal (at item c)))
        "#;
        let p = p(problem);
        let mut e = PlanningEngine::new();
        let out = e.solve(&p, &mut Budget::steps(1_000_000));
        assert_eq!(out.verdict, Verdict::Impossible, "{out:?}");
        e.verify(&p, &out).unwrap();
    }

    #[test]
    fn an_empty_plan_is_valid() {
        let problem = r#"
            (define (problem p) (:domain move) (:objects a)
              (:init (at item a)) (:goal (at item a)))
        "#;
        let p = p(problem);
        let mut e = PlanningEngine::new();
        let out = e.solve(&p, &mut Budget::steps(10_000));
        assert_eq!(out.verdict, Verdict::Found);
        e.verify(&p, &out).unwrap();
    }

    #[test]
    fn tampered_plan_is_rejected() {
        let p = p(PROBLEM);
        let mut e = PlanningEngine::new();
        let out = e.solve(&p, &mut Budget::steps(1_000_000));
        let mut bad = out;
        bad.evidence = Some(Evidence::new(
            PLAN_KIND,
            "length=1;states=1;expanded=1;plan=move(b,a)",
        ));
        assert!(e.verify(&p, &bad).is_err());
    }

    #[test]
    fn typed_input_is_unsupported() {
        let d = "(define (domain d) (:requirements :typing) (:predicates (p ?x)))";
        let p = Problem::planning(d, "(define (problem q) (:domain d) (:init) (:goal (and)))");
        let mut e = PlanningEngine::new();
        let out = e.solve(&p, &mut Budget::steps(1000));
        assert_eq!(out.verdict, Verdict::Unsupported);
    }
}
