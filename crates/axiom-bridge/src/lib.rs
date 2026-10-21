//! Sound cross-domain pipelines built from checked engine outcomes.
//!
//! The first pipeline turns a selected stable model into additional planning
//! initial facts. It is deliberately narrow and explicit:
//!
//! 1. enumerate ASP stable models and verify the enumeration evidence;
//! 2. select one verified model;
//! 3. keep only atoms whose predicate and arity are declared by the PDDL
//!    domain, rejecting malformed shared facts and reporting ignored atoms;
//! 4. add the kept facts to the planning task's initial state;
//! 5. solve and independently verify the planning result against that exact
//!    translated task.
//!
//! The composition therefore proves a plan for the *combined* initial state.
//! It does not claim that the original planning problem, without the ASP
//! facts, has that plan, nor that the ASP model is uniquely determined.
//!
//! # Example
//!
//! ```
//! use axiom::Budget;
//! use axiom_bridge::{AspPlanningRequest, run_asp_to_planning};
//!
//! let domain = r#"
//!   (define (domain move)
//!     (:predicates (at ?x ?y) (connected ?x ?y))
//!     (:action move :parameters (?x ?from ?to)
//!       :precondition (and (at ?x ?from) (connected ?from ?to))
//!       :effect (and (not (at ?x ?from)) (at ?x ?to))))
//! "#;
//! let problem = r#"
//!   (define (problem p) (:domain move) (:objects item a b)
//!     (:init (connected a b)) (:goal (at item b)))
//! "#;
//! let request = AspPlanningRequest::new("at(item,a). connected(a,b).", domain, problem);
//! let out = run_asp_to_planning(&request, &mut Budget::steps(1_000_000)).unwrap();
//! assert_eq!(out.planning.verdict, axiom_core::Verdict::Found);
//! out.verify(&request).unwrap();
//! ```

use axiom::Budget;
use axiom_asp::ground::GAtom;
use axiom_asp::AspEngine;
use axiom_core::{Engine, Outcome, Problem, Verdict};
use axiom_planning::pddl::{self, FAtom, PlanningTask};
use axiom_planning::PlanningEngine;
use std::fmt;

/// A request to combine one selected ASP model with a STRIPS planning task.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AspPlanningRequest {
    pub asp_source: String,
    pub max_models: usize,
    pub model_index: usize,
    pub domain: String,
    pub problem: String,
}

impl AspPlanningRequest {
    pub fn new(
        asp_source: impl Into<String>,
        domain: impl Into<String>,
        problem: impl Into<String>,
    ) -> Self {
        AspPlanningRequest {
            asp_source: asp_source.into(),
            max_models: 64,
            model_index: 0,
            domain: domain.into(),
            problem: problem.into(),
        }
    }

    pub fn with_model_index(mut self, index: usize) -> Self {
        self.model_index = index;
        self
    }

    pub fn with_max_models(mut self, max_models: usize) -> Self {
        self.max_models = max_models;
        self
    }
}

/// Both stage outcomes plus the exact translation that connected them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BridgeOutcome {
    pub asp: Outcome,
    pub planning: Outcome,
    pub model_index: usize,
    pub injected: Vec<FAtom>,
    pub ignored: Vec<GAtom>,
    pub translated_task: PlanningTask,
}

impl BridgeOutcome {
    /// Run the request again and require the same translated task and planning
    /// evidence. This is a full recomputation, not a hash comparison.
    pub fn verify(&self, request: &AspPlanningRequest) -> Result<(), BridgeError> {
        let mut budget = Budget::steps(50_000_000);
        let fresh = request.run(&mut budget)?;
        if fresh.model_index != self.model_index
            || fresh.injected != self.injected
            || fresh.ignored != self.ignored
            || fresh.translated_task != self.translated_task
        {
            return Err(BridgeError::Verification(
                "translation changed on recomputation".into(),
            ));
        }
        if fresh.asp.verdict != self.asp.verdict || fresh.asp.evidence != self.asp.evidence {
            return Err(BridgeError::Verification(
                "ASP outcome changed on recomputation".into(),
            ));
        }
        if fresh.planning.verdict != self.planning.verdict
            || fresh.planning.evidence != self.planning.evidence
        {
            return Err(BridgeError::Verification(
                "planning outcome changed on recomputation".into(),
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BridgeError {
    Asp(String),
    NoModel { index: usize, count: usize },
    Planning(String),
    Translation(String),
    Verification(String),
}

impl fmt::Display for BridgeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BridgeError::Asp(m) => write!(f, "ASP stage failed: {m}"),
            BridgeError::NoModel { index, count } => {
                write!(
                    f,
                    "requested model {index}, but {count} models were produced"
                )
            }
            BridgeError::Planning(m) => write!(f, "planning stage failed: {m}"),
            BridgeError::Translation(m) => write!(f, "translation rejected: {m}"),
            BridgeError::Verification(m) => write!(f, "bridge verification failed: {m}"),
        }
    }
}

impl std::error::Error for BridgeError {}

impl AspPlanningRequest {
    /// Execute the pipeline under one shared budget.
    pub fn run(&self, budget: &mut Budget) -> Result<BridgeOutcome, BridgeError> {
        let asp_problem = Problem::asp(self.asp_source.clone(), self.max_models);
        let mut asp_engine = AspEngine::new();
        let asp = asp_engine.solve(&asp_problem, budget);
        match asp.verdict {
            Verdict::Found => {}
            Verdict::Impossible => {
                return Err(BridgeError::NoModel {
                    index: self.model_index,
                    count: 0,
                })
            }
            Verdict::Error | Verdict::Unsupported | Verdict::ResourceLimit | Verdict::Unknown => {
                return Err(BridgeError::Asp(asp.notes.join("; ")))
            }
            Verdict::Proved | Verdict::Refuted => {
                return Err(BridgeError::Asp(format!(
                    "ASP engine returned unexpected verdict {}",
                    asp.verdict
                )))
            }
        }
        let models = asp_engine
            .models(&asp_problem, &asp)
            .map_err(|e| BridgeError::Asp(e.to_string()))?;
        let model = models
            .get(self.model_index)
            .ok_or(BridgeError::NoModel {
                index: self.model_index,
                count: models.len(),
            })?
            .clone();

        let task = pddl::parse_task(&self.domain, &self.problem)
            .map_err(|e| BridgeError::Planning(e.to_string()))?;
        let mut injected = Vec::new();
        let mut ignored = Vec::new();
        for atom in model {
            let Some(&arity) = task.domain.predicates.get(&atom.predicate) else {
                ignored.push(atom);
                continue;
            };
            if arity != atom.args.len() {
                return Err(BridgeError::Translation(format!(
                    "ASP atom {atom} uses arity {}, but PDDL predicate {} has arity {arity}",
                    atom.args.len(),
                    atom.predicate
                )));
            }
            injected.push(FAtom::new(atom.predicate, atom.args));
        }
        injected.sort();
        injected.dedup();
        let translated_task = task
            .with_added_init(injected.clone())
            .map_err(BridgeError::Translation)?;

        let plan_engine = PlanningEngine::new();
        let planning = plan_engine.solve_task(&translated_task, budget);
        plan_engine
            .verify_task(&translated_task, &planning)
            .map_err(|e| BridgeError::Planning(e.to_string()))?;
        Ok(BridgeOutcome {
            asp,
            planning,
            model_index: self.model_index,
            injected,
            ignored,
            translated_task,
        })
    }
}

/// Convenience wrapper for the common case.
pub fn run_asp_to_planning(
    request: &AspPlanningRequest,
    budget: &mut Budget,
) -> Result<BridgeOutcome, BridgeError> {
    request.run(budget)
}

#[cfg(test)]
mod tests {
    use super::*;
    use axiom_core::Verdict;

    const DOMAIN: &str = r#"
        (define (domain move)
          (:predicates (at ?x ?y) (connected ?x ?y))
          (:action move
            :parameters (?x ?from ?to)
            :precondition (and (at ?x ?from) (connected ?from ?to))
            :effect (and (not (at ?x ?from)) (at ?x ?to))))
    "#;

    const PROBLEM: &str = r#"
        (define (problem p)
          (:domain move)
          (:objects item a b)
          (:init (connected a b))
          (:goal (at item b)))
    "#;

    fn request(source: &str) -> AspPlanningRequest {
        AspPlanningRequest::new(source, DOMAIN, PROBLEM)
    }

    #[test]
    fn stable_model_supplies_planning_init() {
        let req = request("at(item,a). connected(a,b). aux(a).");
        let mut b = Budget::steps(2_000_000);
        let out = req.run(&mut b).unwrap();
        assert_eq!(out.asp.verdict, Verdict::Found);
        assert_eq!(out.planning.verdict, Verdict::Found, "{:?}", out.planning);
        assert_eq!(out.injected.len(), 2);
        assert_eq!(out.ignored.len(), 1);
        assert_eq!(out.ignored[0].predicate, "aux");
        out.verify(&req).unwrap();
    }

    #[test]
    fn model_index_is_selected_deterministically() {
        let src =
            "at(item,a). at(item,b). connected(a,b). connected(b,a). { tag }. :- not at(item,a).";
        let req = request(src).with_model_index(1).with_max_models(16);
        let mut b = Budget::steps(4_000_000);
        let out = req.run(&mut b).unwrap();
        assert_eq!(out.model_index, 1);
        assert_eq!(out.planning.verdict, Verdict::Found);
        out.verify(&req).unwrap();
    }

    #[test]
    fn missing_model_is_explicit() {
        let req = request("at(item,a).").with_model_index(3);
        let mut b = Budget::steps(1_000_000);
        assert!(matches!(
            req.run(&mut b),
            Err(BridgeError::NoModel { index: 3, count: 1 })
        ));
    }

    #[test]
    fn wrong_shared_arity_is_rejected() {
        let req = request("at(item).");
        let mut b = Budget::steps(1_000_000);
        assert!(matches!(req.run(&mut b), Err(BridgeError::Translation(_))));
    }

    #[test]
    fn tampered_planning_evidence_is_rejected() {
        let req = request("at(item,a). connected(a,b).");
        let mut b = Budget::steps(2_000_000);
        let mut out = req.run(&mut b).unwrap();
        out.planning.evidence = Some(axiom_core::Evidence::new(
            "axiom-plan",
            "length=1;states=1;expanded=1;plan=move(item,b,a)",
        ));
        assert!(matches!(
            out.verify(&req),
            Err(BridgeError::Verification(_))
        ));
    }

    #[test]
    fn tampered_asp_evidence_is_rejected() {
        let req = request("at(item,a). connected(a,b).");
        let mut b = Budget::steps(2_000_000);
        let mut out = req.run(&mut b).unwrap();
        out.asp.evidence = Some(axiom_core::Evidence::new(
            "axiom-asp-models",
            "complete=true;count=1;candidates=1;stable_checks=1;universe=1;models={at(item,b)}",
        ));
        assert!(matches!(
            out.verify(&req),
            Err(BridgeError::Verification(_))
        ));
    }
}
