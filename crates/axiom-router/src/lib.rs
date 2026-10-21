//! Axiom v4 cross-domain router.
//!
//! [`Router::standard`] registers the four v4 engines. Routing is by declared
//! [`ProblemKind`](axiom_core::ProblemKind), with first-registered-wins among
//! engines that claim the same kind. Every definite answer is handed back to the
//! producing engine's independent verifier before the router returns it; a
//! verification failure is an explicit error, not a downgraded verdict.
//!
//! # Example
//!
//! ```
//! use axiom::Budget;
//! use axiom_core::Problem;
//! use axiom_router::Router;
//!
//! let mut r = Router::standard();
//! let p = Problem::fol("axiom P(a). goal P(a).");
//! let out = r.solve(&p, &mut Budget::steps(1_000_000)).unwrap();
//! assert_eq!(out.outcome.verdict, axiom_core::Verdict::Proved);
//! ```

use axiom::Budget;
use axiom_core::{EngineRegistry, Problem, RouteError, RoutedOutcome};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RouterError {
    Route(RouteError),
    Verification { engine: String, message: String },
}

impl fmt::Display for RouterError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RouterError::Route(e) => write!(f, "routing failed: {e}"),
            RouterError::Verification { engine, message } => {
                write!(
                    f,
                    "engine {engine} produced unverifiable evidence: {message}"
                )
            }
        }
    }
}

impl std::error::Error for RouterError {}

impl From<RouteError> for RouterError {
    fn from(e: RouteError) -> Self {
        RouterError::Route(e)
    }
}

pub struct Router {
    registry: EngineRegistry,
}

impl Router {
    pub fn new() -> Self {
        Router {
            registry: EngineRegistry::new(),
        }
    }

    /// The standard v4 bundle. Engine order is deterministic.
    pub fn standard() -> Self {
        let mut r = Router::new();
        r.registry.register(axiom_core::DatalogEngine::new());
        r.registry.register(axiom_asp::AspEngine::new());
        r.registry.register(axiom_prover::FolEngine::new());
        r.registry.register(axiom_planning::PlanningEngine::new());
        r
    }

    pub fn register<E: axiom_core::Engine + 'static>(&mut self, engine: E) -> &mut Self {
        self.registry.register(engine);
        self
    }

    pub fn capabilities(&self) -> Vec<axiom_core::Capabilities> {
        self.registry.engines()
    }

    pub fn trace(&self) -> &[axiom_core::RouteRecord] {
        self.registry.trace()
    }

    /// Solve one problem and independently verify a definite outcome.
    pub fn solve(
        &mut self,
        problem: &Problem,
        budget: &mut Budget,
    ) -> Result<RoutedOutcome, RouterError> {
        let routed = self.registry.solve(problem, budget)?;
        if routed.outcome.verdict.is_definite() {
            if let Err(e) = self
                .registry
                .verify(&routed.engine, problem, &routed.outcome)
            {
                return Err(RouterError::Verification {
                    engine: routed.engine,
                    message: e.to_string(),
                });
            }
        }
        Ok(routed)
    }

    /// Solve several problems in order, sharing one budget. Stops at the first
    /// routing or verification error.
    pub fn solve_all(
        &mut self,
        problems: &[Problem],
        budget: &mut Budget,
    ) -> Result<Vec<RoutedOutcome>, RouterError> {
        let mut out = Vec::with_capacity(problems.len());
        for p in problems {
            out.push(self.solve(p, budget)?);
        }
        Ok(out)
    }
}

impl Default for Router {
    fn default() -> Self {
        Router::standard()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axiom_core::Verdict;

    const DOMAIN: &str = r#"
        (define (domain d)
          (:predicates (p) (q))
          (:action go :parameters () :precondition (p) :effect (q)))
    "#;
    const PDDL: &str = r#"
        (define (problem p) (:domain d) (:objects) (:init (p)) (:goal (q)))
    "#;

    #[test]
    fn every_v4_domain_routes_and_verifies() {
        let mut r = Router::standard();
        let problems = vec![
            Problem::datalog(
                "edge(a,b). edge(b,c). path(X,Y) :- edge(X,Y). \
                 path(X,Z) :- path(X,Y), edge(Y,Z).",
                Some("path(a,c)".into()),
            ),
            Problem::asp("{ p }. :- p.", 0),
            Problem::fol("axiom P(a) -> Q(a). axiom P(a). goal Q(a)."),
            Problem::planning(DOMAIN, PDDL),
        ];
        let mut b = Budget::steps(5_000_000);
        let out = r.solve_all(&problems, &mut b).unwrap();
        assert_eq!(out.len(), 4);
        assert_eq!(out[0].outcome.verdict, Verdict::Proved);
        assert_eq!(out[1].outcome.verdict, Verdict::Found);
        assert_eq!(out[2].outcome.verdict, Verdict::Proved);
        assert_eq!(out[3].outcome.verdict, Verdict::Found);
        assert_eq!(r.trace().len(), 4);
        assert_eq!(r.capabilities().len(), 4);
    }

    #[test]
    fn unknown_kind_is_an_explicit_route_error() {
        let mut r = Router::new();
        let mut b = Budget::steps(10);
        assert!(matches!(
            r.solve(&Problem::datalog("p.", None), &mut b),
            Err(RouterError::Route(RouteError::NoEngine(_)))
        ));
    }

    #[test]
    fn malformed_input_is_not_a_found_verdict() {
        // A malformed ASP problem is an error, not a Found verdict.
        let mut r = Router::standard();
        let mut b = Budget::steps(10_000);
        let out = r.solve(&Problem::asp("p(", 0), &mut b).unwrap();
        assert_eq!(out.outcome.verdict, Verdict::Error);
    }
}
