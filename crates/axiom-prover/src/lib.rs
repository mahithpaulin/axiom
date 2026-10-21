//! Axiom v4 first-order prover.
//!
//! Input is a small, explicit FOL syntax (`axiom`, `goal`, optional `pred`/`fun`
//! declarations). The prover negates the goal, converts the resulting set to
//! CNF with Skolemisation, runs bounded given-clause resolution with factoring,
//! and hands the resulting refutation to [`axiom_proof::check_resolution`].
//!
//! The prover never reports `Proved` without a kernel-checked empty clause.
//! Saturation and exhausted caps are `Unknown` and `ResourceLimit`; a failure to
//! find a refutation is never reported as `Refuted`.
//!
//! # Example
//!
//! ```
//! use axiom::Budget;
//! use axiom_prover::{Engine, FolEngine, Problem};
//!
//! let p = Problem::fol("axiom P(a) -> Q(a). axiom P(a). goal Q(a).");
//! let mut engine = FolEngine::new();
//! let out = engine.solve(&p, &mut Budget::steps(1_000_000));
//! assert_eq!(out.verdict, axiom_core::Verdict::Proved);
//! engine.verify(&p, &out).unwrap();
//! ```

pub mod cnf;
pub mod fol;
pub mod resolve;

use axiom::Budget;
use axiom_core::{
    Capabilities, Evidence, Guarantee, Outcome, ProblemKind, Stats, Verdict, VerifyError,
};
use axiom_proof::{check_resolution, KernelError, ResolutionProof};
use std::time::Instant;

pub use axiom_core::{Engine, Problem};
pub use cnf::CnfError;
pub use fol::{FolError, FolProblem};
pub use resolve::{Limits, SearchStatus};

const EVIDENCE_KIND: &str = "axiom-fol-resolution";

#[derive(Clone, Copy, Debug, Default)]
pub struct FolEngine;

impl FolEngine {
    pub fn new() -> Self {
        FolEngine
    }

    fn source(problem: &Problem) -> Result<&str, String> {
        match problem {
            Problem::Fol { source } => Ok(source),
            _ => Err("FOL engine received a non-FOL problem".into()),
        }
    }

    fn parse(&self, problem: &Problem) -> Result<FolProblem, Outcome> {
        let source = Self::source(problem).map_err(Outcome::error)?;
        fol::parse_problem(source).map_err(|e| {
            if e.to_string().contains("equality and arithmetic") {
                Outcome::unsupported(format!("outside the FOL fragment: {e}"))
            } else {
                Outcome::error(format!("FOL parse error: {e}"))
            }
        })
    }

    fn evidence(proof: &ResolutionProof) -> Evidence {
        Evidence::new(EVIDENCE_KIND, proof.to_text())
    }
}

impl Engine for FolEngine {
    fn capabilities(&self) -> Capabilities {
        Capabilities::new("axiom-fol-resolution", env!("CARGO_PKG_VERSION"))
            .handles(ProblemKind::Fol)
            .fragment("first-order formulas with predicate and function symbols")
            .fragment("bounded given-clause resolution with factoring")
            .guarantee(Guarantee::Sound)
            .guarantee(Guarantee::Deterministic)
            .guarantee(Guarantee::EvidenceChecked)
            .limit("no equality, arithmetic, sorts, or higher-order constructs")
            .limit("clause/selection/generation caps and a deterministic step budget")
    }

    fn solve(&mut self, problem: &Problem, budget: &mut Budget) -> Outcome {
        let start = Instant::now();
        let parsed = match self.parse(problem) {
            Ok(p) => p,
            Err(o) => return o,
        };
        let clauses = match cnf::clausal_form(&parsed.axioms, &parsed.goal) {
            Ok(c) => c,
            Err(CnfError::TooLarge(m)) => return Outcome::resource_limit(m),
            Err(e) => return Outcome::error(format!("CNF error: {e}")),
        };
        let result = resolve::search(clauses, budget, Limits::default());
        let stats = Stats::new(budget.spent(), start.elapsed().as_millis() as u64)
            .with("selected", result.selected)
            .with("generated", result.generated);
        match result.status {
            SearchStatus::Proved => {
                let Some(proof) = result.proof else {
                    return Outcome::error("internal prover error: proved without a proof")
                        .with_stats(stats);
                };
                if let Err(e) = check_resolution(&proof) {
                    return Outcome::error(format!("internal proof-kernel rejection: {e}"))
                        .with_stats(stats);
                }
                Outcome::definite(Verdict::Proved, Self::evidence(&proof), stats)
            }
            SearchStatus::Saturated => Outcome::unknown(
                "resolution saturated without an empty clause; validity was not established",
            )
            .with_stats(stats),
            SearchStatus::Limit(m) => Outcome::resource_limit(m).with_stats(stats),
        }
    }

    fn verify(&self, problem: &Problem, outcome: &Outcome) -> Result<(), VerifyError> {
        if outcome.verdict != Verdict::Proved {
            if outcome.evidence.is_some() {
                return Err(VerifyError::InvalidEvidence(
                    "non-definite FOL outcomes must not carry evidence".into(),
                ));
            }
            return Ok(());
        }
        let parsed = fol::parse_problem(Self::source(problem).map_err(VerifyError::Malformed)?)
            .map_err(|e| VerifyError::Malformed(e.to_string()))?;
        let clauses = cnf::clausal_form(&parsed.axioms, &parsed.goal)
            .map_err(|e| VerifyError::Malformed(e.to_string()))?;
        let evidence = outcome
            .evidence
            .as_ref()
            .ok_or(VerifyError::MissingEvidence)?;
        if evidence.kind != EVIDENCE_KIND {
            return Err(VerifyError::InvalidEvidence(format!(
                "wrong evidence kind {}",
                evidence.kind
            )));
        }
        let proof = ResolutionProof::from_text(&evidence.payload)
            .map_err(|e: KernelError| VerifyError::InvalidEvidence(e.to_string()))?;
        // Inputs must be drawn from the deterministic CNF of the problem. This
        // is what stops a valid-looking refutation from smuggling in an axiom.
        for step in &proof.clauses {
            if let axiom_proof::StepRule::Input = step.rule {
                if !clauses.iter().any(|c| c == &step.clause) {
                    return Err(VerifyError::InvalidEvidence(format!(
                        "input clause is not in the problem's CNF: {}",
                        step.clause.to_sexp().render()
                    )));
                }
            }
        }
        check_resolution(&proof).map_err(|e| VerifyError::InvalidEvidence(e.to_string()))?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn solve(src: &str) -> Outcome {
        let p = Problem::fol(src);
        let mut b = Budget::steps(2_000_000);
        let mut e = FolEngine::new();
        let out = e.solve(&p, &mut b);
        e.verify(&p, &out).unwrap();
        out
    }

    #[test]
    fn modus_ponens_is_proved_and_verified() {
        let out = solve("axiom P(a) -> Q(a). axiom P(a). goal Q(a).");
        assert_eq!(out.verdict, Verdict::Proved, "{out:?}");
        assert_eq!(out.evidence.as_ref().unwrap().kind, EVIDENCE_KIND);
    }

    #[test]
    fn universal_syllogism_is_proved() {
        let out = solve(
            "pred Man/1. pred Mortal/1. \
             axiom forall x. Man(x) -> Mortal(x). \
             axiom Man(socrates). \
             goal Mortal(socrates).",
        );
        assert_eq!(out.verdict, Verdict::Proved, "{out:?}");
    }

    #[test]
    fn a_non_theorem_is_unknown_not_refuted() {
        let out = solve("axiom P(a). goal Q(a).");
        assert_eq!(out.verdict, Verdict::Unknown, "{out:?}");
        assert!(out.evidence.is_none());
    }

    #[test]
    fn malformed_input_is_an_error() {
        let p = Problem::fol("axiom .");
        let mut b = Budget::steps(1_000);
        let out = FolEngine::new().solve(&p, &mut b);
        assert_eq!(out.verdict, Verdict::Error);
    }

    #[test]
    fn unsupported_equality_is_explicit() {
        let p = Problem::fol("axiom a = b. goal P(a).");
        let mut b = Budget::steps(1_000);
        let out = FolEngine::new().solve(&p, &mut b);
        assert_eq!(out.verdict, Verdict::Unsupported, "{out:?}");
    }

    #[test]
    fn tampered_evidence_is_rejected() {
        let p = Problem::fol("axiom P(a) -> Q(a). axiom P(a). goal Q(a).");
        let mut b = Budget::steps(2_000_000);
        let mut e = FolEngine::new();
        let out = e.solve(&p, &mut b);
        let mut bad = out.clone();
        bad.evidence = Some(Evidence::new(EVIDENCE_KIND, "(resolution-proof)"));
        assert!(e.verify(&p, &bad).is_err());
    }

    #[test]
    fn smuggled_input_is_rejected() {
        let p = Problem::fol("axiom P(a). goal Q(a).");
        let mut b = Budget::steps(2_000_000);
        let mut e = FolEngine::new();
        let out = e.solve(&p, &mut b);
        let mut proof = ResolutionProof::default();
        proof.clauses.push(axiom_proof::ProofClause {
            clause: axiom_proof::Clause::empty(),
            rule: axiom_proof::StepRule::Input,
        });
        let mut bad = out;
        bad.verdict = Verdict::Proved;
        bad.evidence = Some(Evidence::new(EVIDENCE_KIND, proof.to_text()));
        assert!(e.verify(&p, &bad).is_err());
    }
}
