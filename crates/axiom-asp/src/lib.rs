//! Axiom v4 answer-set programming.
//!
//! Supported fragment:
//!
//! * normal rules with default negation;
//! * choice rules with one or more head atoms;
//! * integrity constraints;
//! * finite Herbrand grounding over the constants appearing in the program;
//! * exhaustive stable-model enumeration under a deterministic atom cap.
//!
//! Not supported: aggregates, cardinality constraints, function symbols,
//! optimisation, `#external`, and `#include`. Those are rejected or reported as
//! unsupported, never interpreted as something else.
//!
//! # Example
//!
//! ```
//! use axiom::Budget;
//! use axiom_asp::{Engine, Problem};
//!
//! let mut e = axiom_asp::AspEngine::new();
//! let p = Problem::asp("{ p }. :- p.", 0);
//! let out = e.solve(&p, &mut Budget::steps(1_000_000));
//! assert_eq!(out.verdict, axiom_core::Verdict::Found);
//! e.verify(&p, &out).unwrap();
//! ```

pub mod ground;
pub mod stable;
pub mod syntax;

use axiom::Budget;
use axiom_core::{
    Capabilities, Evidence, Guarantee, Outcome, ProblemKind, Stats, Verdict, VerifyError,
};
use ground::{GAtom, GroundProgram, MAX_UNIVERSE};
use stable::{EnumError, Enumeration};
use std::collections::BTreeSet;
use std::time::Instant;

pub use axiom_core::{Engine, Problem};
pub use ground::GroundError;
pub use stable::ModelError;
pub use syntax::ParseError;

const VERIFY_STEPS: u64 = 200_000_000;

/// The answer-set engine.
#[derive(Clone, Copy, Debug, Default)]
pub struct AspEngine;

impl AspEngine {
    pub fn new() -> Self {
        AspEngine
    }

    fn parse_problem(problem: &Problem) -> Result<(String, usize), String> {
        match problem {
            Problem::Asp { source, max_models } => Ok((source.clone(), *max_models)),
            _ => Err("ASP engine received a non-ASP problem".into()),
        }
    }

    fn ground_source(&self, source: &str, budget: &mut Budget) -> Result<GroundProgram, Outcome> {
        let program = syntax::parse(source).map_err(|e| {
            if e.message.contains("unsafe") {
                Outcome::unsupported(format!("outside the safe ASP fragment: {e}"))
            } else {
                Outcome::error(format!("ASP parse error: {e}"))
            }
        })?;
        ground::ground(&program, budget).map_err(|e| match e {
            GroundError::Unsafe(m) => Outcome::unsupported(format!("unsafe program: {m}")),
            GroundError::Limit(m) => Outcome::resource_limit(m),
            GroundError::Budget(m) => Outcome::resource_limit(m),
        })
    }

    fn enumerate(
        &self,
        gp: &GroundProgram,
        max_models: usize,
        budget: &mut Budget,
    ) -> Result<Enumeration, Outcome> {
        match stable::enumerate(gp, max_models, budget) {
            Ok(e) => Ok(e),
            Err(EnumError::TooLarge(n)) => Err(Outcome::resource_limit(format!(
                "ground universe has {n} atoms; enumeration is capped at {MAX_UNIVERSE}"
            ))),
            Err(EnumError::Budget(m)) => Err(Outcome::resource_limit(m)),
        }
    }

    fn evidence(gp: &GroundProgram, e: &Enumeration) -> Evidence {
        let models = e
            .models
            .iter()
            .map(stable::model_text)
            .collect::<Vec<_>>()
            .join("|");
        Evidence::new(
            "axiom-asp-models",
            format!(
                "complete={};count={};candidates={};stable_checks={};universe={};models={}",
                e.complete,
                e.models.len(),
                e.candidates_checked,
                e.stable_checks,
                gp.universe.len(),
                models
            ),
        )
    }

    fn stats(budget: &Budget, start: Instant, e: &Enumeration) -> Stats {
        Stats::new(budget.spent(), start.elapsed().as_millis() as u64)
            .with("candidates", e.candidates_checked)
            .with("stable_checks", e.stable_checks)
            .with("models", e.models.len() as u64)
    }

    /// Decode and re-verify the stable models carried by an ASP outcome.
    ///
    /// This is the supported boundary for cross-engine pipelines: callers get
    /// structured [`GAtom`]s only after the evidence has been checked against a
    /// fresh grounding and enumeration.
    pub fn models(
        &self,
        problem: &Problem,
        outcome: &Outcome,
    ) -> Result<Vec<BTreeSet<GAtom>>, VerifyError> {
        let evidence = outcome
            .evidence
            .as_ref()
            .ok_or(VerifyError::MissingEvidence)?;
        if evidence.kind != "axiom-asp-models" {
            return Err(VerifyError::InvalidEvidence(format!(
                "unexpected evidence kind {}",
                evidence.kind
            )));
        }
        Engine::verify(self, problem, outcome)?;
        Ok(parse_evidence(&evidence.payload)?.models)
    }
}

fn parse_gatom(s: &str) -> Option<GAtom> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }
    if let Some(open) = s.find('(') {
        if !s.ends_with(')') {
            return None;
        }
        let pred = &s[..open];
        let inner = &s[open + 1..s.len() - 1];
        let args = if inner.is_empty() {
            Vec::new()
        } else {
            inner.split(',').map(|x| x.trim().to_string()).collect()
        };
        if pred.is_empty() {
            return None;
        }
        Some(GAtom::new(pred, args))
    } else {
        Some(GAtom::new(s, Vec::new()))
    }
}

fn parse_model(text: &str) -> Result<BTreeSet<GAtom>, VerifyError> {
    let mut out = BTreeSet::new();
    if text.trim() == "{}" {
        return Ok(out);
    }
    for a in text.split_whitespace() {
        let atom = parse_gatom(a)
            .ok_or_else(|| VerifyError::InvalidEvidence(format!("bad ASP atom {a:?}")))?;
        if !out.insert(atom) {
            return Err(VerifyError::InvalidEvidence(
                "duplicate atom in model".into(),
            ));
        }
    }
    Ok(out)
}

struct EvidenceData {
    complete: bool,
    count: usize,
    candidates: u64,
    stable_checks: u64,
    universe: usize,
    models: Vec<BTreeSet<GAtom>>,
}

fn parse_evidence(payload: &str) -> Result<EvidenceData, VerifyError> {
    let mut complete = None;
    let mut count = None;
    let mut candidates = None;
    let mut stable_checks = None;
    let mut universe = None;
    let mut models_text = None;
    for field in payload.split(';') {
        let Some((k, v)) = field.split_once('=') else {
            return Err(VerifyError::InvalidEvidence(format!("bad field {field:?}")));
        };
        match k {
            "complete" => complete = Some(v == "true"),
            "count" => {
                count = Some(
                    v.parse()
                        .map_err(|_| VerifyError::InvalidEvidence("bad count".into()))?,
                )
            }
            "candidates" => {
                candidates = Some(
                    v.parse()
                        .map_err(|_| VerifyError::InvalidEvidence("bad candidates".into()))?,
                )
            }
            "stable_checks" => {
                stable_checks = Some(
                    v.parse()
                        .map_err(|_| VerifyError::InvalidEvidence("bad stable_checks".into()))?,
                )
            }
            "universe" => {
                universe = Some(
                    v.parse()
                        .map_err(|_| VerifyError::InvalidEvidence("bad universe".into()))?,
                )
            }
            "models" => models_text = Some(v),
            _ => return Err(VerifyError::InvalidEvidence(format!("unknown field {k}"))),
        }
    }
    let complete =
        complete.ok_or_else(|| VerifyError::InvalidEvidence("missing complete".into()))?;
    let count = count.ok_or_else(|| VerifyError::InvalidEvidence("missing count".into()))?;
    let candidates =
        candidates.ok_or_else(|| VerifyError::InvalidEvidence("missing candidates".into()))?;
    let stable_checks = stable_checks
        .ok_or_else(|| VerifyError::InvalidEvidence("missing stable_checks".into()))?;
    let universe =
        universe.ok_or_else(|| VerifyError::InvalidEvidence("missing universe".into()))?;
    let text = models_text.ok_or_else(|| VerifyError::InvalidEvidence("missing models".into()))?;
    let models = if text.is_empty() {
        Vec::new()
    } else {
        text.split('|')
            .map(parse_model)
            .collect::<Result<Vec<_>, _>>()?
    };
    if models.len() != count {
        return Err(VerifyError::InvalidEvidence(format!(
            "count {count} does not match {} models",
            models.len()
        )));
    }
    Ok(EvidenceData {
        complete,
        count,
        candidates,
        stable_checks,
        universe,
        models,
    })
}

impl Engine for AspEngine {
    fn capabilities(&self) -> Capabilities {
        Capabilities::new("axiom-asp", env!("CARGO_PKG_VERSION"))
            .handles(ProblemKind::Asp)
            .fragment("normal rules with default negation")
            .fragment("choice rules and integrity constraints")
            .fragment("finite Herbrand grounding; no function symbols")
            .guarantee(Guarantee::Sound)
            .guarantee(Guarantee::CompleteForFragment)
            .guarantee(Guarantee::Deterministic)
            .guarantee(Guarantee::EvidenceChecked)
            .limit("exhaustive enumeration is capped at 22 ground atoms")
            .limit("no aggregates, cardinality bounds, optimisation, or functions")
    }

    fn solve(&mut self, problem: &Problem, budget: &mut Budget) -> Outcome {
        let start = Instant::now();
        let (source, max_models) = match Self::parse_problem(problem) {
            Ok(v) => v,
            Err(e) => return Outcome::error(e),
        };
        let gp = match self.ground_source(&source, budget) {
            Ok(g) => g,
            Err(o) => return o,
        };
        let e = match self.enumerate(&gp, max_models, budget) {
            Ok(e) => e,
            Err(o) => return o,
        };
        let verdict = if e.models.is_empty() && e.complete {
            Verdict::Impossible
        } else {
            Verdict::Found
        };
        let mut out = Outcome::new(
            verdict,
            Some(Self::evidence(&gp, &e)),
            Self::stats(budget, start, &e),
        );
        if !e.complete {
            out.notes.push(format!(
                "enumeration stopped at the model cap ({} models); this is not a complete count",
                e.models.len()
            ));
        }
        if e.models.is_empty() {
            out.notes
                .push("no stable model exists in the declared finite fragment".into());
        }
        out
    }

    fn verify(&self, problem: &Problem, outcome: &Outcome) -> Result<(), VerifyError> {
        if !outcome.verdict.is_definite() {
            return Ok(());
        }
        let evidence = outcome
            .evidence
            .as_ref()
            .ok_or(VerifyError::MissingEvidence)?;
        if evidence.kind != "axiom-asp-models" {
            return Err(VerifyError::InvalidEvidence(format!(
                "unexpected evidence kind {}",
                evidence.kind
            )));
        }
        let parsed = parse_evidence(&evidence.payload)?;
        let (source, max_models) = Self::parse_problem(problem).map_err(VerifyError::Malformed)?;
        let mut budget = Budget::steps(VERIFY_STEPS);
        let gp = self
            .ground_source(&source, &mut budget)
            .map_err(|o| VerifyError::Malformed(o.notes.join("; ")))?;
        if gp.universe.len() != parsed.universe {
            return Err(VerifyError::InvalidEvidence("universe size changed".into()));
        }
        for m in &parsed.models {
            stable::validate_model(&gp, m)
                .map_err(|e| VerifyError::InvalidEvidence(e.to_string()))?;
        }
        let fresh = self
            .enumerate(&gp, max_models, &mut budget)
            .map_err(|o| VerifyError::ResourceLimit(o.notes.join("; ")))?;
        let fresh_evidence = Self::evidence(&gp, &fresh);
        if fresh_evidence != *evidence {
            return Err(VerifyError::Mismatch {
                expected: evidence.payload.clone(),
                found: fresh_evidence.payload,
            });
        }
        if parsed.complete && parsed.models.len() != fresh.models.len() {
            return Err(VerifyError::Mismatch {
                expected: parsed.count.to_string(),
                found: fresh.models.len().to_string(),
            });
        }
        let _ = (parsed.candidates, parsed.stable_checks);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn solve(src: &str, max: usize) -> Outcome {
        let mut e = AspEngine::new();
        let p = Problem::asp(src, max);
        e.solve(&p, &mut Budget::steps(10_000_000))
    }

    #[test]
    fn stable_models_verify_independently() {
        let p = Problem::asp("p :- not q. q :- not p.", 0);
        let mut e = AspEngine::new();
        let o = e.solve(&p, &mut Budget::steps(10_000_000));
        assert_eq!(o.verdict, Verdict::Found);
        e.verify(&p, &o).unwrap();
    }

    #[test]
    fn unsat_constraint_is_impossible_only_after_complete_enumeration() {
        let p = Problem::asp("p. :- p.", 0);
        let mut e = AspEngine::new();
        let o = e.solve(&p, &mut Budget::steps(10_000_000));
        assert_eq!(o.verdict, Verdict::Impossible);
        e.verify(&p, &o).unwrap();
    }

    #[test]
    fn truncation_is_not_reported_as_complete() {
        let o = solve("{a; b; c}.", 2);
        assert_eq!(o.verdict, Verdict::Found);
        assert!(o.notes.iter().any(|n| n.contains("not a complete count")));
    }

    #[test]
    fn malformed_source_is_an_error() {
        let o = solve("p(X) :- not q(X).", 0);
        assert_eq!(o.verdict, Verdict::Unsupported);
    }

    #[test]
    fn models_decode_only_after_verification() {
        let p = Problem::asp("{ p }. { q }.", 0);
        let mut e = AspEngine::new();
        let out = e.solve(&p, &mut Budget::steps(1_000_000));
        let models = e.models(&p, &out).unwrap();
        assert_eq!(models.len(), 4);
        assert!(models.iter().any(|m| m.len() == 2));
        let mut bad = out;
        bad.evidence = Some(Evidence::new("axiom-asp-models", "count=0;models="));
        assert!(e.models(&p, &bad).is_err());
    }
}
