//! Reference adapter for the existing `axiom` Datalog/SAT/theory crate.
//!
//! This adapter does not re-implement Datalog. It parses the existing exterior
//! syntax, runs the existing solver, and exposes the result through the common
//! v4 interface. Verification re-parses and re-runs with a fresh solver, checks
//! the returned proof, and compares the independently produced evidence. It does
//! not accept a verdict merely because the same process produced it.

use crate::{
    Capabilities, Engine, Evidence, Guarantee, Outcome, Problem, ProblemKind, Stats, Verdict,
    VerifyError,
};
use axiom::{exterior, Budget, ProofMode, Solver, Status, TermId};
use std::time::Instant;

const VERIFY_STEPS: u64 = 100_000_000;

#[derive(Debug)]
enum RunError {
    Malformed(String),
    Resource(String),
}

/// Adapter over the single-crate Axiom engine.
#[derive(Clone, Copy, Debug, Default)]
pub struct DatalogEngine;

impl DatalogEngine {
    pub fn new() -> Self {
        DatalogEngine
    }

    fn prepare(&self, problem: &Problem) -> Result<(Solver, Option<TermId>), String> {
        let (source, explicit_goal) = match problem {
            Problem::Datalog { source, goal } => (source, goal),
            _ => return Err("datalog engine received a non-Datalog problem".into()),
        };
        let combined = match explicit_goal {
            Some(g) => {
                let g = g
                    .trim()
                    .trim_start_matches("?-")
                    .trim()
                    .trim_end_matches('.');
                format!("{source}\n?- {g}.")
            }
            None => source.clone(),
        };
        let parsed = exterior::parse(&combined).map_err(|e| e.to_string())?;
        let goal = if explicit_goal.is_some() {
            parsed.queries.last().copied()
        } else {
            parsed.queries.first().copied()
        };
        Ok((Solver::new(parsed.program), goal))
    }

    fn status_verdict(status: Status) -> Verdict {
        match status {
            Status::Proved => Verdict::Proved,
            Status::Refuted => Verdict::Refuted,
            Status::Found => Verdict::Found,
            Status::Impossible => Verdict::Impossible,
            Status::Unknown => Verdict::Unknown,
            Status::Exhausted => Verdict::ResourceLimit,
        }
    }

    fn root_stats(stats: axiom::solver::Stats, steps: u64, elapsed_ms: u64) -> Stats {
        Stats::new(steps, elapsed_ms)
            .with("rounds", stats.rounds)
            .with("derivations", stats.derivations)
            .with("candidates", stats.candidates)
            .with("new_facts", stats.new_facts)
            .with("sld_steps", stats.sld_steps)
    }

    fn is_ground(solver: &mut Solver, goal: TermId) -> bool {
        // TermStore::is_ground takes &mut self because it reuses a scratch
        // buffer. Moving it out and back avoids owning a second arena just to
        // ask a read-only question.
        let mut store = std::mem::take(&mut solver.prog.store);
        let out = store.is_ground(goal);
        solver.prog.store = store;
        out
    }

    fn goal_text(solver: &Solver, goal: TermId) -> String {
        solver.prog.store.show(goal, &solver.prog.symbols)
    }

    fn closure_evidence(sat: &axiom::Saturation) -> Evidence {
        Evidence::new(
            "axiom-datalog-closure",
            format!(
                "verdict=found;rounds={};idb_facts={};closure_hash={}",
                sat.rounds, sat.idb_facts, sat.closure_hash
            ),
        )
    }

    fn prove_evidence(goal: &str, verdict: Verdict) -> Evidence {
        Evidence::new(
            "axiom-datalog-goal",
            format!("verdict={verdict};goal={goal}"),
        )
    }

    fn query_evidence(verdict: Verdict, answers: usize, hash: Option<u64>) -> Evidence {
        let hash = hash
            .map(|h| format!(";saturation_hash={h}"))
            .unwrap_or_default();
        Evidence::new(
            "axiom-datalog-query",
            format!("verdict={verdict};answers={answers}{hash}"),
        )
    }

    fn solve_once(
        &self,
        problem: &Problem,
        budget: &mut Budget,
    ) -> Result<(Solver, Option<TermId>, Verdict, Option<Evidence>), RunError> {
        let (mut solver, goal) = self.prepare(problem).map_err(RunError::Malformed)?;
        solver.set_proof_mode(ProofMode::Full);
        match goal {
            None => {
                let sat = solver
                    .least_model(budget)
                    .map_err(|e| RunError::Resource(format!("datalog closure stopped: {e}")))?;
                let ev = Self::closure_evidence(&sat);
                Ok((solver, None, Verdict::Found, Some(ev)))
            }
            Some(g) if Self::is_ground(&mut solver, g) => {
                let out = solver.prove(g, budget);
                let verdict = Self::status_verdict(out.status);
                let ev = if verdict.is_definite() {
                    let text = Self::goal_text(&solver, g);
                    Some(Self::prove_evidence(&text, verdict))
                } else {
                    None
                };
                Ok((solver, Some(g), verdict, ev))
            }
            Some(g) => {
                let q = solver.query(g, budget);
                let verdict = Self::status_verdict(q.status);
                let hash = q.saturation.as_ref().map(|s| s.closure_hash);
                let ev = if verdict.is_definite() {
                    Some(Self::query_evidence(verdict, q.answers.len(), hash))
                } else {
                    None
                };
                Ok((solver, Some(g), verdict, ev))
            }
        }
    }
}

impl Engine for DatalogEngine {
    fn capabilities(&self) -> Capabilities {
        Capabilities::new("axiom-datalog", env!("CARGO_PKG_VERSION"))
            .handles(ProblemKind::Datalog)
            .fragment("stratified Datalog with finite terms")
            .fragment("ground-safe negation; unsafe negation is rejected before solving")
            .guarantee(Guarantee::Sound)
            .guarantee(Guarantee::Deterministic)
            .guarantee(Guarantee::EvidenceChecked)
            .limit("function symbols in rule heads are backward-only and not saturated")
            .limit("verification re-runs the solver with a 100M-step budget")
    }

    fn solve(&mut self, problem: &Problem, budget: &mut Budget) -> Outcome {
        let start = Instant::now();
        let spent0 = budget.spent();
        let run = self.solve_once(problem, budget);
        let (solver, _, verdict, evidence) = match run {
            Ok(v) => v,
            Err(RunError::Malformed(e)) => return Outcome::error(e),
            Err(RunError::Resource(e)) => return Outcome::resource_limit(e),
        };
        let stats = Self::root_stats(
            solver.stats,
            budget.spent().saturating_sub(spent0),
            start.elapsed().as_millis() as u64,
        );
        let mut out = Outcome::new(verdict, evidence, stats);
        if verdict == Verdict::ResourceLimit {
            out.notes
                .push("the solver budget stopped the search; no negative claim is made".into());
        }
        out
    }

    fn verify(&self, problem: &Problem, outcome: &Outcome) -> Result<(), VerifyError> {
        let mut probe = DatalogEngine;
        let mut budget = Budget::steps(VERIFY_STEPS);
        let fresh = probe.solve(problem, &mut budget);
        if fresh.verdict != outcome.verdict {
            return Err(VerifyError::Mismatch {
                expected: outcome.verdict.as_str().into(),
                found: fresh.verdict.as_str().into(),
            });
        }
        if fresh.evidence != outcome.evidence {
            return Err(VerifyError::Mismatch {
                expected: format!("{:?}", outcome.evidence),
                found: format!("{:?}", fresh.evidence),
            });
        }
        if !outcome.verdict.is_definite() {
            return Ok(());
        }
        let (solver, goal) = self.prepare(problem).map_err(VerifyError::Malformed)?;
        // A closure certificate is checked by recomputing it; the fresh solve
        // above already did that and matched the serialised evidence.
        let Some(goal) = goal else {
            return Ok(());
        };
        let mut solver = solver;
        if Self::is_ground(&mut solver, goal) {
            let out = solver.prove(goal, &mut Budget::steps(VERIFY_STEPS));
            if Self::status_verdict(out.status) != outcome.verdict {
                return Err(VerifyError::Mismatch {
                    expected: outcome.verdict.as_str().into(),
                    found: Self::status_verdict(out.status).as_str().into(),
                });
            }
            if let Some(proof) = out.proof {
                solver
                    .verify(&proof)
                    .map_err(|e| VerifyError::InvalidEvidence(format!("{e:?}")))?;
            }
            Ok(())
        } else {
            let q = solver.query(goal, &mut Budget::steps(VERIFY_STEPS));
            if Self::status_verdict(q.status) != outcome.verdict {
                return Err(VerifyError::Mismatch {
                    expected: outcome.verdict.as_str().into(),
                    found: Self::status_verdict(q.status).as_str().into(),
                });
            }
            for answer in &q.answers {
                solver
                    .verify(&answer.proof)
                    .map_err(|e| VerifyError::InvalidEvidence(format!("{e:?}")))?;
            }
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn engine() -> DatalogEngine {
        DatalogEngine::new()
    }

    #[test]
    fn solves_and_verifies_a_ground_goal() {
        let src = "edge(a,b). edge(b,c). path(X,Y) :- edge(X,Y). \
                   path(X,Z) :- path(X,Y), edge(Y,Z).";
        let p = Problem::datalog(src, Some("path(a,c)".into()));
        let mut b = Budget::steps(1_000_000);
        let o = engine().solve(&p, &mut b);
        assert_eq!(o.verdict, Verdict::Proved, "{o:?}");
        engine().verify(&p, &o).unwrap();
    }

    #[test]
    fn malformed_input_is_an_error() {
        let p = Problem::datalog("p(", Some("p".into()));
        let mut b = Budget::steps(10);
        let o = engine().solve(&p, &mut b);
        assert_eq!(o.verdict, Verdict::Error);
    }

    #[test]
    fn closure_without_a_goal_is_found_not_proved() {
        let p = Problem::datalog("edge(a,b). edge(b,c).", None);
        let mut b = Budget::steps(1_000_000);
        let o = engine().solve(&p, &mut b);
        assert_eq!(o.verdict, Verdict::Found);
        engine().verify(&p, &o).unwrap();
    }
}
