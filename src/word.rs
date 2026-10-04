//! Word-problem front end (V2 R4/R3 adapter).
//!
//! A word problem names quantities ("alice", "bob") and relates them with
//! linear (in)equalities over small finite ranges. This adapter compiles that
//! vocabulary into a [`CspProblem`]: each relation becomes one or two
//! `LinearLe` constraints (equalities split into both directions), so the
//! solver and its checker see plain arithmetic, never prose.
//!
//! Range discipline: every quantity declares `[lo, hi]` up front, and the
//! width is capped at 10 000 values. Unbounded integers belong to the theory
//! layer (`crate::theory`, ROADMAP II2b), not to finite-domain search.

use crate::budget::Budget;
use crate::csp::{Constraint, CspOutcome, CspProblem, VarId};
use crate::status::Exhausted;

/// A named-quantity problem under construction.
#[derive(Clone, Debug, Default)]
pub struct WordModel {
    prob: CspProblem,
    names: Vec<(String, VarId)>,
}

impl WordModel {
    pub fn new() -> Self {
        WordModel {
            prob: CspProblem::new(),
            names: Vec::new(),
        }
    }

    /// Declare a quantity ranging over `[lo, hi]` (inclusive).
    pub fn quantity(&mut self, name: &str, lo: i32, hi: i32) -> Result<VarId, String> {
        if self.names.iter().any(|(n, _)| n == name) {
            return Err(format!("duplicate quantity '{name}'"));
        }
        if lo > hi {
            return Err(format!("empty range [{lo}, {hi}] for '{name}'"));
        }
        if hi as i64 - lo as i64 > 10_000 {
            return Err(format!(
                "range [{lo}, {hi}] for '{name}' exceeds 10000 values"
            ));
        }
        let id = self.prob.var(name, (lo..=hi).collect());
        self.names.push((name.to_string(), id));
        Ok(id)
    }

    /// Look up a declared quantity.
    pub fn id(&self, name: &str) -> Result<VarId, String> {
        self.names
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, v)| *v)
            .ok_or_else(|| format!("unknown quantity '{name}'"))
    }

    fn coeffs(&self, terms: &[(&str, i64)]) -> Result<Vec<(VarId, i64)>, String> {
        terms
            .iter()
            .map(|(name, k)| self.id(name).map(|v| (v, *k)))
            .collect()
    }

    /// `sum(k[i] * terms[i]) <= bound`.
    pub fn sum_le(&mut self, terms: &[(&str, i64)], bound: i64) -> Result<(), String> {
        let coeffs = self.coeffs(terms)?;
        self.prob.constrain(Constraint::LinearLe { coeffs, bound });
        Ok(())
    }

    /// `sum(k[i] * terms[i]) == bound` (two opposing bounds).
    pub fn sum_eq(&mut self, terms: &[(&str, i64)], bound: i64) -> Result<(), String> {
        let coeffs = self.coeffs(terms)?;
        self.prob.constrain(Constraint::LinearLe {
            coeffs: coeffs.clone(),
            bound,
        });
        let neg: Vec<(VarId, i64)> = coeffs.into_iter().map(|(v, k)| (v, -k)).collect();
        self.prob.constrain(Constraint::LinearLe {
            coeffs: neg,
            bound: -bound,
        });
        Ok(())
    }

    /// `a < b` (strict).
    pub fn less_than(&mut self, a: &str, b: &str) -> Result<(), String> {
        let (x, y) = (self.id(a)?, self.id(b)?);
        self.prob.constrain(Constraint::LessThan(x, y));
        Ok(())
    }

    /// `a == c`.
    pub fn equals_const(&mut self, a: &str, c: i32) -> Result<(), String> {
        let x = self.id(a)?;
        self.prob.constrain(Constraint::ValueEq(x, c));
        Ok(())
    }

    /// The compiled problem (for inspection and independent checking).
    pub fn problem(&self) -> &CspProblem {
        &self.prob
    }

    /// Solve and read back one quantity from a `Found` outcome.
    pub fn value_of(&self, out: &CspOutcome, name: &str) -> Option<i32> {
        let v = self.id(name).ok()?;
        out.assignment.get(v as usize).copied()
    }

    /// Solve through the finite-domain engine.
    pub fn solve(&self, budget: &mut Budget) -> Result<CspOutcome, Exhausted> {
        crate::csp::solve_csp(&self.prob, budget)
    }
}
