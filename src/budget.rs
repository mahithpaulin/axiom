//! Resource limits.
//!
//! Every unbounded loop in the engine -- saturation rounds, search nodes, proof
//! depth -- is gated here. This is not defensive decoration: forward chaining
//! over rules with function symbols, and backward search without a depth bound,
//! are both non-terminating on inputs a user can trivially write. A reasoning
//! engine that hangs on `p :- not p.` is a denial-of-service bug.
//!
//! **Step budgets are the reproducible ones.** Time budgets are wall-clock and
//! therefore machine-dependent, so benchmarks use step budgets exclusively; see
//! docs/PERFORMANCE.md. Every reported result records which budget bound it.

use crate::status::Exhausted;
use std::time::Instant;

pub struct Budget {
    pub max_steps: u64,
    pub max_time_ms: u64,
    start: Instant,
    steps: u64,
}

impl Budget {
    /// Deterministic: identical on every machine, so results are comparable.
    pub fn steps(max_steps: u64) -> Self {
        Budget {
            max_steps,
            max_time_ms: u64::MAX,
            start: Instant::now(),
            steps: 0,
        }
    }

    pub fn with_time_ms(max_steps: u64, max_time_ms: u64) -> Self {
        Budget {
            max_steps,
            max_time_ms,
            start: Instant::now(),
            steps: 0,
        }
    }

    /// Unlimited; only for tests that have been argued to terminate.
    pub fn unlimited() -> Self {
        Budget {
            max_steps: u64::MAX,
            max_time_ms: u64::MAX,
            start: Instant::now(),
            steps: 0,
        }
    }

    /// Charge n units of work. Time is only sampled every 4096 charges so that
    /// the check does not dominate the loop it guards.
    #[inline]
    pub fn charge(&mut self, n: u64) -> Result<(), Exhausted> {
        self.steps += n;
        if self.steps > self.max_steps {
            return Err(Exhausted::Steps);
        }
        if self.max_time_ms != u64::MAX && self.steps & 0xFFF == 0 {
            if self.start.elapsed().as_millis() as u64 > self.max_time_ms {
                return Err(Exhausted::Time);
            }
        }
        Ok(())
    }

    #[inline]
    pub fn spent(&self) -> u64 {
        self.steps
    }
    pub fn elapsed_ms(&self) -> u64 {
        self.start.elapsed().as_millis() as u64
    }
    /// Why this budget will next refuse, for honest error reporting.
    pub fn nearest_bound(&self) -> Option<Exhausted> {
        if self.steps > self.max_steps {
            Some(Exhausted::Steps)
        } else if self.max_time_ms != u64::MAX && self.elapsed_ms() > self.max_time_ms {
            Some(Exhausted::Time)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn step_budget_is_enforced() {
        let mut b = Budget::steps(10);
        for _ in 0..10 {
            assert!(b.charge(1).is_ok());
        }
        assert_eq!(b.charge(1), Err(Exhausted::Steps));
        assert_eq!(b.spent(), 11);
    }

    #[test]
    fn charge_can_overshoot() {
        let mut b = Budget::steps(10);
        assert_eq!(b.charge(1000), Err(Exhausted::Steps));
    }

    #[test]
    fn unlimited_never_refuses() {
        let mut b = Budget::unlimited();
        for _ in 0..1000 {
            assert!(b.charge(1_000_000).is_ok());
        }
    }
}
