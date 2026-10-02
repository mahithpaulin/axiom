//! The status contract.
//!
//! This type is the single most important honesty mechanism in the engine.
//!
//! The project's charter asks for a system that can solve "any logical game or
//! puzzle with sufficient compute". That is not literally achievable and it is
//! not merely a resource problem: general first-order validity is undecidable,
//! and many individually-encodable families (alternating-quantifier games,
//! planning with unbounded objects, many puzzles) sit above NP.
//!
//! The only defensible response is to make partial knowledge *representable in
//! the return type*, so that a caller cannot accidentally read failure as
//! falsity. `Unknown` and `Exhausted` are therefore not error paths; they are
//! first-class answers that must be surfaced by every solver, and there is no
//! constructor for "solved" that does not carry a checkable proof.
//!
//! Corroboration: the design mirrors the invariant adopted by the `z3rs` pure
//! Rust port of Z3 -- "soundness before completeness: a work budget (or an
//! undecided fragment) yields a sound `unknown`, never a wrong verdict".

use core::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum Status {
    /// The goal was derived. `Proof` is present and re-checkable.
    Proved,
    /// The goal's complement was derived, or the query space was shown empty.
    /// `Proof` is present and re-checkable.
    Refuted,
    /// A witness exists (model, plan, schedule) but optimality is not claimed.
    /// `Proof` certifies existence only.
    Found,
    /// A search ran to a fixpoint or an exhaustive point and found nothing,
    /// under a *complete* method for the fragment in question.
    Impossible,
    /// A resource budget (steps, time, depth, memory) stopped the search.
    /// Says nothing about satisfiability. Never collapse this into `Refuted`.
    Exhausted,
    /// An incomplete method could not decide. Says nothing either way.
    Unknown,
}

impl Status {
    /// True when the engine established something and can back it with a proof.
    pub fn is_definite(self) -> bool {
        matches!(
            self,
            Status::Proved | Status::Refuted | Status::Found | Status::Impossible
        )
    }
    /// True when the engine failed to establish anything. Callers must treat
    /// these as "no result", never as "no solution".
    pub fn is_inconclusive(self) -> bool {
        matches!(self, Status::Exhausted | Status::Unknown)
    }
    /// Whether a proof obligation is attached for this status.
    pub fn requires_proof(self) -> bool {
        matches!(
            self,
            Status::Proved | Status::Refuted | Status::Found | Status::Impossible
        )
    }
}

impl fmt::Display for Status {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Status::Proved => "proved",
            Status::Refuted => "refuted",
            Status::Found => "found",
            Status::Impossible => "impossible",
            Status::Exhausted => "exhausted",
            Status::Unknown => "unknown",
        };
        f.write_str(s)
    }
}

/// Why a budget stopped the search. Kept separate from `Status` so that the
/// caller can distinguish "we were too slow" from "the method cannot decide".
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Exhausted {
    /// Inference/step counter hit.
    Steps,
    /// Wall-clock deadline hit.
    Time,
    /// Proof-search depth bound hit.
    Depth,
    /// Term/atom count exceeded a configured arena ceiling.
    Memory,
    /// The exterior rejected the input; nothing was run.
    Malformed,
}

impl fmt::Display for Exhausted {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Exhausted::Steps => "step budget",
            Exhausted::Time => "time budget",
            Exhausted::Depth => "depth budget",
            Exhausted::Memory => "memory budget",
            Exhausted::Malformed => "malformed input",
        };
        f.write_str(s)
    }
}
