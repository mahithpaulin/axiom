//! Derivation records and the status of a check.
//!
//! A `Derivation` is deliberately **self-contained**: it names a rule, the
//! instantiation of that rule's variables, and the resolved conclusion and
//! premises. It does not hold node ids into the solver's mutable arena, no
//! back-pointers into search state, and nothing about how it was found. A proof
//! is therefore checkable by code that never ran the search, which is the whole
//! point of keeping generation and checking separate.

use crate::program::{Literal, RuleId};
use crate::term::TermId;

pub type DerivId = u32;

/// One forward-chaining inference.
#[derive(Clone)]
pub struct Derivation {
    pub rule: RuleId,
    /// The resolved, ground conclusion atom.
    pub concl: TermId,
    /// Resolved body literals, in rule body order -- *all* of them, so the
    /// checker replays the inference exactly rather than trusting the order the
    /// join happened to visit.
    pub body: Vec<Literal>,
    /// Instantiation of the rule's local variables as `(local var id, ground
    /// term)`. Keyed by local id rather than by arena node so the record is
    /// stable under any renaming the solver performed internally.
    pub inst: Vec<(u32, TermId)>,
}

/// One backward-resolution inference.
#[derive(Clone)]
pub struct ResolutionStep {
    /// Rule applied, with its own variable space.
    pub rule: RuleId,
    /// The goal literal this rule was resolved against.
    pub goal: Literal,
    /// Resolved conclusion of the rule head.
    pub concl: Literal,
    /// Substitution from the rule's local variables to the caller's variables.
    pub inst: Vec<(u32, TermId)>,
    pub premises: Vec<u32>,
}

#[derive(Clone, Default)]
pub struct Proof {
    /// Top-level goal the proof is for.
    pub goal: TermId,
    /// Root forward derivation, when the proof came from saturation.
    pub root: Option<DerivId>,
    /// Backward resolution steps, in application order, when applicable.
    pub steps: Vec<ResolutionStep>,
    /// Certificate for a negative answer: the saturated closure was computed to
    /// completion. `closure_hash` fingerprints the full IDB closure so a checker
    /// can confirm it re-derived exactly this set.
    pub saturation: Option<Saturation>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Saturation {
    pub rounds: u32,
    pub idb_facts: u64,
    pub closure_hash: u64,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CheckErr {
    /// The atom has no seed fact and no derivation. A claim without support.
    Unsupported { atom: TermId },
    /// The conclusion does not follow from the rule and its instantiation.
    ConclusionMismatch { deriv: u32 },
    /// A body literal does not match the recorded premise.
    PremiseMismatch { deriv: u32, index: usize },
    /// A negative premise is actually derivable: the derivation is invalid
    /// under stratified negation.
    NegativeHolds { deriv: u32, index: usize },
    /// The instantiation is missing a rule variable, duplicates one, or binds a
    /// variable to a term containing that variable.
    BadInstantiation { deriv: u32 },
    /// A rule id that does not exist.
    NoSuchRule { deriv: u32 },
    /// A derivation cycle, which would otherwise make the checker loop.
    Cycle { deriv: u32 },
    /// The recorded goal is not the thing the checker was asked about.
    GoalMismatch,
}

impl core::fmt::Display for CheckErr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            CheckErr::Unsupported { atom } => {
                write!(f, "atom {atom} has no seed fact and no derivation")
            }
            CheckErr::ConclusionMismatch { deriv } => {
                write!(f, "derivation {deriv}: conclusion does not follow")
            }
            CheckErr::PremiseMismatch { deriv, index } => {
                write!(
                    f,
                    "derivation {deriv}: body literal {index} does not match premise"
                )
            }
            CheckErr::NegativeHolds { deriv, index } => {
                write!(
                    f,
                    "derivation {deriv}: negated literal {index} is derivable"
                )
            }
            CheckErr::BadInstantiation { deriv } => {
                write!(f, "derivation {deriv}: malformed instantiation")
            }
            CheckErr::NoSuchRule { deriv } => write!(f, "derivation {deriv}: no such rule"),
            CheckErr::Cycle { deriv } => write!(f, "derivation {deriv}: proof cycle"),
            CheckErr::GoalMismatch => write!(f, "proof goal does not match the query"),
        }
    }
}

impl core::error::Error for CheckErr {}
