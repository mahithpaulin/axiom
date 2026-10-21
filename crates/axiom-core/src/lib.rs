//! Axiom v4 common infrastructure.
//!
//! This crate is deliberately small. It defines the contract every engine
//! implements and the vocabulary callers use to route work across engines:
//!
//! * [`Problem`] — a source-level request, not a solver-specific type;
//! * [`Engine`] — `capabilities`, `solve`, `verify`;
//! * [`Outcome`] — a verdict plus optional serialised evidence;
//! * [`EngineRegistry`] — deterministic routing and a trace of what ran.
//!
//! The central rule is that a definite verdict must carry checkable evidence.
//! `Unknown`, `Unsupported` and `ResourceLimit` are first-class outcomes; no
//! engine may collapse them into a negative answer.
//!
//! The Datalog adapter is included here because it is the reference adapter for
//! the existing crate. Other engines live in their own workspace crates and
//! depend on this one, never the reverse.

use axiom::Budget;
use std::fmt;

pub mod datalog;

pub use datalog::DatalogEngine;

/// The kind of source-level problem.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProblemKind {
    Datalog,
    Asp,
    Fol,
    Planning,
}

impl ProblemKind {
    pub fn as_str(self) -> &'static str {
        match self {
            ProblemKind::Datalog => "datalog",
            ProblemKind::Asp => "asp",
            ProblemKind::Fol => "fol",
            ProblemKind::Planning => "planning",
        }
    }
}

impl fmt::Display for ProblemKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A source-level problem. Engines parse only the variant they support.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Problem {
    Datalog {
        source: String,
        goal: Option<String>,
    },
    Asp {
        source: String,
        max_models: usize,
    },
    Fol {
        source: String,
    },
    Planning {
        domain: String,
        problem: String,
    },
}

impl Problem {
    pub fn kind(&self) -> ProblemKind {
        match self {
            Problem::Datalog { .. } => ProblemKind::Datalog,
            Problem::Asp { .. } => ProblemKind::Asp,
            Problem::Fol { .. } => ProblemKind::Fol,
            Problem::Planning { .. } => ProblemKind::Planning,
        }
    }

    pub fn datalog(source: impl Into<String>, goal: Option<String>) -> Self {
        Problem::Datalog {
            source: source.into(),
            goal,
        }
    }

    pub fn asp(source: impl Into<String>, max_models: usize) -> Self {
        Problem::Asp {
            source: source.into(),
            max_models,
        }
    }

    pub fn fol(source: impl Into<String>) -> Self {
        Problem::Fol {
            source: source.into(),
        }
    }

    pub fn planning(domain: impl Into<String>, problem: impl Into<String>) -> Self {
        Problem::Planning {
            domain: domain.into(),
            problem: problem.into(),
        }
    }
}

/// A solver verdict. The names intentionally mirror the responsibility boundary
/// in `axiom::Status`, with two engine-level distinctions:
///
/// * `Unsupported` means the request is outside the declared fragment;
/// * `ResourceLimit` means a deterministic or wall-clock budget stopped work.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Verdict {
    Proved,
    Refuted,
    Found,
    Impossible,
    Unknown,
    Unsupported,
    ResourceLimit,
    Error,
}

impl Verdict {
    pub fn is_definite(self) -> bool {
        matches!(
            self,
            Verdict::Proved | Verdict::Refuted | Verdict::Found | Verdict::Impossible
        )
    }

    pub fn is_inconclusive(self) -> bool {
        matches!(
            self,
            Verdict::Unknown | Verdict::Unsupported | Verdict::ResourceLimit | Verdict::Error
        )
    }

    pub fn as_str(self) -> &'static str {
        match self {
            Verdict::Proved => "proved",
            Verdict::Refuted => "refuted",
            Verdict::Found => "found",
            Verdict::Impossible => "impossible",
            Verdict::Unknown => "unknown",
            Verdict::Unsupported => "unsupported",
            Verdict::ResourceLimit => "resource-limit",
            Verdict::Error => "error",
        }
    }
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A serialised artifact an independent checker can consume.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Evidence {
    pub kind: String,
    pub payload: String,
}

impl Evidence {
    pub fn new(kind: impl Into<String>, payload: impl Into<String>) -> Self {
        Evidence {
            kind: kind.into(),
            payload: payload.into(),
        }
    }
}

/// Deterministic and wall-clock accounting returned by an engine.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Stats {
    pub steps: u64,
    pub elapsed_ms: u64,
    pub detail: Vec<(String, u64)>,
}

impl Stats {
    pub fn new(steps: u64, elapsed_ms: u64) -> Self {
        Stats {
            steps,
            elapsed_ms,
            detail: Vec::new(),
        }
    }

    pub fn with(mut self, name: impl Into<String>, value: u64) -> Self {
        self.detail.push((name.into(), value));
        self
    }

    pub fn get(&self, name: &str) -> Option<u64> {
        self.detail.iter().find(|(k, _)| k == name).map(|(_, v)| *v)
    }
}

/// The result of one engine call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Outcome {
    pub verdict: Verdict,
    pub evidence: Option<Evidence>,
    pub stats: Stats,
    pub notes: Vec<String>,
}

impl Outcome {
    pub fn new(verdict: Verdict, evidence: Option<Evidence>, stats: Stats) -> Self {
        Outcome {
            verdict,
            evidence,
            stats,
            notes: Vec::new(),
        }
    }

    pub fn definite(verdict: Verdict, evidence: Evidence, stats: Stats) -> Self {
        debug_assert!(verdict.is_definite(), "definite outcome required");
        Outcome::new(verdict, Some(evidence), stats)
    }

    pub fn unsupported(message: impl Into<String>) -> Self {
        Outcome::new(Verdict::Unsupported, None, Stats::default()).note(message)
    }

    pub fn resource_limit(message: impl Into<String>) -> Self {
        Outcome::new(Verdict::ResourceLimit, None, Stats::default()).note(message)
    }

    pub fn unknown(message: impl Into<String>) -> Self {
        Outcome::new(Verdict::Unknown, None, Stats::default()).note(message)
    }

    pub fn error(message: impl Into<String>) -> Self {
        Outcome::new(Verdict::Error, None, Stats::default()).note(message)
    }

    pub fn note(mut self, message: impl Into<String>) -> Self {
        self.notes.push(message.into());
        self
    }

    pub fn with_stats(mut self, stats: Stats) -> Self {
        self.stats = stats;
        self
    }

    pub fn with_evidence(mut self, evidence: Evidence) -> Self {
        self.evidence = Some(evidence);
        self
    }
}

/// Why independent verification failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    Unsupported(String),
    Malformed(String),
    MissingEvidence,
    InvalidEvidence(String),
    Mismatch { expected: String, found: String },
    ResourceLimit(String),
    Internal(String),
}

impl fmt::Display for VerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VerifyError::Unsupported(m) => write!(f, "unsupported: {m}"),
            VerifyError::Malformed(m) => write!(f, "malformed: {m}"),
            VerifyError::MissingEvidence => f.write_str("outcome has no checkable evidence"),
            VerifyError::InvalidEvidence(m) => write!(f, "invalid evidence: {m}"),
            VerifyError::Mismatch { expected, found } => {
                write!(f, "mismatch: expected {expected}, found {found}")
            }
            VerifyError::ResourceLimit(m) => write!(f, "verification limit: {m}"),
            VerifyError::Internal(m) => write!(f, "internal verification error: {m}"),
        }
    }
}

impl std::error::Error for VerifyError {}

/// A promise an engine makes. These are claims about the declared fragment, not
/// blanket statements about all inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Guarantee {
    Sound,
    CompleteForFragment,
    Deterministic,
    EvidenceChecked,
}

impl fmt::Display for Guarantee {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Guarantee::Sound => "sound",
            Guarantee::CompleteForFragment => "complete-for-fragment",
            Guarantee::Deterministic => "deterministic",
            Guarantee::EvidenceChecked => "evidence-checked",
        })
    }
}

/// A machine-readable capability declaration.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Capabilities {
    pub engine: String,
    pub version: String,
    pub problems: Vec<ProblemKind>,
    pub fragments: Vec<String>,
    pub guarantees: Vec<Guarantee>,
    pub limits: Vec<String>,
}

impl Capabilities {
    pub fn new(engine: impl Into<String>, version: impl Into<String>) -> Self {
        Capabilities {
            engine: engine.into(),
            version: version.into(),
            problems: Vec::new(),
            fragments: Vec::new(),
            guarantees: Vec::new(),
            limits: Vec::new(),
        }
    }

    pub fn handles(mut self, kind: ProblemKind) -> Self {
        if !self.problems.contains(&kind) {
            self.problems.push(kind);
        }
        self
    }

    pub fn fragment(mut self, fragment: impl Into<String>) -> Self {
        self.fragments.push(fragment.into());
        self
    }

    pub fn guarantee(mut self, guarantee: Guarantee) -> Self {
        if !self.guarantees.contains(&guarantee) {
            self.guarantees.push(guarantee);
        }
        self
    }

    pub fn limit(mut self, limit: impl Into<String>) -> Self {
        self.limits.push(limit.into());
        self
    }

    pub fn supports(&self, kind: ProblemKind) -> bool {
        self.problems.contains(&kind)
    }
}

/// Every reasoning engine implements this contract.
pub trait Engine {
    fn capabilities(&self) -> Capabilities;

    fn solve(&mut self, problem: &Problem, budget: &mut Budget) -> Outcome;

    /// Re-check the evidence in `outcome` against `problem`.
    ///
    /// Implementations must not trust a verdict merely because it came from
    /// their own solver. A definite verdict without valid evidence is an error.
    fn verify(&self, problem: &Problem, outcome: &Outcome) -> Result<(), VerifyError>;
}

/// One routing decision, retained for the cross-domain trace.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RouteRecord {
    pub engine: String,
    pub problem: ProblemKind,
    pub verdict: Verdict,
    pub steps: u64,
}

/// A selected engine and its result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoutedOutcome {
    pub engine: String,
    pub outcome: Outcome,
}

/// Routing failure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RouteError {
    NoEngine(ProblemKind),
    UnknownEngine(String),
}

impl fmt::Display for RouteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RouteError::NoEngine(k) => write!(f, "no registered engine handles {k}"),
            RouteError::UnknownEngine(n) => write!(f, "unknown engine {n}"),
        }
    }
}

impl std::error::Error for RouteError {}

/// Deterministic capability-based registry.
///
/// Selection is first-registered-wins among engines that declare support. The
/// registry records every decision, so a coordinator can explain which engine
/// produced which artifact. There is no fallback that silently maps an
/// unsupported problem to a different logic.
#[derive(Default)]
pub struct EngineRegistry {
    engines: Vec<Box<dyn Engine>>,
    trace: Vec<RouteRecord>,
}

impl EngineRegistry {
    pub fn new() -> Self {
        EngineRegistry::default()
    }

    pub fn register<E: Engine + 'static>(&mut self, engine: E) -> &mut Self {
        self.engines.push(Box::new(engine));
        self
    }

    pub fn engines(&self) -> Vec<Capabilities> {
        self.engines.iter().map(|e| e.capabilities()).collect()
    }

    pub fn trace(&self) -> &[RouteRecord] {
        &self.trace
    }

    pub fn clear_trace(&mut self) {
        self.trace.clear();
    }

    pub fn solve(
        &mut self,
        problem: &Problem,
        budget: &mut Budget,
    ) -> Result<RoutedOutcome, RouteError> {
        let idx = self
            .engines
            .iter()
            .position(|e| e.capabilities().supports(problem.kind()))
            .ok_or(RouteError::NoEngine(problem.kind()))?;
        let engine = self.engines[idx].capabilities().engine;
        let outcome = self.engines[idx].solve(problem, budget);
        self.trace.push(RouteRecord {
            engine: engine.clone(),
            problem: problem.kind(),
            verdict: outcome.verdict,
            steps: outcome.stats.steps,
        });
        Ok(RoutedOutcome { engine, outcome })
    }

    pub fn verify(
        &self,
        engine: &str,
        problem: &Problem,
        outcome: &Outcome,
    ) -> Result<(), VerifyError> {
        let e = self
            .engines
            .iter()
            .find(|e| e.capabilities().engine == engine)
            .ok_or_else(|| VerifyError::Unsupported(format!("unknown engine {engine}")))?;
        e.verify(problem, outcome)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axiom::Budget;

    struct Echo {
        name: &'static str,
        kind: ProblemKind,
    }

    impl Engine for Echo {
        fn capabilities(&self) -> Capabilities {
            Capabilities::new(self.name, "0")
                .handles(self.kind)
                .fragment("echo")
                .guarantee(Guarantee::Sound)
        }

        fn solve(&mut self, _problem: &Problem, _budget: &mut Budget) -> Outcome {
            Outcome::new(
                Verdict::Found,
                Some(Evidence::new("echo", "ok")),
                Stats::new(1, 0),
            )
        }

        fn verify(&self, _problem: &Problem, outcome: &Outcome) -> Result<(), VerifyError> {
            match &outcome.evidence {
                Some(e) if e.kind == "echo" && e.payload == "ok" => Ok(()),
                Some(_) => Err(VerifyError::InvalidEvidence("bad echo".into())),
                None => Err(VerifyError::MissingEvidence),
            }
        }
    }

    #[test]
    fn routing_is_deterministic_and_traced() {
        let mut r = EngineRegistry::new();
        r.register(Echo {
            name: "first",
            kind: ProblemKind::Datalog,
        });
        r.register(Echo {
            name: "second",
            kind: ProblemKind::Datalog,
        });
        let p = Problem::datalog("", None);
        let mut b = Budget::steps(10);
        let a = r.solve(&p, &mut b).unwrap();
        assert_eq!(a.engine, "first");
        assert_eq!(r.trace().len(), 1);
        assert!(r.verify("first", &p, &a.outcome).is_ok());
    }

    #[test]
    fn unhandled_problem_is_an_explicit_error() {
        let mut r = EngineRegistry::new();
        let mut b = Budget::steps(10);
        assert_eq!(
            r.solve(&Problem::fol(""), &mut b).unwrap_err(),
            RouteError::NoEngine(ProblemKind::Fol)
        );
    }

    #[test]
    fn inconclusive_outcomes_are_not_definite() {
        assert!(!Verdict::Unknown.is_definite());
        assert!(!Verdict::ResourceLimit.is_definite());
        assert!(Verdict::Refuted.is_definite());
    }
}
