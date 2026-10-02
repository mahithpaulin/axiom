//! # axiom -- a general symbolic reasoning engine
//!
//! One intermediate representation, several solvers, machine-checkable proofs.
//!
//! ## The architecture in one paragraph
//!
//! The **logical exterior** accepts a problem (a set of facts and rules, a set of
//! constraints, a state-transition system, a goal) and compiles it into the
//! **logical IR** -- a stratified rule program over hash-consed terms. The
//! **logical core** knows nothing about any particular problem domain: it
//! computes the least model, answers queries, runs goal-directed resolution, and
//! emits derivations. Every definite answer comes with a proof object that a
//! separate checker re-verifies from the rules alone, without consulting any
//! state the search produced.
//!
//! ## Layout
//!
//! | Module | Role |
//! |---|---|
//! | [`hash`] | fast hasher used by every internal table |
//! | [`symbol`] | name interning; `u32` everywhere after load |
//! | [`term`] | hash-consed term/atom arena, 16 B per node |
//! | [`subst`] | union-find unification, trail, term resolution |
//! | [`db`] | extensional database and indexes |
//! | [`program`] | rules, literals, stratification, the exterior-side builder |
//! | [`proof`] | derivation records and check errors |
//! | [`check`] | independent proof checking |
//! | [`solver`] | the solver object; public API surface |
//! | [`solver_fwd`] | semi-naive bottom-up evaluation |
//! | [`solver_bwd`] | depth-bounded SLD, `prove`, `query` |
//! | [`exterior`] | text surface syntax and parsers |
//! | [`status`] | the honesty contract: `Status` and `Exhausted` |
//! | [`budget`] | resource limits |
//!
//! ## What this crate does and does not do
//!
//! Stage 1 implements **stratified Datalog**: facts, rules with positive and
//! stratified-negated bodies, function symbols in rule heads handled by
//! resolution rather than saturation, and complete least-model computation. It is
//! complete for that fragment and says so in its `Status`; outside it, it returns
//! `Unknown` or `Exhausted` rather than guessing. Constraints, arithmetic theories,
//! planning, search and strategy selection are specified in docs/ROADMAP.md and are
//! **not** implemented yet. See docs/KNOWN_LIMITATIONS.md.
//!
//! ## Example
//!
//! ```
//! use axiom::{exterior, Budget, Solver, Status};
//!
//! // 1. The problem, in the exterior's surface syntax.
//! let src = "\
//! edge(a, b).
//! edge(b, c).
//! path(X, Y) :- edge(X, Y).
//! path(X, Z) :- path(X, Y), edge(Y, Z).
//! ?- path(a, c).
//! ";
//!
//! // 2. Compiled to the logical IR. Names become symbol ids; terms become
//! //    hash-consed arena nodes. The core sees no domain concepts at all.
//! let parsed = exterior::parse(src).unwrap();
//! let goal = parsed.queries[0];
//!
//! // 3. The core computes the least model.
//! let mut solver = Solver::new(parsed.program);
//! let mut budget = Budget::steps(1_000_000);
//! let sat = solver.least_model(&mut budget).expect("within budget");
//! assert_eq!(sat.idb_facts, 3, "path/2 gains path(a,b), path(b,c), path(a,c)");
//!
//! // 4. Answer with a proof, then re-check it without consulting the search.
//! let out = solver.prove(goal, &mut budget);
//! assert_eq!(out.status, Status::Proved);
//! let proof = out.proof.expect("a definite status must carry a proof");
//! assert!(solver.verify(&proof).is_ok(), "the proof must re-derive independently");
//! assert!(solver.proof_size(&proof) >= 1);
//! ```

pub mod budget;
pub mod check;
pub mod db;
pub mod exterior;
pub mod hash;
pub mod program;
pub mod proof;
pub mod solver;
pub mod solver_bwd;
pub mod solver_fwd;
pub mod status;
pub mod subst;
pub mod symbol;
pub mod term;

pub use budget::Budget;
pub use program::{Builder, Literal, Program, ProgramError, Rule, RuleId};
pub use proof::{CheckErr, DerivId, Derivation, Proof, Saturation};
pub use solver::{Answer, Outcome, QueryOutcome, Solver, Stats};
pub use status::{Exhausted, Status};
pub use term::{TermId, TermStore};

#[cfg(test)]
mod prelude {
    //! Convenience for building programs in tests and examples.
    pub use crate::program::{Builder, Literal};
}

/// Compile-time check that the two promises in the charter which can be checked
/// mechanically are actually true. Each is a real test in `tests/`, and this
/// keeps them visible at the crate root.
#[cfg(test)]
mod contract {
    use super::*;

    /// A proved answer must survive an independent check.
    #[test]
    fn proved_answers_verify() {
        let (prog, goal) = super::tests_fixtures::transitive_closure_program();
        let mut s = Solver::new(prog);
        let mut b = Budget::unlimited();
        let out = s.prove(goal, &mut b);
        assert_eq!(out.status, Status::Proved);
        let proof = out.proof.expect("proved status requires a proof");
        assert!(s.verify(&proof).is_ok(), "{:?}", s.verify(&proof));
    }

    /// An inconclusive answer must never carry a proof.
    #[test]
    fn inconclusive_answers_carry_no_proof() {
        let (prog, goal) = super::tests_fixtures::transitive_closure_program();
        let mut s = Solver::new(prog);
        let mut b = Budget::steps(1); // guaranteed to run out
        let out = s.prove(goal, &mut b);
        if out.status.is_inconclusive() {
            assert!(out.proof.is_none());
        }
    }
}

#[cfg(test)]
pub(crate) mod tests_fixtures {
    use super::*;

    /// `path(X,Y) :- edge(X,Y). path(X,Z) :- path(X,Y), edge(Y,Z).`
    /// plus a three-node chain, and the goal `path(a,c)`.
    pub fn transitive_closure_program() -> (Program, TermId) {
        let mut b = Builder::new();
        b.fact_n("edge", &["a", "b"]);
        b.fact_n("edge", &["b", "c"]);
        let x = b.var("X");
        let y = b.var("Y");
        let z = b.var("Z");
        let h1 = b.atom("path", 2, &[x, y]);
        let l1 = b.pos("edge", 2, &[x, y]);
        b.rule(h1, vec![l1]);
        let h2 = b.atom("path", 2, &[x, z]);
        let p1 = b.pos("path", 2, &[x, y]);
        let e1 = b.pos("edge", 2, &[y, z]);
        b.rule(h2, vec![p1, e1]);
        let goal = b.goal_n("path", &["a", "c"]);
        let prog = b.build().unwrap();
        (prog, goal)
    }
}
