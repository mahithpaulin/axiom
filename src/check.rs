//! Independent proof checking.
//!
//! ## The design constraint that shapes this module
//!
//! The charter demands "differential tests against trusted implementations" and
//! that heuristic search never be its own evidence. Both are answered the same
//! way: **this module does not use `Subst`**. It re-implements instantiation
//! and pattern matching as a structural comparison against recorded atoms, over
//! a plain `FxHashMap<u32, TermId>` variable environment.
//!
//! That is deliberate duplication. A checker that shares the solver's
//! substitution routine cannot catch a bug in unification, which is the highest
//! value class of soundness bug in the engine. Two independent implementations
//! that must agree turn that bug class into a test failure rather than a silent
//! wrong proof. The cost is ~50 lines and one extra structural pass per
//! derivation, both measured (BENCHMARKS.md, `proof_check`).
//!
//! ## No allocation, no second store
//!
//! Comparing ids only works inside one `TermStore`, so an earlier draft that
//! built a parallel term store was unsound. Instead `matches` walks the rule
//! term and the recorded term in parallel, substituting from `env` on the fly.
//! It allocates nothing and needs only `&TermStore`, which means the checker can
//! run while the solver holds its store mutably.
//!
//! ## Two strengths, deliberately separate
//!
//! * `verify_shallow` -- accepts any atom in the fact database. O(1) and trusts
//!   the forward chainer.
//! * `verify` -- re-derives everything from program facts and rules. O(size of
//!   proof) and trusts nothing but the rule set. This is the default, because a
//!   check that trusts the component it is checking is not a check.
//!
//! ## Negative answers
//!
//! Refutation is not free. "The atom is absent from the least model" can only be
//! supported by showing the least model was actually computed, so
//! `verify_saturation` compares a fingerprint of the recomputed closure against
//! the recorded one. That relies on determinism, which the engine guarantees; a
//! determinism bug therefore surfaces as a *spurious check failure*, which is
//! the safe direction to fail.

use crate::db::Db;
use crate::hash::FxHashMap;
use crate::program::Program;
use crate::proof::{CheckErr, DerivId, Derivation, Proof, Saturation};
use crate::term::{TermId, TermStore, T_VAR};

const VISITING: u8 = 1;
const DONE: u8 = 2;

/// Is `t` free of variables? The term graph is acyclic by construction (the
/// occurs check guarantees it), so a plain walk terminates and needs no visited
/// set. Used to reject instantiations that leave a rule variable free.
fn ground(store: &TermStore, t: TermId) -> bool {
    let mut stack = vec![t];
    while let Some(x) = stack.pop() {
        if store.kind(x) == T_VAR {
            return false;
        }
        for &a in store.args(x) {
            stack.push(a);
        }
    }
    true
}

/// Does `t`, with `env` applied, denote the same thing as `target`?
///
/// A var in `t` must be bound in `env`; an unbound one makes the instantiation
/// incomplete and the answer is `false` (never a silent pass).
fn matches(store: &TermStore, t: TermId, env: &FxHashMap<u32, TermId>, target: TermId) -> bool {
    let e = match store.var_id(t) {
        Some(v) => match env.get(&v) {
            Some(&x) => x,
            None => return false,
        },
        None => t,
    };
    if store.kind(e) != store.kind(target) || store.sym(e) != store.sym(target) {
        return false;
    }
    let ea = store.args(e);
    let ta = store.args(target);
    if ea.len() != ta.len() {
        return false;
    }
    for i in 0..ea.len() {
        if !matches(store, ea[i], env, ta[i]) {
            return false;
        }
    }
    true
}

struct Checker<'a> {
    prog: &'a Program,
    db: &'a Db,
    derivs: &'a [Derivation],
    deriv_of: &'a FxHashMap<TermId, DerivId>,
    state: FxHashMap<DerivId, u8>,
}

impl<'a> Checker<'a> {
    fn atom_ok(&mut self, atom: TermId) -> Result<(), CheckErr> {
        if self.db.seed.contains(&atom) {
            return Ok(());
        }
        match self.deriv_of.get(&atom) {
            None => Err(CheckErr::Unsupported { atom }),
            Some(&d) => self.deriv(d),
        }
    }

    fn deriv(&mut self, d: DerivId) -> Result<(), CheckErr> {
        match self.state.get(&d) {
            Some(&VISITING) => return Err(CheckErr::Cycle { deriv: d }),
            Some(&DONE) => return Ok(()),
            _ => {}
        }
        self.state.insert(d, VISITING);

        let dv = match self.derivs.get(d as usize) {
            Some(v) => v.clone(),
            None => return Err(CheckErr::NoSuchRule { deriv: d }),
        };
        let rule = match self.prog.rules.get(dv.rule as usize) {
            Some(r) => r.clone(),
            None => return Err(CheckErr::NoSuchRule { deriv: d }),
        };

        // 1. The instantiation must bind every rule variable exactly once, to a
        //    ground term.
        let bad = || CheckErr::BadInstantiation { deriv: d };
        if dv.inst.len() != rule.local_vars.len() {
            return Err(bad());
        }
        let mut env: FxHashMap<u32, TermId> =
            FxHashMap::with_capacity_and_hasher(dv.inst.len(), Default::default());
        for (v, t) in &dv.inst {
            if env.insert(*v, *t).is_some() || !rule.local_vars.contains(v) {
                return Err(bad());
            }
            if !ground(&self.prog.store, *t) {
                return Err(bad());
            }
        }

        // 2. Applying the instantiation to the rule's *original* head and body
        //    must reproduce exactly what the solver recorded.
        let store = &self.prog.store;
        if !matches(store, rule.head, &env, dv.concl) {
            return Err(CheckErr::ConclusionMismatch { deriv: d });
        }
        if dv.body.len() != rule.body.len() {
            return Err(CheckErr::PremiseMismatch { deriv: d, index: 0 });
        }
        for (i, l) in rule.body.iter().enumerate() {
            let rec = dv.body[i];
            if rec.pos != l.pos || !matches(store, l.atom, &env, rec.atom) {
                return Err(CheckErr::PremiseMismatch { deriv: d, index: i });
            }
        }

        // 3. Positive premises must hold by induction; negated ones must fail.
        for (i, l) in dv.body.iter().enumerate() {
            if l.pos {
                self.atom_ok(l.atom)?;
            } else if self.db.contains(l.atom) {
                return Err(CheckErr::NegativeHolds { deriv: d, index: i });
            }
        }

        self.state.insert(d, DONE);
        Ok(())
    }
}

/// Strong check: re-derive the goal from program facts and rules alone.
pub fn verify(
    prog: &Program,
    db: &Db,
    derivs: &[Derivation],
    deriv_of: &FxHashMap<TermId, DerivId>,
    proof: &Proof,
) -> Result<(), CheckErr> {
    let mut c = Checker {
        prog,
        db,
        derivs,
        deriv_of,
        state: FxHashMap::default(),
    };
    c.atom_ok(proof.goal)
}

/// Cheap check: the goal is in the fact database. Trusts the forward chainer.
pub fn verify_shallow(db: &Db, proof: &Proof) -> Result<(), CheckErr> {
    if db.contains(proof.goal) {
        Ok(())
    } else {
        Err(CheckErr::Unsupported { atom: proof.goal })
    }
}

/// Confirm a recorded saturation certificate by comparison with a freshly
/// recomputed one. Only meaningful for negative answers.
pub fn verify_saturation(recorded: &Saturation, recomputed: &Saturation) -> Result<(), CheckErr> {
    if recorded.rounds != recomputed.rounds
        || recorded.idb_facts != recomputed.idb_facts
        || recorded.closure_hash != recomputed.closure_hash
    {
        return Err(CheckErr::Unsupported { atom: u32::MAX });
    }
    Ok(())
}

/// Number of distinct derivations supporting `goal`. Reported so that proof
/// cost is a visible number rather than an unmeasured tax.
pub fn proof_size(
    derivs: &[Derivation],
    deriv_of: &FxHashMap<TermId, DerivId>,
    goal: TermId,
) -> usize {
    let mut seen: FxHashMap<DerivId, ()> = FxHashMap::default();
    let mut stack = vec![goal];
    let mut n = 0;
    while let Some(a) = stack.pop() {
        if let Some(&d) = deriv_of.get(&a) {
            if seen.insert(d, ()).is_some() {
                continue;
            }
            n += 1;
            for l in &derivs[d as usize].body {
                if l.pos {
                    stack.push(l.atom);
                }
            }
        }
    }
    n
}

/// All derivations supporting `goal`, in post-order, for printing. Cycle-safe.
pub fn derivations_for(
    derivs: &[Derivation],
    deriv_of: &FxHashMap<TermId, DerivId>,
    goal: TermId,
) -> Vec<DerivId> {
    let mut seen: FxHashMap<DerivId, ()> = FxHashMap::default();
    let mut out = Vec::new();
    let mut stack = vec![goal];
    while let Some(a) = stack.pop() {
        if let Some(&d) = deriv_of.get(&a) {
            if seen.insert(d, ()).is_some() {
                continue;
            }
            for l in &derivs[d as usize].body {
                if l.pos {
                    stack.push(l.atom);
                }
            }
            out.push(d);
        }
    }
    out.reverse();
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::status::Status;

    #[test]
    fn checker_rejects_unsupported_goal() {
        let mut b = crate::program::Builder::new();
        let g = b.atom("g", 0, &[]);
        b.fact(g);
        let prog = b.build().unwrap();
        let db = Db::new();
        let proof = Proof {
            goal: g,
            ..Default::default()
        };
        assert_eq!(
            verify(&prog, &db, &[], &FxHashMap::default(), &proof),
            Err(CheckErr::Unsupported { atom: g })
        );
    }

    #[test]
    fn checker_accepts_a_seed_fact() {
        let mut b = crate::program::Builder::new();
        let g = b.atom("g", 0, &[]);
        b.fact(g);
        let prog = b.build().unwrap();
        let mut db = Db::new();
        db.insert(&prog.store, g, true);
        let proof = Proof {
            goal: g,
            ..Default::default()
        };
        assert!(verify(&prog, &db, &[], &FxHashMap::default(), &proof).is_ok());
        assert_eq!(verify_shallow(&db, &proof), Ok(()));
    }

    #[test]
    fn matches_respects_the_environment() {
        let mut s = crate::symbol::SymbolTable::new();
        let p = s.func("p", 1);
        let mut st = TermStore::new();
        let a = st.constant(s.constant("a"));
        let x = st.var(0);
        let pa = st.atom(p, &[a]);
        let px = st.atom(p, &[x]);
        let mut env: FxHashMap<u32, TermId> = FxHashMap::default();
        assert!(!matches(&st, px, &env, pa), "unbound var must not match");
        env.insert(0, a);
        assert!(matches(&st, px, &env, pa));
    }

    #[test]
    fn groundness_detects_nested_variables() {
        let mut s = crate::symbol::SymbolTable::new();
        let f = s.func("f", 1);
        let mut st = TermStore::new();
        let (x, _) = st.fresh_var();
        let t = st.func(f, &[x]);
        assert!(!ground(&st, t));
        let c = st.constant(s.constant("c"));
        let fc = st.func(f, &[c]);
        assert!(ground(&st, fc));
    }

    #[test]
    fn status_semantics_are_not_collapsed() {
        assert!(Status::Proved.is_definite());
        assert!(Status::Exhausted.is_inconclusive());
        assert!(!Status::Unknown.is_definite());
        assert!(Status::Impossible.requires_proof());
        assert!(!Status::Exhausted.requires_proof());
    }
}
