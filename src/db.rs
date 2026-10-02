//! The extensional database: stored facts plus the indexes that make joins
//! cheap.
//!
//! ## Why the index is only one level deep
//!
//! The obvious instinct is a multi-key index. Stage 1 ships a single
//! first-argument hash index plus a per-predicate vector, and that is a
//! *deliberate* choice with a hypothesis attached, not an oversight:
//!
//! **Hypothesis.** For stratified Datalog over hash-consed ground atoms, join
//! cost is dominated by the number of tuples actually examined, and a
//! first-argument index removes most of that at a memory cost of one extra
//! `TermId` per fact. A second index level should pay for itself only on
//! workloads with highly selective non-leading arguments, which the Stage-1
//! benchmark suite is not yet representative of.
//!
//! `benches/kernel.rs` measures index selectivity directly (`bench_index_selectivity`)
//! so the decision is revisited against data rather than taste. The trigger for
//! adding a second level is recorded in docs/ROADMAP.md.
//!
//! Candidates come back as slices, not `Iterator`s: the join loop needs random
//! access to resume where it left off after backtracking, and an iterator
//! adaptor would either allocate or be lost across the mutation.
//!
//! ## Why the store is a parameter and not a field
//!
//! `Db` holds no `TermStore` reference. The solver owns both, and a `&Db`
//! coexisting with the solver's `&mut TermStore` is only expressible if `Db`
//! borrows nothing. Passing `&TermStore` per call keeps the borrow graph flat
//! and makes the dependency explicit.

use crate::hash::FxHashMap;
use crate::hash::FxHashSet;
use crate::symbol::SymId;
use crate::term::{TermId, TermStore, T_ATOM};

pub struct Db {
    /// Facts asserted directly in the program. These are the only atoms a
    /// strong proof check accepts without a derivation.
    pub seed: FxHashSet<TermId>,
    /// Every atom currently believed: seeds plus derivations.
    pub facts: FxHashSet<TermId>,
    /// Predicate -> all its tuples, in insertion order. Insertion order keeps
    /// the whole engine deterministic, which the benchmarks depend on.
    pub by_pred: Vec<Vec<TermId>>,
    /// Predicate -> first argument -> tuples.
    pub by_first: Vec<FxHashMap<TermId, Vec<TermId>>>,
}

impl Default for Db {
    fn default() -> Self {
        Self::new()
    }
}

impl Db {
    pub fn new() -> Self {
        Db {
            seed: FxHashSet::default(),
            facts: FxHashSet::default(),
            by_pred: Vec::new(),
            by_first: Vec::new(),
        }
    }

    #[inline]
    fn ensure(&mut self, pred: SymId) {
        let n = pred as usize + 1;
        if self.by_pred.len() < n {
            self.by_pred.resize(n, Vec::new());
            self.by_first.resize(n, FxHashMap::default());
        }
    }

    #[inline]
    fn first_arg(store: &TermStore, atom: TermId) -> TermId {
        let a = store.args(atom);
        if a.is_empty() {
            u32::MAX
        } else {
            a[0]
        }
    }

    /// Insert a ground atom. Returns true if it was not already present.
    pub fn insert(&mut self, store: &TermStore, atom: TermId, is_seed: bool) -> bool {
        debug_assert_eq!(store.kind(atom), T_ATOM);
        let pred = store.sym(atom);
        self.ensure(pred);
        if is_seed {
            self.seed.insert(atom);
        }
        if !self.facts.insert(atom) {
            return false;
        }
        self.by_pred[pred as usize].push(atom);
        let key = Self::first_arg(store, atom);
        self.by_first[pred as usize]
            .entry(key)
            .or_default()
            .push(atom);
        true
    }

    /// Candidate tuples for `pred`. If `bound_first` is `Some`, only tuples
    /// whose first argument is that term are returned. A nullary predicate has
    /// the sentinel first argument `u32::MAX`, which is unreachable for a real
    /// term id, so nullary lookups never accidentally hit an index bucket.
    pub fn candidates(&self, pred: SymId, bound_first: Option<TermId>) -> &[TermId] {
        let i = pred as usize;
        if i >= self.by_pred.len() {
            return &[];
        }
        match bound_first {
            Some(k) => {
                if k == u32::MAX {
                    &self.by_pred[i]
                } else {
                    match self.by_first[i].get(&k) {
                        Some(v) => v.as_slice(),
                        None => &[],
                    }
                }
            }
            None => self.by_pred[i].as_slice(),
        }
    }

    #[inline]
    pub fn contains(&self, atom: TermId) -> bool {
        self.facts.contains(&atom)
    }

    pub fn count(&self, pred: SymId) -> usize {
        self.by_pred
            .get(pred as usize)
            .map(|v| v.len())
            .unwrap_or(0)
    }

    pub fn total(&self) -> usize {
        self.facts.len()
    }

    /// Payload bytes: one `TermId` per fact per index level, plus set overhead.
    pub fn index_bytes(&self) -> usize {
        let vec_bytes: usize = self
            .by_pred
            .iter()
            .map(|v| v.capacity() * std::mem::size_of::<TermId>())
            .sum();
        let map_bytes: usize = self
            .by_first
            .iter()
            .flat_map(|v| v.iter())
            .map(|m| {
                // load-factor overhead of the key/value table plus the per-bucket
                // vector; an estimate, not an exact allocator figure.
                m.capacity() * (std::mem::size_of::<TermId>() * 2 + 16)
                    + m.values().map(|v: &Vec<TermId>| v.capacity() * 4).sum::<usize>()
            })
            .sum();
        vec_bytes + map_bytes + self.facts.capacity() * 8 + self.seed.capacity() * 8
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::SymbolTable;

    fn setup() -> (SymbolTable, TermStore, Db, SymId, TermId, TermId) {
        let mut s = SymbolTable::new();
        let p = s.predicate("edge", 2);
        let mut st = TermStore::new();
        let a = st.constant(s.constant("a"));
        let b = st.constant(s.constant("b"));
        (s, st, Db::new(), p, a, b)
    }

    #[test]
    fn dedup_and_counts() {
        let (_s, st, mut db, p, a, b) = setup();
        let e1 = st.atom(p, &[a, b]);
        assert!(db.insert(&st, e1, false));
        assert!(!db.insert(&st, e1, false));
        assert_eq!(db.count(p), 1);
        assert_eq!(db.total(), 1);
    }

    #[test]
    fn first_arg_index_selects() {
        let (_s, st, mut db, p, a, b) = setup();
        let c = st.constant(_s.constant("c"));
        db.insert(&st, st.atom(p, &[a, b]), false);
        db.insert(&st, st.atom(p, &[a, c]), false);
        db.insert(&st, st.atom(p, &[b, a]), false);
        assert_eq!(db.candidates(p, Some(a)).len(), 2);
        assert_eq!(db.candidates(p, Some(b)).len(), 1);
        assert_eq!(db.candidates(p, Some(c)).len(), 0);
        assert_eq!(db.candidates(p, None).len(), 3);
    }

    #[test]
    fn seed_membership_is_tracked_separately() {
        let (_s, st, mut db, p, a, b) = setup();
        let e = st.atom(p, &[a, b]);
        db.insert(&st, e, true);
        assert!(db.seed.contains(&e));
        assert!(db.contains(e));
    }

    #[test]
    fn unknown_predicate_yields_no_candidates() {
        let (_s, _st, db, p, a, _b) = setup();
        assert!(db.candidates(p + 99, Some(a)).is_empty());
    }

    #[test]
    fn nullary_predicate_uses_the_unreachable_sentinel() {
        let mut s = SymbolTable::new();
        let p = s.predicate("p", 0);
        let mut st = TermStore::new();
        let mut db = Db::new();
        let a = st.atom(p, &[]);
        db.insert(&st, a, false);
        // A query for the sentinel must not match, but an unbound first arg must.
        assert!(db.candidates(p, Some(u32::MAX)).len() == 1);
        assert!(db.candidates(p, None).len() == 1);
    }
}
