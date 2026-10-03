//! The extensional database: stored facts plus the indexes that make joins
//! cheap.
//!
//! ## Why the index is two levels deep (argument positions 0 and 1)
//!
//! Stage 1 shipped a single first-argument index. ROADMAP I1 then measured the
//! join spending ~everything in unbound scans of literals like `path(X, Y)`
//! with only the *second* argument bound (edge-seeded transitive-closure
//! steps: `edge(Y, Z)` binds `Y`, which sits at position 1 of `path`). A
//! second level keyed on argument 1 removes those scans at one extra `TermId`
//! per binary-and-wider fact plus bucket overhead. Positions 2+ stay
//! unindexed: no workload here binds them selectively, and the trigger for
//! adding more is recorded in docs/ROADMAP.md alongside DD-0006.
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
    /// Predicate -> second argument -> tuples. Only atoms of arity >= 2 are
    /// entered; the map for other predicates stays empty.
    pub by_second: Vec<FxHashMap<TermId, Vec<TermId>>>,
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
            by_second: Vec::new(),
        }
    }

    #[inline]
    fn ensure(&mut self, pred: SymId) {
        let n = pred as usize + 1;
        if self.by_pred.len() < n {
            self.by_pred.resize(n, Vec::new());
            self.by_first.resize(n, FxHashMap::default());
            self.by_second.resize(n, FxHashMap::default());
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

    /// Second argument, if the atom has one. Only binary-and-wider atoms are
    /// entered in the second-argument index.
    #[inline]
    fn second_arg(store: &TermStore, atom: TermId) -> Option<TermId> {
        let a = store.args(atom);
        if a.len() >= 2 {
            Some(a[1])
        } else {
            None
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
        if let Some(key2) = Self::second_arg(store, atom) {
            self.by_second[pred as usize]
                .entry(key2)
                .or_default()
                .push(atom);
        }
        true
    }

    /// Candidate tuples for `pred`. If `bound` is `Some((pos, key))`, only
    /// tuples whose argument at `pos` is that term are returned (positions 0
    /// and 1 are indexed). A nullary predicate has the sentinel first argument
    /// `u32::MAX`, which is unreachable for a real term id, so nullary lookups
    /// never accidentally hit an index bucket. An unindexed position falls
    /// back to the full scan: sound, just slow.
    pub fn candidates(&self, pred: SymId, bound: Option<(usize, TermId)>) -> &[TermId] {
        let i = pred as usize;
        if i >= self.by_pred.len() {
            return &[];
        }
        match bound {
            Some((0, k)) => {
                if k == u32::MAX {
                    &self.by_pred[i]
                } else {
                    match self.by_first[i].get(&k) {
                        Some(v) => v.as_slice(),
                        None => &[],
                    }
                }
            }
            Some((1, k)) => match self.by_second.get(i).and_then(|m| m.get(&k)) {
                Some(v) => v.as_slice(),
                None => &[],
            },
            Some(_) => self.by_pred[i].as_slice(),
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
        fn map_bytes(maps: &[FxHashMap<TermId, Vec<TermId>>]) -> usize {
            maps.iter()
                .map(|m| {
                    // key/value table overhead at load factor, plus the per-bucket
                    // vectors. An estimate, not an exact allocator figure.
                    m.capacity() * (std::mem::size_of::<TermId>() * 2 + 16)
                        + m.values()
                            .map(|v: &Vec<TermId>| v.capacity() * 4)
                            .sum::<usize>()
                })
                .sum()
        }
        let vec_bytes: usize = self
            .by_pred
            .iter()
            .map(|v| v.capacity() * std::mem::size_of::<TermId>())
            .sum();
        vec_bytes
            + map_bytes(&self.by_first)
            + map_bytes(&self.by_second)
            + self.facts.capacity() * 8
            + self.seed.capacity() * 8
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
        let (_s, mut st, mut db, p, a, b) = setup();
        let e1 = st.atom(p, &[a, b]);
        assert!(db.insert(&st, e1, false));
        assert!(!db.insert(&st, e1, false));
        assert_eq!(db.count(p), 1);
        assert_eq!(db.total(), 1);
    }

    #[test]
    fn first_arg_index_selects() {
        let (_s, mut st, mut db, p, a, b) = setup();
        let mut cs = _s;
        let c = st.constant(cs.constant("c"));
        let e1 = st.atom(p, &[a, b]);
        let e2 = st.atom(p, &[a, c]);
        let e3 = st.atom(p, &[b, a]);
        db.insert(&st, e1, false);
        db.insert(&st, e2, false);
        db.insert(&st, e3, false);
        assert_eq!(db.candidates(p, Some((0, a))).len(), 2);
        assert_eq!(db.candidates(p, Some((0, b))).len(), 1);
        assert_eq!(db.candidates(p, Some((0, c))).len(), 0);
        assert_eq!(db.candidates(p, None).len(), 3);
    }

    #[test]
    fn second_arg_index_selects() {
        let (_s, mut st, mut db, p, a, b) = setup();
        let mut cs = _s;
        let c = st.constant(cs.constant("c"));
        let e1 = st.atom(p, &[a, b]);
        let e2 = st.atom(p, &[a, c]);
        let e3 = st.atom(p, &[b, a]);
        db.insert(&st, e1, false);
        db.insert(&st, e2, false);
        db.insert(&st, e3, false);
        // Second arguments: b once (e1), c once (e2), a once (e3).
        assert_eq!(db.candidates(p, Some((1, a))).len(), 1);
        assert_eq!(db.candidates(p, Some((1, b))).len(), 1);
        assert_eq!(db.candidates(p, Some((1, c))).len(), 1);
        assert_eq!(db.candidates(p, Some((1, 9999))).len(), 0);
    }

    #[test]
    fn seed_membership_is_tracked_separately() {
        let (_s, mut st, mut db, p, a, b) = setup();
        let e = st.atom(p, &[a, b]);
        db.insert(&st, e, true);
        assert!(db.seed.contains(&e));
        assert!(db.contains(e));
    }

    #[test]
    fn unknown_predicate_yields_no_candidates() {
        let (_s, _st, db, p, a, _b) = setup();
        assert!(db.candidates(p + 99, Some((0, a))).is_empty());
        assert!(db.candidates(p + 99, Some((1, a))).is_empty());
        assert!(db.candidates(p, None).is_empty());
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
        assert!(db.candidates(p, Some((0, u32::MAX))).len() == 1);
        assert!(db.candidates(p, None).len() == 1);
    }
}
