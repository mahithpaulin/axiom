//! Theory solvers for CDCL(T) (ROADMAP II2a): integer difference logic and
//! congruence closure, combined à la Nelson–Oppen over shared equalities.
//!
//! Both are total decision procedures over explicit inputs (no search, no
//! budgets — both run in polynomial time in the asserted constraints), which
//! is what makes them usable as proof checkers for theory lemmas as well as
//! solvers. The SAT glue (boolean abstraction, lemma emission, the
//! combination loop) lives here too; the clause-level machinery stays in
//! `src/sat.rs`.
//!
//! Scope is deliberately Allen-free: difference logic (`x - y ≤ c` over
//! integers, where negation is exact) rather than full Simplex, and congruence
//! without E-matching. Full linear arithmetic and quantifier instantiation
//! extend the same trait surface later; see ROADMAP II2b.

use crate::budget::Budget;
use crate::hash::FxHashMap;
use crate::sat::{
    AtomDesc, STerm, SatOutcome, SatSolver, TheoryLemma, TheoryResponse, TheoryStats, UnsatProof,
};
use crate::status::Exhausted;
use crate::symbol::SymbolTable;
use crate::term::{TermId, TermStore, T_ATOM, T_CONST, T_FUN, T_VAR};
use std::collections::{HashMap, HashSet};

/// A theory variable is just a term id: constants and variables are leaves in
/// both theories, so one namespace serves the combination.
pub type Tvar = TermId;

/// Integer difference constraint `x - y <= c`. Negation is exact over
/// integers: `¬(x - y ≤ c)` ⟺ `y - x ≤ -c-1`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Diff {
    pub x: Tvar,
    pub y: Tvar,
    pub c: i64,
}

impl Diff {
    pub fn negate(self) -> Diff {
        Diff {
            x: self.y,
            y: self.x,
            c: -self.c - 1,
        }
    }
}

// ---- difference logic: Floyd-Warshall over asserted constraints -------------

/// Distance + next-hop tables from Floyd-Warshall.
type FloydTables = (Vec<Tvar>, Vec<Vec<i64>>, Vec<Vec<Option<usize>>>);

/// A set of asserted difference constraints with all-pairs shortest paths.
/// Cubic in the number of distinct variables; asserted sets here are small
/// (formula atoms, not solver state), and the bound is honest, not hidden.
#[derive(Clone, Default, Debug)]
pub struct DiffSet {
    edges: Vec<Diff>,
}

impl DiffSet {
    pub fn new() -> Self {
        DiffSet { edges: Vec::new() }
    }

    pub fn assert(&mut self, d: Diff) {
        if !self.edges.contains(&d) {
            self.edges.push(d);
        }
    }

    fn nodes(&self) -> Vec<Tvar> {
        let mut v: Vec<Tvar> = Vec::new();
        for e in &self.edges {
            if !v.contains(&e.x) {
                v.push(e.x);
            }
            if !v.contains(&e.y) {
                v.push(e.y);
            }
        }
        v
    }

    /// All-pairs shortest paths. Returns the distance table and a
    /// next-hop table for path reconstruction.
    ///
    /// Triple-index Floyd-Warshall is inherently index-based; an iterator
    /// transcription would obscure the textbook shape without changing the
    /// cubic bound, so the range loops stay (deliberately, not lazily).
    #[allow(clippy::needless_range_loop)]
    fn floyd(&self) -> FloydTables {
        let nodes = self.nodes();
        let n = nodes.len();
        const INF: i64 = i64::MAX / 4;
        let mut dist = vec![vec![INF; n]; n];
        let mut next: Vec<Vec<Option<usize>>> = vec![vec![None; n]; n];
        let idx = |t: Tvar| nodes.iter().position(|&u| u == t).expect("node indexed");
        for i in 0..n {
            dist[i][i] = 0;
        }
        for e in &self.edges {
            let (a, b) = (idx(e.x), idx(e.y));
            // Edge y -> x with weight c encodes x - y <= c.
            if e.c < dist[b][a] {
                dist[b][a] = e.c;
                next[b][a] = Some(a);
            }
        }
        for k in 0..n {
            for i in 0..n {
                if dist[i][k] == INF {
                    continue;
                }
                for j in 0..n {
                    if dist[k][j] == INF {
                        continue;
                    }
                    let nd = dist[i][k].saturating_add(dist[k][j]);
                    if nd < dist[i][j] {
                        dist[i][j] = nd;
                        next[i][j] = next[i][k];
                    }
                }
            }
        }
        (nodes, dist, next)
    }

    /// A negative cycle (= an unsatisfiable core), if any, as edge constraints.
    pub fn conflict(&self) -> Option<Vec<Diff>> {
        let (nodes, dist, next) = self.floyd();
        for (i, row) in dist.iter().enumerate() {
            if row[i] < 0 {
                return Some(self.cycle_through(&nodes, &next, i));
            }
        }
        None
    }

    fn cycle_through(
        &self,
        nodes: &[Tvar],
        next: &[Vec<Option<usize>>],
        start: usize,
    ) -> Vec<Diff> {
        // Walk next-hops from `start` back to `start`, matching each hop to
        // its tightest asserted edge. This is a closed walk of negative
        // total weight — jointly unsatisfiable, hence a sound conflict core,
        // though not necessarily a simple cycle when shortest paths overlap.
        let mut out = Vec::new();
        let mut cur = start;
        let mut guard = 0usize;
        while let Some(h) = next[cur][start] {
            let (u, v) = (nodes[cur], nodes[h]);
            // The tightest asserted edge u -> v, i.e. some `x - y <= c`
            // with y == u and x == v.
            let mut best: Option<Diff> = None;
            for e in &self.edges {
                if e.y == u && e.x == v && best.map(|b| e.c < b.c).unwrap_or(true) {
                    best = Some(*e);
                }
            }
            match best {
                Some(e) => out.push(e),
                None => break,
            }
            cur = h;
            guard += 1;
            if cur == start || guard > nodes.len() + 1 {
                break;
            }
        }
        out
    }

    /// Tightest implied bound on `x - y`, or `None` if disconnected.
    /// Valid only on consistent sets: with a negative cycle present,
    /// Floyd-Warshall reuses the cycle and the distances sink below every
    /// true bound (ex falso noise, not a bound). Callers (`check`,
    /// `implied_eqs`) establish `conflict().is_none()` first.
    pub fn bound(&self, x: Tvar, y: Tvar) -> Option<i64> {
        let (nodes, dist, _) = self.floyd();
        let (mut xi, mut yi) = (None, None);
        for (i, &t) in nodes.iter().enumerate() {
            if t == x {
                xi = Some(i);
            }
            if t == y {
                yi = Some(i);
            }
        }
        match (xi, yi) {
            (Some(a), Some(b)) => {
                let d = dist[b][a];
                if d >= i64::MAX / 4 {
                    None
                } else {
                    Some(d)
                }
            }
            _ => {
                if x == y {
                    Some(0)
                } else {
                    None
                }
            }
        }
    }

    /// Is `x - y <= c` entailed? Same consistency precondition as `bound`.
    /// (On an inconsistent set every bound reads arbitrarily low, so this
    /// answers vacuously true — sound ex falso, but not a measurement.)
    pub fn entails(&self, d: Diff) -> bool {
        match self.bound(d.x, d.y) {
            Some(b) => b <= d.c,
            None => false,
        }
    }

    /// Premise edges implying `x - y <= c` (requires [`DiffSet::entails`]).
    /// Returns one shortest path's edges.
    pub fn explain_bound(&self, x: Tvar, y: Tvar) -> Vec<Diff> {
        let (nodes, _, next) = self.floyd();
        let (mut xi, mut yi) = (None, None);
        for (i, &t) in nodes.iter().enumerate() {
            if t == x {
                xi = Some(i);
            }
            if t == y {
                yi = Some(i);
            }
        }
        let (a, b) = match (xi, yi) {
            (Some(a), Some(b)) => (a, b),
            _ => return Vec::new(),
        };
        // Path from b (= y) to a (= x) following next-hops.
        let mut out = Vec::new();
        let mut cur = b;
        let mut guard = 0usize;
        while cur != a && guard <= nodes.len() {
            let h = match next[cur][a] {
                Some(h) => h,
                None => break,
            };
            let (u, v) = (nodes[cur], nodes[h]);
            let mut best: Option<Diff> = None;
            for e in &self.edges {
                if e.y == u && e.x == v && best.map(|eb| e.c < eb.c).unwrap_or(true) {
                    best = Some(*e);
                }
            }
            match best {
                Some(e) => out.push(e),
                None => break,
            }
            cur = h;
            guard += 1;
        }
        out
    }
}

// ---- congruence closure with explanations -----------------------------------

/// Witness for one union step, with the term pair whose merge caused it.
/// Stored per child-root: explanations walk edges child → parent but check
/// and unfold the *causing* pair, which need not share the roots' shapes.
#[derive(Clone, Debug)]
enum Witness {
    /// An asserted input equality over exactly this pair.
    Asserted(TermId, TermId),
    /// A congruence between same-shaped applications.
    Congruence(TermId, TermId),
}

/// Union-find without path compression (proof forest, like `Subst`'s DD-0005
/// reasoning: compression rewrites would need trailing). Parent pointers form
/// trees; explanations walk to the common root.
#[derive(Clone, Default, Debug)]
pub struct Congruence {
    parent: FxHashMap<TermId, TermId>,
    witness: FxHashMap<TermId, Witness>,
    rank: FxHashMap<TermId, usize>,
    /// Every term of interest (asserted terms plus their subterms, plus any
    /// term added explicitly): congruence only ever merges indexed terms.
    /// Asserting an equality does not invent the sibling terms it must be
    /// compared against — the caller registers the formula's terms first.
    nodes: HashSet<TermId>,
}

impl Congruence {
    pub fn new() -> Self {
        Congruence {
            parent: FxHashMap::default(),
            witness: FxHashMap::default(),
            rank: FxHashMap::default(),
            nodes: HashSet::new(),
        }
    }

    /// Register a term of interest (plus its subterms, iteratively) for
    /// congruence comparison. Must cover every formula term before `check`.
    pub fn add_term(&mut self, store: &TermStore, t: TermId) {
        let mut stack = vec![t];
        while let Some(u) = stack.pop() {
            if !self.nodes.insert(u) {
                continue;
            }
            stack.extend(store.args(u).iter().copied());
        }
    }

    fn find(&self, mut x: TermId) -> TermId {
        while let Some(&p) = self.parent.get(&x) {
            if p == x {
                break;
            }
            x = p;
        }
        x
    }

    fn link(&mut self, a: TermId, b: TermId, w: Witness) {
        let (mut ra, mut rb) = (self.find(a), self.find(b));
        if ra == rb {
            return;
        }
        let (rna, rnb) = (
            self.rank.get(&ra).copied().unwrap_or(0),
            self.rank.get(&rb).copied().unwrap_or(0),
        );
        if rna < rnb {
            std::mem::swap(&mut ra, &mut rb);
        }
        self.parent.insert(rb, ra);
        self.witness.insert(rb, w);
        if rna == rnb {
            self.rank.insert(ra, rna + 1);
        }
    }

    /// Assert `a ≈ b`; merging is closed under congruence over the indexed
    /// terms.
    pub fn assert_eq(&mut self, store: &TermStore, a: TermId, b: TermId) {
        self.add_term(store, a);
        self.add_term(store, b);
        self.link(a, b, Witness::Asserted(a, b));
        self.close_congruence(store);
    }

    /// One congruence-closure pass over the indexed app-nodes: merge
    /// `f(ss)` with `f(ts)` whenever all child pairs share classes.
    /// Quadratic per pass in the indexed apps; asserted sets here are
    /// formula-sized, and the bound is stated, not hidden.
    fn close_congruence(&mut self, store: &TermStore) {
        loop {
            let apps: Vec<TermId> = self
                .nodes
                .iter()
                .copied()
                .filter(|&t| store.kind(t) == T_FUN)
                .collect();
            let mut merged = false;
            for (i, &a) in apps.iter().enumerate() {
                for &b in apps.iter().skip(i + 1) {
                    if self.find(a) == self.find(b) {
                        continue;
                    }
                    if store.sym(a) != store.sym(b) {
                        continue;
                    }
                    let (aa, ba) = (store.args(a), store.args(b));
                    if aa.len() != ba.len() {
                        continue;
                    }
                    if aa
                        .iter()
                        .zip(ba.iter())
                        .all(|(&x, &y)| self.find(x) == self.find(y))
                    {
                        self.link(a, b, Witness::Congruence(a, b));
                        merged = true;
                    }
                }
            }
            if !merged {
                break;
            }
        }
    }

    /// Explain `a ≈ b`: the asserted equalities justifying it (congruence
    /// steps unfold recursively). `assert_lits` maps each merged pair to the
    /// input literals justifying it; pairs merged by congruence contribute
    /// their children's explanations instead.
    pub fn explain(
        &self,
        store: &TermStore,
        a: TermId,
        b: TermId,
        assert_lits: &FxHashMap<(TermId, TermId), Vec<i32>>,
    ) -> Option<Vec<i32>> {
        // Paths to the common root.
        fn path_to_root(cc: &Congruence, mut x: TermId, root: TermId) -> Option<Vec<TermId>> {
            let mut path = vec![x];
            let mut guard = 0usize;
            while x != root {
                x = *cc.parent.get(&x)?;
                path.push(x);
                guard += 1;
                if guard > cc.parent.len() + 1 {
                    return None;
                }
            }
            Some(path)
        }
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            return None;
        }
        let (pa, pb) = (path_to_root(self, a, ra)?, path_to_root(self, b, rb)?);
        let mut out = Vec::new();
        // Walk each union edge child -> parent, resolving its witness. Edges
        // are pushed child-first, so the witness lives on the edge's source.
        let mut work: Vec<(TermId, TermId)> = Vec::new();
        for w in pa.windows(2) {
            work.push((w[0], w[1]));
        }
        for w in pb.windows(2) {
            work.push((w[0], w[1]));
        }
        let mut seen_pairs: HashSet<(TermId, TermId)> = HashSet::new();
        while let Some((x, _)) = work.pop() {
            // Edges are walked child -> parent, but the witness belongs to
            // the causing pair (which may differ from the edge endpoints
            // after rank swaps and later unions).
            let w = self.witness.get(&x).cloned();
            match w {
                // An asserted input equality over exactly this pair.
                Some(Witness::Asserted(a, b)) => {
                    let key = if a < b { (a, b) } else { (b, a) };
                    if !seen_pairs.insert(key) {
                        continue;
                    }
                    let ls = assert_lits.get(&key)?;
                    for &l in ls {
                        if !out.contains(&l) {
                            out.push(l);
                        }
                    }
                }
                // A congruence between same-shaped applications: unfold over
                // the causing pair's children.
                Some(Witness::Congruence(a, b)) => {
                    let key = if a < b { (a, b) } else { (b, a) };
                    if !seen_pairs.insert(key) {
                        continue;
                    }
                    if store.sym(a) != store.sym(b) {
                        return None;
                    }
                    let (xa, ya) = (store.args(a), store.args(b));
                    if xa.len() != ya.len() {
                        return None;
                    }
                    for (&cx, &cy) in xa.iter().zip(ya.iter()) {
                        // Children must already share classes (else the merge
                        // was unsound); explain each pair recursively by
                        // pushing edges along their root paths.
                        let (rx, ry) = (self.find(cx), self.find(cy));
                        if rx != ry {
                            return None;
                        }
                        if let (Some(px), Some(py)) =
                            (path_to_root(self, cx, rx), path_to_root(self, cy, ry))
                        {
                            for w in px.windows(2).chain(py.windows(2)) {
                                work.push((w[0], w[1]));
                            }
                        } else {
                            return None;
                        }
                    }
                }
                None => {
                    // A node with no witness is a root: the edge must be trivial.
                    if x != y {
                        return None;
                    }
                }
            }
        }
        Some(out)
    }
}

/// Are `a` and `b` in the same class?
pub fn congruent(cc: &Congruence, a: TermId, b: TermId) -> bool {
    cc.find(a) == cc.find(b)
}

// ---- Nelson-Oppen combination over shared equalities -------------------------

/// The combination state: one congruence instance plus one difference set,
/// exchanging entailed equalities between shared variables to fixpoint.
/// Theories only ever meet on equalities `x ≈ y` over shared leaves.
#[derive(Clone, Default, Debug)]
pub struct Combination {
    pub cc: Congruence,
    pub diff: DiffSet,
    /// Asserted input equalities with their justifying SAT literals.
    /// Equalities exchanged from difference logic carry their bound-path
    /// literals here too, so explanations never lose premises.
    eq_lits: FxHashMap<(TermId, TermId), Vec<i32>>,
    /// Asserted disequalities `(s, t, lit)`: must stay separated.
    diseqs: Vec<(TermId, TermId, i32)>,
    /// Asserted difference constraints with their SAT literals.
    diff_lits: FxHashMap<Diff, i32>,
}

impl Combination {
    pub fn new() -> Self {
        Combination {
            cc: Congruence::new(),
            diff: DiffSet::new(),
            eq_lits: FxHashMap::default(),
            diseqs: Vec::new(),
            diff_lits: FxHashMap::default(),
        }
    }

    fn key(a: TermId, b: TermId) -> (TermId, TermId) {
        if a < b {
            (a, b)
        } else {
            (b, a)
        }
    }

    /// Assert `s ≈ t` (UF equality) justified by SAT literal `lit`.
    pub fn assert_eq(&mut self, store: &TermStore, s: TermId, t: TermId, lit: i32) {
        let entry = self.eq_lits.entry(Self::key(s, t)).or_default();
        if !entry.contains(&lit) {
            entry.push(lit);
        }
        self.cc.assert_eq(store, s, t);
    }

    /// Assert `s ≠ t` justified by SAT literal `lit`.
    pub fn assert_ne(&mut self, s: TermId, t: TermId, lit: i32) {
        self.diseqs.push((s, t, lit));
    }

    /// Assert `x - y <= c` justified by SAT literal `lit`.
    pub fn assert_diff(&mut self, d: Diff, lit: i32) {
        self.diff_lits.entry(d).or_insert(lit);
        self.diff.assert(d);
    }

    /// Check consistency. Returns the jointly inconsistent set of asserted
    /// (true) SAT literals, or `None`. The driver negates the set into the
    /// conflict clause; every returned literal is true under the current
    /// assignment, which `analyze` relies on.
    /// Difference conflicts are reported before any exchange: bounds are
    /// meaningless on inconsistent sets, so exchange and propagation run
    /// only past this point.
    pub fn check(&mut self, store: &TermStore, shared: &[TermId]) -> Option<Vec<i32>> {
        // Difference conflicts first.
        if let Some(cycle) = self.diff.conflict() {
            let mut out = Vec::new();
            for e in cycle {
                if let Some(&l) = self.diff_lits.get(&e) {
                    if !out.contains(&l) {
                        out.push(l);
                    }
                }
            }
            return Some(out);
        }
        // Exchange: RDL bounds in both directions mean equality.
        loop {
            let mut fresh: Vec<(TermId, TermId, Vec<i32>)> = Vec::new();
            for &x in shared {
                for &y in shared {
                    if x == y || congruent(&self.cc, x, y) {
                        continue;
                    }
                    let fwd = self.diff.bound(x, y);
                    let bwd = self.diff.bound(y, x);
                    if matches!((fwd, bwd), (Some(a), Some(b)) if a <= 0 && b <= 0) {
                        let mut wit = self.diff.explain_bound(x, y);
                        wit.extend(self.diff.explain_bound(y, x));
                        let mut lits = Vec::new();
                        for e in wit {
                            if let Some(&l) = self.diff_lits.get(&e) {
                                if !lits.contains(&l) {
                                    lits.push(l);
                                }
                            }
                        }
                        fresh.push((x, y, lits));
                    }
                }
            }
            if fresh.is_empty() {
                break;
            }
            for (x, y, lits) in fresh {
                let entry = self.eq_lits.entry(Self::key(x, y)).or_default();
                for l in lits {
                    if !entry.contains(&l) {
                        entry.push(l);
                    }
                }
                self.cc.assert_eq(store, x, y);
            }
        }
        // Disequalities violated?
        for (s, t, lit) in self.diseqs.clone() {
            if congruent(&self.cc, s, t) {
                let mut out = self
                    .cc
                    .explain(store, s, t, &self.eq_lits)
                    .expect("congruent pairs explain");
                out.push(lit);
                return Some(out);
            }
        }
        None
    }

    /// Justifying SAT literals for an entailed `x - y <= c` (requires
    /// entailment; call after [`DiffSet::entails`]).
    pub fn diff_witness(&self, x: TermId, y: TermId) -> Vec<i32> {
        let mut out = Vec::new();
        for e in self.diff.explain_bound(x, y) {
            if let Some(&l) = self.diff_lits.get(&e) {
                if !out.contains(&l) {
                    out.push(l);
                }
            }
        }
        out
    }

    /// Justifying SAT literals for a congruent pair, if explainable.
    pub fn eq_witness(&self, store: &TermStore, s: TermId, t: TermId) -> Option<Vec<i32>> {
        self.cc.explain(store, s, t, &self.eq_lits)
    }
}

// ---- DPLL(T) driver: boolean abstraction + theory lemmas ---------------------

/// A theory atom for boolean abstraction: difference constraint, equality,
/// or disequality over terms. Hashable, so abstraction is deduplicated.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TheoryAtom {
    Rdl(Diff),
    Eq(TermId, TermId),
    Neq(TermId, TermId),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TheoryError {
    /// Equality/disequality over predicate atoms (predicates are not terms).
    PredicateAsTerm,
}

impl core::fmt::Display for TheoryError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TheoryError::PredicateAsTerm => {
                write!(f, "equality over predicate atoms is not a theory term")
            }
        }
    }
}

impl core::error::Error for TheoryError {}

/// All subterms of `t` (including `t`), iteratively. Congruence only ever
/// merges indexed terms: asserting `a ≈ b` cannot invent the sibling terms
/// it must be compared against, so every formula term is indexed up front.
fn index_subterms(store: &TermStore, t: TermId, set: &mut HashSet<TermId>) {
    let mut stack = vec![t];
    while let Some(u) = stack.pop() {
        if !set.insert(u) {
            continue;
        }
        stack.extend(store.args(u).iter().copied());
    }
}

/// Leaves of a term: variables, constants, and nullary applications.
fn term_leaves(store: &TermStore, t: TermId, out: &mut Vec<TermId>) {
    let mut stack = vec![t];
    while let Some(u) = stack.pop() {
        match store.kind(u) {
            T_VAR | T_CONST => {
                if !out.contains(&u) {
                    out.push(u);
                }
            }
            _ => {
                let args = store.args(u);
                if args.is_empty() {
                    if !out.contains(&u) {
                        out.push(u);
                    }
                } else {
                    stack.extend(args.iter().copied());
                }
            }
        }
    }
}

/// The [`crate::sat::TheoryHandler`] implementation: a fresh [`Combination`]
/// per call (assertions follow the current assignment, so nothing goes stale),
/// justifications from explanations, everything recorded for the proof.
struct Reasoner {
    comb: Combination,
    var_atom: Vec<Option<TheoryAtom>>,
    /// Every formula term, indexed into each fresh combination: propagation
    /// targets are often never asserted, and congruence cannot compare what
    /// was never indexed.
    terms: HashSet<TermId>,
    lemmas: Vec<TheoryLemma>,
    stats: TheoryStats,
}

impl Reasoner {
    fn refresh(&mut self, store: &TermStore, assign: &[i8]) {
        self.comb = Combination::new();
        for &t in &self.terms {
            self.comb.cc.add_term(store, t);
        }
        for (vi, opt) in self.var_atom.iter().enumerate() {
            let atom = match opt {
                Some(a) => a,
                None => continue,
            };
            if vi >= assign.len() {
                continue;
            }
            let m = assign[vi];
            if m == 0 {
                continue;
            }
            let lit = if m == 1 {
                vi as i32 + 1
            } else {
                -(vi as i32 + 1)
            };
            match atom {
                TheoryAtom::Rdl(d) => {
                    self.comb
                        .assert_diff(if m == 1 { *d } else { d.negate() }, lit);
                }
                TheoryAtom::Eq(s, t) => {
                    if m == 1 {
                        self.comb.assert_eq(store, *s, *t, lit);
                    } else {
                        self.comb.assert_ne(*s, *t, lit);
                    }
                }
                TheoryAtom::Neq(s, t) => {
                    if m == 1 {
                        self.comb.assert_ne(*s, *t, lit);
                    } else {
                        self.comb.assert_eq(store, *s, *t, lit);
                    }
                }
            }
        }
    }

    fn shared_leaves(&self, store: &TermStore) -> Vec<TermId> {
        let mut out = Vec::new();
        for opt in &self.var_atom {
            match opt {
                Some(TheoryAtom::Rdl(d)) => {
                    term_leaves(store, d.x, &mut out);
                    term_leaves(store, d.y, &mut out);
                }
                Some(TheoryAtom::Eq(s, t)) | Some(TheoryAtom::Neq(s, t)) => {
                    term_leaves(store, *s, &mut out);
                    term_leaves(store, *t, &mut out);
                }
                None => {}
            }
        }
        out
    }

    fn mk_lemma(&mut self, just: Vec<i32>, concl: Option<i32>) -> TheoryLemma {
        let mut clause: Vec<i32> = just.iter().map(|&l| -l).collect();
        if let Some(l) = concl {
            clause.push(l);
        }
        let lemma = TheoryLemma {
            clause,
            hyps: just,
            concl,
        };
        self.stats.lemmas += 1;
        self.lemmas.push(lemma.clone());
        lemma
    }

    fn implication_for(
        &mut self,
        store: &TermStore,
        vi: usize,
        atom: &TheoryAtom,
    ) -> Option<(i32, TheoryLemma)> {
        match atom {
            TheoryAtom::Rdl(d) => {
                if self.comb.diff.entails(*d) {
                    let just = self.comb.diff_witness(d.x, d.y);
                    let lemma = self.mk_lemma(just, Some(vi as i32 + 1));
                    return Some((vi as i32 + 1, lemma));
                }
                let nd = d.negate();
                if self.comb.diff.entails(nd) {
                    let just = self.comb.diff_witness(nd.x, nd.y);
                    let lemma = self.mk_lemma(just, Some(-(vi as i32 + 1)));
                    return Some((-(vi as i32 + 1), lemma));
                }
                None
            }
            TheoryAtom::Eq(s, t) => {
                if congruent(&self.comb.cc, *s, *t) {
                    let just = self.comb.eq_witness(store, *s, *t)?;
                    let lemma = self.mk_lemma(just, Some(vi as i32 + 1));
                    return Some((vi as i32 + 1, lemma));
                }
                None
            }
            // No disequality propagation: a separated pair is always
            // satisfiable by splitting, so nothing is ever implied.
            TheoryAtom::Neq(..) => None,
        }
    }
}

impl crate::sat::TheoryHandler for Reasoner {
    fn theory_step(&mut self, store: &TermStore, assign: &[i8], full: bool) -> TheoryResponse {
        self.stats.rounds += 1;
        self.refresh(store, assign);
        let shared = self.shared_leaves(store);
        if let Some(conflict) = self.comb.check(store, &shared) {
            self.stats.conflicts += 1;
            let lemma = self.mk_lemma(conflict, None);
            return TheoryResponse::Conflict(lemma);
        }
        if full {
            return TheoryResponse::Consistent;
        }
        let mut out = Vec::new();
        for vi in 0..self.var_atom.len() {
            if vi < assign.len() && assign[vi] != 0 {
                continue;
            }
            let atom = match &self.var_atom[vi] {
                Some(a) => a.clone(),
                None => continue,
            };
            if let Some((lit, lemma)) = self.implication_for(store, vi, &atom) {
                self.stats.propagations += 1;
                out.push((lit, lemma));
            }
        }
        TheoryResponse::Implications(out)
    }

    fn take_lemmas(&mut self) -> Vec<TheoryLemma> {
        std::mem::take(&mut self.lemmas)
    }

    fn stats(&self) -> TheoryStats {
        self.stats
    }
}

/// Render a term structurally (iterative: depth is input-controlled).
fn render_term(store: &TermStore, symbols: &SymbolTable, t: TermId) -> Option<STerm> {
    fn sym_name(store: &TermStore, symbols: &SymbolTable, u: TermId) -> String {
        symbols.name(store.sym(u)).to_string()
    }
    let mut todo: Vec<(TermId, bool)> = vec![(t, false)];
    let mut vals: Vec<STerm> = Vec::new();
    while let Some((u, expanded)) = todo.pop() {
        if expanded {
            match store.kind(u) {
                T_VAR => vals.push(STerm::Var(sym_name(store, symbols, u))),
                T_CONST => vals.push(STerm::Const(sym_name(store, symbols, u))),
                _ => {
                    let arity = store.args(u).len();
                    let mut kids = Vec::with_capacity(arity);
                    for _ in 0..arity {
                        kids.push(vals.pop().expect("arity many values"));
                    }
                    kids.reverse();
                    vals.push(STerm::App(sym_name(store, symbols, u), kids));
                }
            }
            continue;
        }
        match store.kind(u) {
            T_VAR | T_CONST => {
                todo.push((u, true));
            }
            T_ATOM => return None,
            _ => {
                todo.push((u, true));
                for &c in store.args(u) {
                    todo.push((c, false));
                }
            }
        }
    }
    vals.pop()
}

fn render_atom(store: &TermStore, symbols: &SymbolTable, atom: &TheoryAtom) -> Option<AtomDesc> {
    match atom {
        TheoryAtom::Rdl(d) => Some(AtomDesc::Rdl {
            x: render_term(store, symbols, d.x)?,
            y: render_term(store, symbols, d.y)?,
            c: d.c,
        }),
        TheoryAtom::Eq(s, t) => Some(AtomDesc::Eq(
            render_term(store, symbols, *s)?,
            render_term(store, symbols, *t)?,
        )),
        TheoryAtom::Neq(s, t) => Some(AtomDesc::Neq(
            render_term(store, symbols, *s)?,
            render_term(store, symbols, *t)?,
        )),
    }
}

/// Complete theory proof: atom meanings plus lemmas.
#[derive(Clone, Debug, Default)]
pub struct TheoryProof {
    pub atoms: Vec<(u32, AtomDesc)>,
    pub lemmas: Vec<TheoryLemma>,
}

#[derive(Clone, Debug)]
pub enum TheoryOutcome {
    Sat {
        model: Vec<i8>,
        theory: TheoryProof,
    },
    Unsat {
        sat: UnsatProof,
        theory: TheoryProof,
    },
}

/// Boolean-abstraction driver: owns the SAT solver, lends it a [`Reasoner`]
/// per solve, and assembles certificates. Single-shot per problem (fresh
/// driver per formula, like the usage in `tests/`).
pub struct TheoryDriver {
    sat: SatSolver,
    atom_of: FxHashMap<TheoryAtom, u32>,
    var_atom: Vec<Option<TheoryAtom>>,
    terms: HashSet<TermId>,
    stats: TheoryStats,
}

impl TheoryDriver {
    pub fn new() -> Self {
        TheoryDriver {
            sat: SatSolver::new(),
            atom_of: FxHashMap::default(),
            var_atom: Vec::new(),
            terms: HashSet::new(),
            stats: TheoryStats::default(),
        }
    }

    pub fn stats(&self) -> TheoryStats {
        self.stats
    }

    /// A pure boolean variable (no theory meaning).
    pub fn bool_var(&mut self) -> u32 {
        self.sat.new_var()
    }

    /// The SAT variable abstracting a theory atom (deduplicated). Equality
    /// and disequality over predicate atoms are rejected: predicates are
    /// not terms.
    pub fn theory_var(&mut self, store: &TermStore, atom: TheoryAtom) -> Result<u32, TheoryError> {
        match &atom {
            TheoryAtom::Eq(s, t) | TheoryAtom::Neq(s, t) => {
                if store.kind(*s) == T_ATOM || store.kind(*t) == T_ATOM {
                    return Err(TheoryError::PredicateAsTerm);
                }
            }
            TheoryAtom::Rdl(d) => {
                if store.kind(d.x) == T_ATOM || store.kind(d.y) == T_ATOM {
                    return Err(TheoryError::PredicateAsTerm);
                }
            }
        }
        if let Some(&v) = self.atom_of.get(&atom) {
            return Ok(v);
        }
        // Index every formula term for congruence: propagation targets are
        // often never asserted, and unindexed terms never merge.
        match &atom {
            TheoryAtom::Eq(s, t) | TheoryAtom::Neq(s, t) => {
                index_subterms(store, *s, &mut self.terms);
                index_subterms(store, *t, &mut self.terms);
            }
            TheoryAtom::Rdl(_) => {}
        }
        let v = self.sat.new_var();
        self.atom_of.insert(atom.clone(), v);
        if self.var_atom.len() <= v as usize {
            self.var_atom.resize(v as usize + 1, None);
        }
        self.var_atom[v as usize] = Some(atom);
        Ok(v)
    }

    pub fn add_clause(&mut self, lits: &[i32]) -> Option<usize> {
        self.sat.add_clause(lits)
    }

    pub fn solve(
        &mut self,
        store: &TermStore,
        symbols: &SymbolTable,
        budget: &mut Budget,
    ) -> Result<TheoryOutcome, Exhausted> {
        let reasoner = Reasoner {
            comb: Combination::new(),
            var_atom: self.var_atom.clone(),
            terms: self.terms.clone(),
            lemmas: Vec::new(),
            stats: TheoryStats::default(),
        };
        self.sat.theory = Some(Box::new(reasoner));
        let outcome = self.sat.solve_theory(budget, store);
        // Reclaim the handler's record through the trait (no downcast).
        let (lemmas, tstats) = match self.sat.theory.as_mut() {
            Some(h) => (h.take_lemmas(), h.stats()),
            None => (Vec::new(), TheoryStats::default()),
        };
        self.stats = tstats;
        let mut atoms = Vec::new();
        for (vi, opt) in self.var_atom.iter().enumerate() {
            if let Some(a) = opt {
                let desc = render_atom(store, symbols, a).expect("registered atoms render");
                atoms.push((vi as u32, desc));
            }
        }
        let theory = TheoryProof { atoms, lemmas };
        match outcome {
            Ok(SatOutcome::Sat { model }) => Ok(TheoryOutcome::Sat { model, theory }),
            Ok(SatOutcome::Unsat { .. }) => {
                let sat_proof = self.sat.take_proof();
                Ok(TheoryOutcome::Unsat {
                    sat: sat_proof,
                    theory,
                })
            }
            Err(e) => Err(e),
        }
    }
}

impl Default for TheoryDriver {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TheoryCheckErr {
    Sat(crate::sat::SatCheckErr),
    /// A lemma references an unknown variable or malformed atom.
    BadAtom,
    /// A lemma's justification does not hold.
    Lemma(usize),
    /// The final state does not conflict.
    NotEmpty,
}

impl core::fmt::Display for TheoryCheckErr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TheoryCheckErr::Sat(e) => write!(f, "propositional check failed: {e}"),
            TheoryCheckErr::BadAtom => write!(f, "lemma references an unknown atom"),
            TheoryCheckErr::Lemma(i) => write!(f, "theory lemma {i} unjustified"),
            TheoryCheckErr::NotEmpty => write!(f, "final state does not conflict"),
        }
    }
}

impl core::error::Error for TheoryCheckErr {}

/// Rebuild a checker store from structural terms.
struct Rebuilt {
    store: TermStore,
    symbols: SymbolTable,
    vars: FxHashMap<String, TermId>,
}

impl Rebuilt {
    fn build(&mut self, t: &STerm) -> Result<TermId, TheoryCheckErr> {
        match t {
            STerm::Var(name) => {
                if let Some(&v) = self.vars.get(name) {
                    return Ok(v);
                }
                let (v, _) = self.store.fresh_var();
                self.vars.insert(name.clone(), v);
                Ok(v)
            }
            STerm::Const(name) => {
                let s = self.symbols.constant(name);
                Ok(self.store.constant(s))
            }
            STerm::App(name, kids) => {
                if kids.len() > u16::MAX as usize {
                    return Err(TheoryCheckErr::BadAtom);
                }
                let mut args = Vec::with_capacity(kids.len());
                for k in kids {
                    args.push(self.build(k)?);
                }
                let s = self.symbols.func(name, args.len() as u16);
                Ok(self.store.func(s, &args))
            }
        }
    }
}

/// Verify a theory-unsat certificate: RUP over everything propositional,
/// then every theory lemma replayed in a fresh theory state, then the final
/// conflict. The checker shares no search code with the solver: unit
/// propagation and the theory procedures run here over rebuilt terms.
pub fn verify_theory_unsat(
    sat_input: &[Vec<i32>],
    sat_proof: &UnsatProof,
    theory: &TheoryProof,
) -> Result<(), TheoryCheckErr> {
    use crate::sat::verify_unsat;
    // Atom meanings by variable.
    let mut meaning: HashMap<u32, &AtomDesc> = HashMap::new();
    for (v, d) in &theory.atoms {
        meaning.insert(*v, d);
    }
    // 1. Propositional RUP over inputs plus theory-lemma clauses (a superset:
    // monotone, so over-approximating the database stays sound).
    let mut db: Vec<Vec<i32>> = sat_input.to_vec();
    db.extend(theory.lemmas.iter().map(|l| l.clause.clone()));
    verify_unsat(&db, sat_proof).map_err(TheoryCheckErr::Sat)?;
    // 2. Every theory lemma, in a fresh state.
    for (i, lem) in theory.lemmas.iter().enumerate() {
        let mut rb = Rebuilt {
            store: TermStore::new(),
            symbols: SymbolTable::new(),
            vars: FxHashMap::default(),
        };
        let mut comb = Combination::new();
        for &h in &lem.hyps {
            let v = h.unsigned_abs() - 1;
            let desc = meaning.get(&v).ok_or(TheoryCheckErr::BadAtom)?;
            assert_hyp(&mut rb, &mut comb, desc, h > 0).map_err(|_| TheoryCheckErr::BadAtom)?;
        }
        match lem.concl {
            None => {
                let shared = all_leaves(lem, &meaning)?;
                if comb.check(&rb.store, &shared).is_none() {
                    return Err(TheoryCheckErr::Lemma(i));
                }
            }
            Some(l) => {
                let v = l.unsigned_abs() - 1;
                let desc = meaning.get(&v).ok_or(TheoryCheckErr::BadAtom)?;
                if !concl_holds(&mut rb, &mut comb, desc, l > 0) {
                    return Err(TheoryCheckErr::Lemma(i));
                }
            }
        }
    }
    Ok(())
}

fn assert_hyp(
    rb: &mut Rebuilt,
    comb: &mut Combination,
    desc: &AtomDesc,
    positive: bool,
) -> Result<(), TheoryCheckErr> {
    match desc {
        AtomDesc::Rdl { x, y, c } => {
            let (rx, ry) = (rb.build(x)?, rb.build(y)?);
            let d = Diff {
                x: rx,
                y: ry,
                c: *c,
            };
            comb.assert_diff(if positive { d } else { d.negate() }, 0);
            Ok(())
        }
        AtomDesc::Eq(s, t) => {
            let (rs, rt) = (rb.build(s)?, rb.build(t)?);
            if positive {
                comb.assert_eq(&rb.store, rs, rt, 0);
            } else {
                comb.assert_ne(rs, rt, 0);
            }
            Ok(())
        }
        AtomDesc::Neq(s, t) => {
            let (rs, rt) = (rb.build(s)?, rb.build(t)?);
            if positive {
                comb.assert_ne(rs, rt, 0);
            } else {
                comb.assert_eq(&rb.store, rs, rt, 0);
            }
            Ok(())
        }
    }
}

fn concl_holds(rb: &mut Rebuilt, comb: &mut Combination, desc: &AtomDesc, positive: bool) -> bool {
    match desc {
        AtomDesc::Rdl { x, y, c } => {
            let (Ok(rx), Ok(ry)) = (rb.build(x), rb.build(y)) else {
                return false;
            };
            let d = Diff {
                x: rx,
                y: ry,
                c: *c,
            };
            comb.diff.entails(if positive { d } else { d.negate() })
        }
        AtomDesc::Eq(s, t) => {
            if !positive {
                // No disequality propagation exists; a negated-equality
                // conclusion is malformed proof material.
                return false;
            }
            let (Ok(rs), Ok(rt)) = (rb.build(s), rb.build(t)) else {
                return false;
            };
            // Index the conclusion terms: they were never asserted, and
            // unindexed terms never merge.
            comb.cc.add_term(&rb.store, rs);
            comb.cc.add_term(&rb.store, rt);
            congruent(&comb.cc, rs, rt)
        }
        // Same: the driver never propagates disequalities.
        AtomDesc::Neq(..) => false,
    }
}

fn all_leaves(
    lem: &TheoryLemma,
    meaning: &HashMap<u32, &AtomDesc>,
) -> Result<Vec<TermId>, TheoryCheckErr> {
    // Rebuilt lazily per lemma would duplicate stores; leaves need terms, so
    // rebuild once more into a scratch store purely for leaf collection.
    let mut rb = Rebuilt {
        store: TermStore::new(),
        symbols: SymbolTable::new(),
        vars: FxHashMap::default(),
    };
    let mut out = Vec::new();
    let mut atoms = Vec::new();
    for &h in lem.hyps.iter().chain(lem.concl.iter()) {
        let v = h.unsigned_abs() - 1;
        atoms.push(meaning.get(&v).ok_or(TheoryCheckErr::BadAtom)?);
    }
    for desc in atoms {
        match desc {
            AtomDesc::Rdl { x, y, .. } => {
                for t in [x, y] {
                    let rt = rb.build(t)?;
                    term_leaves(&rb.store, rt, &mut out);
                }
            }
            AtomDesc::Eq(s, t) | AtomDesc::Neq(s, t) => {
                for t in [s, t] {
                    let rt = rb.build(t)?;
                    term_leaves(&rb.store, rt, &mut out);
                }
            }
        }
    }
    Ok(out)
}

/// Verify a theory model: assert the model's theory atoms (both polarities)
/// in a fresh state and confirm consistency.
pub fn verify_theory_sat(model: &[i8], theory: &TheoryProof) -> bool {
    let mut meaning: HashMap<u32, &AtomDesc> = HashMap::new();
    for (v, d) in &theory.atoms {
        meaning.insert(*v, d);
    }
    let mut rb = Rebuilt {
        store: TermStore::new(),
        symbols: SymbolTable::new(),
        vars: FxHashMap::default(),
    };
    let mut comb = Combination::new();
    for (v, d) in &theory.atoms {
        if *v as usize >= model.len() {
            return false;
        }
        let m = model[*v as usize];
        if m == 0 {
            continue;
        }
        if assert_hyp(&mut rb, &mut comb, d, m == 1).is_err() {
            return false;
        }
    }
    let mut shared = Vec::new();
    for (_, d) in &theory.atoms {
        match d {
            AtomDesc::Rdl { x, y, .. } => {
                for t in [x, y] {
                    let Ok(rt) = rb.build(t) else {
                        return false;
                    };
                    term_leaves(&rb.store, rt, &mut shared);
                }
            }
            AtomDesc::Eq(s, t) | AtomDesc::Neq(s, t) => {
                for t in [s, t] {
                    let Ok(rt) = rb.build(t) else {
                        return false;
                    };
                    term_leaves(&rb.store, rt, &mut shared);
                }
            }
        }
    }
    comb.check(&rb.store, &shared).is_none()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::Builder;

    fn const_term(b: &mut Builder, name: &str) -> TermId {
        b.constant(name)
    }

    #[test]
    fn diff_detects_negative_cycle_with_edges() {
        // x - y <= -1, y - x <= -1: unsatisfiable; explanation is both edges.
        let mut b = Builder::new();
        let x = const_term(&mut b, "x");
        let y = const_term(&mut b, "y");
        let mut d = DiffSet::new();
        let (e1, e2) = (Diff { x, y, c: -1 }, Diff { x: y, y: x, c: -1 });
        d.assert(e1);
        d.assert(e2);
        let c = d.conflict().expect("negative cycle");
        assert_eq!(c.len(), 2);
        // Precision on a consistent set: with only e1, x - y <= 5 holds and
        // x - y <= -2 does not. (On the inconsistent two-edge set every bound
        // reads arbitrarily low — ex falso, not a measurement.)
        let mut d1 = DiffSet::new();
        d1.assert(e1);
        assert!(d1.entails(Diff { x, y, c: 5 }));
        assert!(!d1.entails(Diff { x, y, c: -2 }));
    }

    #[test]
    fn diff_explains_bounds() {
        // x - y <= 2, y - z <= 3 entails x - z <= 5 with both premises.
        let mut b = Builder::new();
        let (x, y, z) = (
            const_term(&mut b, "x"),
            const_term(&mut b, "y"),
            const_term(&mut b, "z"),
        );
        let mut d = DiffSet::new();
        d.assert(Diff { x, y, c: 2 });
        d.assert(Diff { x: y, y: z, c: 3 });
        assert!(d.entails(Diff { x, y: z, c: 5 }));
        assert!(!d.entails(Diff { x, y: z, c: 4 }));
        let w = d.explain_bound(x, z);
        assert_eq!(w.len(), 2);
    }

    #[test]
    fn congruence_merges_and_explains() {
        // f(a) ≈ f(b) needs a ≈ b; explanation names the asserted equality.
        let mut b = Builder::new();
        let (a, c) = (const_term(&mut b, "a"), const_term(&mut b, "b"));
        let f = b.symbols.func("f", 1);
        let (fa, fb) = (b.store.func(f, &[a]), b.store.func(f, &[c]));
        let mut cc = Congruence::new();
        // Register the sibling terms: asserting a ≈ b cannot invent the
        // f(·) terms they must be compared against.
        cc.add_term(&b.store, fa);
        cc.add_term(&b.store, fb);
        let mut lits = FxHashMap::default();
        lits.insert(if a < c { (a, c) } else { (c, a) }, vec![11]);
        cc.assert_eq(&b.store, a, c);
        assert!(congruent(&cc, fa, fb));
        let w = cc.explain(&b.store, fa, fb, &lits).expect("explained");
        assert_eq!(w, vec![11]);
    }

    #[test]
    fn congruence_rejects_merged_disequality() {
        let mut b = Builder::new();
        let (a, c) = (const_term(&mut b, "a"), const_term(&mut b, "b"));
        let mut comb = Combination::new();
        comb.assert_eq(&b.store, a, c, 7);
        comb.assert_ne(a, c, 9);
        let conflict = comb.check(&b.store, &[]).expect("conflict");
        assert!(conflict.contains(&7));
        assert!(conflict.contains(&9));
    }

    #[test]
    fn combination_exchanges_rdl_equality() {
        // x - y <= 0 and y - x <= 0 entail x ≈ y; a disequality then conflicts.
        let mut b = Builder::new();
        let (x, y) = (const_term(&mut b, "x"), const_term(&mut b, "y"));
        let mut comb = Combination::new();
        comb.assert_diff(Diff { x, y, c: 0 }, 3);
        comb.assert_diff(Diff { x: y, y: x, c: 0 }, 5);
        comb.assert_ne(x, y, 9);
        let conflict = comb.check(&b.store, &[x, y]).expect("conflict");
        assert!(conflict.contains(&9));
        // Both bound justifications travel with it.
        assert!(conflict.contains(&3));
        assert!(conflict.contains(&5));
    }

    /// Naive reference: brute force over a bounded integer box. Shares no
    /// code with Floyd-Warshall (integer grids, direct comparison), so
    /// agreement is genuine evidence — the `tests/reference.rs` discipline
    /// applied to theories. The box radius covers the small-model bound:
    /// satisfiable difference constraints over `n` variables have a model
    /// within ±(n-1)·max|c|, and the radius below exceeds that for the
    /// fixed n=3 pools used here.
    fn box_radius(constraints: &[(i64, i64, i64)]) -> i64 {
        3 * constraints.iter().map(|c| c.2.abs()).max().unwrap_or(0) + 2
    }

    fn naive_sat(constraints: &[(i64, i64, i64)], nvars: usize) -> bool {
        // Constraints as (x, y, c) index triples meaning v[x] - v[y] <= c.
        fn rec(cs: &[(i64, i64, i64)], nvars: usize, assign: &mut Vec<i64>, r: i64) -> bool {
            if assign.len() == nvars {
                return cs
                    .iter()
                    .all(|&(x, y, c)| assign[x as usize] - assign[y as usize] <= c);
            }
            for v in -r..=r {
                assign.push(v);
                if rec(cs, nvars, assign, r) {
                    return true;
                }
                assign.pop();
            }
            false
        }
        let r = box_radius(constraints);
        rec(constraints, nvars, &mut Vec::new(), r)
    }

    fn naive_entails(constraints: &[(i64, i64, i64)], nvars: usize, q: (i64, i64, i64)) -> bool {
        // Entailed iff constraints + ¬q are unsatisfiable; ¬(x-y≤c) is y-x≤-c-1.
        let mut with_neg = constraints.to_vec();
        with_neg.push((q.1, q.0, -q.2 - 1));
        !naive_sat(&with_neg, nvars)
    }

    #[test]
    fn diff_agrees_with_brute_force() {
        // Variable pools of size 3, constants -2..=2, families covering
        // chains, diamonds, self-loops and contradictory pairs.
        let mut b = Builder::new();
        let mut ids = Vec::new();
        for n in ["x", "y", "z"] {
            ids.push(const_term(&mut b, n));
        }
        let mut families: Vec<Vec<(i64, i64, i64)>> = vec![vec![]];
        for c in -2..=2 {
            families.push(vec![(0, 1, c), (1, 2, 2)]);
            families.push(vec![(0, 1, 1), (1, 0, c)]);
            families.push(vec![(0, 0, c)]);
            families.push(vec![(0, 1, c), (1, 2, c), (2, 0, c)]);
        }
        families.push(vec![(0, 1, -1), (1, 0, -1)]);
        families.push(vec![(0, 1, 0), (1, 0, 0), (0, 1, -1)]);
        families.push(vec![(0, 1, 3), (0, 2, 1), (1, 2, 1)]);
        for fam in &families {
            let mut d = DiffSet::new();
            for &(x, y, c) in fam {
                d.assert(Diff {
                    x: ids[x as usize],
                    y: ids[y as usize],
                    c,
                });
            }
            assert_eq!(
                d.conflict().is_none(),
                naive_sat(fam, 3),
                "sat disagreement on {fam:?}"
            );
            if d.conflict().is_none() {
                for &(x, y, c) in &[(0i64, 1i64, 0i64), (0, 2, 4), (1, 0, -3)] {
                    let q = Diff {
                        x: ids[x as usize],
                        y: ids[y as usize],
                        c,
                    };
                    assert_eq!(
                        d.entails(q),
                        naive_entails(fam, 3, (x, y, c)),
                        "entailment disagreement on {fam:?} query {:?}",
                        (x, y, c)
                    );
                }
            }
        }
    }

    /// Naive congruence over structural terms: union-find with path halving
    /// plus a fixpoint congruence pass. Different representation (owned trees,
    /// not arenas) and different algorithm shape (compressing finds) from
    /// `Congruence`, so agreement is evidence.
    #[derive(Clone, PartialEq, Eq, Hash, Debug)]
    enum NT {
        C(String),
        F(String, Vec<NT>),
    }

    struct NaiveCc {
        parent: Vec<usize>,
        terms: Vec<NT>,
    }

    impl NaiveCc {
        fn new() -> Self {
            NaiveCc {
                parent: Vec::new(),
                terms: Vec::new(),
            }
        }

        fn intern(&mut self, t: NT) -> usize {
            // Register children first: the term DAG stays complete, so the
            // congruence fixpoint never meets a term it hasn't compared.
            if let NT::F(_, kids) = &t {
                for k in kids.clone() {
                    self.intern(k);
                }
            }
            if let Some(i) = self.terms.iter().position(|u| u == &t) {
                return i;
            }
            self.terms.push(t);
            self.parent.push(self.terms.len() - 1);
            self.terms.len() - 1
        }

        fn find(&mut self, x: usize) -> usize {
            let mut r = x;
            while self.parent[r] != r {
                self.parent[r] = self.parent[self.parent[r]];
                r = self.parent[r];
            }
            r
        }

        fn union(&mut self, a: usize, b: usize) {
            let (ra, rb) = (self.find(a), self.find(b));
            if ra != rb {
                self.parent[rb] = ra;
            }
            self.close();
        }

        fn close(&mut self) {
            loop {
                let mut merged = false;
                let apps: Vec<usize> = (0..self.terms.len())
                    .filter(|&i| matches!(self.terms[i], NT::F(..)))
                    .collect();
                for (i, &a) in apps.iter().enumerate() {
                    for &b in apps.iter().skip(i + 1) {
                        let (NT::F(fa, ca), NT::F(fb, cb)) =
                            (self.terms[a].clone(), self.terms[b].clone())
                        else {
                            continue;
                        };
                        if fa != fb || ca.len() != cb.len() {
                            continue;
                        }
                        // Compare child classes by interning children first.
                        let mut same = true;
                        for (x, y) in ca.iter().zip(cb.iter()) {
                            let (ix, iy) = (self.intern(x.clone()), self.intern(y.clone()));
                            if self.find(ix) != self.find(iy) {
                                same = false;
                                break;
                            }
                        }
                        if same && self.find(a) != self.find(b) {
                            let (ra, rb) = (self.find(a), self.find(b));
                            self.parent[rb] = ra;
                            merged = true;
                        }
                    }
                }
                if !merged {
                    break;
                }
            }
        }
    }

    /// Both engines on the same scenarios: same partitions, and every engine
    /// explanation replays in the naive one.
    #[test]
    fn congruence_agrees_with_naive() {
        // Scenario terms, engine side (Builder) and naive side (NT).
        let mut b = Builder::new();
        let (a, c, d) = (
            const_term(&mut b, "a"),
            const_term(&mut b, "b"),
            const_term(&mut b, "c"),
        );
        let f = b.symbols.func("f", 1);
        let g = b.symbols.func("g", 1);
        let (fa, fb) = (b.store.func(f, &[a]), b.store.func(f, &[c]));
        let (gfa, gfc) = (b.store.func(g, &[fa]), b.store.func(g, &[fb]));
        let _ = d;
        let (na, nb, nc) = (
            NT::C("a".to_string()),
            NT::C("b".to_string()),
            NT::C("c".to_string()),
        );
        let (nfa, nfb) = (
            NT::F("f".to_string(), vec![na.clone()]),
            NT::F("f".to_string(), vec![nb.clone()]),
        );
        let (ngfa, ngfc) = (
            NT::F("g".to_string(), vec![nfa.clone()]),
            NT::F("g".to_string(), vec![nfb.clone()]),
        );

        // Engine: a ≈ b (lit 1).
        let mut cc = Congruence::new();
        for t in [a, c, fa, fb, gfa, gfc] {
            cc.add_term(&b.store, t);
        }
        let mut lits = FxHashMap::default();
        lits.insert(Combination::key(a, c), vec![1]);
        cc.assert_eq(&b.store, a, c);
        // Naive mirror.
        let mut nc_ = NaiveCc::new();
        let (ia, ib) = (nc_.intern(na.clone()), nc_.intern(nb.clone()));
        let (ifa, ifb) = (nc_.intern(nfa.clone()), nc_.intern(nfb.clone()));
        let (igfa, igfc) = (nc_.intern(ngfa.clone()), nc_.intern(ngfc.clone()));
        nc_.union(ia, ib);

        // Same partitions both ways, including one-way congruence.
        for (x, y, nx, ny, expect) in [
            (a, c, ia, ib, true),
            (fa, fb, ifa, ifb, true),
            (gfa, gfc, igfa, igfc, true),
            (a, d, ia, nc_.intern(nc), false),
        ] {
            assert_eq!(congruent(&cc, x, y), expect);
            assert_eq!(nc_.find(nx) == nc_.find(ny), expect);
        }
        // Engine explanations replay naively: assert the explained premises,
        // the pair must merge.
        for (x, y) in [(fa, fb), (gfa, gfc)] {
            let w = cc.explain(&b.store, x, y, &lits).expect("explained");
            assert_eq!(w, vec![1]);
            let mut check = NaiveCc::new();
            let (ja, jb) = (check.intern(na.clone()), check.intern(nb.clone()));
            check.union(ja, jb);
            let (jx, jy) = (
                check.intern(if x == fa { nfa.clone() } else { ngfa.clone() }),
                check.intern(if y == fb { nfb.clone() } else { ngfc.clone() }),
            );
            // Interning does not close: run the fixpoint explicitly, exactly
            // as `union` would have.
            check.close();
            assert!(check.find(jx) == check.find(jy));
        }
    }
}
