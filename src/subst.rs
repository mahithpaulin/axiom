//! Unification by union-find with a trail, plus term resolution.
//!
//! ## Why union-find rather than Robinson substitution lists
//!
//! Robinson unification with explicit substitution lists re-copies every
//! affected term on each binding, so it is quadratic on a rule with n variables
//! and allocates heavily. The Martelli--Montanari--Pietrini "efficient
//! unification" formulation instead treats terms as a DAG and *merges nodes*:
//! binding `x` to `f(a)` is one pointer write and every occurrence of `x` sees
//! the binding for free. That is what makes an arena representation pay off.
//!
//! ## Link direction is load-bearing
//!
//! `find` returns the representative, and "resolve" means "follow to the
//! representative". So the representative must always be the more *concrete*
//! side of a merge. Plain union-by-rank violates this: if a variable that has
//! accumulated rank meets a function term, rank elects the variable as root and
//! the binding becomes invisible. Therefore:
//!
//! * variable vs variable -> union by rank (either root is a variable, so
//!   semantics are preserved and chains stay O(log n));
//! * variable vs non-variable -> the variable is *always* attached underneath.
//!
//! Chains therefore follow term nesting and are bounded by term depth, which
//! `resolve` already walks. This is also why path compression is left off: it
//! would shorten chains but every rewrite must be trailed for undo, inflating
//! the trail and the undo cost. Union by rank bounds `find` at O(log n) for the
//! variable-only chains. Measured both ways; see DD-0011.
//!
//! ## The occurs check is not optional
//!
//! Merging `x` with `f(x)` builds a cyclic term graph, after which every
//! traversal is an infinite loop. The occurs check is a soundness requirement,
//! not an optimisation. It is generation-stamped, so it is linear in the size of
//! the offending term and allocation-free after warm-up.

use crate::term::{TermId, TermStore, T_ATOM, T_CONST, T_FUN, T_VAR};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnifyErr {
    /// Distinct function symbols or arities.
    Clash,
    /// `x = f(x)`; rejecting this keeps the term graph acyclic.
    Occurs,
}

#[derive(Clone, Copy)]
enum Trail {
    Parent(u32, u32),
    Rank(u32, u8),
}

pub struct Subst {
    parent: Vec<u32>,
    rank: Vec<u8>,
    trail: Vec<Trail>,
    seen: Vec<u32>,
    seen_gen: u32,
    stack: Vec<TermId>,
    vals: Vec<TermId>,
    work: Vec<(TermId, u16)>,
    // ---- instrumentation (see docs/PERFORMANCE.md) ----
    pub unify_calls: u64,
    pub bind_calls: u64,
    pub occurs_checks: u64,
    pub occurs_nodes: u64,
}

impl Default for Subst {
    fn default() -> Self {
        Self::new()
    }
}

impl Subst {
    pub fn new() -> Self {
        Subst {
            parent: Vec::new(),
            rank: Vec::new(),
            trail: Vec::new(),
            seen: Vec::new(),
            seen_gen: 0,
            stack: Vec::new(),
            vals: Vec::new(),
            work: Vec::new(),
            unify_calls: 0,
            bind_calls: 0,
            occurs_checks: 0,
            occurs_nodes: 0,
        }
    }

    #[inline]
    pub fn ensure(&mut self, nodes: usize) {
        if self.parent.len() < nodes {
            let start = self.parent.len();
            self.parent.resize(nodes, 0);
            self.rank.resize(nodes, 0);
            self.seen.resize(nodes, 0);
            for i in start..nodes {
                self.parent[i] = i as u32;
            }
        }
    }

    #[inline]
    pub fn find(&self, x: TermId) -> TermId {
        let mut y = x;
        while self.parent[y as usize] != y as u32 {
            y = self.parent[y as usize];
        }
        y
    }

    #[inline]
    pub fn bound(&self, x: TermId) -> bool {
        self.parent[x as usize] != x as u32
    }

    /// Merge two variable roots, union by rank. Both sides are variables, so
    /// either choice of representative preserves `find` semantics.
    #[inline]
    fn link_vars(&mut self, a: u32, b: u32) {
        debug_assert_ne!(a, b);
        let (root, child) = if self.rank[a as usize] >= self.rank[b as usize] {
            (a, b)
        } else {
            (b, a)
        };
        self.trail
            .push(Trail::Parent(child, self.parent[child as usize]));
        self.parent[child as usize] = root;
        if self.rank[root as usize] == self.rank[child as usize] {
            self.trail.push(Trail::Rank(root, self.rank[root as usize]));
            self.rank[root as usize] += 1;
        }
    }

    /// Attach a variable root underneath a non-variable root. Never the
    /// reverse; see the module note on link direction.
    #[inline]
    fn link_var_under(&mut self, var_root: u32, term_root: u32) {
        debug_assert_ne!(var_root, term_root);
        self.trail
            .push(Trail::Parent(var_root, self.parent[var_root as usize]));
        self.parent[var_root as usize] = term_root;
    }

    #[inline]
    pub fn mark(&self) -> usize {
        self.trail.len()
    }

    /// Undo every binding made since `mark`. This is the engine's only
    /// backtracking mechanism, so it must be exact: a leaked binding is a
    /// soundness bug, and `tests/soundness.rs` hunts for exactly that.
    pub fn undo_to(&mut self, mark: usize) {
        while self.trail.len() > mark {
            match self.trail.pop().unwrap() {
                Trail::Parent(c, old) => self.parent[c as usize] = old,
                Trail::Rank(n, old) => self.rank[n as usize] = old,
            }
        }
    }

    /// Linear-time occurs check, generation-stamped so it costs no allocation.
    pub fn occurs(&mut self, store: &TermStore, root: u32, t: TermId) -> bool {
        self.occurs_checks += 1;
        self.ensure(store.node_count());
        self.seen_gen = self.seen_gen.wrapping_add(1);
        if self.seen_gen == 0 {
            self.seen.iter_mut().for_each(|s| *s = 0);
            self.seen_gen = 1;
        }
        let gen = self.seen_gen;
        self.stack.clear();
        self.stack.push(t);
        while let Some(x) = self.stack.pop() {
            self.occurs_nodes += 1;
            let r = self.find(x);
            if self.seen[r as usize] == gen {
                continue;
            }
            self.seen[r as usize] = gen;
            if r == root {
                return true;
            }
            if store.kind(r) == T_VAR {
                continue;
            }
            for &a in store.args(r) {
                self.stack.push(a);
            }
        }
        false
    }

    /// Full unification. Both sides may contain variables.
    pub fn unify(&mut self, store: &TermStore, a: TermId, b: TermId) -> Result<(), UnifyErr> {
        self.unify_calls += 1;
        self.ensure(store.node_count());
        self.stack.clear();
        self.stack.push(a);
        self.stack.push(b);
        while let Some(y) = self.stack.pop() {
            let x = self.stack.pop().unwrap();
            let ra = self.find(x);
            let rb = self.find(y);
            if ra == rb {
                continue;
            }
            let ka = store.kind(ra);
            let kb = store.kind(rb);
            match (ka, kb) {
                (T_VAR, T_VAR) => self.link_vars(ra as u32, rb as u32),
                (T_VAR, _) => {
                    if self.occurs(store, ra as u32, rb) {
                        return Err(UnifyErr::Occurs);
                    }
                    self.link_var_under(ra as u32, rb as u32);
                }
                (_, T_VAR) => {
                    if self.occurs(store, rb as u32, ra) {
                        return Err(UnifyErr::Occurs);
                    }
                    self.link_var_under(rb as u32, ra as u32);
                }
                (T_CONST, T_CONST) => {
                    if store.sym(ra) != store.sym(rb) {
                        return Err(UnifyErr::Clash);
                    }
                }
                (T_FUN, T_FUN) | (T_ATOM, T_ATOM) => {
                    let na = store.node(ra);
                    let nb = store.node(rb);
                    if na.sym != nb.sym || na.len != nb.len {
                        return Err(UnifyErr::Clash);
                    }
                    // Push the pattern child first so that the *second* pop
                    // yields it: `y` must be the target and `x` the pattern.
                    // Reversing this silently swaps the roles, which makes
                    // `match_into` see a variable on the target side and
                    // correctly report Clash -- an unsound-looking but
                    // actually fatal ordering bug.
                    for i in (0..na.len as usize).rev() {
                        self.stack.push(store.args(ra)[i]);
                        self.stack.push(store.args(rb)[i]);
                    }
                }
                _ => return Err(UnifyErr::Clash),
            }
        }
        Ok(())
    }

    /// One-way matching: bind only variables occurring in `pat`; a variable on
    /// the `fact` side is a clash. Used to join a rule body literal against a
    /// stored tuple.
    pub fn match_into(
        &mut self,
        store: &TermStore,
        pat: TermId,
        fact: TermId,
    ) -> Result<(), UnifyErr> {
        self.bind_calls += 1;
        self.ensure(store.node_count());
        self.stack.clear();
        self.stack.push(pat);
        self.stack.push(fact);
        while let Some(y) = self.stack.pop() {
            let x = self.stack.pop().unwrap();
            let ra = self.find(x);
            let rb = self.find(y);
            if ra == rb {
                continue;
            }
            let ka = store.kind(ra);
            let kb = store.kind(rb);
            match (ka, kb) {
                (T_VAR, T_VAR) => self.link_vars(ra as u32, rb as u32),
                (T_VAR, _) => {
                    if self.occurs(store, ra as u32, rb) {
                        return Err(UnifyErr::Occurs);
                    }
                    self.link_var_under(ra as u32, rb as u32);
                }
                (_, T_VAR) => return Err(UnifyErr::Clash),
                (T_CONST, T_CONST) => {
                    if store.sym(ra) != store.sym(rb) {
                        return Err(UnifyErr::Clash);
                    }
                }
                (T_FUN, T_FUN) | (T_ATOM, T_ATOM) => {
                    let na = store.node(ra);
                    let nb = store.node(rb);
                    if na.sym != nb.sym || na.len != nb.len {
                        return Err(UnifyErr::Clash);
                    }
                    // Push the pattern child first so that the *second* pop
                    // yields it: `y` must be the target and `x` the pattern.
                    // Reversing this silently swaps the roles, which makes
                    // `match_into` see a variable on the target side and
                    // correctly report Clash -- an unsound-looking but
                    // actually fatal ordering bug.
                    for i in (0..na.len as usize).rev() {
                        self.stack.push(store.args(ra)[i]);
                        self.stack.push(store.args(rb)[i]);
                    }
                }
                _ => return Err(UnifyErr::Clash),
            }
        }
        Ok(())
    }

    /// Apply the current binding to `t`, returning a hash-consed term.
    ///
    /// Iterative post-order with an explicit frame stack: term depth is
    /// input-controlled, and a 100k-element list must not reach the native
    /// stack. No memoisation in Stage 1; measured in DD-0012.
    pub fn resolve(&mut self, store: &mut TermStore, t: TermId) -> TermId {
        self.ensure(store.node_count());
        self.vals.clear();
        self.work.clear();
        self.work.push((t, 0));
        while !self.work.is_empty() {
            let (node, i) = self.work[self.work.len() - 1];
            let r = self.find(node);
            let n = store.node(r);
            if i < n.len {
                let last = self.work.len() - 1;
                self.work[last].1 = i + 1;
                let child = store.args(r)[i as usize];
                self.work.push((child, 0));
                continue;
            }
            let base = self.vals.len() - n.len as usize;
            let rebuilt = match n.kind {
                T_VAR => r,
                T_CONST => store.constant(n.sym),
                T_FUN => {
                    let (_, kids) = self.vals.split_at(base);
                    store.func(n.sym, kids)
                }
                T_ATOM => {
                    let (_, kids) = self.vals.split_at(base);
                    store.atom(n.sym, kids)
                }
                _ => r,
            };
            self.vals.truncate(base);
            self.vals.push(rebuilt);
            self.work.pop();
        }
        self.vals.pop().unwrap_or(t)
    }

    /// Wipe the binding table. Called between top-level queries so a stale
    /// binding can never leak into a fresh derivation.
    pub fn clear(&mut self, nodes: usize) {
        self.ensure(nodes);
        for i in 0..self.parent.len() {
            self.parent[i] = i as u32;
            self.rank[i] = 0;
        }
        self.trail.clear();
        self.stack.clear();
    }

    /// Total number of live bindings; used by tests to assert no leakage.
    pub fn binding_count(&self, nodes: usize) -> usize {
        (0..nodes).filter(|&i| self.parent[i] != i as u32).count()
    }
}
