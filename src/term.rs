//! Hash-consed term and atom representation.
//!
//! ## Shape
//!
//! Every term node is 16 bytes and lives in one flat `Vec`; children live in a
//! second flat `Vec` addressed by `(start, len)`. There is no per-node
//! allocation, no `Rc`, no `Box`, and no pointer to chase. A node id is a
//! `u32` index, so a term is a slice of `u32` and equality of terms is
//! `memcmp`.
//!
//! ```text
//! TermNode { kind: u8, sym: u32, start: u32, len: u16 }   // 16 B
//! ```
//!
//! ## Why hash-consing
//!
//! `intern` guarantees one node id per distinct `(kind, sym, args)` tuple. That
//! single invariant buys four things at once:
//!
//! * **Structural sharing** -- `f(a)` built in two different rules is one node.
//! * **Memoisation** -- a derived ground fact is deduplicated by a single
//!   integer comparison.
//! * **O(1) structural equality** -- `a == b` on `TermId` is term equality.
//! * **Cheap fingerprints** -- hashing a term is hashing a `u32` slice.
//!
//! ## The one thing hash-consing does NOT give you
//!
//! Unification merges *distinct* nodes (`Var(3)` and `f(a)` become equivalent),
//! and it does so outside the hash-cons table. So two ids may denote the same
//! term after a substitution has been applied. Consequence: any code that
//! compares terms for equality must resolve them first (see `subst::resolve`).
//! This is the single sharpest edge in the design and it is called out again in
//! docs/IR_SPEC.md. `assert_no_dead_children` and the debug build's tests guard
//! the arena invariants that make the fast path legal.

use crate::hash::{mix, FxHashMap};
use crate::symbol::SymId;

pub type TermId = u32;

pub const T_VAR: u8 = 0;
pub const T_CONST: u8 = 1;
pub const T_FUN: u8 = 2;
pub const T_ATOM: u8 = 3;

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct TermNode {
    pub kind: u8,
    pub sym: SymId,
    pub start: u32,
    pub len: u16,
}

#[derive(Default, Clone)]
pub struct TermStore {
    nodes: Vec<TermNode>,
    children: Vec<TermId>,
    /// Content hash -> candidate node ids. A `Vec` handles the rare collision
    /// without a second table, and `Vec::new` does not allocate, so the
    /// hit path stays allocation-free.
    buckets: FxHashMap<u64, Vec<TermId>>,
    var_ids: FxHashMap<u32, TermId>,
    next_var: u32,
    /// Reusable scratch for variable-containment checks, generation-stamped so
    /// the O(node count) clear happens once per growth rather than per query.
    stamp: Vec<u32>,
    stamp_gen: u32,
    stack: Vec<TermId>,
}

/// Content hash of a term under construction. Deliberately excludes the child
/// arena offset: two identical `f(a)` built at different times have different
/// offsets but must intern to the same node.
#[inline]
fn content_hash(kind: u8, sym: SymId, args: &[TermId]) -> u64 {
    let mut h = mix((kind as u64) << 56, sym as u64);
    for &a in args {
        h = mix(h, a as u64);
    }
    h
}

impl TermStore {
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    pub fn node(&self, t: TermId) -> TermNode {
        self.nodes[t as usize]
    }
    #[inline]
    pub fn kind(&self, t: TermId) -> u8 {
        self.nodes[t as usize].kind
    }
    #[inline]
    pub fn sym(&self, t: TermId) -> SymId {
        self.nodes[t as usize].sym
    }
    #[inline]
    pub fn args(&self, t: TermId) -> &[TermId] {
        let n = self.nodes[t as usize];
        &self.children[n.start as usize..n.start as usize + n.len as usize]
    }
    /// Single child by arena index, for loops that must not hold a slice.
    #[inline]
    pub fn children_at(&self, i: usize) -> TermId {
        self.children[i]
    }
    #[inline]
    pub fn child(&self, t: TermId, i: usize) -> TermId {
        let n = self.nodes[t as usize];
        self.children[n.start as usize + i]
    }
    #[inline]
    pub fn arity(&self, t: TermId) -> usize {
        self.nodes[t as usize].len as usize
    }
    #[inline]
    pub fn var_id(&self, t: TermId) -> Option<u32> {
        if self.kind(t) == T_VAR {
            Some(self.nodes[t as usize].sym)
        } else {
            None
        }
    }

    /// Structural variable containment. Iterative and allocation-free after
    /// warm-up: term depth is input-controlled and must not reach the native
    /// stack, and this runs on every derived head.
    pub fn contains_var(&mut self, t: TermId) -> bool {
        if self.stamp.len() < self.nodes.len() {
            self.stamp.resize(self.nodes.len(), 0);
        }
        self.stamp_gen = self.stamp_gen.wrapping_add(1);
        if self.stamp_gen == 0 {
            self.stamp.iter_mut().for_each(|s| *s = 0);
            self.stamp_gen = 1;
        }
        let gen = self.stamp_gen;
        self.stack.clear();
        self.stack.push(t);
        while let Some(x) = self.stack.pop() {
            if self.stamp[x as usize] == gen {
                continue;
            }
            self.stamp[x as usize] = gen;
            let n = self.nodes[x as usize];
            if n.kind == T_VAR {
                return true;
            }
            let (s, l) = (n.start as usize, n.len as usize);
            for i in (0..l).rev() {
                let c = self.children[s + i];
                self.stack.push(c);
            }
        }
        false
    }

    #[inline]
    pub fn is_ground(&mut self, t: TermId) -> bool {
        !self.contains_var(t)
    }

    // ---- constructors -----------------------------------------------------

    /// A variable with the given id. Repeated calls return the same node, so
    /// variable identity is stable and usable as a hash key.
    pub fn var(&mut self, id: u32) -> TermId {
        if let Some(&t) = self.var_ids.get(&id) {
            return t;
        }
        let t = self.intern(T_VAR, id, &[], None);
        self.var_ids.insert(id, t);
        t
    }

    /// Allocate a globally fresh variable. Never returns an id handed out
    /// before, for the lifetime of the store.
    pub fn fresh_var(&mut self) -> (TermId, u32) {
        let id = self.next_var;
        self.next_var += 1;
        let t = self.var(id);
        (t, id)
    }

    #[inline]
    pub fn next_var_id(&self) -> u32 {
        self.next_var
    }

    pub fn constant(&mut self, sym: SymId) -> TermId {
        self.intern(T_CONST, sym, &[], Some(0))
    }

    pub fn func(&mut self, sym: SymId, args: &[TermId]) -> TermId {
        self.intern(T_FUN, sym, args, None)
    }

    /// Atoms are hash-consed in the *same* space as terms (kind `T_ATOM`), so a
    /// ground fact is one `u32` and dedup is one integer compare. This is what
    /// lets the fact table be a `FxHashSet<TermId>` rather than a set of vectors.
    pub fn atom(&mut self, pred: SymId, args: &[TermId]) -> TermId {
        self.intern(T_ATOM, pred, args, None)
    }

    /// `arity_check` is supplied for constants only, where a `len` of 0 must be
    /// recorded without disturbing the child arena.
    fn intern(&mut self, kind: u8, sym: SymId, args: &[TermId], _const: Option<u8>) -> TermId {
        let h = content_hash(kind, sym, args);
        if let Some(&id) = self.buckets.get(&h) {
            for &id in bucket {
                let c = self.nodes[id as usize];
                if c.kind == kind && c.sym == sym && c.len as usize == args.len() {
                    let (s, l) = (c.start as usize, c.len as usize);
                    if self.children[s..s + l] == *args {
                        return id;
                    }
                }
            }
        }
        let start = self.children.len() as u32;
        self.children.extend_from_slice(args);
        let id = self.nodes.len() as TermId;
        self.nodes.push(TermNode {
            kind,
            sym,
            start,
            len: args.len() as u16,
        });
        self.buckets.entry(h).or_default().push(id);
        id
    }

    // ---- inspection -------------------------------------------------------

    #[inline]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }
    #[inline]
    pub fn child_count(&self) -> usize {
        self.children.len()
    }
    /// Lower bound on live payload bytes: no `String`, no `Rc`, no per-node heap
    /// block. Hash-table overhead is excluded; see docs/PERFORMANCE.md.
    pub fn bytes(&self) -> usize {
        self.nodes.len() * std::mem::size_of::<TermNode>()
            + self.children.len() * std::mem::size_of::<TermId>()
    }
    pub const fn node_size_bytes() -> usize {
        std::mem::size_of::<TermNode>()
    }

    /// Debug aid: confirm the arena holds no dead child storage, i.e. that a
    /// duplicate `intern` never left an orphaned argument vector behind.
    pub fn assert_no_dead_children(&self) {
        let mut next = 0u32;
        for n in &self.nodes {
            assert_eq!(n.start, next, "child arena has a gap before node");
            next = n.start + n.len as u32;
        }
        assert_eq!(next as usize, self.children.len(), "trailing child storage");
    }

    /// Pre-order structural walk. Iterative: depth is input-controlled.
    pub fn walk(&self, t: TermId, f: &mut impl FnMut(TermId)) {
        let mut stack = Vec::new();
        stack.push(t);
        while let Some(x) = stack.pop() {
            f(x);
            let n = self.nodes[x as usize];
            let (s, l) = (n.start as usize, n.len as usize);
            for i in (0..l).rev() {
                let c = self.children[s + i];
                stack.push(c);
            }
        }
    }

    /// Renderer for proofs, error messages and tests. Not a hot path.
    /// Rename variables through `env`, returning a hash-consed term.
    ///
    /// Used once per rule to build the cached "fresh" copy that inference
    /// reuses across every derivation. Iterative, and bounded by `depth` so a
    /// hostile input cannot reach the native stack. Not a hot path.
    pub fn rename(&mut self, t: TermId, env: &FxHashMap<u32, TermId>, depth: usize) -> TermId {
        const MAX: usize = 4096;
        if depth > MAX {
            return t;
        }
        let n = self.nodes[t as usize];
        match n.kind {
            T_VAR => match env.get(&n.sym) {
                Some(&g) => g,
                None => t,
            },
            T_CONST => t,
            _ => {
                let len = n.len as usize;
                let mut kids = Vec::with_capacity(len);
                let (s, l) = (n.start as usize, n.len as usize);
                for i in 0..l {
                    let c = self.children[s + i];
                    kids.push(self.rename(c, env, depth + 1));
                }
                if n.kind == T_FUN {
                    self.func(n.sym, &kids)
                } else {
                    self.atom(n.sym, &kids)
                }
            }
        }
    }

    pub fn show(&self, t: TermId, syms: &crate::symbol::SymbolTable) -> String {
        let mut out = String::new();
        self.show_into(t, syms, &mut out);
        out
    }

    fn show_into(&self, t: TermId, syms: &crate::symbol::SymbolTable, out: &mut String) {
        let n = self.nodes[t as usize];
        match n.kind {
            T_VAR => {
                out.push('_');
                out.push_str(&n.sym.to_string());
            }
            T_CONST => out.push_str(syms.name(n.sym)),
            T_FUN | T_ATOM => {
                out.push_str(syms.name(n.sym));
                if n.len > 0 {
                    out.push('(');
                    for (i, &a) in self.args(t).iter().enumerate() {
                        if i > 0 {
                            out.push(',');
                        }
                        self.show_into(a, syms, out);
                    }
                    out.push(')');
                }
            }
            _ => out.push('?'),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::SymbolTable;

    #[test]
    fn structural_sharing() {
        let mut s = SymbolTable::new();
        let a = s.constant("a");
        let f = s.func("f", 1);
        let mut ts = TermStore::new();
        assert_eq!(ts.func(f, &[a]), ts.func(f, &[a]));
    }

    #[test]
    fn distinct_terms_do_not_share() {
        let mut s = SymbolTable::new();
        let a = s.constant("a");
        let b = s.constant("b");
        let f = s.func("f", 1);
        let mut ts = TermStore::new();
        assert_ne!(ts.func(f, &[a]), ts.func(f, &[b]));
        assert_eq!(ts.func(f, &[a]).min(ts.func(f, &[b])), ts.func(f, &[a]));
    }

    #[test]
    fn interning_leaves_no_dead_child_storage() {
        let mut s = SymbolTable::new();
        let a = s.constant("a");
        let g = s.func("g", 1);
        let mut ts = TermStore::new();
        for _ in 0..100 {
            ts.func(g, &[a]);
            ts.func(g, &[a]);
        }
        ts.assert_no_dead_children();
    }

    #[test]
    fn var_identity_is_stable() {
        let mut ts = TermStore::new();
        let (v, id) = ts.fresh_var();
        assert_eq!(ts.var(id), v);
        let (w, _) = ts.fresh_var();
        assert_ne!(v, w);
    }

    #[test]
    fn groundness() {
        let mut s = SymbolTable::new();
        let a = s.constant("a");
        let f = s.func("f", 1);
        let mut ts = TermStore::new();
        let fa = ts.func(f, &[a]);
        assert!(ts.is_ground(fa));
        let (v, _) = ts.fresh_var();
        assert!(!ts.is_ground(ts.func(f, &[v])));
        assert!(ts.is_ground(a));
    }

    #[test]
    fn atoms_are_hash_consed() {
        let mut s = SymbolTable::new();
        let a = s.constant("a");
        let p = s.predicate("p", 1);
        let mut ts = TermStore::new();
        let x = ts.atom(p, &[a]);
        assert_eq!(x, ts.atom(p, &[a]));
        assert_eq!(ts.kind(x), T_ATOM);
        ts.assert_no_dead_children();
    }

    #[test]
    fn deep_terms_do_not_overflow_the_stack() {
        let mut s = SymbolTable::new();
        let cons = s.func("cons", 2);
        let mut ts = TermStore::new();
        let x = ts.constant(s.constant("x"));
        let y = ts.constant(s.constant("y"));
        let mut t = x;
        for i in 0..100_000 {
            t = ts.func(cons, &[if i % 2 == 0 { x } else { y }, t]);
        }
        let mut count = 0u64;
        ts.walk(t, &mut |_| count += 1);
        assert_eq!(count, 200_001);
    }

    #[test]
    fn renderer_handles_nesting() {
        let mut s = SymbolTable::new();
        let f = s.func("f", 1);
        let g = s.func("g", 2);
        let mut ts = TermStore::new();
        let a = ts.constant(s.constant("a"));
        let b = ts.constant(s.constant("b"));
        let inner = ts.func(f, &[a]);
        let outer = ts.func(g, &[inner, b]);
        assert_eq!(ts.show(outer, &s), "g(f(a),b)");
    }
}
