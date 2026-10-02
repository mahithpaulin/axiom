//! Symbol interning.
//!
//! Every name that can appear in a term or an atom is interned to a `u32` once
//! and never stored as a `String` again on any hot path. Two reasons:
//!
//! 1. `TermNode` is 16 bytes. Storing a name inline would make it 24+ and add a
//!    pointer chase to every structural comparison.
//! 2. Predicate identity drives indexing. A `pred: u32` is a direct array
//!    index into per-predicate index structures; a `&str` requires a lookup.
//!
//! Constants, function symbols and predicates share one id space but are
//! namespaced by `SymKind`, so `a` as a constant and `a/0` as a nullary
//! predicate do not collide.

use crate::hash::FxHashMap;
use core::fmt;

pub type SymId = u32;
pub type NameId = u32;

pub const SK_CONST: u8 = 0;
pub const SK_FUN: u8 = 1;
pub const SK_PRED: u8 = 2;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Sym {
    name: NameId,
    arity: u16,
    kind: u8,
}

#[derive(Default)]
pub struct SymbolTable {
    name_ids: FxHashMap<Box<str>, NameId>,
    names: Vec<Box<str>>,
    sym_ids: FxHashMap<Sym, SymId>,
    syms: Vec<Sym>,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern `name/arity` in the given namespace. Idempotent.
    pub fn intern(&mut self, name: &str, arity: u16, kind: u8) -> SymId {
        let key: Box<str> = match self.name_ids.get(name) {
            Some(&id) => {
                let _ = id;
                return self.intern_existing(name, arity, kind);
            }
            None => name.into(),
        };
        let name_id = self.names.len() as NameId;
        self.names.push(key.clone());
        self.name_ids.insert(key, name_id);
        self.insert_sym(Sym {
            name: name_id,
            arity,
            kind,
        })
    }

    #[inline]
    fn intern_existing(&mut self, name: &str, arity: u16, kind: u8) -> SymId {
        let name_id = self.name_ids[name];
        self.insert_sym(Sym {
            name: name_id,
            arity,
            kind,
        })
    }

    #[inline]
    fn insert_sym(&mut self, s: Sym) -> SymId {
        if let Some(&id) = self.sym_ids.get(&s) {
            return id;
        }
        let id = self.syms.len() as SymId;
        self.syms.push(s);
        self.sym_ids.insert(s, id);
        id
    }

    pub fn constant(&mut self, name: &str) -> SymId {
        self.intern(name, 0, SK_CONST)
    }
    pub fn func(&mut self, name: &str, arity: u16) -> SymId {
        self.intern(name, arity, SK_FUN)
    }
    pub fn predicate(&mut self, name: &str, arity: u16) -> SymId {
        self.intern(name, arity, SK_PRED)
    }

    /// Render as `name/arity`, the conventional logical notation.
    pub fn render(&self, s: SymId) -> String {
        let sym = self.syms[s as usize];
        format!("{}/{}", &self.names[sym.name as usize], sym.arity)
    }

    #[inline]
    pub fn name(&self, s: SymId) -> &str {
        &self.names[self.syms[s as usize].name as usize]
    }
    #[inline]
    pub fn arity(&self, s: SymId) -> u16 {
        self.syms[s as usize].arity
    }
    #[inline]
    pub fn kind(&self, s: SymId) -> u8 {
        self.syms[s as usize].kind
    }
    #[inline]
    pub fn count(&self) -> usize {
        self.syms.len()
    }
}

impl fmt::Debug for SymbolTable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SymbolTable")
            .field("symbols", &self.syms.len())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interning_is_idempotent() {
        let mut t = SymbolTable::new();
        let a = t.constant("x");
        let b = t.constant("x");
        assert_eq!(a, b);
    }

    #[test]
    fn namespaces_do_not_collide() {
        let mut t = SymbolTable::new();
        let c = t.constant("a");
        let p = t.predicate("a", 0);
        assert_ne!(c, p, "a/0 constant and a/0 predicate must differ");
        assert_eq!(t.kind(c), SK_CONST);
        assert_eq!(t.kind(p), SK_PRED);
    }

    #[test]
    fn arity_is_part_of_identity() {
        let mut t = SymbolTable::new();
        assert_ne!(t.func("f", 1), t.func("f", 2));
    }
}
