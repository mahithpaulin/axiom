//! The logical program: rules, literals, stratification, and the exterior-side
//! builder that produces them.
//!
//! ## Deliberate restriction: stratified Datalog, not Prolog
//!
//! Rules have a single positive head and a body of literals. This is
//! *Stratified Datalog* (a subset of Horn logic), chosen because it is
//! **decidable and has a unique least model**. That is not a limitation to work
//! around, it is the property that makes soundness claims possible:
//!
//! * Negation is *stratified negation*, not negation-as-failure. NAF is a
//!   database idiom, not a logical one; it makes the "is this true" question
//!   unanswerable and completeness claims meaningless. Under stratification,
//!   every IDB predicate has a well-defined least fixed point that the engine
//!   computes exactly.
//! * Because the fixpoint is unique, `Refuted` is a real claim: "the atom is
//!   absent from the least model", not "the search gave up".
//!
//! Rules whose head contains a function symbol, or whose head contains
//! variables in a position that cannot be bound by an EDB constant, are marked
//! `backward_only`. Forward chaining simply cannot enumerate them, and saying so
//! explicitly is better than silently dropping them or looping forever. They
//! remain usable by backward resolution, which is exactly why both engines
//! exist.
//!
//! ## Stratification
//!
//! `h` depends positively on `p` => `stratum(h) >= stratum(p)`
//! `h` depends negatively on `p` => `stratum(h) >  stratum(p)`
//! Computed by bound relaxation (Bellman--Ford over `max`), which handles
//! positive cycles -- e.g. transitive closure -- without a Tarjan pass. A
//! negative edge that cannot be made strictly downward means the program is not
//! stratified, and the builder rejects it rather than guessing.

use crate::hash::FxHashMap;
use crate::symbol::SymbolTable;
use crate::term::{TermId, TermStore, T_ATOM, T_VAR};
use core::fmt;

pub type RuleId = u32;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Literal {
    /// true = positive, false = negative (stratified negation).
    pub pos: bool,
    pub atom: TermId,
}

impl Literal {
    #[inline]
    pub fn pos(atom: TermId) -> Self {
        Literal { pos: true, atom }
    }
    #[inline]
    pub fn neg(atom: TermId) -> Self {
        Literal { pos: false, atom }
    }
}

#[derive(Clone)]
pub struct Rule {
    pub id: RuleId,
    pub head: TermId,
    pub body: Vec<Literal>,
    pub stratum: u32,
    /// Local variable ids appearing in head or body, in first-seen order.
    pub local_vars: Vec<u32>,
    /// Cannot be evaluated by bottom-up forward chaining (function symbols in
    /// the head). Still usable by backward resolution.
    pub backward_only: bool,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ProgramError {
    /// `p` appears both positively and negatively in a cycle, so no
    /// stratification exists.
    NotStratified { pred: u32 },
    /// A declared predicate was used at the wrong arity.
    ArityMismatch { pred: u32, declared: u16, used: u16 },
    /// Duplicate or empty predicate name.
    BadPredicate { name: String },
}

impl fmt::Display for ProgramError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProgramError::NotStratified { pred } => {
                write!(
                    f,
                    "program is not stratified: negative cycle through predicate #{pred}"
                )
            }
            ProgramError::ArityMismatch {
                pred,
                declared,
                used,
            } => write!(
                f,
                "predicate #{pred} declared with arity {declared} but used with arity {used}"
            ),
            ProgramError::BadPredicate { name } => {
                write!(f, "invalid predicate declaration '{name}'")
            }
        }
    }
}

#[derive(Clone)]
pub struct Program {
    pub symbols: SymbolTable,
    pub store: TermStore,
    pub rules: Vec<Rule>,
    /// Number of strata.
    pub num_strata: u32,
    pub pred_stratum: Vec<u32>,
    /// True for predicates defined by at least one rule head.
    pub pred_idb: Vec<bool>,
    /// Rules bucketed by stratum, so the evaluator iterates only what applies.
    pub by_stratum: Vec<Vec<RuleId>>,
    /// Predicates that appear in a body but never in a head.
    pub pred_edb: Vec<bool>,
}

impl Program {
    pub fn rule(&self, id: RuleId) -> &Rule {
        &self.rules[id as usize]
    }
    #[inline]
    pub fn pred_of(&self, atom: TermId) -> u32 {
        self.store.sym(atom)
    }
    #[inline]
    pub fn num_preds(&self) -> usize {
        self.pred_stratum.len()
    }
    /// Total rules that forward chaining may evaluate.
    pub fn forward_rules(&self) -> usize {
        self.rules.iter().filter(|r| !r.backward_only).count()
    }
    pub fn arity_check(&self) -> Result<(), ProgramError> {
        for r in &self.rules {
            for a in std::iter::once(&r.head).chain(r.body.iter().map(|l| &l.atom)) {
                let p = self.store.sym(*a);
                let used = self.store.arity(*a) as u16;
                if self.symbols.arity(p) != used {
                    return Err(ProgramError::ArityMismatch {
                        pred: p,
                        declared: self.symbols.arity(p),
                        used,
                    });
                }
            }
        }
        Ok(())
    }
    pub fn payload_bytes(&self) -> usize {
        self.store.bytes()
    }
}

/// Exterior-side builder.
///
/// Rule-local variables are namespaced by name *per rule*: two rules that both
/// mention `X` get distinct global variable ids, so their atoms can never be
/// confused. This is the mechanism that lets a cached, once-renamed copy of a
/// rule be reused across thousands of derivations without any risk of capture.
pub struct Builder {
    pub symbols: SymbolTable,
    pub store: TermStore,
    rules: Vec<Rule>,
    pred_idb: Vec<bool>,
    pred_edb: Vec<bool>,
    cur_vars: FxHashMap<String, (u32, TermId)>,
    cur_var_order: Vec<u32>,
}

impl Builder {
    pub fn new() -> Self {
        Builder {
            symbols: SymbolTable::new(),
            store: TermStore::new(),
            rules: Vec::new(),
            pred_idb: Vec::new(),
            pred_edb: Vec::new(),
            cur_vars: FxHashMap::default(),
            cur_var_order: Vec::new(),
        }
    }

    /// Declare a predicate so its stratum vector is sized before use. Optional;
    /// undeclared predicates are added on first appearance.
    pub fn declare_pred(&mut self, name: &str, arity: u16) {
        let p = self.symbols.predicate(name, arity);
        self.size_to(p);
    }

    /// Grow the per-predicate vectors to cover symbol id `p`.
    ///
    /// Must only ever *grow*. `Vec::resize` truncates when given a smaller
    /// length, and symbol ids are not allocated in index order across the
    /// constant/function/predicate namespaces, so a later `p` can easily be
    /// smaller than an earlier one. Using `resize` here silently shrank the
    /// vectors and every subsequent `rule` call indexed out of bounds --
    /// caught by `tests/soundness.rs::predicate_vectors_never_shrink`.
    fn size_to(&mut self, p: u32) {
        let n = p as usize + 1;
        if self.pred_idb.len() < n {
            self.pred_idb.resize(n, false);
        }
        if self.pred_edb.len() < n {
            self.pred_edb.resize(n, false);
        }
    }

    pub fn constant(&mut self, name: &str) -> TermId {
        let s = self.symbols.constant(name);
        self.store.constant(s)
    }

    pub fn func(&mut self, name: &str, arity: u16, args: &[TermId]) -> TermId {
        let s = self.symbols.func(name, arity);
        self.store.func(s, args)
    }

    /// Rule-local variable. Resets at every `fact`/`rule` boundary.
    pub fn var(&mut self, name: &str) -> TermId {
        if let Some(&(_, t)) = self.cur_vars.get(name) {
            return t;
        }
        let (t, id) = self.store.fresh_var();
        self.cur_vars.insert(name.to_string(), (id, t));
        self.cur_var_order.push(id);
        t
    }

    pub fn atom(&mut self, name: &str, arity: u16, args: &[TermId]) -> TermId {
        if name.is_empty() {
            // The exterior cannot silently create an unnamed predicate; callers
            // get an interned private symbol rather than a panic.
            let p = self.symbols.predicate("", arity);
            self.size_to(p);
            return self.store.atom(p, args);
        }
        let p = self.symbols.predicate(name, arity);
        self.size_to(p);
        self.store.atom(p, args)
    }

    /// Positive body literal. Exists so rule bodies can be written as
    /// `vec![b.pos(...), b.pos(...)]` without a temporary per literal.
    pub fn pos(&mut self, name: &str, arity: u16, args: &[TermId]) -> Literal {
        let a = self.atom(name, arity, args);
        Literal::pos(a)
    }

    /// Negated body literal.
    pub fn neg(&mut self, name: &str, arity: u16, args: &[TermId]) -> Literal {
        let a = self.atom(name, arity, args);
        Literal::neg(a)
    }

    /// Ground fact from plain names: `fact_n("edge", &["a", "b"])`.
    pub fn fact_n(&mut self, name: &str, args: &[&str]) -> RuleId {
        let mut ts = Vec::with_capacity(args.len());
        for a in args {
            ts.push(self.constant(a));
        }
        let head = self.atom(name, args.len() as u16, &ts);
        self.fact(head)
    }

    /// Ground atom from plain names, for use as a goal.
    pub fn goal_n(&mut self, name: &str, args: &[&str]) -> TermId {
        let mut ts = Vec::with_capacity(args.len());
        for a in args {
            ts.push(self.constant(a));
        }
        self.atom(name, args.len() as u16, &ts)
    }

    /// A ground fact: a rule with an empty body.
    pub fn fact(&mut self, head: TermId) -> RuleId {
        debug_assert_eq!(self.store.kind(head), T_ATOM);
        self.pred_idb[self.store.sym(head) as usize] = true;
        let id = self.rules.len() as RuleId;
        self.rules.push(Rule {
            id,
            head,
            body: Vec::new(),
            stratum: 0,
            local_vars: Vec::new(),
            backward_only: false,
        });
        self.cur_vars.clear();
        self.cur_var_order.clear();
        id
    }

    /// Convenience: a predicate with no arguments (propositional atom).
    pub fn nullary(&mut self, name: &str) -> TermId {
        self.atom(name, 0, &[])
    }

    pub fn rule(&mut self, head: TermId, body: Vec<Literal>) -> RuleId {
        debug_assert_eq!(self.store.kind(head), T_ATOM);
        let hp = self.store.sym(head);
        self.pred_idb[hp as usize] = true;
        for l in &body {
            let p = self.store.sym(l.atom);
            if !self.pred_idb[p as usize] {
                self.pred_edb[p as usize] = true;
            }
        }
        // Only variables that actually *occur* in the rule are listed. A
        // variable created by the builder but left unused must not appear, or
        // the proof checker would demand an instantiation for it and reject
        // every derivation.
        let local_vars = self.collect_vars(head, &body);
        self.cur_vars.clear();
        self.cur_var_order.clear();
        let backward_only = self.head_is_unenumerable(head);
        let id = self.rules.len() as RuleId;
        self.rules.push(Rule {
            id,
            head,
            body,
            stratum: 0,
            local_vars,
            backward_only,
        });
        self.cur_vars.clear();
        id
    }

    /// Variables occurring in the head or any body literal, in deterministic
    /// pre-order (head first, then body literals left to right, arguments left
    /// to right). Deterministic order matters: it fixes the shape of recorded
    /// proofs, so an identical program produces byte-identical derivations and
    /// benchmarks are reproducible.
    fn collect_vars(&mut self, head: TermId, body: &[Literal]) -> Vec<u32> {
        let mut out: Vec<u32> = Vec::new();
        let mut stack = vec![head];
        for l in body {
            stack.push(l.atom);
        }
        while let Some(x) = stack.pop() {
            let n = self.store.node(x);
            if n.kind == T_VAR {
                if !out.contains(&n.sym) {
                    out.push(n.sym);
                }
                continue;
            }
            let (s, l) = (n.start as usize, n.len as usize);
            for i in (0..l).rev() {
                let c = self.store.children_at(s + i);
                stack.push(c);
            }
        }
        out
    }

    /// A head is unenumerable bottom-up if it contains a function symbol (the
    /// relation has an infinite domain) -- variables are fine, because a
    /// forward-chaining head is always instantiated from ground premises.
    fn head_is_unenumerable(&self, head: TermId) -> bool {
        let mut found = false;
        let mut stack = vec![head];
        while let Some(x) = stack.pop() {
            let n = self.store.node(x);
            if n.kind == crate::term::T_FUN {
                found = true;
                break;
            }
            if n.kind == crate::term::T_VAR {
                continue;
            }
            for &a in self.store.args(x) {
                stack.push(a);
            }
        }
        found
    }

    pub fn build(mut self) -> Result<Program, ProgramError> {
        let num_preds = self.symbols.count();
        self.pred_idb.resize(num_preds, false);
        self.pred_edb.resize(num_preds, false);

        // Relaxation to a stratification, enforcing both edge kinds in the
        // *same* loop:
        //
        //     positive literal:   stratum(h) >= stratum(p)
        //     negative literal:   stratum(h) >  stratum(p)
        //
        // Folding the negative bound in only after the loop -- as an earlier
        // version did -- accepts programs whose negation cycle is reached
        // through a positive edge, leaving a positive edge pointing at a
        // *higher* stratum. Such a program has no stratification, and
        // evaluating it produced wrong answers while reporting success.
        let np = num_preds;
        let mut stratum = vec![0u32; np];
        let mut rounds = 0usize;
        loop {
            let mut changed = false;
            for r in &self.rules {
                let h = self.store.sym(r.head) as usize;
                for l in &r.body {
                    let p = self.store.sym(l.atom) as usize;
                    let want = if l.pos { stratum[p] } else { stratum[p] + 1 };
                    if stratum[h] < want {
                        stratum[h] = want;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
            rounds += 1;
            // Strata are bounded by the predicate count; exceeding it means a
            // cycle no assignment can satisfy, i.e. no stratification exists.
            // Checked in release too, so a pathological program is rejected
            // rather than looping.
            if rounds > np + 2 {
                return Err(ProgramError::NotStratified { pred: u32::MAX });
            }
        }

        for r in &mut self.rules {
            r.stratum = stratum[self.store.sym(r.head) as usize];
        }
        let num_strata = stratum.iter().copied().max().unwrap_or(0) + 1;
        let mut by_stratum = vec![Vec::new(); num_strata as usize];
        for r in &self.rules {
            by_stratum[r.stratum as usize].push(r.id);
        }

        let prog = Program {
            symbols: self.symbols,
            store: self.store,
            rules: self.rules,
            num_strata,
            pred_stratum: stratum,
            pred_idb: self.pred_idb,
            pred_edb: self.pred_edb,
            by_stratum,
        };
        prog.arity_check()?;
        Ok(prog)
    }
}

impl Default for Builder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rule_local_variables_are_namespaced_per_rule() {
        let mut b = Builder::new();
        let x1 = b.var("X");
        let h1 = b.atom("p", 1, &[x1]);
        let body1 = vec![b.pos("q", 1, &[x1])];
        b.rule(h1, body1);
        let x2 = b.var("X");
        assert_ne!(x1, x2, "X in two rules must be distinct variables");
    }

    #[test]
    fn transitive_closure_is_stratified() {
        let mut b = Builder::new();
        b.fact_n("edge", &["a", "b"]);
        let x = b.var("X");
        let y = b.var("Y");
        let z = b.var("Z");
        let head = b.atom("path", 2, &[x, z]);
        let e = b.pos("edge", 2, &[x, y]);
        let p = b.pos("path", 2, &[y, z]);
        b.rule(head, vec![e, p]);
        let prog = b.build().unwrap();
        assert_eq!(prog.num_strata, 1);
        // Positive self-cycle must be allowed.
        assert_eq!(prog.forward_rules(), 2);
    }

    #[test]
    fn negative_cycles_are_rejected() {
        // p :- not q ;  q :- not p
        let mut b = Builder::new();
        let p = b.atom("p", 0, &[]);
        let q = b.atom("q", 0, &[]);
        let np = Literal::neg(q);
        let nq = Literal::neg(p);
        b.rule(p, vec![np]);
        b.rule(q, vec![nq]);
        assert!(matches!(b.build(), Err(ProgramError::NotStratified { .. })));
    }

    #[test]
    fn stratified_negation_gets_a_strictly_higher_stratum() {
        let mut b = Builder::new();
        b.fact_n("e", &["x"]);
        let x = b.var("X");
        let p = b.atom("p", 0, &[]);
        let ex = b.atom("e", 1, &[x]);
        let pe = b.pos("e", 1, &[x]);
        let ne = Literal::neg(ex);
        b.rule(p, vec![pe, ne]);
        let mut prog = b.build().unwrap();
        let pp = prog.symbols.predicate("p", 0);
        let ee = prog.symbols.predicate("e", 1);
        assert!(prog.pred_stratum[pp as usize] > prog.pred_stratum[ee as usize]);
        assert_eq!(prog.num_strata, 2);
    }

    #[test]
    fn function_symbols_in_the_head_are_backward_only() {
        let mut b = Builder::new();
        let q = b.nullary("q");
        let x = b.var("X");
        let succ = b.symbols.func("succ", 1);
        let hx = b.store.func(succ, &[x]);
        let head = b.atom("q", 1, &[hx]);
        let pq = Literal::pos(q);
        b.rule(head, vec![pq]);
        let prog = b.build().unwrap();
        assert_eq!(prog.forward_rules(), 0);
        assert_eq!(prog.rules.len(), 1);
        assert!(prog.rules[0].backward_only);
    }

    #[test]
    fn arity_is_enforced() {
        // A predicate is interned per (name, arity), so a mismatch cannot occur
        // through the builder; this pins that property.
        let mut b = Builder::new();
        let x = b.var("X");
        let h = b.atom("p", 1, &[x]);
        b.fact(h);
        let prog = b.build().unwrap();
        assert!(prog.arity_check().is_ok());
    }

    #[test]
    fn symbol_kind_is_predicate_for_atoms() {
        let mut b = Builder::new();
        let a = b.atom("p", 1, &[]);
        assert_eq!(b.store.kind(a), T_ATOM);
        assert_eq!(b.symbols.kind(b.store.sym(a)), crate::symbol::SK_PRED);
    }
}
