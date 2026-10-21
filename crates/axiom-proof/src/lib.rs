//! Axiom v4 trusted proof kernel.
//!
//! Two independent checks live here:
//!
//! * [`check_resolution`] validates a first-order resolution/factoring
//!   refutation, including every unifier and every derived clause;
//! * [`stlc`] is a small simply typed lambda-calculus kernel with explicit
//!   types, used as the typed-proof core and as a check on the Curry–Howard
//!   bridge.
//!
//! The kernel does **not** trust the prover that produced a proof. It repeats
//! unification and clause construction from the recorded steps. It does trust
//! the input clauses, which are the clausal form of the problem; CNF conversion
//! is a prover-side obligation documented in `docs/v4/VERIFICATION.md`.

use axiom_ir::{IrError, Sexp};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

pub mod stlc;

pub use stlc::{check_type, infer_type, Expr, StlcError, Type};

/// A first-order variable is an interned name. There are no sorts in the
/// resolution kernel; the typed IR is the front-end representation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Term {
    Var(String),
    Const(String),
    App(String, Vec<Term>),
}

impl Term {
    pub fn var(name: impl Into<String>) -> Self {
        Term::Var(name.into())
    }

    pub fn constant(name: impl Into<String>) -> Self {
        Term::Const(name.into())
    }

    pub fn app(name: impl Into<String>, args: Vec<Term>) -> Self {
        Term::App(name.into(), args)
    }

    pub fn apply(&self, subst: &Subst) -> Term {
        match self {
            Term::Var(v) => match subst.get(v) {
                Some(t) => t.apply(subst),
                None => self.clone(),
            },
            Term::Const(_) => self.clone(),
            Term::App(f, args) => {
                Term::App(f.clone(), args.iter().map(|t| t.apply(subst)).collect())
            }
        }
    }

    pub fn vars(&self, out: &mut BTreeSet<String>) {
        match self {
            Term::Var(v) => {
                out.insert(v.clone());
            }
            Term::Const(_) => {}
            Term::App(_, args) => {
                for a in args {
                    a.vars(out);
                }
            }
        }
    }

    pub fn to_sexp(&self) -> Sexp {
        match self {
            Term::Var(v) => Sexp::List(vec![Sexp::atom("var"), Sexp::atom(v.clone())]),
            Term::Const(c) => Sexp::List(vec![Sexp::atom("const"), Sexp::atom(c.clone())]),
            Term::App(f, args) => Sexp::List(vec![
                Sexp::atom("app"),
                Sexp::atom(f.clone()),
                Sexp::List(args.iter().map(Term::to_sexp).collect()),
            ]),
        }
    }

    pub fn from_sexp(s: &Sexp) -> Result<Self, KernelError> {
        let xs = list(s, "term")?;
        let tag = head_of(&xs, "term")?;
        match tag {
            "var" if xs.len() == 2 => Ok(Term::var(atom(&xs[1], "variable")?)),
            "const" if xs.len() == 2 => Ok(Term::constant(atom(&xs[1], "constant")?)),
            "app" if xs.len() == 3 => {
                let args = list(&xs[2], "application")?
                    .iter()
                    .map(Term::from_sexp)
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Term::app(atom(&xs[1], "function")?, args))
            }
            _ => Err(KernelError::Malformed(format!("bad term form {tag}"))),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(v) => f.write_str(v),
            Term::Const(c) => f.write_str(c),
            Term::App(n, args) => {
                write!(f, "{n}(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        f.write_str(",")?;
                    }
                    write!(f, "{a}")?;
                }
                f.write_str(")")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Atom {
    pub predicate: String,
    pub args: Vec<Term>,
}

impl Atom {
    pub fn new(predicate: impl Into<String>, args: Vec<Term>) -> Self {
        Atom {
            predicate: predicate.into(),
            args,
        }
    }

    pub fn apply(&self, subst: &Subst) -> Atom {
        Atom::new(
            self.predicate.clone(),
            self.args.iter().map(|t| t.apply(subst)).collect(),
        )
    }

    pub fn to_sexp(&self) -> Sexp {
        Sexp::List(vec![
            Sexp::atom("atom"),
            Sexp::atom(self.predicate.clone()),
            Sexp::List(self.args.iter().map(Term::to_sexp).collect()),
        ])
    }

    pub fn from_sexp(s: &Sexp) -> Result<Self, KernelError> {
        let xs = list(s, "atom")?;
        if xs.len() != 3 || head_of(&xs, "atom")? != "atom" {
            return Err(KernelError::Malformed("atom form".into()));
        }
        let args = list(&xs[2], "atom args")?
            .iter()
            .map(Term::from_sexp)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Atom::new(atom(&xs[1], "predicate")?, args))
    }
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.predicate)?;
        for (i, a) in self.args.iter().enumerate() {
            if i > 0 {
                f.write_str(",")?;
            }
            write!(f, "{a}")?;
        }
        f.write_str(")")
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Literal {
    pub positive: bool,
    pub atom: Atom,
}

impl Literal {
    pub fn positive(atom: Atom) -> Self {
        Literal {
            positive: true,
            atom,
        }
    }

    pub fn negative(atom: Atom) -> Self {
        Literal {
            positive: false,
            atom,
        }
    }

    pub fn apply(&self, subst: &Subst) -> Literal {
        Literal {
            positive: self.positive,
            atom: self.atom.apply(subst),
        }
    }

    pub fn to_sexp(&self) -> Sexp {
        Sexp::List(vec![
            Sexp::atom("lit"),
            Sexp::atom(if self.positive { "pos" } else { "neg" }),
            self.atom.to_sexp(),
        ])
    }

    pub fn from_sexp(s: &Sexp) -> Result<Self, KernelError> {
        let xs = list(s, "literal")?;
        if xs.len() != 3 || head_of(&xs, "literal")? != "lit" {
            return Err(KernelError::Malformed("literal form".into()));
        }
        let atom = Atom::from_sexp(&xs[2])?;
        match atom_str(&xs[1], "polarity")? {
            "pos" => Ok(Literal::positive(atom)),
            "neg" => Ok(Literal::negative(atom)),
            _ => Err(KernelError::Malformed("bad literal polarity".into())),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Clause {
    pub literals: Vec<Literal>,
}

impl Clause {
    pub fn new(literals: Vec<Literal>) -> Self {
        Clause {
            literals: normalize(literals),
        }
    }

    pub fn empty() -> Self {
        Clause::default()
    }

    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }

    pub fn to_sexp(&self) -> Sexp {
        Sexp::List(
            std::iter::once(Sexp::atom("clause"))
                .chain(self.literals.iter().map(Literal::to_sexp))
                .collect(),
        )
    }

    pub fn from_sexp(s: &Sexp) -> Result<Self, KernelError> {
        let xs = list(s, "clause")?;
        if xs.first().and_then(Sexp::as_atom) != Some("clause") {
            return Err(KernelError::Malformed("clause form".into()));
        }
        let literals = xs[1..]
            .iter()
            .map(Literal::from_sexp)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Clause::new(literals))
    }
}

fn normalize(mut literals: Vec<Literal>) -> Vec<Literal> {
    literals.sort();
    literals.dedup();
    literals
}

/// A substitution produced by unification. Variables are keyed by name.
pub type Subst = BTreeMap<String, Term>;

/// How a clause in a resolution proof was obtained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StepRule {
    Input,
    Factor {
        parent: usize,
        first: usize,
        second: usize,
    },
    Resolve {
        left: usize,
        right: usize,
        left_lit: usize,
        right_lit: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProofClause {
    pub clause: Clause,
    pub rule: StepRule,
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct ResolutionProof {
    pub clauses: Vec<ProofClause>,
}

impl ResolutionProof {
    pub fn to_sexp(&self) -> Sexp {
        Sexp::List(
            std::iter::once(Sexp::atom("resolution-proof"))
                .chain(self.clauses.iter().map(|c| {
                    Sexp::List(vec![
                        Sexp::atom("step"),
                        rule_to_sexp(&c.rule),
                        c.clause.to_sexp(),
                    ])
                }))
                .collect(),
        )
    }

    pub fn from_sexp(s: &Sexp) -> Result<Self, KernelError> {
        let xs = list(s, "resolution proof")?;
        if xs.first().and_then(Sexp::as_atom) != Some("resolution-proof") {
            return Err(KernelError::Malformed("resolution proof form".into()));
        }
        let clauses = xs[1..]
            .iter()
            .map(|step| {
                let ys = list(step, "proof step")?;
                if ys.len() != 3 || ys.first().and_then(Sexp::as_atom) != Some("step") {
                    return Err(KernelError::Malformed("proof step form".into()));
                }
                Ok(ProofClause {
                    rule: rule_from_sexp(&ys[1])?,
                    clause: Clause::from_sexp(&ys[2])?,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(ResolutionProof { clauses })
    }

    pub fn to_text(&self) -> String {
        self.to_sexp().render()
    }

    pub fn from_text(text: &str) -> Result<Self, KernelError> {
        let s = Sexp::parse(text).map_err(ir_err)?;
        Self::from_sexp(&s)
    }
}

fn rule_to_sexp(r: &StepRule) -> Sexp {
    match r {
        StepRule::Input => Sexp::List(vec![Sexp::atom("input")]),
        StepRule::Factor {
            parent,
            first,
            second,
        } => Sexp::List(vec![
            Sexp::atom("factor"),
            Sexp::atom(parent.to_string()),
            Sexp::atom(first.to_string()),
            Sexp::atom(second.to_string()),
        ]),
        StepRule::Resolve {
            left,
            right,
            left_lit,
            right_lit,
        } => Sexp::List(vec![
            Sexp::atom("resolve"),
            Sexp::atom(left.to_string()),
            Sexp::atom(right.to_string()),
            Sexp::atom(left_lit.to_string()),
            Sexp::atom(right_lit.to_string()),
        ]),
    }
}

fn rule_from_sexp(s: &Sexp) -> Result<StepRule, KernelError> {
    let xs = list(s, "rule")?;
    let tag = head_of(&xs, "rule")?;
    let num = |i: usize| -> Result<usize, KernelError> {
        let v = xs
            .get(i)
            .ok_or_else(|| KernelError::Malformed("missing rule field".into()))?;
        atom(v, "rule field")?
            .parse()
            .map_err(|_| KernelError::Malformed("rule field is not a number".into()))
    };
    match tag {
        "input" if xs.len() == 1 => Ok(StepRule::Input),
        "factor" if xs.len() == 4 => Ok(StepRule::Factor {
            parent: num(1)?,
            first: num(2)?,
            second: num(3)?,
        }),
        "resolve" if xs.len() == 6 => Ok(StepRule::Resolve {
            left: num(1)?,
            right: num(2)?,
            left_lit: num(3)?,
            right_lit: num(4)?,
        }),
        _ => Err(KernelError::Malformed(format!("bad rule form {tag}"))),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KernelError {
    Malformed(String),
    BadReference(String),
    Unification(String),
    ClauseMismatch {
        step: usize,
        expected: String,
        found: String,
    },
    NotARefutation,
    Stlc(String),
}

impl fmt::Display for KernelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            KernelError::Malformed(m) => write!(f, "malformed proof: {m}"),
            KernelError::BadReference(m) => write!(f, "bad proof reference: {m}"),
            KernelError::Unification(m) => write!(f, "unification failed: {m}"),
            KernelError::ClauseMismatch {
                step,
                expected,
                found,
            } => write!(
                f,
                "step {step} clause mismatch: expected {expected}, found {found}"
            ),
            KernelError::NotARefutation => f.write_str("proof does not end in the empty clause"),
            KernelError::Stlc(m) => write!(f, "typing error: {m}"),
        }
    }
}

impl std::error::Error for KernelError {}

fn list<'a>(s: &'a Sexp, what: &str) -> Result<&'a [Sexp], KernelError> {
    s.as_list()
        .ok_or_else(|| KernelError::Malformed(format!("expected a list for {what}")))
}

fn atom<'a>(s: &'a Sexp, what: &str) -> Result<&'a str, KernelError> {
    s.as_atom()
        .ok_or_else(|| KernelError::Malformed(format!("expected an atom for {what}")))
}

fn atom_str<'a>(s: &'a Sexp, what: &str) -> Result<&'a str, KernelError> {
    atom(s, what)
}

fn head_of<'a>(xs: &'a [Sexp], what: &str) -> Result<&'a str, KernelError> {
    xs.first()
        .and_then(Sexp::as_atom)
        .ok_or_else(|| KernelError::Malformed(format!("missing {what} tag")))
}

fn ir_err(e: IrError) -> KernelError {
    KernelError::Malformed(e.to_string())
}

fn occurs(var: &str, term: &Term, subst: &Subst) -> bool {
    match term {
        Term::Var(v) => {
            if v == var {
                true
            } else if let Some(t) = subst.get(v) {
                occurs(var, t, subst)
            } else {
                false
            }
        }
        Term::Const(_) => false,
        Term::App(_, args) => args.iter().any(|a| occurs(var, a, subst)),
    }
}

fn unify_terms(a: &Term, b: &Term, subst: &mut Subst) -> bool {
    let a = a.apply(subst);
    let b = b.apply(subst);
    match (a, b) {
        (Term::Var(x), Term::Var(y)) if x == y => true,
        (Term::Var(x), t) => {
            if occurs(&x, &t, subst) {
                false
            } else {
                subst.insert(x, t);
                true
            }
        }
        (t, Term::Var(y)) => {
            if occurs(&y, &t, subst) {
                false
            } else {
                subst.insert(y, t);
                true
            }
        }
        (Term::Const(x), Term::Const(y)) => x == y,
        (Term::App(f, xs), Term::App(g, ys)) if f == g && xs.len() == ys.len() => xs
            .iter()
            .zip(ys.iter())
            .all(|(x, y)| unify_terms(x, y, subst)),
        _ => false,
    }
}

pub fn unify_atoms(a: &Atom, b: &Atom) -> Option<Subst> {
    if a.predicate != b.predicate || a.args.len() != b.args.len() {
        return None;
    }
    let mut subst = Subst::new();
    for (x, y) in a.args.iter().zip(b.args.iter()) {
        if !unify_terms(x, y, &mut subst) {
            return None;
        }
    }
    Some(subst)
}

fn check_step(i: usize, proof: &ResolutionProof) -> Result<(), KernelError> {
    let step = &proof.clauses[i];
    match &step.rule {
        StepRule::Input => {
            // Inputs are canonical clauses by contract. Reject a non-canonical
            // input instead of silently normalising it, because the proof's
            // indices must refer to the exact clauses the prover used.
            if step.clause.literals != normalize(step.clause.literals.clone()) {
                return Err(KernelError::Malformed(format!(
                    "step {i} is an input clause but is not canonical"
                )));
            }
            Ok(())
        }
        StepRule::Factor {
            parent,
            first,
            second,
        } => {
            if *parent >= i {
                return Err(KernelError::BadReference(format!(
                    "factor parent {parent} is not earlier than {i}"
                )));
            }
            let p = &proof.clauses[*parent].clause;
            let a = p.literals.get(*first).ok_or_else(|| {
                KernelError::BadReference(format!("factor literal {first} out of range"))
            })?;
            let b = p.literals.get(*second).ok_or_else(|| {
                KernelError::BadReference(format!("factor literal {second} out of range"))
            })?;
            if a.positive != b.positive {
                return Err(KernelError::Unification(
                    "cannot factor literals of opposite polarity".into(),
                ));
            }
            let subst = unify_atoms(&a.atom, &b.atom).ok_or_else(|| {
                KernelError::Unification(format!(
                    "factor literals {first} and {second} do not unify"
                ))
            })?;
            let expected = Clause::new(p.literals.iter().map(|l| l.apply(&subst)).collect());
            if expected != step.clause {
                return Err(KernelError::ClauseMismatch {
                    step: i,
                    expected: expected.to_sexp().render(),
                    found: step.clause.to_sexp().render(),
                });
            }
            Ok(())
        }
        StepRule::Resolve {
            left,
            right,
            left_lit,
            right_lit,
        } => {
            if *left >= i || *right >= i {
                return Err(KernelError::BadReference(format!(
                    "resolve parents {left},{right} must be earlier than {i}"
                )));
            }
            let lc = &proof.clauses[*left].clause;
            let rc = &proof.clauses[*right].clause;
            let ll = lc.literals.get(*left_lit).ok_or_else(|| {
                KernelError::BadReference(format!("left literal {left_lit} out of range"))
            })?;
            let rl = rc.literals.get(*right_lit).ok_or_else(|| {
                KernelError::BadReference(format!("right literal {right_lit} out of range"))
            })?;
            if ll.positive == rl.positive {
                return Err(KernelError::Unification(
                    "resolution needs opposite polarities".into(),
                ));
            }
            let subst = unify_atoms(&ll.atom, &rl.atom).ok_or_else(|| {
                KernelError::Unification(format!(
                    "resolve literals {left_lit}/{right_lit} do not unify"
                ))
            })?;
            let mut literals = Vec::new();
            for (j, l) in lc.literals.iter().enumerate() {
                if j != *left_lit {
                    literals.push(l.apply(&subst));
                }
            }
            for (j, l) in rc.literals.iter().enumerate() {
                if j != *right_lit {
                    literals.push(l.apply(&subst));
                }
            }
            let expected = Clause::new(literals);
            if expected != step.clause {
                return Err(KernelError::ClauseMismatch {
                    step: i,
                    expected: expected.to_sexp().render(),
                    found: step.clause.to_sexp().render(),
                });
            }
            Ok(())
        }
    }
}

/// Check that every step is a valid input, factor, or binary resolution and that
/// the final clause is empty. The checker repeats unification and clause
/// construction; it never asks the prover whether a step is valid.
pub fn check_resolution(proof: &ResolutionProof) -> Result<(), KernelError> {
    if proof.clauses.is_empty() {
        return Err(KernelError::NotARefutation);
    }
    for i in 0..proof.clauses.len() {
        check_step(i, proof)?;
    }
    if !proof
        .clauses
        .last()
        .map(|c| c.clause.is_empty())
        .unwrap_or(false)
    {
        return Err(KernelError::NotARefutation);
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(x: Term) -> Atom {
        Atom::new("P", vec![x])
    }
    fn q(x: Term) -> Atom {
        Atom::new("Q", vec![x])
    }

    fn input(c: Clause, proof: &mut ResolutionProof) -> usize {
        proof.clauses.push(ProofClause {
            clause: c,
            rule: StepRule::Input,
        });
        proof.clauses.len() - 1
    }

    fn resolve(
        proof: &mut ResolutionProof,
        left: usize,
        right: usize,
        ll: usize,
        rl: usize,
    ) -> usize {
        let lc = &proof.clauses[left].clause;
        let rc = &proof.clauses[right].clause;
        let a = &lc.literals[ll];
        let b = &rc.literals[rl];
        let s = unify_atoms(&a.atom, &b.atom).unwrap();
        let mut lits = Vec::new();
        for (i, l) in lc.literals.iter().enumerate() {
            if i != ll {
                lits.push(l.apply(&s));
            }
        }
        for (i, l) in rc.literals.iter().enumerate() {
            if i != rl {
                lits.push(l.apply(&s));
            }
        }
        proof.clauses.push(ProofClause {
            clause: Clause::new(lits),
            rule: StepRule::Resolve {
                left,
                right,
                left_lit: ll,
                right_lit: rl,
            },
        });
        proof.clauses.len() - 1
    }

    #[test]
    fn modus_ponens_refutes() {
        let mut proof = ResolutionProof::default();
        let a = input(
            Clause::new(vec![
                Literal::positive(q(Term::constant("a"))),
                Literal::negative(p(Term::constant("a"))),
            ]),
            &mut proof,
        );
        let b = input(
            Clause::new(vec![Literal::positive(p(Term::constant("a")))]),
            &mut proof,
        );
        let c = input(
            Clause::new(vec![Literal::negative(q(Term::constant("a")))]),
            &mut proof,
        );
        let d = resolve(&mut proof, a, b, 1, 0);
        let _ = resolve(&mut proof, d, c, 0, 0);
        check_resolution(&proof).unwrap();
        let text = proof.to_text();
        let parsed = ResolutionProof::from_text(&text).unwrap();
        check_resolution(&parsed).unwrap();
    }

    #[test]
    fn a_tampered_clause_is_rejected() {
        let mut proof = ResolutionProof::default();
        input(
            Clause::new(vec![Literal::positive(p(Term::constant("a")))]),
            &mut proof,
        );
        proof.clauses.push(ProofClause {
            clause: Clause::empty(),
            rule: StepRule::Factor {
                parent: 0,
                first: 0,
                second: 0,
            },
        });
        assert!(check_resolution(&proof).is_err());
    }

    #[test]
    fn factoring_is_checked() {
        let mut proof = ResolutionProof::default();
        let a = input(
            Clause::new(vec![
                Literal::positive(p(Term::var("x"))),
                Literal::positive(p(Term::constant("a"))),
            ]),
            &mut proof,
        );
        proof.clauses.push(ProofClause {
            clause: Clause::new(vec![Literal::positive(p(Term::constant("a")))]),
            rule: StepRule::Factor {
                parent: a,
                first: 0,
                second: 1,
            },
        });
        // Not a refutation (no empty clause), but the factor step is valid.
        assert_eq!(check_resolution(&proof), Err(KernelError::NotARefutation));
    }

    #[test]
    fn occurs_check_prevents_cycles() {
        let a = Atom::new("P", vec![Term::var("x")]);
        let b = Atom::new("P", vec![Term::app("f", vec![Term::var("x")])]);
        assert!(unify_atoms(&a, &b).is_none());
    }
}
