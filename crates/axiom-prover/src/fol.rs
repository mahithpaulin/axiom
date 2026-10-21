//! First-order syntax for the Axiom prover.
//!
//! The fragment is deliberately small and explicit:
//!
//! * `axiom <formula>.` and `goal <formula>.` (one goal required);
//! * `pred p/2.`, `fun f/1.`, `const a.` declarations are optional;
//! * `true`, `false`, `not`/`~`/`!`, `and`/`&`, `or`/`|`, `->`, `<->`;
//! * `forall x, y. ...` and `exists x. ...`;
//! * predicate/function symbols with fixed arities;
//! * infix equality `t = u` over terms; ground equality is normalised by
//!   congruence closure, non-ground equality is handled by equality axioms;
//! * no sorts, arithmetic, or higher-order constructs.
//!
//! Variables are exactly those bound by a quantifier. An identifier used as a
//! term outside any quantifier is a constant. Parse errors are errors; nothing
//! is guessed.

use axiom_proof::{Atom, Term};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Formula {
    True,
    False,
    Atom(Atom),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Iff(Box<Formula>, Box<Formula>),
    Forall(Vec<String>, Box<Formula>),
    Exists(Vec<String>, Box<Formula>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    pub predicates: BTreeMap<String, usize>,
    pub functions: BTreeMap<String, usize>,
    pub constants: BTreeSet<String>,
}

fn equality_formula(lhs: Term, rhs: Term) -> Formula {
    Formula::Atom(Atom::new("=", vec![lhs, rhs]))
}

fn conjoin(parts: Vec<Formula>) -> Formula {
    match parts.len() {
        0 => Formula::True,
        1 => parts.into_iter().next().expect("one formula"),
        _ => Formula::And(parts),
    }
}

impl Signature {
    pub fn has_equality(&self) -> bool {
        self.predicates.get("=") == Some(&2)
    }

    /// Equality axioms for the current signature.
    ///
    /// Equality is not built into the resolution calculus. These axioms make it
    /// available to the existing clausal prover without changing the kernel.
    pub fn equality_axioms(&self) -> Vec<Formula> {
        if !self.has_equality() {
            return Vec::new();
        }
        let mut out = Vec::new();
        let x = "eq_x".to_string();
        let y = "eq_y".to_string();
        let z = "eq_z".to_string();
        out.push(Formula::Forall(
            vec![x.clone()],
            Box::new(equality_formula(Term::var(&x), Term::var(&x))),
        ));
        out.push(Formula::Forall(
            vec![x.clone(), y.clone()],
            Box::new(Formula::Implies(
                Box::new(equality_formula(Term::var(&x), Term::var(&y))),
                Box::new(equality_formula(Term::var(&y), Term::var(&x))),
            )),
        ));
        out.push(Formula::Forall(
            vec![x.clone(), y.clone(), z.clone()],
            Box::new(Formula::Implies(
                Box::new(conjoin(vec![
                    equality_formula(Term::var(&x), Term::var(&y)),
                    equality_formula(Term::var(&y), Term::var(&z)),
                ])),
                Box::new(equality_formula(Term::var(&x), Term::var(&z))),
            )),
        ));

        for (name, &arity) in &self.functions {
            if arity == 0 {
                continue;
            }
            let xs: Vec<String> = (0..arity).map(|i| format!("eq_fx{i}")).collect();
            let ys: Vec<String> = (0..arity).map(|i| format!("eq_fy{i}")).collect();
            let mut vars = xs.clone();
            vars.extend(ys.iter().cloned());
            let premises = xs
                .iter()
                .zip(&ys)
                .map(|(a, b)| equality_formula(Term::var(a), Term::var(b)))
                .collect();
            let lhs = Term::app(name.clone(), xs.iter().map(Term::var).collect());
            let rhs = Term::app(name.clone(), ys.iter().map(Term::var).collect());
            out.push(Formula::Forall(
                vars,
                Box::new(Formula::Implies(
                    Box::new(conjoin(premises)),
                    Box::new(equality_formula(lhs, rhs)),
                )),
            ));
        }

        for (name, &arity) in &self.predicates {
            if name == "=" || arity == 0 {
                continue;
            }
            let xs: Vec<String> = (0..arity).map(|i| format!("eq_px{i}")).collect();
            let ys: Vec<String> = (0..arity).map(|i| format!("eq_py{i}")).collect();
            let mut vars = xs.clone();
            vars.extend(ys.iter().cloned());
            let mut premises: Vec<Formula> = xs
                .iter()
                .zip(&ys)
                .map(|(a, b)| equality_formula(Term::var(a), Term::var(b)))
                .collect();
            premises.push(Formula::Atom(Atom::new(
                name.clone(),
                xs.iter().map(Term::var).collect(),
            )));
            out.push(Formula::Forall(
                vars,
                Box::new(Formula::Implies(
                    Box::new(conjoin(premises)),
                    Box::new(Formula::Atom(Atom::new(
                        name.clone(),
                        ys.iter().map(Term::var).collect(),
                    ))),
                )),
            ));
        }
        out
    }

    fn new() -> Self {
        Signature {
            predicates: BTreeMap::new(),
            functions: BTreeMap::new(),
            constants: BTreeSet::new(),
        }
    }

    fn arity(map: &mut BTreeMap<String, usize>, name: &str, arity: usize) -> Result<(), FolError> {
        match map.get(name) {
            Some(&old) if old != arity => Err(FolError::Arity {
                name: name.to_string(),
                declared: old,
                used: arity,
            }),
            Some(_) => Ok(()),
            None => {
                map.insert(name.to_string(), arity);
                Ok(())
            }
        }
    }

    fn function(&mut self, name: &str, arity: usize) -> Result<(), FolError> {
        if self.constants.contains(name) {
            return Err(FolError::Message(format!(
                "symbol {name} is used as both a constant and a function"
            )));
        }
        Self::arity(&mut self.functions, name, arity)
    }

    fn constant(&mut self, name: &str) -> Result<(), FolError> {
        if self.functions.contains_key(name) {
            return Err(FolError::Message(format!(
                "symbol {name} is used as both a constant and a function"
            )));
        }
        self.constants.insert(name.to_string());
        Ok(())
    }

    fn term(&mut self, term: &Term) -> Result<(), FolError> {
        match term {
            Term::Var(_) => Ok(()),
            Term::Const(c) => self.constant(c),
            Term::App(f, args) => {
                self.function(f, args.len())?;
                for a in args {
                    self.term(a)?;
                }
                Ok(())
            }
        }
    }

    fn formula(&mut self, f: &Formula) -> Result<(), FolError> {
        match f {
            Formula::True | Formula::False => Ok(()),
            Formula::Atom(a) => {
                Self::arity(&mut self.predicates, &a.predicate, a.args.len())?;
                for t in &a.args {
                    self.term(t)?;
                }
                Ok(())
            }
            Formula::Not(x) => self.formula(x),
            Formula::And(xs) | Formula::Or(xs) => {
                for x in xs {
                    self.formula(x)?;
                }
                Ok(())
            }
            Formula::Implies(a, b) | Formula::Iff(a, b) => {
                self.formula(a)?;
                self.formula(b)
            }
            Formula::Forall(_, x) | Formula::Exists(_, x) => self.formula(x),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FolProblem {
    pub axioms: Vec<Formula>,
    pub goal: Formula,
    pub signature: Signature,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FolError {
    Parse {
        offset: usize,
        message: String,
    },
    Arity {
        name: String,
        declared: usize,
        used: usize,
    },
    MissingGoal,
    MultipleGoals,
    Message(String),
}

impl fmt::Display for FolError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FolError::Parse { offset, message } => write!(f, "at byte {offset}: {message}"),
            FolError::Arity {
                name,
                declared,
                used,
            } => write!(
                f,
                "symbol {name} is used with arity {used}, but arity {declared} was established"
            ),
            FolError::MissingGoal => f.write_str("the problem has no goal"),
            FolError::MultipleGoals => f.write_str("the problem has more than one goal"),
            FolError::Message(m) => f.write_str(m),
        }
    }
}

impl std::error::Error for FolError {}

fn parse_err(offset: usize, message: impl Into<String>) -> FolError {
    FolError::Parse {
        offset,
        message: message.into(),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Word(String),
    LParen,
    RParen,
    Comma,
    Dot,
    Slash,
    Not,
    And,
    Or,
    Implies,
    Iff,
    Forall,
    Exists,
    True,
    False,
    Eq,
}

fn lex(input: &str) -> Result<Vec<(usize, Tok)>, FolError> {
    let chars: Vec<char> = input.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c == '%' || c == '#' {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        let start = i;
        match c {
            '(' => {
                out.push((start, Tok::LParen));
                i += 1;
            }
            ')' => {
                out.push((start, Tok::RParen));
                i += 1;
            }
            ',' => {
                out.push((start, Tok::Comma));
                i += 1;
            }
            '=' => {
                out.push((start, Tok::Eq));
                i += 1;
            }
            '.' => {
                out.push((start, Tok::Dot));
                i += 1;
            }
            '~' | '!' => {
                out.push((start, Tok::Not));
                i += 1;
            }
            '&' => {
                out.push((start, Tok::And));
                i += 1;
            }
            '|' => {
                out.push((start, Tok::Or));
                i += 1;
            }
            '/' if chars.get(i + 1) == Some(&'\\') => {
                out.push((start, Tok::And));
                i += 2;
            }
            '\\' if chars.get(i + 1) == Some(&'/') => {
                out.push((start, Tok::Or));
                i += 2;
            }
            '/' => {
                out.push((start, Tok::Slash));
                i += 1;
            }
            '-' if chars.get(i + 1) == Some(&'>') => {
                out.push((start, Tok::Implies));
                i += 2;
            }
            '<' if chars.get(i + 1) == Some(&'-') && chars.get(i + 2) == Some(&'>') => {
                out.push((start, Tok::Iff));
                i += 3;
            }
            _ if c.is_alphanumeric() || c == '_' => {
                while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                    i += 1;
                }
                let w: String = chars[start..i].iter().collect();
                let tok = match w.to_ascii_lowercase().as_str() {
                    "not" => Tok::Not,
                    "and" => Tok::And,
                    "or" => Tok::Or,
                    "implies" => Tok::Implies,
                    "iff" => Tok::Iff,
                    "forall" => Tok::Forall,
                    "exists" => Tok::Exists,
                    "true" => Tok::True,
                    "false" => Tok::False,
                    _ => Tok::Word(w),
                };
                out.push((start, tok));
            }
            _ => {
                return Err(parse_err(
                    start,
                    format!("unexpected character {c:?} (arithmetic is not in this fragment)"),
                ))
            }
        }
    }
    Ok(out)
}

struct Parser {
    toks: Vec<(usize, Tok)>,
    pos: usize,
}

impl Parser {
    fn new(toks: Vec<(usize, Tok)>) -> Self {
        Parser { toks, pos: 0 }
    }

    fn offset(&self) -> usize {
        self.toks
            .get(self.pos)
            .map(|(o, _)| *o)
            .or_else(|| self.toks.last().map(|(o, _)| *o))
            .unwrap_or(0)
    }

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|(_, t)| t)
    }

    fn bump(&mut self) -> Option<Tok> {
        let t = self.peek().cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    fn expect(&mut self, expected: &Tok) -> Result<(), FolError> {
        match self.bump() {
            Some(ref t) if t == expected => Ok(()),
            Some(t) => Err(parse_err(
                self.offset(),
                format!("expected {expected:?}, found {t:?}"),
            )),
            None => Err(parse_err(self.offset(), "unexpected end of input")),
        }
    }

    fn word(&mut self) -> Result<String, FolError> {
        match self.bump() {
            Some(Tok::Word(w)) => Ok(w),
            Some(t) => Err(parse_err(
                self.offset(),
                format!("expected a name, found {t:?}"),
            )),
            None => Err(parse_err(
                self.offset(),
                "expected a name, found end of input",
            )),
        }
    }

    fn formula(&mut self, bound: &BTreeSet<String>) -> Result<Formula, FolError> {
        self.iff(bound)
    }

    fn iff(&mut self, bound: &BTreeSet<String>) -> Result<Formula, FolError> {
        let mut left = self.implies(bound)?;
        while matches!(self.peek(), Some(Tok::Iff)) {
            self.bump();
            let right = self.implies(bound)?;
            left = Formula::Iff(Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn implies(&mut self, bound: &BTreeSet<String>) -> Result<Formula, FolError> {
        let left = self.or(bound)?;
        if matches!(self.peek(), Some(Tok::Implies)) {
            self.bump();
            let right = self.implies(bound)?;
            Ok(Formula::Implies(Box::new(left), Box::new(right)))
        } else {
            Ok(left)
        }
    }

    fn or(&mut self, bound: &BTreeSet<String>) -> Result<Formula, FolError> {
        let mut parts = vec![self.and(bound)?];
        while matches!(self.peek(), Some(Tok::Or)) {
            self.bump();
            parts.push(self.and(bound)?);
        }
        Ok(if parts.len() == 1 {
            parts.remove(0)
        } else {
            Formula::Or(parts)
        })
    }

    fn and(&mut self, bound: &BTreeSet<String>) -> Result<Formula, FolError> {
        let mut parts = vec![self.unary(bound)?];
        while matches!(self.peek(), Some(Tok::And)) {
            self.bump();
            parts.push(self.unary(bound)?);
        }
        Ok(if parts.len() == 1 {
            parts.remove(0)
        } else {
            Formula::And(parts)
        })
    }

    fn unary(&mut self, bound: &BTreeSet<String>) -> Result<Formula, FolError> {
        match self.bump() {
            Some(Tok::Not) => Ok(Formula::Not(Box::new(self.unary(bound)?))),
            Some(Tok::Forall) => self.quantifier(true, bound),
            Some(Tok::Exists) => self.quantifier(false, bound),
            Some(Tok::True) => Ok(Formula::True),
            Some(Tok::False) => Ok(Formula::False),
            Some(Tok::LParen) => {
                let f = self.formula(bound)?;
                self.expect(&Tok::RParen)?;
                Ok(f)
            }
            Some(Tok::Word(name)) => {
                let left = self.atom_after_name(name, bound)?;
                if matches!(self.peek(), Some(Tok::Eq)) {
                    self.bump();
                    let lhs = Self::atom_as_term(left, bound)?;
                    let rhs = self.term(bound)?;
                    Ok(Formula::Atom(Atom::new("=", vec![lhs, rhs])))
                } else {
                    Ok(left)
                }
            }
            Some(t) => Err(parse_err(
                self.offset(),
                format!("expected a formula, found {t:?}"),
            )),
            None => Err(parse_err(
                self.offset(),
                "expected a formula, found end of input",
            )),
        }
    }

    fn quantifier(
        &mut self,
        universal: bool,
        outer: &BTreeSet<String>,
    ) -> Result<Formula, FolError> {
        let mut vars = vec![self.word()?];
        while matches!(self.peek(), Some(Tok::Comma)) {
            self.bump();
            vars.push(self.word()?);
        }
        self.expect(&Tok::Dot)?;
        let mut bound = outer.clone();
        bound.extend(vars.iter().cloned());
        let body = self.formula(&bound)?;
        Ok(if universal {
            Formula::Forall(vars, Box::new(body))
        } else {
            Formula::Exists(vars, Box::new(body))
        })
    }

    fn atom_as_term(atom: Formula, bound: &BTreeSet<String>) -> Result<Term, FolError> {
        let Formula::Atom(atom) = atom else {
            return Err(FolError::Message(
                "internal parser error: expected an atom".into(),
            ));
        };
        if atom.args.is_empty() {
            if bound.contains(&atom.predicate) {
                Ok(Term::var(atom.predicate))
            } else {
                Ok(Term::constant(atom.predicate))
            }
        } else if bound.contains(&atom.predicate) {
            Err(FolError::Message(format!(
                "variable {} cannot be used as a function",
                atom.predicate
            )))
        } else {
            Ok(Term::app(atom.predicate, atom.args))
        }
    }

    fn atom_after_name(
        &mut self,
        predicate: String,
        bound: &BTreeSet<String>,
    ) -> Result<Formula, FolError> {
        let mut args = Vec::new();
        if matches!(self.peek(), Some(Tok::LParen)) {
            self.bump();
            if !matches!(self.peek(), Some(Tok::RParen)) {
                loop {
                    args.push(self.term(bound)?);
                    if matches!(self.peek(), Some(Tok::Comma)) {
                        self.bump();
                    } else {
                        break;
                    }
                }
            }
            self.expect(&Tok::RParen)?;
        }
        Ok(Formula::Atom(Atom::new(predicate, args)))
    }

    fn term(&mut self, bound: &BTreeSet<String>) -> Result<Term, FolError> {
        let name = self.word()?;
        if matches!(self.peek(), Some(Tok::LParen)) {
            self.bump();
            let mut args = Vec::new();
            if !matches!(self.peek(), Some(Tok::RParen)) {
                loop {
                    args.push(self.term(bound)?);
                    if matches!(self.peek(), Some(Tok::Comma)) {
                        self.bump();
                    } else {
                        break;
                    }
                }
            }
            self.expect(&Tok::RParen)?;
            Ok(Term::app(name, args))
        } else if bound.contains(&name) {
            Ok(Term::var(name))
        } else {
            Ok(Term::constant(name))
        }
    }
}

fn is_ground(term: &Term) -> bool {
    match term {
        Term::Var(_) => false,
        Term::Const(_) => true,
        Term::App(_, args) => args.iter().all(is_ground),
    }
}

fn collect_ground_terms(formula: &Formula, out: &mut BTreeSet<Term>) {
    match formula {
        Formula::Atom(atom) => {
            for arg in &atom.args {
                collect_ground_terms_in_term(arg, out);
            }
        }
        Formula::Not(x) => collect_ground_terms(x, out),
        Formula::And(xs) | Formula::Or(xs) => {
            for x in xs {
                collect_ground_terms(x, out);
            }
        }
        Formula::Implies(a, b) | Formula::Iff(a, b) => {
            collect_ground_terms(a, out);
            collect_ground_terms(b, out);
        }
        Formula::Forall(_, x) | Formula::Exists(_, x) => collect_ground_terms(x, out),
        Formula::True | Formula::False => {}
    }
}

fn collect_ground_terms_in_term(term: &Term, out: &mut BTreeSet<Term>) {
    if is_ground(term) {
        out.insert(term.clone());
    }
    if let Term::App(_, args) = term {
        for arg in args {
            collect_ground_terms_in_term(arg, out);
        }
    }
}

fn collect_equality_atoms(formula: &Formula, out: &mut Vec<Atom>) {
    match formula {
        Formula::Atom(atom) => {
            if atom.predicate == "=" {
                out.push(atom.clone());
            }
        }
        Formula::Not(x) => collect_equality_atoms(x, out),
        Formula::And(xs) | Formula::Or(xs) => {
            for x in xs {
                collect_equality_atoms(x, out);
            }
        }
        Formula::Implies(a, b) | Formula::Iff(a, b) => {
            collect_equality_atoms(a, out);
            collect_equality_atoms(b, out);
        }
        Formula::Forall(_, x) | Formula::Exists(_, x) => collect_equality_atoms(x, out),
        Formula::True | Formula::False => {}
    }
}

fn rewrite_term(term: &Term, canon: &BTreeMap<Term, Term>) -> Term {
    if let Some(c) = canon.get(term) {
        return c.clone();
    }
    match term {
        Term::Var(_) | Term::Const(_) => term.clone(),
        Term::App(f, args) => Term::App(
            f.clone(),
            args.iter().map(|a| rewrite_term(a, canon)).collect(),
        ),
    }
}

fn rewrite_formula(formula: &Formula, canon: &BTreeMap<Term, Term>) -> Formula {
    match formula {
        Formula::Atom(atom) => {
            let args: Vec<Term> = atom.args.iter().map(|t| rewrite_term(t, canon)).collect();
            if atom.predicate == "=" && args.len() == 2 && args[0] == args[1] {
                Formula::True
            } else {
                Formula::Atom(Atom::new(atom.predicate.clone(), args))
            }
        }
        Formula::Not(x) => match rewrite_formula(x, canon) {
            Formula::True => Formula::False,
            Formula::False => Formula::True,
            other => Formula::Not(Box::new(other)),
        },
        Formula::And(xs) => Formula::And(xs.iter().map(|x| rewrite_formula(x, canon)).collect()),
        Formula::Or(xs) => Formula::Or(xs.iter().map(|x| rewrite_formula(x, canon)).collect()),
        Formula::Implies(a, b) => Formula::Implies(
            Box::new(rewrite_formula(a, canon)),
            Box::new(rewrite_formula(b, canon)),
        ),
        Formula::Iff(a, b) => Formula::Iff(
            Box::new(rewrite_formula(a, canon)),
            Box::new(rewrite_formula(b, canon)),
        ),
        Formula::Forall(vars, x) => {
            Formula::Forall(vars.clone(), Box::new(rewrite_formula(x, canon)))
        }
        Formula::Exists(vars, x) => {
            Formula::Exists(vars.clone(), Box::new(rewrite_formula(x, canon)))
        }
        Formula::True | Formula::False => formula.clone(),
    }
}

#[derive(Default)]
struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<u8>,
}

impl UnionFind {
    fn add(&mut self) -> usize {
        let id = self.parent.len();
        self.parent.push(id);
        self.rank.push(0);
        id
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }

    fn union(&mut self, a: usize, b: usize) -> bool {
        let (mut a, mut b) = (self.find(a), self.find(b));
        if a == b {
            return false;
        }
        if self.rank[a] < self.rank[b] {
            std::mem::swap(&mut a, &mut b);
        }
        self.parent[b] = a;
        if self.rank[a] == self.rank[b] {
            self.rank[a] += 1;
        }
        true
    }
}

/// Normalise ground equality by congruence closure.
///
/// This is deliberately narrow: every equality atom must be ground, and
/// equality may appear in the goal but in axioms only as a positive unit
/// `a = b.`. Under those conditions, rewriting with the unit equalities and
/// computing congruence closure is sound and avoids the infinite saturation
/// that the general equality axioms can cause. Anything else returns `None`
/// and uses [`Signature::equality_axioms`] instead.
pub fn normalize_ground_equality(problem: &FolProblem) -> Option<FolProblem> {
    let mut all_equalities = Vec::new();
    for axiom in &problem.axioms {
        collect_equality_atoms(axiom, &mut all_equalities);
    }
    collect_equality_atoms(&problem.goal, &mut all_equalities);
    if all_equalities.is_empty() || all_equalities.iter().any(|a| !a.args.iter().all(is_ground)) {
        return None;
    }

    let mut units = Vec::new();
    for axiom in &problem.axioms {
        match axiom {
            Formula::Atom(a) if a.predicate == "=" && a.args.len() == 2 => {
                units.push((a.args[0].clone(), a.args[1].clone()));
            }
            other => {
                let mut nested = Vec::new();
                collect_equality_atoms(other, &mut nested);
                if !nested.is_empty() {
                    return None;
                }
            }
        }
    }

    let mut terms = BTreeSet::new();
    for axiom in &problem.axioms {
        collect_ground_terms(axiom, &mut terms);
    }
    collect_ground_terms(&problem.goal, &mut terms);
    for (a, b) in &units {
        terms.insert(a.clone());
        terms.insert(b.clone());
    }

    let mut ids = BTreeMap::new();
    let mut uf = UnionFind::default();
    for term in &terms {
        ids.insert(term.clone(), uf.add());
    }
    for (a, b) in &units {
        if let (Some(&ia), Some(&ib)) = (ids.get(a), ids.get(b)) {
            uf.union(ia, ib);
        }
    }

    loop {
        let mut classes: BTreeMap<(String, Vec<usize>), usize> = BTreeMap::new();
        let mut changed = false;
        for (term, &id) in &ids {
            if let Term::App(f, args) = term {
                let key = (
                    f.clone(),
                    args.iter().map(|a| uf.find(ids[a])).collect::<Vec<_>>(),
                );
                match classes.get(&key) {
                    Some(&other) => changed |= uf.union(id, other),
                    None => {
                        classes.insert(key, id);
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    let mut groups: BTreeMap<usize, Vec<Term>> = BTreeMap::new();
    for (term, &id) in &ids {
        groups.entry(uf.find(id)).or_default().push(term.clone());
    }
    let mut canon = BTreeMap::new();
    for group in groups.values() {
        let representative = group.iter().min().cloned().expect("non-empty group");
        for term in group {
            canon.insert(term.clone(), representative.clone());
        }
    }

    let axioms = problem
        .axioms
        .iter()
        .map(|a| rewrite_formula(a, &canon))
        .filter(|a| *a != Formula::True)
        .collect();
    let goal = rewrite_formula(&problem.goal, &canon);
    Some(FolProblem {
        axioms,
        goal,
        signature: problem.signature.clone(),
    })
}

/// Parse a complete problem. Declarations may appear before or after formulas.
pub fn parse_problem(input: &str) -> Result<FolProblem, FolError> {
    let toks = lex(input)?;
    let mut p = Parser::new(toks);
    let mut axioms = Vec::new();
    let mut goal = None;
    let mut declared_preds = BTreeMap::new();
    let mut declared_funs = BTreeMap::new();
    let mut declared_consts = BTreeSet::new();

    while p.peek().is_some() {
        if let Some(Tok::Word(w)) = p.peek() {
            match w.as_str() {
                "axiom" => {
                    p.bump();
                    axioms.push(p.formula(&BTreeSet::new())?);
                    p.expect(&Tok::Dot)?;
                    continue;
                }
                "goal" | "conjecture" => {
                    p.bump();
                    if goal.is_some() {
                        return Err(FolError::MultipleGoals);
                    }
                    goal = Some(p.formula(&BTreeSet::new())?);
                    p.expect(&Tok::Dot)?;
                    continue;
                }
                "pred" | "fun" => {
                    let is_pred = w == "pred";
                    p.bump();
                    let name = p.word()?;
                    let arity = if matches!(p.peek(), Some(Tok::Slash)) {
                        p.bump();
                        match p.bump() {
                            Some(Tok::Word(n)) => n.parse::<usize>().map_err(|_| {
                                parse_err(p.offset(), "declaration arity is not a number")
                            })?,
                            Some(Tok::Dot) => {
                                // `pred p.` means arity 0.
                                p.pos -= 1;
                                0
                            }
                            other => {
                                return Err(parse_err(
                                    p.offset(),
                                    format!("expected arity after '/', found {other:?}"),
                                ))
                            }
                        }
                    } else {
                        0
                    };
                    p.expect(&Tok::Dot)?;
                    let map = if is_pred {
                        &mut declared_preds
                    } else {
                        &mut declared_funs
                    };
                    Signature::arity(map, &name, arity)?;
                    continue;
                }
                "const" => {
                    p.bump();
                    let name = p.word()?;
                    p.expect(&Tok::Dot)?;
                    declared_consts.insert(name);
                    continue;
                }
                _ => {}
            }
        }
        // A bare formula is accepted as an axiom.
        axioms.push(p.formula(&BTreeSet::new())?);
        p.expect(&Tok::Dot)?;
    }

    let goal = goal.ok_or(FolError::MissingGoal)?;
    let mut signature = Signature::new();
    signature.predicates = declared_preds;
    signature.functions = declared_funs;
    signature.constants = declared_consts;
    for f in &axioms {
        signature.formula(f)?;
    }
    signature.formula(&goal)?;
    Ok(FolProblem {
        axioms,
        goal,
        signature,
    })
}

/// Parse one formula without the problem wrapper.
pub fn parse_formula(input: &str) -> Result<Formula, FolError> {
    let toks = lex(input)?;
    let mut p = Parser::new(toks);
    let f = p.formula(&BTreeSet::new())?;
    if p.peek().is_some() {
        return Err(parse_err(p.offset(), "trailing tokens after formula"));
    }
    Ok(f)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_a_small_problem() {
        let p = parse_problem("pred P/1. axiom forall x. P(x). goal P(a).").unwrap();
        assert_eq!(p.axioms.len(), 1);
        assert_eq!(p.signature.predicates.get("P"), Some(&1));
        assert!(p.signature.constants.contains("a"));
    }

    #[test]
    fn bare_formulas_are_axioms() {
        let p = parse_problem("P(a). goal P(a).").unwrap();
        assert_eq!(p.axioms.len(), 1);
    }

    #[test]
    fn quantifier_scope_and_terms() {
        let f = parse_formula("forall x. P(f(x)) -> Q(x)").unwrap();
        match f {
            Formula::Forall(vars, body) => {
                assert_eq!(vars, vec!["x"]);
                assert!(matches!(*body, Formula::Implies(_, _)));
            }
            other => panic!("unexpected {other:?}"),
        }
    }

    #[test]
    fn arity_conflicts_are_errors() {
        assert!(parse_problem("axiom P(a). axiom P(a,b). goal P(a).").is_err());
        assert!(parse_problem("pred P/1. axiom P(a,b). goal P(a).").is_err());
    }

    #[test]
    fn goal_is_required() {
        assert_eq!(
            parse_problem("axiom P(a).").unwrap_err(),
            FolError::MissingGoal
        );
    }

    #[test]
    fn equality_is_parsed_as_a_binary_atom() {
        let p = parse_problem("axiom a = b. goal P(a).").unwrap();
        assert_eq!(p.signature.predicates.get("="), Some(&2));
        match &p.axioms[0] {
            Formula::Atom(a) => {
                assert_eq!(a.predicate, "=");
                assert_eq!(a.args.len(), 2);
            }
            other => panic!("unexpected {other:?}"),
        }
    }

    #[test]
    fn ground_equality_normalisation_rewrites_congruent_terms() {
        let p = parse_problem("axiom a = b. axiom f(a) = c. goal f(b) = c.").unwrap();
        let n = normalize_ground_equality(&p).expect("ground equality");
        assert_eq!(n.goal, Formula::True);
        assert!(n.axioms.is_empty());
    }

    #[test]
    fn non_ground_equality_uses_axioms() {
        let p = parse_problem("axiom forall x. x = f(x). goal f(a) = a.").unwrap();
        assert!(normalize_ground_equality(&p).is_none());
        assert!(!p.signature.equality_axioms().is_empty());
    }

    #[test]
    fn conditional_equality_uses_axioms() {
        let p = parse_problem("axiom P(a) -> a = b. goal b = a.").unwrap();
        assert!(normalize_ground_equality(&p).is_none());
    }

    #[test]
    fn equality_terms_respect_quantifier_scope() {
        let f = parse_formula("forall x. x = f(x)").unwrap();
        match f {
            Formula::Forall(_, body) => match *body {
                Formula::Atom(a) => {
                    assert_eq!(a.predicate, "=");
                    assert_eq!(a.args[0], Term::var("x"));
                    assert_eq!(a.args[1], Term::app("f", vec![Term::var("x")]));
                }
                other => panic!("unexpected {other:?}"),
            },
            other => panic!("unexpected {other:?}"),
        }
    }
}
