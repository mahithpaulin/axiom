//! Axiom v4 typed intermediate representation.
//!
//! The v4 workspace deliberately separates *representation* from *engines*.
//! This crate owns the shared, dependency-free data model:
//!
//! * a small many-sorted term language with variables, constants and functions;
//! * Horn facts and rules over typed atoms;
//! * a first-order formula language used by the proof layer;
//! * a deterministic, lossless S-expression serialisation with a bounded parser.
//!
//! The representation is not a claim that every engine supports every feature.
//! An engine declares the fragment it implements and rejects or reports the rest.
//! In particular, this crate accepts typed function symbols in terms but the
//! Datalog executor only enumerates the function-free finite fragment.
//!
//! # Example
//!
//! ```
//! use axiom_ir::{Atom, Rule, Signature, Sort, Term, TypedProgram};
//!
//! let mut sig = Signature::new();
//! sig.add_sort("Person");
//! sig.add_constant("alice", Sort::Named("Person".into())).unwrap();
//! sig.add_constant("bob", Sort::Named("Person".into())).unwrap();
//! sig.add_predicate("edge", vec![Sort::Named("Person".into()); 2]).unwrap();
//!
//! let x = Term::var("X", Sort::Named("Person".into()));
//! let y = Term::var("Y", Sort::Named("Person".into()));
//! let fact = Atom::new("edge", vec![
//!     Term::constant("alice", Sort::Named("Person".into())),
//!     Term::constant("bob", Sort::Named("Person".into())),
//! ]);
//! let rule = Rule::new(
//!     Atom::new("edge", vec![x, y]),
//!     vec![],
//! );
//! let mut program = TypedProgram::new(sig);
//! program.facts.push(fact);
//! program.rules.push(rule);
//! program.check().unwrap();
//!
//! let text = program.to_sexp().render();
//! assert_eq!(TypedProgram::from_sexp(&axiom_ir::Sexp::parse(&text).unwrap()).unwrap(), program);
//! ```

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// Maximum nesting accepted by the S-expression parser.
pub const MAX_SEXP_DEPTH: usize = 256;
/// Maximum input length accepted by the S-expression parser.
pub const MAX_SEXP_BYTES: usize = 1 << 22;

/// A many-sorted type.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Sort {
    Bool,
    Int,
    Real,
    Named(String),
}

impl Sort {
    pub fn named(name: impl Into<String>) -> Self {
        Sort::Named(name.into())
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Bool => f.write_str("Bool"),
            Sort::Int => f.write_str("Int"),
            Sort::Real => f.write_str("Real"),
            Sort::Named(s) => f.write_str(s),
        }
    }
}

/// A typed logical variable.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Var {
    pub name: String,
    pub sort: Sort,
}

impl Var {
    pub fn new(name: impl Into<String>, sort: Sort) -> Self {
        Var {
            name: name.into(),
            sort,
        }
    }
}

/// A typed term.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Term {
    Var(Var),
    Const(String, Sort),
    App(String, Vec<Term>, Sort),
}

impl Term {
    pub fn var(name: impl Into<String>, sort: Sort) -> Self {
        Term::Var(Var::new(name, sort))
    }

    pub fn constant(name: impl Into<String>, sort: Sort) -> Self {
        Term::Const(name.into(), sort)
    }

    pub fn app(name: impl Into<String>, args: Vec<Term>, sort: Sort) -> Self {
        Term::App(name.into(), args, sort)
    }

    pub fn sort(&self) -> &Sort {
        match self {
            Term::Var(v) => &v.sort,
            Term::Const(_, s) => s,
            Term::App(_, _, s) => s,
        }
    }

    pub fn is_variable(&self) -> bool {
        matches!(self, Term::Var(_))
    }

    pub fn collect_vars(&self, out: &mut BTreeMap<String, Sort>) {
        match self {
            Term::Var(v) => {
                out.entry(v.name.clone()).or_insert_with(|| v.sort.clone());
            }
            Term::Const(_, _) => {}
            Term::App(_, args, _) => {
                for a in args {
                    a.collect_vars(out);
                }
            }
        }
    }

    pub fn variables(&self) -> BTreeMap<String, Sort> {
        let mut out = BTreeMap::new();
        self.collect_vars(&mut out);
        out
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(v) => write!(f, "?{}:{}", v.name, v.sort),
            Term::Const(n, s) => write!(f, "{}:{}", n, s),
            Term::App(n, args, _) => {
                write!(f, "{n}(")?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{a}")?;
                }
                f.write_str(")")
            }
        }
    }
}

/// A typed predicate application.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Atom {
    pub predicate: String,
    pub terms: Vec<Term>,
}

impl Atom {
    pub fn new(predicate: impl Into<String>, terms: Vec<Term>) -> Self {
        Atom {
            predicate: predicate.into(),
            terms,
        }
    }

    pub fn collect_vars(&self, out: &mut BTreeMap<String, Sort>) {
        for t in &self.terms {
            t.collect_vars(out);
        }
    }

    pub fn variables(&self) -> BTreeMap<String, Sort> {
        let mut out = BTreeMap::new();
        self.collect_vars(&mut out);
        out
    }
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.predicate)?;
        for (i, t) in self.terms.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{t}")?;
        }
        f.write_str(")")
    }
}

/// A possibly negated atom.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Literal {
    pub negated: bool,
    pub atom: Atom,
}

impl Literal {
    pub fn positive(atom: Atom) -> Self {
        Literal {
            negated: false,
            atom,
        }
    }

    pub fn negative(atom: Atom) -> Self {
        Literal {
            negated: true,
            atom,
        }
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.negated {
            write!(f, "not {}", self.atom)
        } else {
            write!(f, "{}", self.atom)
        }
    }
}

/// A disjunction of literals. Used by the resolution proof format.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, Default)]
pub struct Clause {
    pub literals: Vec<Literal>,
}

impl Clause {
    pub fn new(literals: Vec<Literal>) -> Self {
        Clause { literals }
    }

    pub fn is_empty(&self) -> bool {
        self.literals.is_empty()
    }
}

/// A definite Horn rule. A fact is a rule with an empty body.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Rule {
    pub head: Atom,
    pub body: Vec<Literal>,
}

impl Rule {
    pub fn new(head: Atom, body: Vec<Literal>) -> Self {
        Rule { head, body }
    }

    pub fn fact(head: Atom) -> Self {
        Rule {
            head,
            body: Vec::new(),
        }
    }

    /// Standard range restriction for Datalog: every variable in the head and
    /// in a negative body literal also occurs in a positive body literal.
    pub fn is_safe(&self) -> bool {
        let mut positive = BTreeSet::new();
        for l in &self.body {
            if !l.negated {
                for v in l.atom.variables().keys() {
                    positive.insert(v.clone());
                }
            }
        }
        for v in self.head.variables().keys() {
            if !positive.contains(v) {
                return false;
            }
        }
        for l in &self.body {
            if l.negated {
                for v in l.atom.variables().keys() {
                    if !positive.contains(v) {
                        return false;
                    }
                }
            }
        }
        true
    }
}

/// Constant declaration in a signature.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ConstDecl {
    pub name: String,
    pub sort: Sort,
}

/// Function declaration in a signature.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FunctionDecl {
    pub name: String,
    pub args: Vec<Sort>,
    pub result: Sort,
}

/// Predicate declaration in a signature.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PredicateDecl {
    pub name: String,
    pub args: Vec<Sort>,
}

/// The typed names used by a program or formula.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Signature {
    pub sorts: Vec<String>,
    pub constants: Vec<ConstDecl>,
    pub functions: Vec<FunctionDecl>,
    pub predicates: Vec<PredicateDecl>,
}

impl Signature {
    pub fn new() -> Self {
        Signature::default()
    }

    pub fn add_sort(&mut self, name: impl Into<String>) -> bool {
        let name = name.into();
        if name.is_empty() || self.sorts.iter().any(|s| s == &name) {
            return false;
        }
        self.sorts.push(name);
        true
    }

    pub fn add_constant(&mut self, name: impl Into<String>, sort: Sort) -> Result<(), TypeError> {
        let name = name.into();
        if name.is_empty() {
            return Err(TypeError::BadName("constant".into()));
        }
        if self.constants.iter().any(|c| c.name == name) {
            return Err(TypeError::Duplicate(format!("constant {name}")));
        }
        self.constants.push(ConstDecl { name, sort });
        Ok(())
    }

    pub fn add_function(
        &mut self,
        name: impl Into<String>,
        args: Vec<Sort>,
        result: Sort,
    ) -> Result<(), TypeError> {
        let name = name.into();
        if name.is_empty() {
            return Err(TypeError::BadName("function".into()));
        }
        if self.functions.iter().any(|f| f.name == name) {
            return Err(TypeError::Duplicate(format!("function {name}")));
        }
        self.functions.push(FunctionDecl { name, args, result });
        Ok(())
    }

    pub fn add_predicate(
        &mut self,
        name: impl Into<String>,
        args: Vec<Sort>,
    ) -> Result<(), TypeError> {
        let name = name.into();
        if name.is_empty() {
            return Err(TypeError::BadName("predicate".into()));
        }
        if self.predicates.iter().any(|p| p.name == name) {
            return Err(TypeError::Duplicate(format!("predicate {name}")));
        }
        self.predicates.push(PredicateDecl { name, args });
        Ok(())
    }

    pub fn sort_exists(&self, sort: &Sort) -> bool {
        match sort {
            Sort::Bool | Sort::Int | Sort::Real => true,
            Sort::Named(n) => self.sorts.iter().any(|s| s == n),
        }
    }

    pub fn constant(&self, name: &str) -> Option<&ConstDecl> {
        self.constants.iter().find(|c| c.name == name)
    }

    pub fn function(&self, name: &str) -> Option<&FunctionDecl> {
        self.functions.iter().find(|f| f.name == name)
    }

    pub fn predicate(&self, name: &str) -> Option<&PredicateDecl> {
        self.predicates.iter().find(|p| p.name == name)
    }

    /// Validate declaration-level invariants (no duplicate names, non-empty
    /// sort and symbol names, every sort used is declared).
    pub fn validate(&self) -> Result<(), Vec<TypeError>> {
        let mut errors = Vec::new();
        let mut seen = BTreeSet::new();
        for s in &self.sorts {
            if s.is_empty() {
                errors.push(TypeError::BadName("sort".into()));
            }
            if !seen.insert(s.clone()) {
                errors.push(TypeError::Duplicate(format!("sort {s}")));
            }
        }
        let mut terms = BTreeSet::new();
        for c in &self.constants {
            if c.name.is_empty() {
                errors.push(TypeError::BadName("constant".into()));
            }
            if !terms.insert(c.name.clone()) {
                errors.push(TypeError::Duplicate(format!("term symbol {}", c.name)));
            }
            if !self.sort_exists(&c.sort) {
                errors.push(TypeError::UnknownSort(c.sort.clone()));
            }
        }
        for f in &self.functions {
            if f.name.is_empty() {
                errors.push(TypeError::BadName("function".into()));
            }
            if !terms.insert(f.name.clone()) {
                errors.push(TypeError::Duplicate(format!("term symbol {}", f.name)));
            }
            for a in &f.args {
                if !self.sort_exists(a) {
                    errors.push(TypeError::UnknownSort(a.clone()));
                }
            }
            if !self.sort_exists(&f.result) {
                errors.push(TypeError::UnknownSort(f.result.clone()));
            }
        }
        let mut predicates = BTreeSet::new();
        for p in &self.predicates {
            if p.name.is_empty() {
                errors.push(TypeError::BadName("predicate".into()));
            }
            if !predicates.insert(p.name.clone()) {
                errors.push(TypeError::Duplicate(format!("predicate {}", p.name)));
            }
            for a in &p.args {
                if !self.sort_exists(a) {
                    errors.push(TypeError::UnknownSort(a.clone()));
                }
            }
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

/// A finite typed Horn program.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct TypedProgram {
    pub signature: Signature,
    pub facts: Vec<Atom>,
    pub rules: Vec<Rule>,
}

impl TypedProgram {
    pub fn new(signature: Signature) -> Self {
        TypedProgram {
            signature,
            facts: Vec::new(),
            rules: Vec::new(),
        }
    }

    /// Type-check every fact and rule against the signature.
    ///
    /// This checks arity and sort agreement. It does not enforce Datalog range
    /// restriction, because a rule may be intended for a resolution engine; use
    /// [`Rule::is_safe`] when the Datalog fragment is required.
    pub fn check(&self) -> Result<(), Vec<TypeError>> {
        let mut errors = match self.signature.validate() {
            Ok(()) => Vec::new(),
            Err(e) => e,
        };
        for fact in &self.facts {
            self.check_atom(fact, &mut errors);
        }
        for rule in &self.rules {
            let mut vars = BTreeMap::new();
            self.check_atom(&rule.head, &mut errors);
            collect_atom_vars(&rule.head, &mut vars, &mut errors);
            for l in &rule.body {
                self.check_atom(&l.atom, &mut errors);
                collect_atom_vars(&l.atom, &mut vars, &mut errors);
            }
        }
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    fn check_atom(&self, atom: &Atom, errors: &mut Vec<TypeError>) {
        let Some(decl) = self.signature.predicate(&atom.predicate) else {
            errors.push(TypeError::UnknownPredicate(atom.predicate.clone()));
            return;
        };
        if decl.args.len() != atom.terms.len() {
            errors.push(TypeError::Arity {
                symbol: atom.predicate.clone(),
                expected: decl.args.len(),
                got: atom.terms.len(),
            });
            return;
        }
        for (t, expected) in atom.terms.iter().zip(decl.args.iter()) {
            self.check_term(t, expected, errors);
        }
    }

    fn check_term(&self, term: &Term, expected: &Sort, errors: &mut Vec<TypeError>) {
        if term.sort() != expected {
            errors.push(TypeError::SortMismatch {
                expected: expected.clone(),
                got: term.sort().clone(),
            });
        }
        if !self.signature.sort_exists(term.sort()) {
            errors.push(TypeError::UnknownSort(term.sort().clone()));
        }
        match term {
            Term::Var(_) => {}
            Term::Const(name, sort) => match self.signature.constant(name) {
                Some(c) if &c.sort == sort => {}
                Some(c) => errors.push(TypeError::SortMismatch {
                    expected: c.sort.clone(),
                    got: sort.clone(),
                }),
                None => errors.push(TypeError::UnknownConstant(name.clone())),
            },
            Term::App(name, args, result) => match self.signature.function(name) {
                Some(f) => {
                    if &f.result != result {
                        errors.push(TypeError::SortMismatch {
                            expected: f.result.clone(),
                            got: result.clone(),
                        });
                    }
                    if f.args.len() != args.len() {
                        errors.push(TypeError::Arity {
                            symbol: name.clone(),
                            expected: f.args.len(),
                            got: args.len(),
                        });
                    } else {
                        for (a, e) in args.iter().zip(f.args.iter()) {
                            self.check_term(a, e, errors);
                        }
                    }
                }
                None => errors.push(TypeError::UnknownFunction(name.clone())),
            },
        }
    }
}

fn collect_atom_vars(atom: &Atom, out: &mut BTreeMap<String, Sort>, errors: &mut Vec<TypeError>) {
    for t in &atom.terms {
        let vars = t.variables();
        for (name, sort) in vars {
            if let Some(previous) = out.get(&name) {
                if previous != &sort {
                    errors.push(TypeError::VariableSort {
                        name,
                        first: previous.clone(),
                        second: sort,
                    });
                }
            } else {
                out.insert(name, sort);
            }
        }
    }
}

/// First-order formulas used by the proof layer.
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
    Forall(Var, Box<Formula>),
    Exists(Var, Box<Formula>),
}

impl Formula {
    pub fn atom(atom: Atom) -> Self {
        Formula::Atom(atom)
    }

    pub fn negated(f: Formula) -> Self {
        Formula::Not(Box::new(f))
    }

    pub fn and(fs: Vec<Formula>) -> Self {
        Formula::And(fs)
    }

    pub fn or(fs: Vec<Formula>) -> Self {
        Formula::Or(fs)
    }

    pub fn implies(a: Formula, b: Formula) -> Self {
        Formula::Implies(Box::new(a), Box::new(b))
    }

    pub fn iff(a: Formula, b: Formula) -> Self {
        Formula::Iff(Box::new(a), Box::new(b))
    }

    pub fn forall(v: Var, f: Formula) -> Self {
        Formula::Forall(v, Box::new(f))
    }

    pub fn exists(v: Var, f: Formula) -> Self {
        Formula::Exists(v, Box::new(f))
    }
}

/// A type-checking or declaration error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeError {
    BadName(String),
    Duplicate(String),
    UnknownSort(Sort),
    UnknownConstant(String),
    UnknownFunction(String),
    UnknownPredicate(String),
    Arity {
        symbol: String,
        expected: usize,
        got: usize,
    },
    SortMismatch {
        expected: Sort,
        got: Sort,
    },
    VariableSort {
        name: String,
        first: Sort,
        second: Sort,
    },
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::BadName(k) => write!(f, "empty {k} name"),
            TypeError::Duplicate(n) => write!(f, "duplicate declaration: {n}"),
            TypeError::UnknownSort(s) => write!(f, "unknown sort {s}"),
            TypeError::UnknownConstant(n) => write!(f, "unknown constant {n}"),
            TypeError::UnknownFunction(n) => write!(f, "unknown function {n}"),
            TypeError::UnknownPredicate(n) => write!(f, "unknown predicate {n}"),
            TypeError::Arity {
                symbol,
                expected,
                got,
            } => write!(f, "{symbol} expects {expected} arguments, got {got}"),
            TypeError::SortMismatch { expected, got } => {
                write!(f, "expected sort {expected}, got {got}")
            }
            TypeError::VariableSort {
                name,
                first,
                second,
            } => {
                write!(f, "variable {name} used at both {first} and {second}")
            }
        }
    }
}

impl std::error::Error for TypeError {}

/// A parser or serialisation error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IrError {
    pub offset: usize,
    pub message: String,
}

impl IrError {
    fn new(offset: usize, message: impl Into<String>) -> Self {
        IrError {
            offset,
            message: message.into(),
        }
    }
}

impl fmt::Display for IrError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "IR error at {}: {}", self.offset, self.message)
    }
}

impl std::error::Error for IrError {}

/// A tiny lossless S-expression tree used by every v4 serialised artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

impl Sexp {
    pub fn atom(s: impl Into<String>) -> Self {
        Sexp::Atom(s.into())
    }

    pub fn list(items: Vec<Sexp>) -> Self {
        Sexp::List(items)
    }

    pub fn parse(input: &str) -> Result<Sexp, IrError> {
        if input.len() > MAX_SEXP_BYTES {
            return Err(IrError::new(0, "input exceeds serialisation limit"));
        }
        let mut p = SexpParser {
            chars: input.chars().collect(),
            pos: 0,
        };
        p.skip_space();
        if p.eof() {
            return Err(IrError::new(0, "empty S-expression"));
        }
        let out = p.expr(0)?;
        p.skip_space();
        if !p.eof() {
            return Err(IrError::new(p.pos, "trailing input after S-expression"));
        }
        Ok(out)
    }

    pub fn render(&self) -> String {
        let mut out = String::new();
        self.render_into(&mut out);
        out
    }

    fn render_into(&self, out: &mut String) {
        match self {
            Sexp::Atom(a) => render_atom(a, out),
            Sexp::List(items) => {
                out.push('(');
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    item.render_into(out);
                }
                out.push(')');
            }
        }
    }

    pub fn as_list(&self) -> Option<&[Sexp]> {
        match self {
            Sexp::List(v) => Some(v),
            _ => None,
        }
    }

    pub fn as_atom(&self) -> Option<&str> {
        match self {
            Sexp::Atom(s) => Some(s),
            _ => None,
        }
    }
}

fn render_atom(a: &str, out: &mut String) {
    let simple = !a.is_empty()
        && a.chars().all(|c| {
            c.is_ascii_alphanumeric()
                || matches!(
                    c,
                    '_' | '-'
                        | '+'
                        | '*'
                        | '/'
                        | '<'
                        | '>'
                        | '='
                        | '!'
                        | '?'
                        | '.'
                        | ':'
                        | '#'
                        | '@'
                        | '%'
                        | '&'
                        | '|'
                        | '^'
                        | '~'
                )
        });
    if simple {
        out.push_str(a);
        return;
    }
    out.push('"');
    for c in a.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            _ => out.push(c),
        }
    }
    out.push('"');
}

struct SexpParser {
    chars: Vec<char>,
    pos: usize,
}

impl SexpParser {
    fn eof(&self) -> bool {
        self.pos >= self.chars.len()
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.pos += 1;
        Some(c)
    }

    fn skip_space(&mut self) {
        loop {
            while matches!(self.peek(), Some(c) if c.is_whitespace()) {
                self.pos += 1;
            }
            if self.peek() == Some(';') {
                while let Some(c) = self.bump() {
                    if c == '\n' {
                        break;
                    }
                }
                continue;
            }
            break;
        }
    }

    fn expr(&mut self, depth: usize) -> Result<Sexp, IrError> {
        if depth > MAX_SEXP_DEPTH {
            return Err(IrError::new(self.pos, "S-expression nesting too deep"));
        }
        self.skip_space();
        match self.peek() {
            None => Err(IrError::new(self.pos, "unexpected end of input")),
            Some('(') => {
                self.bump();
                let mut items = Vec::new();
                loop {
                    self.skip_space();
                    match self.peek() {
                        None => return Err(IrError::new(self.pos, "unclosed list")),
                        Some(')') => {
                            self.bump();
                            return Ok(Sexp::List(items));
                        }
                        Some(_) => items.push(self.expr(depth + 1)?),
                    }
                }
            }
            Some(')') => Err(IrError::new(self.pos, "unexpected ')'")),
            Some('"') => self.string(),
            Some(_) => {
                let start = self.pos;
                while let Some(c) = self.peek() {
                    if c.is_whitespace() || c == '(' || c == ')' || c == ';' {
                        break;
                    }
                    self.pos += 1;
                }
                Ok(Sexp::Atom(self.chars[start..self.pos].iter().collect()))
            }
        }
    }

    fn string(&mut self) -> Result<Sexp, IrError> {
        self.bump();
        let mut out = String::new();
        loop {
            let Some(c) = self.bump() else {
                return Err(IrError::new(self.pos, "unclosed string"));
            };
            match c {
                '"' => return Ok(Sexp::Atom(out)),
                '\\' => {
                    let Some(e) = self.bump() else {
                        return Err(IrError::new(self.pos, "unclosed escape"));
                    };
                    out.push(match e {
                        '\\' => '\\',
                        '"' => '"',
                        'n' => '\n',
                        'r' => '\r',
                        't' => '\t',
                        other => {
                            return Err(IrError::new(self.pos, format!("unknown escape \\{other}")))
                        }
                    });
                }
                _ => out.push(c),
            }
        }
    }
}

fn list<'a>(s: &'a Sexp, what: &str) -> Result<&'a [Sexp], IrError> {
    s.as_list()
        .ok_or_else(|| IrError::new(0, format!("expected list for {what}")))
}

fn atom<'a>(s: &'a Sexp, what: &str) -> Result<&'a str, IrError> {
    s.as_atom()
        .ok_or_else(|| IrError::new(0, format!("expected atom for {what}")))
}

fn head(s: &Sexp, expected: &str) -> Result<(), IrError> {
    let items = list(s, expected)?;
    match items.first().and_then(Sexp::as_atom) {
        Some(tag) if tag == expected => Ok(()),
        Some(tag) => Err(IrError::new(0, format!("expected {expected}, found {tag}"))),
        None => Err(IrError::new(0, format!("empty list, expected {expected}"))),
    }
}

fn usize_atom(s: &Sexp, what: &str) -> Result<usize, IrError> {
    let a = atom(s, what)?;
    a.parse()
        .map_err(|_| IrError::new(0, format!("{what} is not a number: {a}")))
}

// ---- serialisation -------------------------------------------------------

impl Signature {
    pub fn to_sexp(&self) -> Sexp {
        let sorts = Sexp::List(
            vec![Sexp::atom("sorts")]
                .into_iter()
                .chain(self.sorts.iter().map(|s| Sexp::atom(s.clone())))
                .collect(),
        );
        let constants = Sexp::List(
            std::iter::once(Sexp::atom("constants"))
                .chain(self.constants.iter().map(|c| {
                    Sexp::List(vec![
                        Sexp::atom("const"),
                        Sexp::atom(c.name.clone()),
                        sort_to_sexp(&c.sort),
                    ])
                }))
                .collect(),
        );
        let functions = Sexp::List(
            std::iter::once(Sexp::atom("functions"))
                .chain(self.functions.iter().map(|f| {
                    Sexp::List(vec![
                        Sexp::atom("func"),
                        Sexp::atom(f.name.clone()),
                        Sexp::List(f.args.iter().map(sort_to_sexp).collect()),
                        sort_to_sexp(&f.result),
                    ])
                }))
                .collect(),
        );
        let predicates = Sexp::List(
            std::iter::once(Sexp::atom("predicates"))
                .chain(self.predicates.iter().map(|p| {
                    Sexp::List(vec![
                        Sexp::atom("pred"),
                        Sexp::atom(p.name.clone()),
                        Sexp::List(p.args.iter().map(sort_to_sexp).collect()),
                    ])
                }))
                .collect(),
        );
        Sexp::List(vec![
            Sexp::atom("signature"),
            sorts,
            constants,
            functions,
            predicates,
        ])
    }

    pub fn from_sexp(s: &Sexp) -> Result<Self, IrError> {
        head(s, "signature")?;
        let items = list(s, "signature")?;
        if items.len() != 5 {
            return Err(IrError::new(0, "signature needs four sections"));
        }
        let mut sig = Signature::new();
        let sorts = list(&items[1], "sorts")?;
        if sorts.first().and_then(Sexp::as_atom) != Some("sorts") {
            return Err(IrError::new(0, "expected sorts section"));
        }
        for item in &sorts[1..] {
            sig.add_sort(atom(item, "sort")?);
        }
        let constants = list(&items[2], "constants")?;
        if constants.first().and_then(Sexp::as_atom) != Some("constants") {
            return Err(IrError::new(0, "expected constants section"));
        }
        for item in &constants[1..] {
            head(item, "const")?;
            let v = list(item, "const")?;
            if v.len() != 3 {
                return Err(IrError::new(0, "const needs name and sort"));
            }
            sig.add_constant(atom(&v[1], "constant name")?, sort_from_sexp(&v[2])?)
                .map_err(|e| IrError::new(0, e.to_string()))?;
        }
        let functions = list(&items[3], "functions")?;
        if functions.first().and_then(Sexp::as_atom) != Some("functions") {
            return Err(IrError::new(0, "expected functions section"));
        }
        for item in &functions[1..] {
            head(item, "func")?;
            let v = list(item, "func")?;
            if v.len() != 4 {
                return Err(IrError::new(
                    0,
                    "func needs name, argument sorts and result sort",
                ));
            }
            let args = list(&v[2], "argument sorts")?
                .iter()
                .map(sort_from_sexp)
                .collect::<Result<Vec<_>, _>>()?;
            sig.add_function(atom(&v[1], "function name")?, args, sort_from_sexp(&v[3])?)
                .map_err(|e| IrError::new(0, e.to_string()))?;
        }
        let predicates = list(&items[4], "predicates")?;
        if predicates.first().and_then(Sexp::as_atom) != Some("predicates") {
            return Err(IrError::new(0, "expected predicates section"));
        }
        for item in &predicates[1..] {
            head(item, "pred")?;
            let v = list(item, "pred")?;
            if v.len() != 3 {
                return Err(IrError::new(0, "pred needs name and argument sorts"));
            }
            let args = list(&v[2], "predicate sorts")?
                .iter()
                .map(sort_from_sexp)
                .collect::<Result<Vec<_>, _>>()?;
            sig.add_predicate(atom(&v[1], "predicate name")?, args)
                .map_err(|e| IrError::new(0, e.to_string()))?;
        }
        Ok(sig)
    }
}

impl TypedProgram {
    pub fn to_sexp(&self) -> Sexp {
        let facts = Sexp::List(
            std::iter::once(Sexp::atom("facts"))
                .chain(self.facts.iter().map(atom_to_sexp))
                .collect(),
        );
        let rules = Sexp::List(
            std::iter::once(Sexp::atom("rules"))
                .chain(self.rules.iter().map(rule_to_sexp))
                .collect(),
        );
        Sexp::List(vec![
            Sexp::atom("axiom-ir"),
            Sexp::List(vec![Sexp::atom("version"), Sexp::atom("1")]),
            self.signature.to_sexp(),
            facts,
            rules,
        ])
    }

    pub fn from_sexp(s: &Sexp) -> Result<Self, IrError> {
        head(s, "axiom-ir")?;
        let items = list(s, "axiom-ir")?;
        if items.len() != 5 {
            return Err(IrError::new(
                0,
                "axiom-ir needs version, signature, facts and rules",
            ));
        }
        let version = list(&items[1], "version")?;
        if version.len() != 2 || atom(&version[1], "version")? != "1" {
            return Err(IrError::new(0, "unsupported IR version"));
        }
        let signature = Signature::from_sexp(&items[2])?;
        let facts_s = list(&items[3], "facts")?;
        if facts_s.first().and_then(Sexp::as_atom) != Some("facts") {
            return Err(IrError::new(0, "expected facts section"));
        }
        let facts = facts_s[1..]
            .iter()
            .map(atom_from_sexp)
            .collect::<Result<Vec<_>, _>>()?;
        let rules_s = list(&items[4], "rules")?;
        if rules_s.first().and_then(Sexp::as_atom) != Some("rules") {
            return Err(IrError::new(0, "expected rules section"));
        }
        let rules = rules_s[1..]
            .iter()
            .map(rule_from_sexp)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(TypedProgram {
            signature,
            facts,
            rules,
        })
    }
}

impl Formula {
    pub fn to_sexp(&self) -> Sexp {
        match self {
            Formula::True => Sexp::List(vec![Sexp::atom("true")]),
            Formula::False => Sexp::List(vec![Sexp::atom("false")]),
            Formula::Atom(a) => atom_to_sexp(a),
            Formula::Not(f) => Sexp::List(vec![Sexp::atom("not"), f.to_sexp()]),
            Formula::And(fs) => Sexp::List(
                std::iter::once(Sexp::atom("and"))
                    .chain(fs.iter().map(Formula::to_sexp))
                    .collect(),
            ),
            Formula::Or(fs) => Sexp::List(
                std::iter::once(Sexp::atom("or"))
                    .chain(fs.iter().map(Formula::to_sexp))
                    .collect(),
            ),
            Formula::Implies(a, b) => {
                Sexp::List(vec![Sexp::atom("implies"), a.to_sexp(), b.to_sexp()])
            }
            Formula::Iff(a, b) => Sexp::List(vec![Sexp::atom("iff"), a.to_sexp(), b.to_sexp()]),
            Formula::Forall(v, f) => {
                Sexp::List(vec![Sexp::atom("forall"), var_to_sexp(v), f.to_sexp()])
            }
            Formula::Exists(v, f) => {
                Sexp::List(vec![Sexp::atom("exists"), var_to_sexp(v), f.to_sexp()])
            }
        }
    }

    pub fn from_sexp(s: &Sexp) -> Result<Self, IrError> {
        let items = list(s, "formula")?;
        let tag = items
            .first()
            .and_then(Sexp::as_atom)
            .ok_or_else(|| IrError::new(0, "empty formula"))?;
        match tag {
            "true" if items.len() == 1 => Ok(Formula::True),
            "false" if items.len() == 1 => Ok(Formula::False),
            "atom" => Ok(Formula::Atom(atom_from_sexp(s)?)),
            "not" if items.len() == 2 => Ok(Formula::negated(Formula::from_sexp(&items[1])?)),
            "and" => Ok(Formula::and(
                items[1..]
                    .iter()
                    .map(Formula::from_sexp)
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            "or" => Ok(Formula::or(
                items[1..]
                    .iter()
                    .map(Formula::from_sexp)
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            "implies" if items.len() == 3 => Ok(Formula::implies(
                Formula::from_sexp(&items[1])?,
                Formula::from_sexp(&items[2])?,
            )),
            "iff" if items.len() == 3 => Ok(Formula::iff(
                Formula::from_sexp(&items[1])?,
                Formula::from_sexp(&items[2])?,
            )),
            "forall" | "exists" if items.len() == 3 => {
                let v = var_from_sexp(&items[1])?;
                let f = Formula::from_sexp(&items[2])?;
                if tag == "forall" {
                    Ok(Formula::forall(v, f))
                } else {
                    Ok(Formula::exists(v, f))
                }
            }
            _ => Err(IrError::new(0, format!("bad formula form: {tag}"))),
        }
    }
}

fn sort_to_sexp(s: &Sort) -> Sexp {
    match s {
        Sort::Bool => Sexp::atom("Bool"),
        Sort::Int => Sexp::atom("Int"),
        Sort::Real => Sexp::atom("Real"),
        Sort::Named(n) => Sexp::atom(n.clone()),
    }
}

fn sort_from_sexp(s: &Sexp) -> Result<Sort, IrError> {
    let name = atom(s, "sort")?;
    Ok(match name {
        "Bool" => Sort::Bool,
        "Int" => Sort::Int,
        "Real" => Sort::Real,
        _ => Sort::Named(name.to_string()),
    })
}

fn var_to_sexp(v: &Var) -> Sexp {
    Sexp::List(vec![
        Sexp::atom("var"),
        Sexp::atom(v.name.clone()),
        sort_to_sexp(&v.sort),
    ])
}

fn var_from_sexp(s: &Sexp) -> Result<Var, IrError> {
    head(s, "var")?;
    let items = list(s, "var")?;
    if items.len() != 3 {
        return Err(IrError::new(0, "var needs name and sort"));
    }
    Ok(Var::new(
        atom(&items[1], "variable name")?,
        sort_from_sexp(&items[2])?,
    ))
}

fn term_to_sexp(t: &Term) -> Sexp {
    match t {
        Term::Var(v) => var_to_sexp(v),
        Term::Const(n, s) => Sexp::List(vec![
            Sexp::atom("const"),
            Sexp::atom(n.clone()),
            sort_to_sexp(s),
        ]),
        Term::App(n, args, s) => Sexp::List(vec![
            Sexp::atom("app"),
            Sexp::atom(n.clone()),
            Sexp::List(args.iter().map(term_to_sexp).collect()),
            sort_to_sexp(s),
        ]),
    }
}

fn term_from_sexp(s: &Sexp) -> Result<Term, IrError> {
    let items = list(s, "term")?;
    let tag = items
        .first()
        .and_then(Sexp::as_atom)
        .ok_or_else(|| IrError::new(0, "empty term"))?;
    match tag {
        "var" => Ok(Term::Var(var_from_sexp(s)?)),
        "const" if items.len() == 3 => Ok(Term::constant(
            atom(&items[1], "constant name")?,
            sort_from_sexp(&items[2])?,
        )),
        "app" if items.len() == 4 => {
            let args = list(&items[2], "application arguments")?
                .iter()
                .map(term_from_sexp)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Term::app(
                atom(&items[1], "function name")?,
                args,
                sort_from_sexp(&items[3])?,
            ))
        }
        _ => Err(IrError::new(0, format!("bad term form: {tag}"))),
    }
}

fn atom_to_sexp(a: &Atom) -> Sexp {
    Sexp::List(vec![
        Sexp::atom("atom"),
        Sexp::atom(a.predicate.clone()),
        Sexp::List(a.terms.iter().map(term_to_sexp).collect()),
    ])
}

fn atom_from_sexp(s: &Sexp) -> Result<Atom, IrError> {
    head(s, "atom")?;
    let items = list(s, "atom")?;
    if items.len() != 3 {
        return Err(IrError::new(0, "atom needs predicate and terms"));
    }
    let terms = list(&items[2], "atom terms")?
        .iter()
        .map(term_from_sexp)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Atom::new(atom(&items[1], "predicate name")?, terms))
}

fn literal_to_sexp(l: &Literal) -> Sexp {
    Sexp::List(vec![
        Sexp::atom("literal"),
        Sexp::atom(if l.negated { "neg" } else { "pos" }),
        atom_to_sexp(&l.atom),
    ])
}

fn literal_from_sexp(s: &Sexp) -> Result<Literal, IrError> {
    head(s, "literal")?;
    let items = list(s, "literal")?;
    if items.len() != 3 {
        return Err(IrError::new(0, "literal needs polarity and atom"));
    }
    let a = atom_from_sexp(&items[2])?;
    match atom(&items[1], "literal polarity")? {
        "pos" => Ok(Literal::positive(a)),
        "neg" => Ok(Literal::negative(a)),
        other => Err(IrError::new(0, format!("bad polarity {other}"))),
    }
}

fn rule_to_sexp(r: &Rule) -> Sexp {
    Sexp::List(vec![
        Sexp::atom("rule"),
        atom_to_sexp(&r.head),
        Sexp::List(r.body.iter().map(literal_to_sexp).collect()),
    ])
}

fn rule_from_sexp(s: &Sexp) -> Result<Rule, IrError> {
    head(s, "rule")?;
    let items = list(s, "rule")?;
    if items.len() != 3 {
        return Err(IrError::new(0, "rule needs head and body"));
    }
    let head = atom_from_sexp(&items[1])?;
    let body = list(&items[2], "rule body")?
        .iter()
        .map(literal_from_sexp)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Rule::new(head, body))
}

/// Parse a versioned serialised program.
pub fn parse_program(input: &str) -> Result<TypedProgram, IrError> {
    TypedProgram::from_sexp(&Sexp::parse(input)?)
}

/// Parse a versioned serialised formula.
pub fn parse_formula(input: &str) -> Result<Formula, IrError> {
    Formula::from_sexp(&Sexp::parse(input)?)
}

/// Parse an integer list used by tiny test artifacts.
pub fn parse_usize_list(input: &str) -> Result<Vec<usize>, IrError> {
    let s = Sexp::parse(input)?;
    list(&s, "usize list")?
        .iter()
        .map(|x| usize_atom(x, "list item"))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn person() -> Sort {
        Sort::Named("Person".into())
    }

    fn example() -> TypedProgram {
        let mut sig = Signature::new();
        sig.add_sort("Person");
        sig.add_constant("alice", person()).unwrap();
        sig.add_constant("bob", person()).unwrap();
        sig.add_predicate("edge", vec![person(), person()]).unwrap();
        let mut program = TypedProgram::new(sig);
        program.facts.push(Atom::new(
            "edge",
            vec![
                Term::constant("alice", person()),
                Term::constant("bob", person()),
            ],
        ));
        program.rules.push(Rule::new(
            Atom::new(
                "edge",
                vec![Term::var("X", person()), Term::var("Y", person())],
            ),
            vec![Literal::positive(Atom::new(
                "edge",
                vec![Term::var("X", person()), Term::var("Y", person())],
            ))],
        ));
        program
    }

    #[test]
    fn program_round_trips_without_loss() {
        let program = example();
        program.check().unwrap();
        let text = program.to_sexp().render();
        let parsed = TypedProgram::from_sexp(&Sexp::parse(&text).unwrap()).unwrap();
        assert_eq!(program, parsed);
    }

    #[test]
    fn type_errors_are_reported() {
        let mut p = example();
        p.facts
            .push(Atom::new("edge", vec![Term::constant("alice", person())]));
        let errors = p.check().unwrap_err();
        assert!(errors.iter().any(|e| matches!(e, TypeError::Arity { .. })));
    }

    #[test]
    fn duplicate_declarations_are_rejected() {
        let mut sig = Signature::new();
        sig.add_sort("A");
        assert!(!sig.add_sort("A"));
        assert!(sig.add_constant("a", Sort::named("A")).is_ok());
        assert!(sig.add_constant("a", Sort::named("A")).is_err());
    }

    #[test]
    fn quoted_symbols_round_trip() {
        let s = Sexp::List(vec![Sexp::atom("a b"), Sexp::atom("quote\"slash\\")]);
        let text = s.render();
        assert_eq!(Sexp::parse(&text).unwrap(), s);
    }

    #[test]
    fn malformed_sexp_is_an_error_not_a_panic() {
        assert!(Sexp::parse("(a (b)").is_err());
        assert!(Sexp::parse(")").is_err());
        assert!(Sexp::parse("").is_err());
        let deep = format!("{}x{}", "(".repeat(300), ")".repeat(300));
        assert!(Sexp::parse(&deep).is_err());
    }

    #[test]
    fn formula_round_trips() {
        let f = Formula::forall(
            Var::new("x", person()),
            Formula::implies(
                Formula::atom(Atom::new("human", vec![Term::var("x", person())])),
                Formula::atom(Atom::new("mortal", vec![Term::var("x", person())])),
            ),
        );
        let text = f.to_sexp().render();
        assert_eq!(Formula::from_sexp(&Sexp::parse(&text).unwrap()).unwrap(), f);
    }

    #[test]
    fn safety_is_computed_not_assumed() {
        let safe = Rule::new(
            Atom::new("safe", vec![Term::var("X", person())]),
            vec![
                Literal::positive(Atom::new("node", vec![Term::var("X", person())])),
                Literal::negative(Atom::new("blocked", vec![Term::var("X", person())])),
            ],
        );
        assert!(safe.is_safe());
        let unsafe_rule = Rule::new(
            Atom::new("safe", vec![Term::var("X", person())]),
            vec![Literal::negative(Atom::new(
                "blocked",
                vec![Term::var("X", person())],
            ))],
        );
        assert!(!unsafe_rule.is_safe());
    }
}
