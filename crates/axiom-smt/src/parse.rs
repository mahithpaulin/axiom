//! SMT-LIB 2 reader for the Axiom quantifier-free difference-logic fragment.
//!
//! The accepted surface is deliberately small and explicit:
//!
//! * commands: `set-logic`, `set-info`, `set-option`, `declare-fun`,
//!   `declare-const`, `assert`, `check-sat`, `get-model`, `exit`;
//! * sorts: `Int` and `Bool`;
//! * terms: numerals, declared constants, uninterpreted function application,
//!   `+`, `-`, `*` (a numeral coefficient of `1` or `-1` only);
//! * formulas: `true`, `false`, declared Boolean constants, `not`, `and`,
//!   `or`, `xor`, `=>`, `ite`, `=`, `distinct`, `<`, `<=`, `>`, `>=`.
//!
//! Everything outside that surface is an error, and outside the *fragment* it
//! is an explicit `Unsupported`. Nothing is guessed: a numeral coefficient of
//! `2` is rejected rather than silently dropped.

use std::fmt;

/// A parse or fragment error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SmtError {
    Parse { offset: usize, message: String },
    Unsupported { offset: usize, message: String },
}

impl fmt::Display for SmtError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SmtError::Parse { offset, message } => write!(f, "at byte {offset}: {message}"),
            SmtError::Unsupported { offset, message } => {
                write!(f, "at byte {offset}: outside the SMT fragment: {message}")
            }
        }
    }
}

impl std::error::Error for SmtError {}

pub type Result<T> = std::result::Result<T, SmtError>;

fn parse_err<T>(offset: usize, message: impl Into<String>) -> Result<T> {
    Err(SmtError::Parse {
        offset,
        message: message.into(),
    })
}

fn unsupported<T>(offset: usize, message: impl Into<String>) -> Result<T> {
    Err(SmtError::Unsupported {
        offset,
        message: message.into(),
    })
}

// ---------------------------------------------------------------------------
// S-expressions
// ---------------------------------------------------------------------------

/// One s-expression with its byte offset.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SExpr {
    Atom(String, usize),
    List(Vec<SExpr>, usize),
}

impl SExpr {
    pub fn offset(&self) -> usize {
        match self {
            SExpr::Atom(_, o) | SExpr::List(_, o) => *o,
        }
    }

    fn head(&self) -> Option<&str> {
        match self {
            SExpr::List(items, _) => match items.first() {
                Some(SExpr::Atom(name, _)) => Some(name.as_str()),
                _ => None,
            },
            SExpr::Atom(_, _) => None,
        }
    }
}

struct Reader {
    chars: Vec<char>,
    pos: usize,
}

impl Reader {
    fn new(input: &str) -> Self {
        Reader {
            chars: input.chars().collect(),
            pos: 0,
        }
    }

    fn skip_trivia(&mut self) {
        while self.pos < self.chars.len() {
            let c = self.chars[self.pos];
            if c.is_whitespace() {
                self.pos += 1;
            } else if c == ';' {
                while self.pos < self.chars.len() && self.chars[self.pos] != '\n' {
                    self.pos += 1;
                }
            } else {
                break;
            }
        }
    }

    fn read(&mut self) -> Result<Option<SExpr>> {
        self.skip_trivia();
        if self.pos >= self.chars.len() {
            return Ok(None);
        }
        let start = self.pos;
        match self.chars[self.pos] {
            '(' => {
                self.pos += 1;
                let mut items = Vec::new();
                loop {
                    self.skip_trivia();
                    if self.pos >= self.chars.len() {
                        return parse_err(start, "unterminated list");
                    }
                    if self.chars[self.pos] == ')' {
                        self.pos += 1;
                        return Ok(Some(SExpr::List(items, start)));
                    }
                    match self.read()? {
                        Some(item) => items.push(item),
                        None => return parse_err(start, "unterminated list"),
                    }
                }
            }
            ')' => parse_err(start, "unexpected ')'"),
            _ => {
                while self.pos < self.chars.len() {
                    let c = self.chars[self.pos];
                    if c.is_whitespace() || c == '(' || c == ')' || c == ';' {
                        break;
                    }
                    self.pos += 1;
                }
                let text: String = self.chars[start..self.pos].iter().collect();
                if text.is_empty() {
                    return parse_err(start, "empty symbol");
                }
                Ok(Some(SExpr::Atom(text, start)))
            }
        }
    }
}

fn read_all(input: &str) -> Result<Vec<SExpr>> {
    let mut reader = Reader::new(input);
    let mut out = Vec::new();
    while let Some(expr) = reader.read()? {
        out.push(expr);
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Problem AST
// ---------------------------------------------------------------------------

/// A term that stands for a value on its own: a declared constant, an
/// uninterpreted function application, or a numeral.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum BaseTerm {
    Var(String),
    App(String, Vec<BaseTerm>),
    Num(i64),
    /// The implicit zero of the difference-logic fragment. Every constraint is
    /// a difference of terms, so the whole system is defined only up to a
    /// constant shift; the origin is the term that shift is measured from.
    Origin,
}

/// A theory atom in the fragment.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Atom {
    /// `x - y <= c` over terms.
    Rdl { x: BaseTerm, y: BaseTerm, c: i64 },
    /// `x = y` over terms.
    Eq(BaseTerm, BaseTerm),
    /// `x != y` over terms.
    Neq(BaseTerm, BaseTerm),
}

/// A formula over theory atoms and Boolean structure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Formula {
    Bool(bool),
    Prop(String),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Xor(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Ite(Box<Formula>, Box<Formula>, Box<Formula>),
    Atom(Atom),
}

/// A declared symbol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decl {
    /// An `Int` constant (a zero-argument `declare-fun` or a `declare-const`).
    IntConst(String),
    /// An `Int` uninterpreted function.
    IntFunc(String, usize),
    /// A `Bool` constant.
    BoolConst(String),
}

/// One `check-sat` command: the assertions that were in scope when it ran.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Check {
    pub assertions: Vec<Formula>,
}

/// A parsed SMT-LIB problem: the declarations, the assertion scopes, and the
/// `check-sat` commands.
///
/// Scopes model `push`/`pop`: scope 0 is the top level, and each `push` adds
/// one. A `check-sat` snapshots the assertions in scope, so the same file can
/// ask several questions with different assertion sets and a `pop` cannot
/// change an answer that was already given.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct SmtProblem {
    pub logic: Option<String>,
    pub decls: Vec<Decl>,
    pub scopes: Vec<Vec<Formula>>,
    pub checks: Vec<Check>,
}

impl SmtProblem {
    /// The assertions of every check, in order. A file with no `check-sat`
    /// has one implicit check over everything that was asserted.
    pub fn check_assertions(&self) -> Vec<Vec<Formula>> {
        if self.checks.is_empty() {
            vec![self.scopes.iter().flat_map(|s| s.iter().cloned()).collect()]
        } else {
            self.checks.iter().map(|c| c.assertions.clone()).collect()
        }
    }
}

// ---------------------------------------------------------------------------
// Command parsing
// ---------------------------------------------------------------------------

struct Ctx {
    decls: Vec<Decl>,
    int_consts: Vec<String>,
    int_funcs: Vec<(String, usize)>,
    bool_consts: Vec<String>,
}

impl Ctx {
    fn new() -> Self {
        Ctx {
            decls: Vec::new(),
            int_consts: Vec::new(),
            int_funcs: Vec::new(),
            bool_consts: Vec::new(),
        }
    }

    fn declare_int_const(&mut self, name: &str) -> Result<()> {
        if self.int_consts.iter().any(|n| n == name)
            || self.int_funcs.iter().any(|(n, _)| n == name)
            || self.bool_consts.iter().any(|n| n == name)
        {
            return parse_err(0, format!("symbol {name} is declared twice"));
        }
        self.int_consts.push(name.to_string());
        self.decls.push(Decl::IntConst(name.to_string()));
        Ok(())
    }

    fn declare_int_func(&mut self, name: &str, arity: usize) -> Result<()> {
        if self.int_consts.iter().any(|n| n == name)
            || self.int_funcs.iter().any(|(n, _)| n == name)
            || self.bool_consts.iter().any(|n| n == name)
        {
            return parse_err(0, format!("symbol {name} is declared twice"));
        }
        self.int_funcs.push((name.to_string(), arity));
        self.decls.push(Decl::IntFunc(name.to_string(), arity));
        Ok(())
    }

    fn declare_bool_const(&mut self, name: &str) -> Result<()> {
        if self.int_consts.iter().any(|n| n == name)
            || self.int_funcs.iter().any(|(n, _)| n == name)
            || self.bool_consts.iter().any(|n| n == name)
        {
            return parse_err(0, format!("symbol {name} is declared twice"));
        }
        self.bool_consts.push(name.to_string());
        self.decls.push(Decl::BoolConst(name.to_string()));
        Ok(())
    }
}

fn atom_text(expr: &SExpr) -> Option<&str> {
    match expr {
        SExpr::Atom(name, _) => Some(name.as_str()),
        _ => None,
    }
}

/// Parse one SMT-LIB source file into a problem.
///
/// `check-sat` is optional; the answer always describes the conjunction of all
/// assertions. `push`/`pop` scopes and several `check-sat` commands are
/// supported: each check is answered independently, and no learnt clause or
/// theory state is reused between them.
pub fn parse_problem(source: &str) -> Result<SmtProblem> {
    let exprs = read_all(source)?;
    let mut ctx = Ctx::new();
    let mut problem = SmtProblem {
        scopes: vec![Vec::new()],
        ..SmtProblem::default()
    };
    let mut check_count = 0usize;
    for expr in &exprs {
        let offset = expr.offset();
        let SExpr::List(items, _) = expr else {
            return parse_err(offset, "expected a command");
        };
        let Some(head) = expr.head() else {
            return parse_err(offset, "expected a command name");
        };
        match head {
            "set-logic" => {
                if items.len() != 2 {
                    return parse_err(offset, "set-logic takes one argument");
                }
                let name = atom_text(&items[1]).unwrap_or_default();
                match name {
                    "QF_UF" | "QF_IDL" | "QF_UFLIA" | "QF_UFIDL" | "ALL" => {}
                    other => return unsupported(offset, format!("logic {other} is not supported")),
                }
                problem.logic = Some(name.to_string());
            }
            "set-info" | "set-option" => {}
            "declare-fun" => {
                if items.len() != 4 {
                    return parse_err(offset, "declare-fun takes a name, arguments and a sort");
                }
                let name = atom_text(&items[1]).unwrap_or_default().to_string();
                let SExpr::List(args, _) = &items[2] else {
                    return parse_err(offset, "declare-fun arguments must be a list");
                };
                let arity = args.len();
                let sort = atom_text(&items[3]).unwrap_or_default();
                match sort {
                    "Int" => {
                        if arity == 0 {
                            ctx.declare_int_const(&name)?;
                        } else {
                            ctx.declare_int_func(&name, arity)?;
                        }
                    }
                    "Bool" => {
                        if arity != 0 {
                            return unsupported(offset, "Boolean functions are not supported");
                        }
                        ctx.declare_bool_const(&name)?;
                    }
                    other => return unsupported(offset, format!("sort {other} is not supported")),
                }
            }
            "declare-const" => {
                if items.len() != 3 {
                    return parse_err(offset, "declare-const takes a name and a sort");
                }
                let name = atom_text(&items[1]).unwrap_or_default().to_string();
                match atom_text(&items[2]).unwrap_or_default() {
                    "Int" => ctx.declare_int_const(&name)?,
                    "Bool" => ctx.declare_bool_const(&name)?,
                    other => return unsupported(offset, format!("sort {other} is not supported")),
                }
            }
            "assert" => {
                if items.len() != 2 {
                    return parse_err(offset, "assert takes one formula");
                }
                let formula = parse_formula(&items[1], &ctx)?;
                if let Some(scope) = problem.scopes.last_mut() {
                    scope.push(formula);
                }
            }
            "check-sat" => {
                if items.len() != 1 {
                    return parse_err(offset, "check-sat takes no arguments");
                }
                check_count += 1;
                let assertions = problem
                    .scopes
                    .iter()
                    .flat_map(|scope| scope.iter().cloned())
                    .collect();
                problem.checks.push(Check { assertions });
            }
            "get-model" | "get-value" | "get-info" | "exit" => {}
            "push" => {
                let count = scope_count(&items[1..], offset)?;
                for _ in 0..count {
                    problem.scopes.push(Vec::new());
                }
            }
            "pop" => {
                let count = scope_count(&items[1..], offset)?;
                for _ in 0..count {
                    if problem.scopes.len() <= 1 {
                        return parse_err(offset, "pop would remove the top-level scope");
                    }
                    problem.scopes.pop();
                }
            }
            other => return unsupported(offset, format!("command {other} is not supported")),
        }
    }
    let _ = check_count;
    problem.decls = ctx.decls.clone();
    Ok(problem)
}

// ---------------------------------------------------------------------------
// Formulas
// ---------------------------------------------------------------------------

fn parse_formula(expr: &SExpr, ctx: &Ctx) -> Result<Formula> {
    let offset = expr.offset();
    match expr {
        SExpr::Atom(name, _) => match name.as_str() {
            "true" => Ok(Formula::Bool(true)),
            "false" => Ok(Formula::Bool(false)),
            other => {
                if ctx.bool_consts.iter().any(|n| n == other) {
                    Ok(Formula::Prop(other.to_string()))
                } else {
                    parse_err(offset, format!("unknown symbol {other}"))
                }
            }
        },
        SExpr::List(items, _) => {
            let Some(head) = expr.head() else {
                return parse_err(offset, "expected a formula");
            };
            match head {
                "not" => {
                    if items.len() != 2 {
                        return parse_err(offset, "not takes one argument");
                    }
                    Ok(Formula::Not(Box::new(parse_formula(&items[1], ctx)?)))
                }
                "and" | "or" => {
                    if items.len() < 2 {
                        return parse_err(offset, format!("{head} needs at least one argument"));
                    }
                    let mut parts = Vec::new();
                    for item in &items[1..] {
                        parts.push(parse_formula(item, ctx)?);
                    }
                    if head == "and" {
                        Ok(Formula::And(parts))
                    } else {
                        Ok(Formula::Or(parts))
                    }
                }
                "xor" => {
                    if items.len() != 3 {
                        return parse_err(offset, "xor takes two arguments");
                    }
                    Ok(Formula::Xor(
                        Box::new(parse_formula(&items[1], ctx)?),
                        Box::new(parse_formula(&items[2], ctx)?),
                    ))
                }
                "=>" => {
                    if items.len() < 3 {
                        return parse_err(offset, "=> takes at least two arguments");
                    }
                    let mut parts = Vec::new();
                    for item in &items[1..] {
                        parts.push(parse_formula(item, ctx)?);
                    }
                    // `=>` is right-associative.
                    let mut iter = parts.into_iter().rev();
                    let mut acc = iter.next().expect("at least one part");
                    for part in iter {
                        acc = Formula::Implies(Box::new(part), Box::new(acc));
                    }
                    Ok(acc)
                }
                "ite" => {
                    if items.len() != 4 {
                        return parse_err(offset, "ite takes three arguments");
                    }
                    Ok(Formula::Ite(
                        Box::new(parse_formula(&items[1], ctx)?),
                        Box::new(parse_formula(&items[2], ctx)?),
                        Box::new(parse_formula(&items[3], ctx)?),
                    ))
                }
                "=" | "distinct" => {
                    if items.len() < 3 {
                        return parse_err(offset, format!("{head} needs at least two arguments"));
                    }
                    let mut terms = Vec::new();
                    for item in &items[1..] {
                        terms.push(parse_int_term(item, ctx)?);
                    }
                    let formulas = if head == "=" {
                        equalities(&terms, offset)?
                    } else {
                        disequalities(&terms, offset)?
                    };
                    Ok(conjoin(formulas))
                }
                "<" | "<=" | ">" | ">=" => {
                    if items.len() != 3 {
                        return parse_err(offset, format!("{head} takes two arguments"));
                    }
                    let lhs = parse_int_term(&items[1], ctx)?;
                    let rhs = parse_int_term(&items[2], ctx)?;
                    compare(head, &lhs, &rhs, offset)
                }
                other => parse_err(offset, format!("unknown operator {other}")),
            }
        }
    }
}

/// The optional count of a `push`/`pop` command (default 1).
fn scope_count(items: &[SExpr], offset: usize) -> Result<usize> {
    match items.len() {
        0 => Ok(1),
        1 => {
            let text = atom_text(&items[0]).unwrap_or_default();
            let n: usize = match text.parse() {
                Ok(n) => n,
                Err(_) => return parse_err(offset, format!("scope count {text} is not a number")),
            };
            if n == 0 {
                return parse_err(offset, "scope count must be at least 1");
            }
            Ok(n)
        }
        _ => parse_err(offset, "push/pop takes at most one argument"),
    }
}

fn conjoin(mut parts: Vec<Formula>) -> Formula {
    if parts.is_empty() {
        Formula::Bool(true)
    } else if parts.len() == 1 {
        parts.remove(0)
    } else {
        Formula::And(parts)
    }
}

// ---------------------------------------------------------------------------
// Integer terms
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
enum IntTerm {
    Num(i64),
    Symbol(String),
    App(String, Vec<IntTerm>),
    Add(Vec<IntTerm>),
    Sub(Box<IntTerm>, Box<IntTerm>),
    Neg(Box<IntTerm>),
    Mul(Box<IntTerm>, Box<IntTerm>),
}

fn parse_int_term(expr: &SExpr, ctx: &Ctx) -> Result<IntTerm> {
    let offset = expr.offset();
    match expr {
        SExpr::Atom(name, _) => {
            if let Ok(k) = name.parse::<i64>() {
                return Ok(IntTerm::Num(k));
            }
            if ctx.int_consts.iter().any(|n| n == name) {
                return Ok(IntTerm::Symbol(name.clone()));
            }
            parse_err(offset, format!("unknown integer symbol {name}"))
        }
        SExpr::List(items, _) => {
            let Some(head) = expr.head() else {
                return parse_err(offset, "expected a term");
            };
            match head {
                "+" => {
                    if items.len() < 2 {
                        return parse_err(offset, "+ needs at least one argument");
                    }
                    let mut parts = Vec::new();
                    for item in &items[1..] {
                        parts.push(parse_int_term(item, ctx)?);
                    }
                    Ok(IntTerm::Add(parts))
                }
                "-" => {
                    if items.len() == 2 {
                        return Ok(IntTerm::Neg(Box::new(parse_int_term(&items[1], ctx)?)));
                    }
                    if items.len() == 3 {
                        return Ok(IntTerm::Sub(
                            Box::new(parse_int_term(&items[1], ctx)?),
                            Box::new(parse_int_term(&items[2], ctx)?),
                        ));
                    }
                    parse_err(offset, "- takes one or two arguments")
                }
                "*" => {
                    if items.len() != 3 {
                        return parse_err(offset, "* takes two arguments");
                    }
                    Ok(IntTerm::Mul(
                        Box::new(parse_int_term(&items[1], ctx)?),
                        Box::new(parse_int_term(&items[2], ctx)?),
                    ))
                }
                other => {
                    let arity = items.len() - 1;
                    let expected = ctx
                        .int_funcs
                        .iter()
                        .find(|(n, _)| n == other)
                        .map(|(_, a)| *a);
                    match expected {
                        Some(a) if a == arity => {
                            let mut args = Vec::new();
                            for item in &items[1..] {
                                args.push(parse_int_term(item, ctx)?);
                            }
                            Ok(IntTerm::App(other.to_string(), args))
                        }
                        Some(a) => parse_err(
                            offset,
                            format!(
                                "function {other} is declared with arity {a}, used with {arity}"
                            ),
                        ),
                        None => {
                            if ctx.int_consts.iter().any(|n| n == other) {
                                parse_err(offset, format!("constant {other} cannot be applied"))
                            } else {
                                parse_err(offset, format!("unknown function {other}"))
                            }
                        }
                    }
                }
            }
        }
    }
}

/// A linear expression: distinct terms with coefficient `+1` or `-1`, plus an
/// integer offset.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Linear {
    terms: Vec<(BaseTerm, i64)>,
    offset: i64,
}

impl Linear {
    fn constant(offset: i64) -> Self {
        Linear {
            terms: Vec::new(),
            offset,
        }
    }

    fn negated(&self) -> Self {
        Linear {
            terms: self.terms.iter().map(|(t, c)| (t.clone(), -c)).collect(),
            offset: -self.offset,
        }
    }

    fn add(&self, other: &Linear) -> Result<Linear> {
        let mut terms = self.terms.clone();
        for (term, coeff) in &other.terms {
            match terms.iter_mut().find(|(t, _)| t == term) {
                Some((_, c)) => *c += coeff,
                None => terms.push((term.clone(), *coeff)),
            }
        }
        let offset = self.offset + other.offset;
        Linear::from_terms(terms, offset)
    }

    fn sub(&self, other: &Linear) -> Result<Linear> {
        self.add(&other.negated())
    }

    fn from_terms(mut terms: Vec<(BaseTerm, i64)>, offset: i64) -> Result<Linear> {
        terms.retain(|(_, c)| *c != 0);
        for (_, coeff) in &terms {
            if *coeff != 1 && *coeff != -1 {
                return unsupported(
                    0,
                    format!("coefficient {coeff} is outside difference logic"),
                );
            }
        }
        Ok(Linear { terms, offset })
    }
}

fn linear(term: &IntTerm, offset: usize) -> Result<Linear> {
    match term {
        IntTerm::Num(k) => Ok(Linear::constant(*k)),
        IntTerm::Symbol(name) => Ok(Linear {
            terms: vec![(BaseTerm::Var(name.clone()), 1)],
            offset: 0,
        }),
        IntTerm::App(name, args) => {
            let mut base_args = Vec::new();
            for arg in args {
                base_args.push(base_arg(arg)?);
            }
            Ok(Linear {
                terms: vec![(BaseTerm::App(name.clone(), base_args), 1)],
                offset: 0,
            })
        }
        IntTerm::Add(parts) => {
            let mut acc = Linear::constant(0);
            for part in parts {
                acc = acc.add(&linear(part, offset)?)?;
            }
            Ok(acc)
        }
        IntTerm::Sub(a, b) => linear(a, offset)?.sub(&linear(b, offset)?),
        IntTerm::Neg(a) => Ok(linear(a, offset)?.negated()),
        IntTerm::Mul(a, b) => {
            let la = linear(a, offset)?;
            let lb = linear(b, offset)?;
            match (la.terms.is_empty(), lb.terms.is_empty()) {
                (true, true) => Ok(Linear::constant(la.offset * lb.offset)),
                (false, true) => {
                    let k = lb.offset;
                    match k {
                        1 => Ok(la),
                        -1 => Ok(la.negated()),
                        other => unsupported(
                            offset,
                            format!("coefficient {other} is outside difference logic"),
                        ),
                    }
                }
                (true, false) => {
                    let k = la.offset;
                    match k {
                        1 => Ok(lb),
                        -1 => Ok(lb.negated()),
                        other => unsupported(
                            offset,
                            format!("coefficient {other} is outside difference logic"),
                        ),
                    }
                }
                (false, false) => unsupported(offset, "product of two terms is not supported"),
            }
        }
    }
}

/// The pure term of an argument position: a constant or an application.
fn base_arg(term: &IntTerm) -> Result<BaseTerm> {
    match term {
        IntTerm::Num(k) => unsupported(
            0,
            format!("numeral {k} cannot be a function argument in this fragment"),
        ),
        IntTerm::Symbol(name) => Ok(BaseTerm::Var(name.clone())),
        IntTerm::App(name, args) => {
            let mut base_args = Vec::new();
            for arg in args {
                base_args.push(base_arg(arg)?);
            }
            Ok(BaseTerm::App(name.clone(), base_args))
        }
        _ => unsupported(0, "arithmetic inside a function argument is not supported"),
    }
}

/// The difference `lhs - rhs` as a plus term, a minus term and an offset.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Difference {
    plus: Option<BaseTerm>,
    minus: Option<BaseTerm>,
    offset: i64,
}

fn difference(lhs: &Linear, rhs: &Linear) -> Result<Difference> {
    let diff = lhs.sub(rhs)?;
    let mut plus = None;
    let mut minus = None;
    for (term, coeff) in &diff.terms {
        match coeff {
            1 => {
                if plus.is_some() {
                    return unsupported(
                        0,
                        "more than one positive term is outside difference logic",
                    );
                }
                plus = Some(term.clone());
            }
            _ => {
                if minus.is_some() {
                    return unsupported(
                        0,
                        "more than one negative term is outside difference logic",
                    );
                }
                minus = Some(term.clone());
            }
        }
    }
    Ok(Difference {
        plus,
        minus,
        offset: diff.offset,
    })
}

fn origin_or(term: Option<BaseTerm>) -> BaseTerm {
    term.unwrap_or(BaseTerm::Origin)
}

fn rdl(diff: &Difference, c: i64) -> Atom {
    Atom::Rdl {
        x: origin_or(diff.plus.clone()),
        y: origin_or(diff.minus.clone()),
        c,
    }
}

fn compare(op: &str, lhs: &IntTerm, rhs: &IntTerm, offset: usize) -> Result<Formula> {
    let la = linear(lhs, offset)?;
    let lb = linear(rhs, offset)?;
    let diff = difference(&la, &lb)?;
    if diff.plus.is_none() && diff.minus.is_none() {
        // A constant comparison: decide it directly.
        let value = diff.offset;
        let holds = match op {
            "<" => value < 0,
            "<=" => value <= 0,
            ">" => value > 0,
            ">=" => value >= 0,
            _ => unreachable!("operator checked by the caller"),
        };
        return Ok(Formula::Bool(holds));
    }
    let formula = match op {
        "<=" => Formula::Atom(rdl(&diff, -diff.offset)),
        "<" => Formula::Atom(rdl(&diff, -diff.offset - 1)),
        ">=" => Formula::Atom(rdl(
            &Difference {
                plus: diff.minus.clone(),
                minus: diff.plus.clone(),
                offset: diff.offset,
            },
            diff.offset,
        )),
        ">" => Formula::Atom(rdl(
            &Difference {
                plus: diff.minus.clone(),
                minus: diff.plus.clone(),
                offset: diff.offset,
            },
            diff.offset - 1,
        )),
        _ => unreachable!("operator checked by the caller"),
    };
    Ok(formula)
}

/// `a = b` for one pair of terms.
fn equality(lhs: &IntTerm, rhs: &IntTerm, offset: usize) -> Result<Formula> {
    let la = linear(lhs, offset)?;
    let lb = linear(rhs, offset)?;
    let diff = difference(&la, &lb)?;
    if diff.plus.is_none() && diff.minus.is_none() {
        return Ok(Formula::Bool(diff.offset == 0));
    }
    if diff.offset == 0 {
        if let (Some(plus), Some(minus)) = (&diff.plus, &diff.minus) {
            return Ok(Formula::Atom(Atom::Eq(plus.clone(), minus.clone())));
        }
    }
    // `plus - minus = -offset`, written as the two bounds that pin it:
    // `plus - minus <= -offset` and `minus - plus <= offset`.
    let forward = rdl(&diff, -diff.offset);
    let backward = rdl(
        &Difference {
            plus: diff.minus.clone(),
            minus: diff.plus.clone(),
            offset: diff.offset,
        },
        diff.offset,
    );
    Ok(Formula::And(vec![
        Formula::Atom(forward),
        Formula::Atom(backward),
    ]))
}

/// `a != b` for one pair of terms.
fn disequality(lhs: &IntTerm, rhs: &IntTerm, offset: usize) -> Result<Formula> {
    let la = linear(lhs, offset)?;
    let lb = linear(rhs, offset)?;
    let diff = difference(&la, &lb)?;
    if diff.plus.is_none() && diff.minus.is_none() {
        return Ok(Formula::Bool(diff.offset != 0));
    }
    if diff.offset == 0 {
        if let (Some(plus), Some(minus)) = (&diff.plus, &diff.minus) {
            return Ok(Formula::Atom(Atom::Neq(plus.clone(), minus.clone())));
        }
    }
    let forward = rdl(&diff, -diff.offset);
    let backward = rdl(
        &Difference {
            plus: diff.minus.clone(),
            minus: diff.plus.clone(),
            offset: diff.offset,
        },
        diff.offset - 1,
    );
    Ok(Formula::Or(vec![
        Formula::Atom(backward),
        Formula::Atom(forward),
    ]))
}

fn equalities(terms: &[IntTerm], offset: usize) -> Result<Vec<Formula>> {
    let mut out = Vec::new();
    for pair in terms.windows(2) {
        out.push(equality(&pair[0], &pair[1], offset)?);
    }
    Ok(out)
}

fn disequalities(terms: &[IntTerm], offset: usize) -> Result<Vec<Formula>> {
    let mut out = Vec::new();
    for i in 0..terms.len() {
        for j in (i + 1)..terms.len() {
            out.push(disequality(&terms[i], &terms[j], offset)?);
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn formula(src: &str) -> Formula {
        let source =
            format!("(declare-fun x () Int) (declare-fun y () Int) (assert {src}) (check-sat)");
        let problem = parse_problem(&source).unwrap();
        problem
            .check_assertions()
            .into_iter()
            .next()
            .expect("one check")
            .into_iter()
            .next()
            .expect("one assertion")
    }

    #[test]
    fn parses_a_difference_constraint() {
        let f = formula("(<= (- y x) 3)");
        match f {
            Formula::Atom(Atom::Rdl { x, y, c }) => {
                assert_eq!(x, BaseTerm::Var("y".into()));
                assert_eq!(y, BaseTerm::Var("x".into()));
                assert_eq!(c, 3);
            }
            other => panic!("unexpected {other:?}"),
        }
    }

    #[test]
    fn a_bare_numeral_uses_the_origin() {
        let f = formula("(<= x 3)");
        match f {
            Formula::Atom(Atom::Rdl { x, y, c }) => {
                assert_eq!(x, BaseTerm::Var("x".into()));
                assert_eq!(y, BaseTerm::Origin);
                assert_eq!(c, 3);
            }
            other => panic!("unexpected {other:?}"),
        }
    }

    #[test]
    fn equality_with_equal_offsets_is_one_atom() {
        let f = formula("(= x y)");
        assert_eq!(
            f,
            Formula::Atom(Atom::Eq(
                BaseTerm::Var("x".into()),
                BaseTerm::Var("y".into())
            ))
        );
    }

    #[test]
    fn equality_with_offsets_is_two_constraints() {
        let f = formula("(= x (+ y 1))");
        match f {
            Formula::And(parts) => assert_eq!(parts.len(), 2),
            other => panic!("unexpected {other:?}"),
        }
    }

    #[test]
    fn a_coefficient_of_two_is_rejected() {
        let err = parse_problem("(declare-fun x () Int) (assert (<= (* 2 x) 3))").unwrap_err();
        assert!(matches!(err, SmtError::Unsupported { .. }), "{err}");
    }

    #[test]
    fn push_and_pop_open_and_close_scopes() {
        let p = parse_problem(
            "(declare-fun x () Int) (assert (<= x 2)) (push 1) (assert (>= x 5)) \
             (check-sat) (pop 1) (check-sat)",
        )
        .unwrap();
        assert_eq!(p.scopes.len(), 1, "the pushed scope is closed again");
        let checks = p.check_assertions();
        assert_eq!(checks.len(), 2);
        assert_eq!(
            checks[0].len(),
            2,
            "the check inside the pushed scope sees both"
        );
        assert_eq!(
            checks[1].len(),
            1,
            "the check after the pop sees the base scope only"
        );
    }

    #[test]
    fn unknown_symbols_are_errors() {
        let err = parse_problem("(assert (= x y))").unwrap_err();
        assert!(matches!(err, SmtError::Parse { .. }), "{err}");
    }

    #[test]
    fn constant_comparisons_fold() {
        assert_eq!(formula("(< 1 2)"), Formula::Bool(true));
        assert_eq!(formula("(<= 2 1)"), Formula::Bool(false));
    }
}
