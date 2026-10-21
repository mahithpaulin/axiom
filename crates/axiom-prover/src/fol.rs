//! First-order syntax for the Axiom prover.
//!
//! The fragment is deliberately small and explicit:
//!
//! * `axiom <formula>.` and `goal <formula>.` (one goal required);
//! * `pred p/2.`, `fun f/1.`, `const a.` declarations are optional;
//! * `true`, `false`, `not`/`~`/`!`, `and`/`&`, `or`/`|`, `->`, `<->`;
//! * `forall x, y. ...` and `exists x. ...`;
//! * predicate/function symbols with fixed arities; no equality, sorts,
//!   arithmetic, or higher-order constructs.
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

impl Formula {
    fn from_binary(op: BinOp, left: Formula, right: Formula) -> Self {
        match op {
            BinOp::And => Formula::And(vec![left, right]),
            BinOp::Or => Formula::Or(vec![left, right]),
            BinOp::Implies => Formula::Implies(Box::new(left), Box::new(right)),
            BinOp::Iff => Formula::Iff(Box::new(left), Box::new(right)),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BinOp {
    And,
    Or,
    Implies,
    Iff,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    pub predicates: BTreeMap<String, usize>,
    pub functions: BTreeMap<String, usize>,
    pub constants: BTreeSet<String>,
}

impl Signature {
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
                    format!(
                    "unexpected character {c:?} (equality and arithmetic are not in this fragment)"
                ),
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
            left = Formula::from_binary(BinOp::Iff, left, right);
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
            Some(Tok::Word(name)) => self.atom_after_name(name, bound),
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
    fn equality_is_rejected_explicitly() {
        let e = parse_problem("axiom a = b. goal P(a).").unwrap_err();
        assert!(format!("{e}").contains("equality"));
    }
}
