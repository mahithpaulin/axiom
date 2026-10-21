//! A deliberately small ASP surface language.
//!
//! Supported forms:
//!
//! ```text
//! p(a).
//! q(X) :- p(X), not r(X).
//! { s(X); t(X) } :- p(X).
//! :- p(X), not q(X).
//! #show s/1.
//! ```
//!
//! There are no aggregates, function symbols, cardinality bounds, or `#minimize`
//! directives. The parser rejects them rather than pretending to support them.

use std::collections::BTreeSet;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Term {
    Var(String),
    Const(String),
}

impl Term {
    pub fn is_var(&self) -> bool {
        matches!(self, Term::Var(_))
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(v) => f.write_str(v),
            Term::Const(c) => f.write_str(c),
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

    pub fn variables(&self) -> BTreeSet<String> {
        let mut out = BTreeSet::new();
        for a in &self.args {
            if let Term::Var(v) = a {
                out.insert(v.clone());
            }
        }
        out
    }

    pub fn is_ground(&self) -> bool {
        self.args.iter().all(|a| matches!(a, Term::Const(_)))
    }
}

impl fmt::Display for Atom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.args.is_empty() {
            return f.write_str(&self.predicate);
        }
        write!(f, "{}(", self.predicate)?;
        for (i, a) in self.args.iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{a}")?;
        }
        f.write_str(")")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Literal {
    pub negated: bool,
    pub atom: Atom,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rule {
    pub head: Atom,
    pub body: Vec<Literal>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Choice {
    pub heads: Vec<Atom>,
    pub body: Vec<Literal>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Statement {
    Fact(Atom),
    Rule(Rule),
    Choice(Choice),
    Constraint(Vec<Literal>),
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Program {
    pub statements: Vec<Statement>,
    pub shown: Vec<(String, usize)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub offset: usize,
    pub message: String,
}

impl ParseError {
    fn new(offset: usize, message: impl Into<String>) -> Self {
        ParseError {
            offset,
            message: message.into(),
        }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ASP parse error at {}: {}", self.offset, self.message)
    }
}

impl std::error::Error for ParseError {}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Word(String),
    Number(String),
    LParen,
    RParen,
    Comma,
    Dot,
    ColonDash,
    Semi,
    LBrace,
    RBrace,
    Slash,
    Show,
}

fn tokenize(src: &str) -> Result<Vec<(usize, Tok)>, ParseError> {
    let chars: Vec<char> = src.chars().collect();
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c == '%' {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
            continue;
        }
        match c {
            '(' => {
                out.push((i, Tok::LParen));
                i += 1;
            }
            ')' => {
                out.push((i, Tok::RParen));
                i += 1;
            }
            ',' => {
                out.push((i, Tok::Comma));
                i += 1;
            }
            '.' => {
                out.push((i, Tok::Dot));
                i += 1;
            }
            ';' => {
                out.push((i, Tok::Semi));
                i += 1;
            }
            '{' => {
                out.push((i, Tok::LBrace));
                i += 1;
            }
            '}' => {
                out.push((i, Tok::RBrace));
                i += 1;
            }
            '/' => {
                out.push((i, Tok::Slash));
                i += 1;
            }
            ':' if i + 1 < chars.len() && chars[i + 1] == '-' => {
                out.push((i, Tok::ColonDash));
                i += 2;
            }
            '#' => {
                let start = i;
                i += 1;
                let wstart = i;
                while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                    i += 1;
                }
                let word: String = chars[wstart..i].iter().collect();
                if word == "show" {
                    out.push((start, Tok::Show));
                } else {
                    return Err(ParseError::new(
                        start,
                        format!("unsupported directive #{word}"),
                    ));
                }
            }
            c if c.is_ascii_digit() => {
                let start = i;
                while i < chars.len() && chars[i].is_ascii_digit() {
                    i += 1;
                }
                out.push((start, Tok::Number(chars[start..i].iter().collect())));
            }
            c if c.is_ascii_alphabetic() || c == '_' => {
                let start = i;
                while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                    i += 1;
                }
                out.push((start, Tok::Word(chars[start..i].iter().collect())));
            }
            other => {
                return Err(ParseError::new(
                    i,
                    format!("unexpected character {other:?}"),
                ));
            }
        }
    }
    Ok(out)
}

struct Parser {
    toks: Vec<(usize, Tok)>,
    pos: usize,
    anon: u32,
}

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|(_, t)| t)
    }

    fn offset(&self) -> usize {
        self.toks
            .get(self.pos)
            .map(|(o, _)| *o)
            .unwrap_or_else(|| self.toks.last().map(|(o, _)| *o).unwrap_or(0))
    }

    fn bump(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos)?.1.clone();
        self.pos += 1;
        Some(t)
    }

    fn expect(&mut self, expected: Tok) -> Result<(), ParseError> {
        match self.bump() {
            Some(t) if t == expected => Ok(()),
            Some(t) => Err(ParseError::new(
                self.offset(),
                format!("expected {expected:?}, found {t:?}"),
            )),
            None => Err(ParseError::new(self.offset(), "unexpected end of input")),
        }
    }

    fn atom(&mut self) -> Result<Atom, ParseError> {
        let name = match self.bump() {
            Some(Tok::Word(w)) => w,
            other => {
                return Err(ParseError::new(
                    self.offset(),
                    format!("expected predicate name, found {other:?}"),
                ))
            }
        };
        let mut args = Vec::new();
        if self.peek() == Some(&Tok::LParen) {
            self.bump();
            if self.peek() == Some(&Tok::RParen) {
                self.bump();
            } else {
                loop {
                    args.push(self.term()?);
                    match self.bump() {
                        Some(Tok::Comma) => {}
                        Some(Tok::RParen) => break,
                        other => {
                            return Err(ParseError::new(
                                self.offset(),
                                format!("expected ',' or ')', found {other:?}"),
                            ))
                        }
                    }
                }
            }
        }
        Ok(Atom::new(name, args))
    }

    fn term(&mut self) -> Result<Term, ParseError> {
        match self.bump() {
            Some(Tok::Word(w)) => {
                let first = w.chars().next().unwrap_or('_');
                if first.is_ascii_uppercase() {
                    Ok(Term::Var(w))
                } else if w == "_" {
                    let name = format!("_anon{}", self.anon);
                    self.anon += 1;
                    Ok(Term::Var(name))
                } else {
                    Ok(Term::Const(w))
                }
            }
            Some(Tok::Number(n)) => Ok(Term::Const(n)),
            other => Err(ParseError::new(
                self.offset(),
                format!("expected term, found {other:?}"),
            )),
        }
    }

    fn body(&mut self) -> Result<Vec<Literal>, ParseError> {
        let mut body = Vec::new();
        if self.peek() == Some(&Tok::Dot) {
            return Ok(body);
        }
        loop {
            let negated = if self.peek() == Some(&Tok::Word("not".into())) {
                self.bump();
                true
            } else {
                false
            };
            let atom = self.atom()?;
            body.push(Literal { negated, atom });
            match self.bump() {
                Some(Tok::Comma) => {}
                Some(Tok::Dot) => break,
                other => {
                    return Err(ParseError::new(
                        self.offset(),
                        format!("expected ',' or '.', found {other:?}"),
                    ))
                }
            }
        }
        Ok(body)
    }

    fn statement(&mut self) -> Result<Statement, ParseError> {
        match self.peek() {
            Some(Tok::ColonDash) => {
                self.bump();
                let body = self.body()?;
                let stmt = Statement::Constraint(body);
                check_safety(&stmt)?;
                return Ok(stmt);
            }
            Some(Tok::LBrace) => {
                self.bump();
                let mut heads = Vec::new();
                loop {
                    heads.push(self.atom()?);
                    match self.bump() {
                        Some(Tok::Semi) => {}
                        Some(Tok::RBrace) => break,
                        other => {
                            return Err(ParseError::new(
                                self.offset(),
                                format!("expected ';' or '}}', found {other:?}"),
                            ))
                        }
                    }
                }
                let body = if self.peek() == Some(&Tok::ColonDash) {
                    self.bump();
                    self.body()?
                } else {
                    self.expect(Tok::Dot)?;
                    Vec::new()
                };
                let stmt = Statement::Choice(Choice { heads, body });
                check_safety(&stmt)?;
                return Ok(stmt);
            }
            Some(Tok::Show) => {
                self.bump();
                let name = match self.bump() {
                    Some(Tok::Word(w)) => w,
                    other => {
                        return Err(ParseError::new(
                            self.offset(),
                            format!("expected predicate after #show, found {other:?}"),
                        ))
                    }
                };
                let arity: usize = match self.bump() {
                    Some(Tok::Slash) => match self.bump() {
                        Some(Tok::Number(n)) => n
                            .parse::<usize>()
                            .map_err(|_| ParseError::new(self.offset(), "invalid #show arity"))?,
                        other => {
                            return Err(ParseError::new(
                                self.offset(),
                                format!("expected arity after '/', found {other:?}"),
                            ))
                        }
                    },
                    Some(Tok::Dot) => {
                        // `#show p.` is accepted as arity 0.
                        return Ok(Statement::Fact(Atom::new(format!("#shown:{name}"), vec![])));
                    }
                    other => {
                        return Err(ParseError::new(
                            self.offset(),
                            format!("expected '/' or '.', found {other:?}"),
                        ))
                    }
                };
                self.expect(Tok::Dot)?;
                // A synthetic statement is ugly. The caller filters it.
                Ok(Statement::Fact(Atom::new(
                    format!("#shown:{}", name),
                    vec![Term::Const(arity.to_string())],
                )))
            }
            None => Err(ParseError::new(self.offset(), "unexpected end of input")),
            _ => {
                let head = self.atom()?;
                if self.peek() == Some(&Tok::ColonDash) {
                    self.bump();
                    let body = self.body()?;
                    let stmt = Statement::Rule(Rule { head, body });
                    check_safety(&stmt)?;
                    Ok(stmt)
                } else {
                    self.expect(Tok::Dot)?;
                    if !head.is_ground() {
                        return Err(ParseError::new(self.offset(), "a fact must be ground"));
                    }
                    Ok(Statement::Fact(head))
                }
            }
        }
    }
}

fn check_safety(stmt: &Statement) -> Result<(), ParseError> {
    let (heads, body) = match stmt {
        Statement::Fact(a) => {
            if !a.is_ground() {
                return Err(ParseError::new(0, "a fact must be ground"));
            }
            return Ok(());
        }
        Statement::Rule(r) => (vec![&r.head], r.body.as_slice()),
        Statement::Choice(c) => (c.heads.iter().collect(), c.body.as_slice()),
        Statement::Constraint(b) => (Vec::new(), b.as_slice()),
    };
    let mut positive = BTreeSet::new();
    for l in body {
        if !l.negated {
            positive.extend(l.atom.variables());
        }
    }
    for h in heads {
        for v in h.variables() {
            if !positive.contains(&v) {
                return Err(ParseError::new(
                    0,
                    format!("unsafe rule: variable {v} in a head is not bound by a positive body literal"),
                ));
            }
        }
    }
    for l in body {
        if l.negated {
            for v in l.atom.variables() {
                if !positive.contains(&v) {
                    return Err(ParseError::new(
                        0,
                        format!("unsafe rule: variable {v} in a negative literal is not bound by a positive body literal"),
                    ));
                }
            }
        }
    }
    Ok(())
}

/// Parse an ASP program. `#show` directives are retained in `Program::shown`
/// and otherwise have no effect on grounding or semantics.
pub fn parse(src: &str) -> Result<Program, ParseError> {
    let toks = tokenize(src)?;
    let mut p = Parser {
        toks,
        pos: 0,
        anon: 0,
    };
    let mut program = Program::default();
    while p.pos < p.toks.len() {
        match p.peek() {
            Some(Tok::Show) => {
                // Reparse the directive without the synthetic-fact detour.
                p.bump();
                let name = match p.bump() {
                    Some(Tok::Word(w)) => w,
                    other => {
                        return Err(ParseError::new(
                            p.offset(),
                            format!("expected predicate after #show, found {other:?}"),
                        ))
                    }
                };
                let arity = match p.bump() {
                    Some(Tok::Slash) => match p.bump() {
                        Some(Tok::Number(n)) => n
                            .parse()
                            .map_err(|_| ParseError::new(p.offset(), "invalid #show arity"))?,
                        other => {
                            return Err(ParseError::new(
                                p.offset(),
                                format!("expected arity after '/', found {other:?}"),
                            ))
                        }
                    },
                    Some(Tok::Dot) => {
                        program.shown.push((name, 0));
                        continue;
                    }
                    other => {
                        return Err(ParseError::new(
                            p.offset(),
                            format!("expected '/' or '.', found {other:?}"),
                        ))
                    }
                };
                p.expect(Tok::Dot)?;
                program.shown.push((name, arity));
            }
            _ => {
                let stmt = p.statement()?;
                // `statement` also has a #show path for direct callers; skip the
                // synthetic fact if it ever appears.
                if let Statement::Fact(a) = &stmt {
                    if a.predicate.starts_with("#shown:") {
                        continue;
                    }
                }
                program.statements.push(stmt);
            }
        }
    }
    Ok(program)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_the_core_forms() {
        let p = parse(
            "p(a). q(X) :- p(X), not r(X). { s(X); t(X) } :- p(X). \
             :- s(X), not t(X). #show s/1.",
        )
        .unwrap();
        assert_eq!(p.statements.len(), 4);
        assert_eq!(p.shown, vec![("s".into(), 1)]);
    }

    #[test]
    fn rejects_unsafe_negation() {
        let e = parse("p(X) :- not q(X).").unwrap_err();
        assert!(e.message.contains("unsafe"));
    }

    #[test]
    fn rejects_unknown_directives_and_aggregates() {
        assert!(parse("#minimize{ X : p(X) }.").is_err());
        assert!(parse("p(1..3).").is_err());
    }

    #[test]
    fn anonymous_variables_are_distinct() {
        let p = parse("p(_,_).").unwrap_err();
        assert!(p.message.contains("ground"));
    }

    #[test]
    fn facts_must_be_ground() {
        assert!(parse("p(X).").is_err());
    }
}
