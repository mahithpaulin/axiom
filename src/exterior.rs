//! The logical exterior: text surface syntax and parsers.
//!
//! ## Scope
//!
//! The exterior is the *only* place allowed to know what a problem means. Today
//! it provides a Prolog-flavoured surface syntax for stratified Datalog:
//!
//! ```text
//! # comment
//! edge(a, b).
//! path(X, Y) :- edge(X, Y).
//! path(X, Z) :- path(X, Y), edge(Y, Z).
//! safe(X)   :- node(X), not blocked(X).
//! ?- path(a, c).
//! ```
//!
//! Each accepted program is *compiled*, not interpreted: identifiers become
//! interned symbol ids, terms become hash-consed arena nodes, variables become
//! rule-local slots, and the result is a `Program` the core can execute with no
//! further knowledge of the source language.
//!
//! ## Hostile input
//!
//! §21 requires the exterior to treat input as hostile, so the parser is
//! bounded on every axis that an attacker controls: token count, nesting depth,
//! term arity and program size. Every failure is a `ParseError` with a position;
//! nothing panics and nothing loops. `tests/malformed.rs` asserts that.

use crate::program::{Builder, Literal, Program, ProgramError};
use crate::term::{TermId, TermStore, T_FUN};

/// Hard limits. Exceeding any of them is a parse error, not a hang.
#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub max_tokens: usize,
    pub max_depth: usize,
    pub max_arity: usize,
    pub max_rules: usize,
}

impl Default for Limits {
    fn default() -> Self {
        // Generous for hand-written programs, far too small for an attack.
        Limits {
            max_tokens: 1 << 22,
            max_depth: 256,
            max_arity: 4096,
            max_rules: 1 << 20,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ParseError {
    pub line: u32,
    pub col: u32,
    pub message: String,
}

impl core::fmt::Display for ParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.col, self.message)
    }
}

impl std::error::Error for ParseError {}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Tok {
    Ident(String),
    Number(i64),
    LParen,
    RParen,
    Comma,
    Dot,
    ColonDash,
    QueryDash,
}

#[derive(Clone, Debug)]
struct Spanned {
    tok: Tok,
    line: u32,
    col: u32,
}

pub fn tokenize(src: &str, limits: &Limits) -> Result<Vec<Spanned>, ParseError> {
    let mut out = Vec::new();
    let b: Vec<char> = src.chars().collect();
    let (mut i, mut line, mut col) = (0usize, 1u32, 1u32);
    let err = |line: u32, col: u32, m: &str| ParseError {
        line,
        col,
        message: m.to_string(),
    };
    while i < b.len() {
        let c = b[i];
        match c {
            '\n' => {
                i += 1;
                line += 1;
                col = 1;
            }
            c if c.is_whitespace() => {
                i += 1;
                col += 1;
            }
            '#' => {
                while i < b.len() && b[i] != '\n' {
                    i += 1;
                }
            }
            '(' => {
                out.push(Spanned {
                    tok: Tok::LParen,
                    line,
                    col,
                });
                i += 1;
                col += 1;
            }
            ')' => {
                out.push(Spanned {
                    tok: Tok::RParen,
                    line,
                    col,
                });
                i += 1;
                col += 1;
            }
            ',' => {
                out.push(Spanned {
                    tok: Tok::Comma,
                    line,
                    col,
                });
                i += 1;
                col += 1;
            }
            '.' => {
                out.push(Spanned {
                    tok: Tok::Dot,
                    line,
                    col,
                });
                i += 1;
                col += 1;
            }
            ':' if i + 1 < b.len() && b[i + 1] == '-' => {
                out.push(Spanned {
                    tok: Tok::ColonDash,
                    line,
                    col,
                });
                i += 2;
                col += 2;
            }
            '?' if i + 1 < b.len() && b[i + 1] == '-' => {
                out.push(Spanned {
                    tok: Tok::QueryDash,
                    line,
                    col,
                });
                i += 2;
                col += 2;
            }
            _ => {
                let start = i;
                let start_col = col;
                while i < b.len()
                    && (b[i].is_alphanumeric() || b[i] == '_' || b[i] == '\'' || b[i] == '-')
                {
                    i += 1;
                    col += 1;
                }
                if i == start {
                    return Err(err(line, col, &format!("unexpected character '{c}'")));
                }
                let word: String = b[start..i].iter().collect();
                if let Ok(n) = word.parse::<i64>() {
                    out.push(Spanned {
                        tok: Tok::Number(n),
                        line,
                        col: start_col,
                    });
                } else {
                    // Case is *preserved*. Lowercasing collapses `X` into the
                    // constant `x`, silently turning every rule into a ground
                    // fact -- a soundness bug, not a style choice.
                    out.push(Spanned { tok: Tok::Ident(word), line, col: start_col });
                }
            }
        }
        if out.len() > limits.max_tokens {
            return Err(err(line, col, "token limit exceeded"));
        }
    }
    Ok(out)
}

/// A parsed program plus its queries.
pub struct Parsed {
    pub program: Program,
    pub queries: Vec<TermId>,
}

struct Parser<'a> {
    toks: &'a [Spanned],
    pos: usize,
    limits: Limits,
    b: Builder,
    queries: Vec<TermId>,
    rules: usize,
}

impl<'a> Parser<'a> {
    fn err<T>(&self, m: &str) -> Result<T, ParseError> {
        let (line, col) = match self.toks.get(self.pos) {
            Some(t) => (t.line, t.col),
            None => self.toks.last().map(|t| (t.line, t.col)).unwrap_or((1, 1)),
        };
        Err(ParseError {
            line,
            col,
            message: m.to_string(),
        })
    }

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|s| &s.tok)
    }

    fn eat(&mut self, t: &Tok) -> bool {
        if self.peek() == Some(t) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, t: &Tok, what: &str) -> Result<(), ParseError> {
        if self.eat(t) {
            Ok(())
        } else {
            self.err(&format!("expected {what}"))
        }
    }

    fn ident(&mut self) -> Result<String, ParseError> {
        match self.toks.get(self.pos).map(|s| s.tok.clone()) {
            Some(Tok::Ident(s)) => {
                self.pos += 1;
                Ok(s)
            }
            _ => self.err("expected an identifier"),
        }
    }

    /// A term: an identifier, an integer, or a compound `f(args)`.
    fn term(&mut self, depth: usize) -> Result<TermId, ParseError> {
        if depth > self.limits.max_depth {
            return self.err("nesting depth limit exceeded");
        }
        match self.toks.get(self.pos).map(|s| s.tok.clone()) {
            Some(Tok::Number(n)) => {
                self.pos += 1;
                let s = self
                    .b
                    .symbols
                    .intern(&n.to_string(), 0, crate::symbol::SK_CONST);
                Ok(self.b.store.constant(s))
            }
            Some(Tok::Ident(name)) => {
                self.pos += 1;
                if self.peek() == Some(&Tok::LParen) {
                    self.pos += 1;
                    let mut args = Vec::new();
                    if self.peek() != Some(&Tok::RParen) {
                        loop {
                            args.push(self.term(depth + 1)?);
                            if args.len() > self.limits.max_arity {
                                return self.err("arity limit exceeded");
                            }
                            if !self.eat(&Tok::Comma) {
                                break;
                            }
                        }
                    }
                    self.expect(&Tok::RParen, "')'")?;
                    if args.is_empty() {
                        return self.err("a compound term needs at least one argument");
                    }
                    let sym = self.b.symbols.func(&name, args.len() as u16);
                    Ok(self.b.store.func(sym, &args))
                } else if is_variable(&name) {
                    Ok(self.b.var(&name))
                } else {
                    let sym = self.b.symbols.constant(&name);
                    Ok(self.b.store.constant(sym))
                }
            }
            _ => self.err("expected a term"),
        }
    }

    /// A predicate atom: `p` or `p(a, b)`. Variables are permitted only where a
    /// term would be, and the parser does not distinguish them here.
    fn atom(&mut self, depth: usize) -> Result<TermId, ParseError> {
        if depth > self.limits.max_depth {
            return self.err("nesting depth limit exceeded");
        }
        let name = self.ident()?;
        // Delegating to `Builder::atom` matters: it is what sizes the
        // per-predicate stratum vectors. Building the atom inline here skipped
        // that step and every subsequent rule indexed out of bounds.
        if !self.eat(&Tok::LParen) {
            return Ok(self.b.nullary(&name));
        }
        let mut args = Vec::new();
        if self.peek() != Some(&Tok::RParen) {
            loop {
                args.push(self.term(depth + 1)?);
                if args.len() > self.limits.max_arity {
                    return self.err("arity limit exceeded");
                }
                if !self.eat(&Tok::Comma) {
                    break;
                }
            }
        }
        self.expect(&Tok::RParen, "')'")?;
        let arity = args.len() as u16;
        Ok(self.b.atom(&name, arity, &args))
    }

    fn body(&mut self) -> Result<Vec<Literal>, ParseError> {
        let mut lits = Vec::new();
        loop {
            let neg = if let Some(Tok::Ident(w)) = self.peek() {
                if w == "not" || w == "neg" {
                    self.pos += 1;
                    true
                } else {
                    false
                }
            } else {
                false
            };
            let a = self.atom(0)?;
            lits.push(if neg {
                Literal::neg(a)
            } else {
                Literal::pos(a)
            });
            if !self.eat(&Tok::Comma) {
                break;
            }
        }
        Ok(lits)
    }

    fn item(&mut self) -> Result<(), ParseError> {
        if self.eat(&Tok::QueryDash) {
            let q = self.atom(0)?;
            self.queries.push(q);
            self.expect(&Tok::Dot, "'.' after query")?;
            return Ok(());
        }
        let head = self.atom(0)?;
        if self.eat(&Tok::ColonDash) {
            self.rules += 1;
            if self.rules > self.limits.max_rules {
                return self.err("rule limit exceeded");
            }
            let body = self.body()?;
            if body.is_empty() {
                return self.err("a rule needs at least one body literal");
            }
            if self.b.store.kind(head) != crate::term::T_ATOM {
                return self.err("rule head must be an atom");
            }
            self.b.rule(head, body);
            self.expect(&Tok::Dot, "'.' after rule")?;
        } else {
            self.expect(&Tok::Dot, "'.' or ':-'")?;
            if self.b.store.kind(head) != crate::term::T_ATOM {
                return self.err("a fact must be an atom");
            }
            if !self.b.store.is_ground(head) {
                return self.err("a fact must be ground");
            }
            self.b.fact(head);
        }
        Ok(())
    }
}

fn is_variable(name: &str) -> bool {
    let mut cs = name.chars();
    match cs.next() {
        Some(c) if c.is_ascii_uppercase() || c == '_' => true,
        _ => false,
    }
}

/// Parse a whole program.
pub fn parse(src: &str) -> Result<Parsed, ParseError> {
    parse_with(src, Limits::default())
}

pub fn parse_with(src: &str, limits: Limits) -> Result<Parsed, ParseError> {
    let toks = tokenize(src, &limits)?;
    let mut p = Parser {
        toks: &toks,
        pos: 0,
        limits,
        b: Builder::new(),
        queries: Vec::new(),
        rules: 0,
    };
    while p.pos < p.toks.len() {
        p.item()?;
    }
    let program = p.b.build().map_err(|e: ProgramError| ParseError {
        line: 0,
        col: 0,
        message: e.to_string(),
    })?;
    Ok(Parsed {
        program,
        queries: p.queries,
    })
}

/// Render a program back to source. Used to show that a problem compiled to the
/// IR and back without loss.
pub fn show(prog: &Program) -> String {
    let mut out = String::new();
    for r in &prog.rules {
        out.push_str(&prog.store.show(r.head, &prog.symbols));
        if !r.body.is_empty() {
            out.push_str(" :-\n  ");
            let parts: Vec<String> = r
                .body
                .iter()
                .map(|l| {
                    let s = prog.store.show(l.atom, &prog.symbols);
                    if l.pos {
                        s
                    } else {
                        format!("not {s}")
                    }
                })
                .collect();
            out.push_str(&parts.join(",\n  "));
        }
        out.push_str(".\n");
    }
    out
}

/// Unused helper kept for symmetry with `show`: which node kind is this?
pub fn kind_name(store: &TermStore, t: TermId) -> &'static str {
    match store.kind(t) {
        crate::term::T_VAR => "var",
        crate::term::T_CONST => "const",
        T_FUN => "fun",
        _ => "atom",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_facts_rules_and_queries() {
        let src = "\
# a small graph
edge(a, b).
edge(b, c).
path(X, Y) :- edge(X, Y).
path(X, Z) :- path(X, Y), edge(Y, Z).
?- path(a, c).
";
        let p = parse(src).unwrap();
        assert_eq!(p.program.rules.len(), 4);
        assert_eq!(p.queries.len(), 1);
    }

    #[test]
    fn uppercase_is_a_variable() {
        // `X` must survive tokenisation as a variable and not decay into the
        // constant `x`. If it did, `q(X).` would parse as a ground fact.
        match parse("q(X).") {
            Err(pe) => assert_eq!(pe.message, "a fact must be ground"),
            Ok(_) => panic!("X must not be tokenised as a constant"),
        }
        // In rule position the same identifier is accepted as a variable.
        let p = parse("q(X) :- r(X).").unwrap();
        assert_eq!(p.program.rules.len(), 1);
    }

    #[test]
    fn non_ground_fact_is_rejected() {
        let e = parse("q(X).");
        assert!(e.is_err(), "a fact with a variable must be rejected");
    }

    #[test]
    fn unterminated_is_reported_not_panicked() {
        assert!(parse("edge(a, b").is_err());
        assert!(parse("edge(a,b).").is_ok());
        assert!(parse("edge(a,b) :- .").is_err());
        assert!(parse("").is_ok(), "empty program is valid");
        assert!(parse(":- .").is_err());
        assert!(parse("edge((a).").is_err());
        assert!(parse("edge(a)).").is_err());
    }

    #[test]
    fn negation_is_accepted() {
        let p = parse("safe(X) :- node(X), not blocked(X).").unwrap();
        assert_eq!(p.program.rules.len(), 1);
        assert!(!p.program.rules[0].body[1].pos);
    }

    #[test]
    fn depth_limit_is_enforced() {
        let limits = Limits {
            max_depth: 3,
            ..Default::default()
        };
        let src = "p(a(a(a(a(a))))) .";
        assert!(parse_with(src, limits).is_err());
    }

    #[test]
    fn show_round_trips() {
        let src = "edge(a, b).\npath(X, Y) :- edge(X, Y).\n";
        let p = parse(src).unwrap();
        let text = show(&p.program);
        let q = parse(&text).unwrap();
        assert_eq!(q.program.rules.len(), p.program.rules.len());
    }

    #[test]
    fn numbers_become_constants() {
        let p = parse("n(1).\nn(2).\n").unwrap();
        assert_eq!(p.program.rules.len(), 2);
    }
}
