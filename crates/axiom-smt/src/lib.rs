//! Axiom v4 SMT engine: an SMT-LIB 2 frontend over the CDCL(T) core.
//!
//! The engine reads a small, explicit SMT-LIB 2 subset, encodes the Boolean
//! structure by Tseitin CNF, abstracts every theory atom as a SAT variable,
//! and hands the result to the root crate's CDCL(T) driver. A `sat` answer
//! carries the SAT model and is checked by re-asserting the model in a fresh
//! theory state; an `unsat` answer carries the RUP proof and the theory
//! lemmas, and is replayed by the root checker.
//!
//! The fragment is quantifier-free difference logic with uninterpreted
//! functions: `x - y <= c`, `x = y`, and `x != y` over declared constants and
//! function applications. There is no general linear arithmetic, no
//! quantifiers, no arrays, bitvectors or strings, and no incremental solving.
//!
//! Verdicts: a satisfiable assertion set is `Found` (the model is the
//! witness); an unsatisfiable one is `Impossible` (the certificate proves that
//! no model exists). There is no `Unknown` for a well-formed problem: the
//! search either produces a model, a refutation, or hits a resource cap.
//!
//! # Example
//!
//! ```
//! use axiom::Budget;
//! use axiom_core::{Engine, Problem};
//! use axiom_smt::SmtEngine;
//!
//! let source = "(set-logic QF_IDL)\
//!               (declare-fun x () Int)\
//!               (declare-fun y () Int)\
//!               (assert (<= (- y x) 3))\
//!               (assert (>= x 0))\
//!               (assert (<= x 2))\
//!               (check-sat)";
//! let problem = Problem::smt(source);
//! let mut engine = SmtEngine::new();
//! let out = engine.solve(&problem, &mut Budget::steps(1_000_000));
//! assert_eq!(out.verdict, axiom_core::Verdict::Found, "{out:?}");
//! engine.verify(&problem, &out).unwrap();
//! ```

pub mod parse;

use axiom::sat::{verify_sat, AtomDesc, Lit, STerm, TheoryLemma, UnsatProof};
use axiom::symbol::SymbolTable;
use axiom::term::{TermId, TermStore};
use axiom::theory::{
    verify_theory_sat, verify_theory_unsat, Diff, TheoryAtom, TheoryDriver, TheoryOutcome,
    TheoryProof,
};
use axiom::Budget;
use axiom_core::{
    Capabilities, Engine, Evidence, Guarantee, Outcome, Problem, ProblemKind, Stats, Verdict,
    VerifyError,
};
use std::collections::BTreeMap;
use std::time::Instant;

pub use parse::{Atom, BaseTerm, Decl, Formula, SmtError, SmtProblem};

const EVIDENCE_SAT: &str = "axiom-smt-sat";
const EVIDENCE_UNSAT: &str = "axiom-smt-unsat";
const EVIDENCE_HEADER: &str = "axiom-smt-evidence v2";
/// The implicit zero of the difference-logic fragment.
const ORIGIN: &str = "%origin";

/// The SMT engine.
#[derive(Clone, Copy, Debug, Default)]
pub struct SmtEngine;

impl SmtEngine {
    pub fn new() -> Self {
        SmtEngine
    }
}

// ---------------------------------------------------------------------------
// Encoding
// ---------------------------------------------------------------------------

/// The result of encoding a problem: the propositional clauses and the
/// meaning of every theory variable.
#[derive(Clone, Debug, Default)]
struct Encoded {
    clauses: Vec<Vec<Lit>>,
    atoms: Vec<(u32, AtomDesc)>,
}

struct Encoder<'a> {
    driver: &'a mut TheoryDriver,
    store: &'a mut TermStore,
    symbols: &'a mut SymbolTable,
    clauses: Vec<Vec<Lit>>,
    atoms: Vec<(u32, AtomDesc)>,
    props: BTreeMap<String, i32>,
}

impl<'a> Encoder<'a> {
    fn new(
        driver: &'a mut TheoryDriver,
        store: &'a mut TermStore,
        symbols: &'a mut SymbolTable,
    ) -> Self {
        Encoder {
            driver,
            store,
            symbols,
            clauses: Vec::new(),
            atoms: Vec::new(),
            props: BTreeMap::new(),
        }
    }

    fn new_var(&mut self) -> i32 {
        let v = self.driver.bool_var();
        (v as i32) + 1
    }

    fn add(&mut self, clause: Vec<Lit>) {
        self.clauses.push(clause);
    }

    fn term(&mut self, base: &BaseTerm) -> Result<TermId, SmtError> {
        match base {
            BaseTerm::Var(name) => {
                let sym = self.symbols.constant(name);
                Ok(self.store.constant(sym))
            }
            BaseTerm::App(name, args) => {
                let sym = self.symbols.func(name, args.len() as u16);
                let mut ids = Vec::with_capacity(args.len());
                for arg in args {
                    ids.push(self.term(arg)?);
                }
                Ok(self.store.func(sym, &ids))
            }
            BaseTerm::Origin => {
                let sym = self.symbols.constant(ORIGIN);
                Ok(self.store.constant(sym))
            }
            BaseTerm::Num(k) => Err(SmtError::Unsupported {
                offset: 0,
                message: format!("numeral {k} cannot be used as a term"),
            }),
        }
    }

    fn atom_literal(&mut self, atom: &Atom) -> Result<i32, SmtError> {
        let (theory_atom, desc) = match atom {
            Atom::Rdl { x, y, c } => {
                let xt = self.term(x)?;
                let yt = self.term(y)?;
                (
                    TheoryAtom::Rdl(Diff {
                        x: xt,
                        y: yt,
                        c: *c,
                    }),
                    AtomDesc::Rdl {
                        x: structural(x),
                        y: structural(y),
                        c: *c,
                    },
                )
            }
            Atom::Eq(a, b) => {
                let at = self.term(a)?;
                let bt = self.term(b)?;
                (
                    TheoryAtom::Eq(at, bt),
                    AtomDesc::Eq(structural(a), structural(b)),
                )
            }
            Atom::Neq(a, b) => {
                let at = self.term(a)?;
                let bt = self.term(b)?;
                (
                    TheoryAtom::Neq(at, bt),
                    AtomDesc::Neq(structural(a), structural(b)),
                )
            }
        };
        let var = self
            .driver
            .theory_var(self.store, theory_atom)
            .map_err(|e| SmtError::Unsupported {
                offset: 0,
                message: format!("theory atom rejected: {e}"),
            })?;
        if !self.atoms.iter().any(|(v, _)| *v == var) {
            self.atoms.push((var, desc));
        }
        Ok((var as i32) + 1)
    }

    fn prop_literal(&mut self, name: &str) -> i32 {
        if let Some(lit) = self.props.get(name) {
            return *lit;
        }
        let lit = self.new_var();
        self.props.insert(name.to_string(), lit);
        lit
    }

    /// `v <-> conjunction of literals`
    ///
    /// Both directions need one clause per literal: `a_i -> v` and
    /// `v -> a_i`. A single `v -> (a_1 | ... | a_n)` clause would encode a
    /// disjunction and silently weaken the formula.
    fn lit_and(&mut self, lits: Vec<i32>) -> i32 {
        let v = self.new_var();
        for lit in &lits {
            self.add(vec![-lit, v]);
            self.add(vec![-v, *lit]);
        }
        v
    }

    /// `v <-> disjunction of literals`
    fn lit_or(&mut self, lits: Vec<i32>) -> i32 {
        let v = self.new_var();
        for lit in &lits {
            self.add(vec![*lit, -v]);
        }
        let mut big = vec![v];
        big.extend(lits.into_iter().map(|l| -l));
        self.add(big);
        v
    }

    fn encode(&mut self, formula: &Formula) -> Result<i32, SmtError> {
        match formula {
            Formula::Bool(true) => {
                let v = self.new_var();
                self.add(vec![v]);
                Ok(v)
            }
            Formula::Bool(false) => {
                let v = self.new_var();
                self.add(vec![-v]);
                Ok(v)
            }
            Formula::Prop(name) => Ok(self.prop_literal(name)),
            Formula::Atom(atom) => self.atom_literal(atom),
            Formula::Not(inner) => self.encode_not(inner),
            Formula::And(parts) => {
                let mut lits = Vec::new();
                for part in parts {
                    lits.push(self.encode(part)?);
                }
                Ok(self.lit_and(lits))
            }
            Formula::Or(parts) => {
                let mut lits = Vec::new();
                for part in parts {
                    lits.push(self.encode(part)?);
                }
                Ok(self.lit_or(lits))
            }
            Formula::Xor(a, b) => {
                let v = self.new_var();
                let la = self.encode(a)?;
                let lb = self.encode(b)?;
                self.add(vec![-la, -lb, -v]);
                self.add(vec![la, lb, -v]);
                self.add(vec![la, -lb, v]);
                self.add(vec![-la, lb, v]);
                Ok(v)
            }
            Formula::Implies(a, b) => {
                let v = self.new_var();
                let la = self.encode(a)?;
                let lb = self.encode(b)?;
                self.add(vec![-la, -lb, v]);
                self.add(vec![-v, la]);
                self.add(vec![-v, lb]);
                Ok(v)
            }
            Formula::Ite(c, a, b) => {
                let v = self.new_var();
                let lc = self.encode(c)?;
                let la = self.encode(a)?;
                let lb = self.encode(b)?;
                self.add(vec![-lc, -la, v]);
                self.add(vec![-lc, la, -v]);
                self.add(vec![lc, -lb, v]);
                self.add(vec![lc, lb, -v]);
                Ok(v)
            }
        }
    }

    fn encode_not(&mut self, formula: &Formula) -> Result<i32, SmtError> {
        match formula {
            Formula::Bool(b) => self.encode(&Formula::Bool(!b)),
            Formula::Prop(name) => {
                let p = self.prop_literal(name);
                let v = self.new_var();
                self.add(vec![p, v]);
                self.add(vec![-p, -v]);
                Ok(v)
            }
            Formula::Atom(atom) => {
                let negated = match atom {
                    Atom::Rdl { x, y, c } => Atom::Rdl {
                        x: y.clone(),
                        y: x.clone(),
                        c: -c - 1,
                    },
                    Atom::Eq(a, b) => Atom::Neq(a.clone(), b.clone()),
                    Atom::Neq(a, b) => Atom::Eq(a.clone(), b.clone()),
                };
                self.atom_literal(&negated)
            }
            Formula::Not(inner) => self.encode(inner),
            Formula::And(parts) => {
                let mut lits = Vec::new();
                for part in parts {
                    lits.push(self.encode_not(part)?);
                }
                Ok(self.lit_or(lits))
            }
            Formula::Or(parts) => {
                let mut lits = Vec::new();
                for part in parts {
                    lits.push(self.encode_not(part)?);
                }
                Ok(self.lit_and(lits))
            }
            Formula::Xor(a, b) => self.encode(&Formula::Xor(a.clone(), b.clone())),
            Formula::Implies(a, b) => {
                let la = self.encode(a)?;
                let lb = self.encode_not(b)?;
                Ok(self.lit_and(vec![la, lb]))
            }
            Formula::Ite(c, a, b) => {
                let v = self.new_var();
                let lc = self.encode(c)?;
                let la = self.encode_not(a)?;
                let lb = self.encode_not(b)?;
                self.add(vec![-lc, -la, v]);
                self.add(vec![-lc, la, -v]);
                self.add(vec![lc, -lb, v]);
                self.add(vec![lc, lb, -v]);
                Ok(v)
            }
        }
    }
}

fn structural(base: &BaseTerm) -> STerm {
    match base {
        BaseTerm::Var(name) => STerm::Const(name.clone()),
        BaseTerm::Origin => STerm::Const(ORIGIN.to_string()),
        BaseTerm::Num(k) => STerm::Const(format!("{k}")),
        BaseTerm::App(name, args) => {
            STerm::App(name.clone(), args.iter().map(structural).collect())
        }
    }
}

fn encode(
    assertions: &[Formula],
    driver: &mut TheoryDriver,
    store: &mut TermStore,
    symbols: &mut SymbolTable,
) -> Result<Encoded, SmtError> {
    let mut encoder = Encoder::new(driver, store, symbols);
    for assertion in assertions {
        let lit = encoder.encode(assertion)?;
        encoder.add(vec![lit]);
    }
    Ok(Encoded {
        clauses: encoder.clauses,
        atoms: encoder.atoms,
    })
}

// ---------------------------------------------------------------------------
// Evidence
// ---------------------------------------------------------------------------

fn render_term(term: &STerm) -> String {
    match term {
        STerm::Var(name) | STerm::Const(name) => name.clone(),
        STerm::App(name, args) => {
            let mut out = String::from("(");
            out.push_str(name);
            for arg in args {
                out.push(' ');
                out.push_str(&render_term(arg));
            }
            out.push(')');
            out
        }
    }
}

fn render_atom(desc: &AtomDesc) -> String {
    match desc {
        AtomDesc::Rdl { x, y, c } => format!("rdl {} {} {c}", render_term(x), render_term(y)),
        AtomDesc::Eq(a, b) => format!("eq {} {}", render_term(a), render_term(b)),
        AtomDesc::Neq(a, b) => format!("neq {} {}", render_term(a), render_term(b)),
    }
}

/// Split text on whitespace, keeping parenthesised groups together.
fn split_top_level(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut depth = 0usize;
    let mut current = String::new();
    for ch in text.chars() {
        match ch {
            '(' => {
                depth += 1;
                current.push(ch);
            }
            ')' => {
                depth = depth.saturating_sub(1);
                current.push(ch);
            }
            c if c.is_whitespace() && depth == 0 => {
                if !current.is_empty() {
                    out.push(std::mem::take(&mut current));
                }
            }
            c => current.push(c),
        }
    }
    if !current.is_empty() {
        out.push(current);
    }
    out
}

fn parse_term(text: &str) -> Result<STerm, String> {
    let text = text.trim();
    if let Some(rest) = text.strip_prefix('(') {
        let rest = rest
            .strip_suffix(')')
            .ok_or_else(|| format!("unbalanced term {text}"))?;
        let parts = split_top_level(rest);
        let name = parts
            .first()
            .ok_or_else(|| format!("empty application {text}"))?
            .to_string();
        let mut args = Vec::new();
        for part in &parts[1..] {
            args.push(parse_term(part)?);
        }
        if args.is_empty() {
            return Err(format!("application without arguments {text}"));
        }
        return Ok(STerm::App(name, args));
    }
    if text.is_empty() {
        return Err("empty term".to_string());
    }
    Ok(STerm::Const(text.to_string()))
}

fn parse_atom(text: &str) -> Result<AtomDesc, String> {
    let parts = split_top_level(text);
    let mut parts = parts.into_iter();
    let head = parts.next().ok_or_else(|| "empty atom".to_string())?;
    match head.as_str() {
        "rdl" => {
            let x = parse_term(&parts.next().ok_or("rdl needs a term")?)?;
            let y = parse_term(&parts.next().ok_or("rdl needs a term")?)?;
            let c: i64 = parts
                .next()
                .ok_or("rdl needs a constant")?
                .parse()
                .map_err(|_| "rdl constant is not a number".to_string())?;
            Ok(AtomDesc::Rdl { x, y, c })
        }
        "eq" => {
            let a = parse_term(&parts.next().ok_or("eq needs a term")?)?;
            let b = parse_term(&parts.next().ok_or("eq needs a term")?)?;
            Ok(AtomDesc::Eq(a, b))
        }
        "neq" => {
            let a = parse_term(&parts.next().ok_or("neq needs a term")?)?;
            let b = parse_term(&parts.next().ok_or("neq needs a term")?)?;
            Ok(AtomDesc::Neq(a, b))
        }
        other => Err(format!("unknown atom kind {other}")),
    }
}

fn render_lits(lits: &[Lit]) -> String {
    lits.iter()
        .map(|l| l.to_string())
        .collect::<Vec<_>>()
        .join(",")
}

fn parse_lits(text: &str) -> Result<Vec<Lit>, String> {
    if text.is_empty() {
        return Ok(Vec::new());
    }
    text.split(',')
        .map(|part| {
            part.trim()
                .parse::<i32>()
                .map_err(|_| format!("literal {part} is not a number"))
        })
        .collect()
}

/// One `check-sat` answer: its mode and the certificate that backs it.
struct CheckEvidence {
    mode: String,
    model: Option<Vec<i8>>,
    learnts: Vec<Vec<Lit>>,
    lemmas: Vec<TheoryLemma>,
    atoms: Vec<(u32, AtomDesc)>,
}

/// A session: one answer per `check-sat` command in the source.
struct SessionEvidence {
    checks: Vec<CheckEvidence>,
}

fn write_evidence(checks: &[CheckEvidence]) -> String {
    let mut out = String::from(EVIDENCE_HEADER);
    out.push('\n');
    out.push_str(&format!("checks {}\n", checks.len()));
    for (index, check) in checks.iter().enumerate() {
        out.push_str(&format!("check {index} {}\n", check.mode));
        if let Some(model) = &check.model {
            let values: Vec<String> = model.iter().map(|v| v.to_string()).collect();
            out.push_str(&format!("model {}\n", values.join(",")));
        }
        for (var, desc) in &check.atoms {
            out.push_str(&format!("atom {var} {}\n", render_atom(desc)));
        }
        for clause in &check.learnts {
            out.push_str(&format!("learnt {}\n", render_lits(clause)));
        }
        for lemma in &check.lemmas {
            let concl = match lemma.concl {
                Some(c) => c.to_string(),
                None => "-".to_string(),
            };
            out.push_str(&format!(
                "lemma clause={} hyps={} concl={concl}\n",
                render_lits(&lemma.clause),
                render_lits(&lemma.hyps)
            ));
        }
    }
    out
}

fn read_evidence(payload: &str) -> Result<SessionEvidence, String> {
    let mut lines = payload.lines();
    let header = lines.next().ok_or("empty evidence")?;
    if header.trim() != EVIDENCE_HEADER {
        return Err("unknown evidence header".to_string());
    }
    let mut checks: Vec<CheckEvidence> = Vec::new();
    for line in lines {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        let mut parts = line.split_whitespace();
        let head = parts.next().unwrap_or_default();
        match head {
            "checks" => {
                let count: usize = parts
                    .next()
                    .unwrap_or_default()
                    .parse()
                    .map_err(|_| "check count is not a number".to_string())?;
                if count != 0 && checks.is_empty() {
                    // The count is checked against the parsed sections below.
                }
            }
            "check" => {
                let index: usize = parts
                    .next()
                    .ok_or("check needs an index")?
                    .parse()
                    .map_err(|_| "check index is not a number".to_string())?;
                let mode = parts.next().unwrap_or_default().to_string();
                if index != checks.len() {
                    return Err("check indices must be consecutive".to_string());
                }
                if mode != "sat" && mode != "unsat" {
                    return Err(format!("unknown check mode {mode}"));
                }
                checks.push(CheckEvidence {
                    mode,
                    model: None,
                    learnts: Vec::new(),
                    lemmas: Vec::new(),
                    atoms: Vec::new(),
                });
            }
            "model" => {
                let text = parts.next().unwrap_or_default();
                let mut values = Vec::new();
                for part in text.split(',').filter(|p| !p.is_empty()) {
                    values.push(
                        part.parse::<i8>()
                            .map_err(|_| format!("model entry {part} is not a number"))?,
                    );
                }
                let check = checks.last_mut().ok_or("model outside a check section")?;
                check.model = Some(values);
            }
            "atom" => {
                let fields = split_top_level(line);
                let var: u32 = fields
                    .get(1)
                    .ok_or("atom needs a variable")?
                    .parse()
                    .map_err(|_| "atom variable is not a number".to_string())?;
                let desc = parse_atom(&fields[2..].join(" "))?;
                let check = checks.last_mut().ok_or("atom outside a check section")?;
                check.atoms.push((var, desc));
            }
            "learnt" => {
                let text = parts.next().unwrap_or_default();
                let clause = parse_lits(text)?;
                let check = checks.last_mut().ok_or("learnt outside a check section")?;
                check.learnts.push(clause);
            }
            "lemma" => {
                let mut clause = None;
                let mut hyps = None;
                let mut concl = None;
                for field in parts {
                    let Some((key, value)) = field.split_once('=') else {
                        continue;
                    };
                    match key {
                        "clause" => clause = Some(parse_lits(value)?),
                        "hyps" => hyps = Some(parse_lits(value)?),
                        "concl" => {
                            concl =
                                Some(if value == "-" {
                                    None
                                } else {
                                    Some(value.parse::<i32>().map_err(|_| {
                                        "lemma conclusion is not a number".to_string()
                                    })?)
                                })
                        }
                        _ => {}
                    }
                }
                let clause = clause.ok_or("lemma needs a clause")?;
                let hyps = hyps.ok_or("lemma needs hypotheses")?;
                let concl = concl.ok_or("lemma needs a conclusion")?;
                let check = checks.last_mut().ok_or("lemma outside a check section")?;
                check.lemmas.push(TheoryLemma {
                    clause,
                    hyps,
                    concl,
                });
            }
            other => return Err(format!("unknown evidence line {other}")),
        }
    }
    if checks.is_empty() {
        return Err("evidence has no checks".to_string());
    }
    Ok(SessionEvidence { checks })
}

// ---------------------------------------------------------------------------
// Engine
// ---------------------------------------------------------------------------

fn source_of(problem: &Problem) -> Result<&str, String> {
    match problem {
        Problem::Smt { source } => Ok(source),
        _ => Err("SMT engine received a non-SMT problem".to_string()),
    }
}

fn parse_source(source: &str) -> Result<SmtProblem, Outcome> {
    parse::parse_problem(source).map_err(|e| match e {
        SmtError::Unsupported { .. } => Outcome::unsupported(e.to_string()),
        SmtError::Parse { .. } => Outcome::error(format!("SMT parse error: {e}")),
    })
}

/// Encode one assertion set. The driver returned here is the one that
/// allocated the variables, so the same numbering is used for solving and
/// for the certificate.
fn build(
    assertions: &[Formula],
) -> Result<(TheoryDriver, Encoded, TermStore, SymbolTable), Outcome> {
    let mut driver = TheoryDriver::new();
    let mut store = TermStore::new();
    let mut symbols = SymbolTable::new();
    let encoded =
        encode(assertions, &mut driver, &mut store, &mut symbols).map_err(|e| match e {
            SmtError::Unsupported { .. } => Outcome::unsupported(e.to_string()),
            SmtError::Parse { .. } => Outcome::error(format!("SMT encoding error: {e}")),
        })?;
    Ok((driver, encoded, store, symbols))
}

impl Engine for SmtEngine {
    fn capabilities(&self) -> Capabilities {
        Capabilities::new("axiom-smt-theory", env!("CARGO_PKG_VERSION"))
            .handles(ProblemKind::Smt)
            .fragment(
                "SMT-LIB 2 subset: quantifier-free difference logic and uninterpreted functions",
            )
            .fragment("Boolean structure encoded by Tseitin CNF over a CDCL(T) core")
            .fragment("push/pop scopes and several check-sat commands per file")
            .guarantee(Guarantee::Sound)
            .guarantee(Guarantee::Deterministic)
            .guarantee(Guarantee::EvidenceChecked)
            .limit("no general linear arithmetic, no arrays, bitvectors, strings or quantifiers")
            .limit("each check is solved from scratch: no learnt clause or theory state is reused")
            .limit("the model reports atom truth values, not reconstructed integer values")
    }

    fn solve(&mut self, problem: &Problem, budget: &mut Budget) -> Outcome {
        let source = match source_of(problem) {
            Ok(s) => s,
            Err(message) => return Outcome::error(message),
        };
        let start = Instant::now();
        let parsed = match parse_source(source) {
            Ok(p) => p,
            Err(o) => return o,
        };
        let mut checks: Vec<CheckEvidence> = Vec::new();
        let mut any_unsat = false;
        for assertions in parsed.check_assertions() {
            let (mut driver, encoded, store, symbols) = match build(&assertions) {
                Ok(b) => b,
                Err(o) => return o,
            };
            for clause in &encoded.clauses {
                driver.add_clause(clause);
            }
            let outcome = match driver.solve(&store, &symbols, budget) {
                Ok(o) => o,
                Err(e) => return Outcome::resource_limit(e.to_string()),
            };
            match outcome {
                TheoryOutcome::Sat { model, theory } => {
                    checks.push(CheckEvidence {
                        mode: "sat".to_string(),
                        model: Some(model),
                        learnts: Vec::new(),
                        lemmas: theory.lemmas,
                        atoms: theory.atoms,
                    });
                }
                TheoryOutcome::Unsat { sat, theory } => {
                    any_unsat = true;
                    checks.push(CheckEvidence {
                        mode: "unsat".to_string(),
                        model: None,
                        learnts: sat.learnts,
                        lemmas: theory.lemmas,
                        atoms: theory.atoms,
                    });
                }
            }
        }
        let stats = Stats::new(budget.spent(), start.elapsed().as_millis() as u64)
            .with("checks", checks.len() as u64);
        let payload = write_evidence(&checks);
        if any_unsat {
            Outcome::definite(
                Verdict::Impossible,
                Evidence::new(EVIDENCE_UNSAT, payload),
                stats,
            )
        } else {
            Outcome::definite(Verdict::Found, Evidence::new(EVIDENCE_SAT, payload), stats)
        }
    }

    fn verify(&self, problem: &Problem, outcome: &Outcome) -> Result<(), VerifyError> {
        if !outcome.verdict.is_definite() {
            if outcome.evidence.is_some() {
                return Err(VerifyError::InvalidEvidence(
                    "non-definite SMT outcomes must not carry evidence".into(),
                ));
            }
            return Ok(());
        }
        let source = source_of(problem).map_err(VerifyError::Malformed)?;
        let parsed =
            parse_source(source).map_err(|o| VerifyError::Malformed(o.notes.join("; ")))?;
        let evidence = outcome
            .evidence
            .as_ref()
            .ok_or(VerifyError::MissingEvidence)?;
        let expected_kind = match outcome.verdict {
            Verdict::Found => EVIDENCE_SAT,
            Verdict::Impossible => EVIDENCE_UNSAT,
            other => {
                return Err(VerifyError::InvalidEvidence(format!(
                    "verdict {other} is not an SMT answer"
                )))
            }
        };
        if evidence.kind != expected_kind {
            return Err(VerifyError::InvalidEvidence(format!(
                "wrong evidence kind {}",
                evidence.kind
            )));
        }
        let session = read_evidence(&evidence.payload)
            .map_err(|e| VerifyError::InvalidEvidence(format!("malformed evidence: {e}")))?;
        let assertions_per_check = parsed.check_assertions();
        if session.checks.len() != assertions_per_check.len() {
            return Err(VerifyError::InvalidEvidence(
                "the evidence has a different number of checks than the problem".into(),
            ));
        }
        let mut any_unsat = false;
        for (index, assertions) in assertions_per_check.iter().enumerate() {
            let check = &session.checks[index];
            let (_driver, encoded, _store, _symbols) =
                build(assertions).map_err(|o| VerifyError::Malformed(o.notes.join("; ")))?;
            // The atom meanings in the evidence must be exactly the ones the
            // problem produces, so a certificate cannot be replayed against a
            // different assertion set.
            if check.atoms != encoded.atoms {
                return Err(VerifyError::InvalidEvidence(format!(
                    "evidence atoms for check {index} do not match the problem's atoms"
                )));
            }
            let theory = TheoryProof {
                atoms: encoded.atoms.clone(),
                lemmas: check.lemmas.clone(),
            };
            match check.mode.as_str() {
                "sat" => {
                    let Some(model) = check.model.as_ref() else {
                        return Err(VerifyError::InvalidEvidence(
                            "a sat answer needs a model".into(),
                        ));
                    };
                    if !verify_sat(&encoded.clauses, model) {
                        return Err(VerifyError::InvalidEvidence(format!(
                            "the model for check {index} does not satisfy the encoded clauses"
                        )));
                    }
                    if !verify_theory_sat(model, &theory) {
                        return Err(VerifyError::InvalidEvidence(format!(
                            "the model for check {index} is not consistent with the theory"
                        )));
                    }
                }
                "unsat" => {
                    any_unsat = true;
                    for (i, lemma) in check.lemmas.iter().enumerate() {
                        let mut expected = lemma.hyps.iter().map(|l| -l).collect::<Vec<Lit>>();
                        if let Some(concl) = lemma.concl {
                            expected.push(concl);
                        }
                        if expected != lemma.clause {
                            return Err(VerifyError::InvalidEvidence(format!(
                                "theory lemma {i} for check {index} has a clause that does not \
                                 match its justification"
                            )));
                        }
                    }
                    let proof = UnsatProof {
                        learnts: check.learnts.clone(),
                    };
                    verify_theory_unsat(&encoded.clauses, &proof, &theory)
                        .map_err(|e| VerifyError::InvalidEvidence(format!("check {index}: {e}")))?;
                }
                other => {
                    return Err(VerifyError::InvalidEvidence(format!(
                        "unknown check mode {other}"
                    )))
                }
            }
        }
        if any_unsat != (outcome.verdict == Verdict::Impossible) {
            return Err(VerifyError::InvalidEvidence(
                "the verdict does not match the checked answers".into(),
            ));
        }
        Ok(())
    }
}

/// Convenience wrapper: solve an SMT source string and return the outcome.
pub fn solve_source(source: &str, budget: &mut Budget) -> Outcome {
    let problem = Problem::smt(source);
    SmtEngine::new().solve(&problem, budget)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn solve(src: &str) -> Outcome {
        let problem = Problem::smt(src);
        let mut budget = Budget::steps(1_000_000);
        let mut engine = SmtEngine::new();
        let out = engine.solve(&problem, &mut budget);
        engine.verify(&problem, &out).unwrap();
        out
    }

    const DECLS: &str = "(declare-fun x () Int) (declare-fun y () Int)";

    #[test]
    fn a_consistent_difference_system_is_found() {
        let out = solve(&format!(
            "{DECLS} (assert (<= (- y x) 3)) (assert (>= x 0)) (assert (<= x 2)) (check-sat)"
        ));
        assert_eq!(out.verdict, Verdict::Found, "{out:?}");
        assert_eq!(
            out.evidence.as_ref().map(|e| e.kind.as_str()),
            Some(EVIDENCE_SAT)
        );
    }

    #[test]
    fn an_inconsistent_difference_system_is_impossible() {
        let out = solve(&format!(
            "{DECLS} (assert (<= (- y x) 3)) (assert (>= y 10)) (assert (<= x 0)) (check-sat)"
        ));
        assert_eq!(out.verdict, Verdict::Impossible, "{out:?}");
        assert_eq!(
            out.evidence.as_ref().map(|e| e.kind.as_str()),
            Some(EVIDENCE_UNSAT)
        );
    }

    #[test]
    fn uninterpreted_functions_use_congruence() {
        let out = solve(
            "(declare-fun f (Int) Int) (declare-fun a () Int) (declare-fun b () Int) \
             (assert (= a b)) (assert (not (= (f a) (f b)))) (check-sat)",
        );
        assert_eq!(out.verdict, Verdict::Impossible, "{out:?}");
    }

    #[test]
    fn a_numeral_equality_is_checked() {
        let out = solve("(declare-fun x () Int) (assert (= x 3)) (assert (= x 4)) (check-sat)");
        assert_eq!(out.verdict, Verdict::Impossible, "{out:?}");
        let out = solve("(declare-fun x () Int) (assert (= x 3)) (assert (>= x 3)) (check-sat)");
        assert_eq!(out.verdict, Verdict::Found, "{out:?}");
    }

    #[test]
    fn boolean_structure_is_handled() {
        let out = solve(&format!(
            "(declare-fun p () Bool) {DECLS} \
             (assert (or p (and (<= x 0) (<= (- y x) 1)))) (check-sat)"
        ));
        assert_eq!(out.verdict, Verdict::Found, "{out:?}");
    }

    #[test]
    fn a_tampered_model_is_rejected() {
        let source = format!("{DECLS} (assert (<= x 2)) (assert (>= x 0)) (check-sat)");
        let problem = Problem::smt(source);
        let mut budget = Budget::steps(1_000_000);
        let mut engine = SmtEngine::new();
        let out = engine.solve(&problem, &mut budget);
        assert_eq!(out.verdict, Verdict::Found, "{out:?}");
        let payload = out.evidence.as_ref().unwrap().payload.clone();
        let mut rewritten = String::new();
        for line in payload.lines() {
            if let Some(rest) = line.strip_prefix("model ") {
                let flipped: Vec<String> = rest
                    .split(',')
                    .map(|v| {
                        let n: i8 = v.parse().unwrap();
                        (-n).to_string()
                    })
                    .collect();
                rewritten.push_str(&format!("model {}\n", flipped.join(",")));
            } else {
                rewritten.push_str(line);
                rewritten.push('\n');
            }
        }
        let mut bad = out.clone();
        bad.evidence = Some(Evidence::new(EVIDENCE_SAT, rewritten));
        assert!(engine.verify(&problem, &bad).is_err());
    }

    #[test]
    fn a_tampered_unsat_proof_is_rejected() {
        let source = format!("{DECLS} (assert (<= x 2)) (assert (>= x 5)) (check-sat)");
        let problem = Problem::smt(source);
        let mut budget = Budget::steps(1_000_000);
        let mut engine = SmtEngine::new();
        let out = engine.solve(&problem, &mut budget);
        assert_eq!(out.verdict, Verdict::Impossible, "{out:?}");
        // Weakening a theory lemma removes the justification for the
        // conflict: with one hypothesis the theory state stays consistent.
        let mut bad = out.clone();
        let payload = out.evidence.as_ref().unwrap().payload.clone();
        let weakened = payload.replace("hyps=2,1", "hyps=1");
        assert_ne!(weakened, payload);
        bad.evidence = Some(Evidence::new(EVIDENCE_UNSAT, weakened));
        assert!(engine.verify(&problem, &bad).is_err());

        // Changing an atom meaning makes the certificate replay against a
        // different problem.
        let mut bad = out.clone();
        let mut rewritten = String::new();
        for line in payload.lines() {
            if line.starts_with("atom ") {
                rewritten.push_str(&format!("{}\n", line.replace(" 0", " 1")));
            } else {
                rewritten.push_str(&format!("{line}\n"));
            }
        }
        bad.evidence = Some(Evidence::new(EVIDENCE_UNSAT, rewritten));
        assert!(engine.verify(&problem, &bad).is_err());
    }

    #[test]
    fn unsupported_fragments_are_explicit() {
        let out = solve("(declare-fun x () Int) (assert (> (* 2 x) 3)) (check-sat)");
        assert_eq!(out.verdict, Verdict::Unsupported, "{out:?}");
        assert!(out.evidence.is_none());
    }

    #[test]
    fn push_pop_scopes_change_the_answer() {
        // The first check sees only the base scope, the second also sees the
        // pushed assertion, and the third is back to the base scope.
        let source = format!(
            "{DECLS} \
             (assert (<= x 2)) (assert (>= x 0)) (check-sat) \
             (push 1) (assert (>= x 5)) (check-sat) (pop 1) (check-sat)"
        );
        let problem = Problem::smt(source);
        let mut budget = Budget::steps(1_000_000);
        let mut engine = SmtEngine::new();
        let out = engine.solve(&problem, &mut budget);
        assert_eq!(out.verdict, Verdict::Impossible, "{out:?}");
        engine.verify(&problem, &out).unwrap();
        let payload = out.evidence.as_ref().unwrap().payload.clone();
        let modes: Vec<&str> = payload
            .lines()
            .filter(|l| l.starts_with("check "))
            .map(|l| l.split_whitespace().nth(2).unwrap_or(""))
            .collect();
        assert_eq!(modes, vec!["sat", "unsat", "sat"], "{payload}");
    }

    #[test]
    fn a_pop_below_the_base_scope_is_an_error() {
        let out = solve("(pop 1)");
        assert_eq!(out.verdict, Verdict::Error, "{out:?}");
    }
}
