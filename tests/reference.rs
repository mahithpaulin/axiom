//! A deliberately naive reference implementation, used only by the tests.
//!
//! ## Why this file exists
//!
//! §11 of the charter asks for differential tests against trusted
//! implementations. There is no trusted implementation of *this* engine, so the
//! second implementation has to be written here, from scratch, in the simplest
//! way that could possibly be correct:
//!
//! * terms are `String`s, not arena nodes;
//! * matching is a recursive `String` comparison with a `HashMap` of variables;
//! * saturation re-evaluates every rule from scratch until nothing changes;
//! * there is no index, no trail, no hash-consing, no delta.
//!
//! It is roughly two orders of magnitude slower than the engine and would never
//! ship. That is the point. It shares *no code* with the engine -- not the
//! arena, not `Subst`, not `Db`, not the join -- so agreement between the two is
//! genuine evidence rather than a tautology. A bug in hash-consing, in the
//! union-find trail, in the join cursors, or in semi-naive delta handling cannot
//! hide from it.
//!
//! It is a *reference*, not an oracle: it is obviously correct by inspection, not
//! proven correct.

use std::collections::{HashMap, HashSet};

/// A rendered term: a constant, `f(a,b)`, or a variable written `_0`.
pub type Term = String;
pub type Atom = String;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RefRule {
    pub head: Atom,
    pub body: Vec<(bool, Atom)>,
    pub backward_only: bool,
}

/// Split a rendered term into a constructor name and argument strings.
/// `f(a,b)` -> ("f", ["a","b"]);  `a` -> ("a", []).
pub fn parse_term(s: &str) -> (String, Vec<Term>) {
    if let Some(open) = s.find('(') {
        let name = s[..open].to_string();
        let inner = &s[open + 1..s.len() - 1];
        let mut args = Vec::new();
        let mut depth = 0usize;
        let mut start = 0usize;
        for (i, c) in inner.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => depth -= 1,
                ',' if depth == 0 => {
                    args.push(inner[start..i].to_string());
                    start = i + 1;
                }
                _ => {}
            }
        }
        if start < inner.len() {
            args.push(inner[start..].to_string());
        }
        (name, args)
    } else {
        (s.to_string(), Vec::new())
    }
}

fn is_var(s: &str) -> bool {
    s.starts_with('_')
}

/// One-way match: bind only variables occurring in `pat`.
fn match_term(pat: &str, fact: &str, env: &mut HashMap<String, Term>) -> bool {
    if is_var(pat) {
        match env.get(pat) {
            Some(bound) => bound == fact,
            None => {
                env.insert(pat.to_string(), fact.to_string());
                true
            }
        }
    } else {
        let (pn, pa) = parse_term(pat);
        let (fn_, fa) = parse_term(fact);
        if pn != fn_ || pa.len() != fa.len() {
            return false;
        }
        for (x, y) in pa.iter().zip(fa.iter()) {
            if !match_term(x, y, env) {
                return false;
            }
        }
        true
    }
}

fn apply(s: &str, env: &HashMap<String, Term>) -> Term {
    if is_var(s) {
        return env.get(s).cloned().unwrap_or_else(|| s.to_string());
    }
    let (name, args) = parse_term(s);
    if args.is_empty() {
        name
    } else {
        let parts: Vec<String> = args.iter().map(|a| apply(a, env)).collect();
        format!("{name}({})", parts.join(","))
    }
}

/// All ground instances of a rule body, left to right with backtracking.
/// Results are `Option<()>`-free because the body is always satisfiable or not;
/// a `None` bound map simply means "no solution".
fn solve_body(body: &[(bool, Atom)], pred_facts: &HashMap<String, Vec<Atom>>) -> Vec<HashMap<String, Term>> {
    let mut path: Vec<HashMap<String, Term>> = vec![HashMap::new()];
    for (positive, atom) in body.iter() {
        if *positive {
            let (name, args) = parse_term(atom);
            let key = format!("{name}/{}", args.len());
            let candidates: Vec<Atom> = match pred_facts.get(&key) {
                Some(v) => v.clone(),
                None => Vec::new(),
            };
            let mut next: Vec<HashMap<String, Term>> = Vec::new();
            for env in &path {
                for c in &candidates {
                    let mut e2 = env.clone();
                    let cargs: Vec<Term> = parse_term(c).1;
                    if args.iter().zip(cargs.iter()).all(|(p, f)| match_term(p, f, &mut e2)) {
                        next.push(e2);
                    }
                }
            }
            path = next;
        } else {
            // A negated literal filters the environments accumulated so far.
            path = path
                .into_iter()
                .filter(|env| {
                    let inst = apply(atom, env);
                    let (n2, a2) = parse_term(&inst);
                    let k2 = format!("{n2}/{}", a2.len());
                    match pred_facts.get(&k2) {
                        Some(v) => !v.contains(&inst),
                        None => true,
                    }
                })
                .collect();
        }
        if path.is_empty() {
            return Vec::new();
        }
    }
    path
}

/// Naive fixpoint. Returns the complete closure, including seed facts.
///
/// Restricted to rules whose heads contain no function symbols, so the closure
/// is finite; rules that would not terminate bottom-up are returned in the
/// second element so a test can assert they were excluded rather than silently
/// ignored.
pub fn least_model(rules: &[RefRule], max_rounds: usize) -> (HashSet<Atom>, Vec<RefRule>) {
    let mut closure: HashSet<Atom> = HashSet::new();
    let mut skipped: Vec<RefRule> = Vec::new();
    let usable: Vec<&RefRule> = rules.iter().filter(|r| !r.backward_only).collect();

    // Seed facts.
    for r in &usable {
        if r.body.is_empty() {
            closure.insert(r.head.clone());
        }
    }

    for _ in 0..max_rounds {
        let before = closure.len();
        for r in &usable {
            if r.body.is_empty() {
                continue;
            }
            // Rebuilt per rule, not per round: that is what makes this
            // reference naive, and what makes it agree with the engine on
            // within-round propagation rather than only at the fixpoint.
            let by_pred = group_by_predicate(&closure);
            for env in solve_body(&r.body, &by_pred) {
                let inst = apply(&r.head, &env);
                closure.insert(inst);
            }
        }
        if closure.len() == before {
            break;
        }
    }
    for r in &usable {
        let (_, args) = parse_term(&r.head);
        if args.iter().any(|a| a.contains('(')) {
            skipped.push((*r).clone());
        }
    }
    (closure, skipped)
}

pub fn group_by_predicate(closure: &HashSet<Atom>) -> HashMap<String, Vec<Atom>> {
    let mut m: HashMap<String, Vec<Atom>> = HashMap::new();
    for a in closure {
        let (n, args) = parse_term(a);
        m.entry(format!("{n}/{}", args.len()))
            .or_default()
            .push(a.clone());
    }
    m
}

/// Extract a rule list from an engine `Program` by rendering it. This keeps the
/// reference independent of the engine's IR: it sees only text.
pub fn rules_from_source(src: &str) -> Vec<RefRule> {
    let parsed = axiom::exterior::parse(src).expect("reference needs a parseable program");
    let prog = parsed.program;
    let mut out = Vec::new();
    for r in &prog.rules {
        let head = prog.store.show(r.head, &prog.symbols);
        let body = r
            .body
            .iter()
            .map(|l| (l.pos, prog.store.show(l.atom, &prog.symbols)))
            .collect();
        out.push(RefRule {
            head,
            body,
            backward_only: r.backward_only,
        });
    }
    out
}
