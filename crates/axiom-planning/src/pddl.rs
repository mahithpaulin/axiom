//! A small, untyped STRIPS PDDL fragment.
//!
//! Supported: `:strips`, `:negative-preconditions`, predicates, actions with
//! parameter lists, conjunctive preconditions and add/delete effects, `:objects`
//! (and domain `:constants`), `:init`, and conjunctive goals.
//!
//! Rejected explicitly: typing, equality, numeric fluents, conditional effects,
//! quantified goals, disjunctive goals, and action costs. Rejecting is better
//! than silently changing the semantics.

use axiom_ir::Sexp;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FAtom {
    pub predicate: String,
    pub args: Vec<String>,
}

impl FAtom {
    pub fn new(predicate: impl Into<String>, args: Vec<String>) -> Self {
        FAtom {
            predicate: predicate.into(),
            args,
        }
    }
}

impl fmt::Display for FAtom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.predicate)?;
        for (i, a) in self.args.iter().enumerate() {
            if i > 0 {
                f.write_str(",")?;
            }
            f.write_str(a)?;
        }
        f.write_str(")")
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Arg {
    Var(String),
    Const(String),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PLiteral {
    pub positive: bool,
    pub atom: FAtom,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PddlError {
    Malformed(String),
    Unsupported(String),
    Limit(String),
}

impl fmt::Display for PddlError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PddlError::Malformed(m) => f.write_str(m),
            PddlError::Unsupported(m) => write!(f, "unsupported PDDL fragment: {m}"),
            PddlError::Limit(m) => f.write_str(m),
        }
    }
}

impl std::error::Error for PddlError {}

fn bad(m: impl Into<String>) -> PddlError {
    PddlError::Malformed(m.into())
}

fn unsupported(m: impl Into<String>) -> PddlError {
    PddlError::Unsupported(m.into())
}

fn list<'a>(s: &'a Sexp, what: &str) -> Result<&'a [Sexp], PddlError> {
    s.as_list()
        .ok_or_else(|| bad(format!("expected a list for {what}")))
}

fn atom<'a>(s: &'a Sexp, what: &str) -> Result<&'a str, PddlError> {
    s.as_atom()
        .ok_or_else(|| bad(format!("expected an atom for {what}")))
}

fn head<'a>(xs: &'a [Sexp], what: &str) -> Result<&'a str, PddlError> {
    xs.first()
        .and_then(Sexp::as_atom)
        .ok_or_else(|| bad(format!("missing {what}")))
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Action {
    pub name: String,
    pub params: Vec<String>,
    pub preconditions: Vec<PLiteral>,
    pub adds: Vec<FAtom>,
    pub dels: Vec<FAtom>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Domain {
    pub name: String,
    pub predicates: BTreeMap<String, usize>,
    pub constants: BTreeSet<String>,
    pub actions: Vec<Action>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Problem {
    pub name: String,
    pub domain: String,
    pub objects: BTreeSet<String>,
    pub init: BTreeSet<FAtom>,
    pub goal: Vec<PLiteral>,
}

fn untyped_names(xs: &[Sexp], what: &str) -> Result<Vec<String>, PddlError> {
    let mut out = Vec::new();
    for x in xs {
        let name = atom(x, what)?;
        if name == "-" || name == ":" || name.starts_with(':') {
            return Err(unsupported(format!(
                "typed/unexpected token {name:?} in {what}"
            )));
        }
        out.push(name.to_string());
    }
    Ok(out)
}

fn parse_predicates(s: &Sexp) -> Result<BTreeMap<String, usize>, PddlError> {
    let xs = list(s, ":predicates")?;
    let mut out = BTreeMap::new();
    for p in xs {
        let ps = list(p, "predicate declaration")?;
        let name = head(ps, "predicate name")?.to_string();
        if name.starts_with(':') {
            return Err(bad(format!("bad predicate name {name}")));
        }
        let mut arity = 0;
        for a in &ps[1..] {
            let v = atom(a, "predicate parameter")?;
            if v == "-" {
                return Err(unsupported("typed predicates"));
            }
            if !v.starts_with('?') {
                return Err(bad(format!(
                    "predicate parameter {v:?} must start with '?'"
                )));
            }
            arity += 1;
        }
        if let Some(&old) = out.get(&name) {
            if old != arity {
                return Err(bad(format!("predicate {name} declared with two arities")));
            }
        } else {
            out.insert(name, arity);
        }
    }
    Ok(out)
}

fn parse_atom(
    s: &Sexp,
    preds: &BTreeMap<String, usize>,
    params: Option<&BTreeSet<String>>,
) -> Result<FAtom, PddlError> {
    let xs = list(s, "atom")?;
    let pred = head(xs, "predicate")?;
    if pred == "=" {
        return Err(unsupported("equality is not supported"));
    }
    let arity = *preds
        .get(pred)
        .ok_or_else(|| bad(format!("undeclared predicate {pred}")))?;
    if xs.len() != arity + 1 {
        return Err(bad(format!(
            "predicate {pred} expects {arity} arguments, found {}",
            xs.len() - 1
        )));
    }
    let mut args = Vec::new();
    for a in &xs[1..] {
        let v = atom(a, "atom argument")?;
        if v.starts_with('?') {
            if !params.map(|p| p.contains(v)).unwrap_or(false) {
                return Err(bad(format!("unbound variable {v} in atom {pred}")));
            }
            args.push(v.to_string());
        } else {
            args.push(v.to_string());
        }
    }
    Ok(FAtom::new(pred, args))
}

fn parse_literal(
    s: &Sexp,
    preds: &BTreeMap<String, usize>,
    params: Option<&BTreeSet<String>>,
) -> Result<PLiteral, PddlError> {
    let xs = list(s, "literal")?;
    if xs.first().and_then(Sexp::as_atom) == Some("not") {
        if xs.len() != 2 {
            return Err(bad("not takes exactly one atom"));
        }
        return Ok(PLiteral {
            positive: false,
            atom: parse_atom(&xs[1], preds, params)?,
        });
    }
    Ok(PLiteral {
        positive: true,
        atom: parse_atom(s, preds, params)?,
    })
}

fn parse_gd(
    s: &Sexp,
    preds: &BTreeMap<String, usize>,
    params: Option<&BTreeSet<String>>,
) -> Result<Vec<PLiteral>, PddlError> {
    let xs = list(s, "goal description")?;
    let tag = head(xs, "goal description")?;
    match tag {
        "and" => {
            let mut out = Vec::new();
            for x in &xs[1..] {
                out.extend(parse_gd(x, preds, params)?);
            }
            Ok(out)
        }
        "or" | "exists" | "forall" | "imply" | "when" => {
            Err(unsupported(format!("{tag} in a precondition/goal")))
        }
        _ => Ok(vec![parse_literal(s, preds, params)?]),
    }
}

fn parse_effects(
    s: &Sexp,
    preds: &BTreeMap<String, usize>,
    params: Option<&BTreeSet<String>>,
) -> Result<(Vec<FAtom>, Vec<FAtom>), PddlError> {
    let xs = list(s, "effect")?;
    let tag = head(xs, "effect")?;
    let mut adds = Vec::new();
    let mut dels = Vec::new();
    match tag {
        "and" => {
            for x in &xs[1..] {
                let (a, d) = parse_effects(x, preds, params)?;
                adds.extend(a);
                dels.extend(d);
            }
        }
        "when" | "forall" | "exists" => {
            return Err(unsupported(format!("{tag} effect")));
        }
        "not" => {
            if xs.len() != 2 {
                return Err(bad("negative effect takes one atom"));
            }
            dels.push(parse_atom(&xs[1], preds, params)?);
        }
        _ => adds.push(parse_atom(s, preds, params)?),
    }
    Ok((adds, dels))
}

fn parse_params(s: &Sexp) -> Result<Vec<String>, PddlError> {
    let xs = list(s, ":parameters")?;
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();
    for x in xs {
        let name = atom(x, "parameter")?;
        if name == "-" {
            return Err(unsupported("typed action parameters"));
        }
        if !name.starts_with('?') {
            return Err(bad(format!(
                "action parameter {name:?} must start with '?'"
            )));
        }
        if !seen.insert(name.to_string()) {
            return Err(bad(format!("duplicate action parameter {name}")));
        }
        out.push(name.to_string());
    }
    Ok(out)
}

fn parse_action(s: &Sexp, preds: &BTreeMap<String, usize>) -> Result<Action, PddlError> {
    let xs = list(s, "action")?;
    if head(xs, "action tag")? != ":action" {
        return Err(bad("expected (:action ...)"));
    }
    let name = xs
        .get(1)
        .ok_or_else(|| bad("action has no name"))
        .and_then(|x| atom(x, "action name"))?
        .to_string();
    let mut params = Vec::new();
    let mut preconditions = Vec::new();
    let mut adds = Vec::new();
    let mut dels = Vec::new();
    let mut seen_effect = false;
    let mut i = 2;
    while i < xs.len() {
        let key = atom(&xs[i], "action field")?;
        let val = xs
            .get(i + 1)
            .ok_or_else(|| bad(format!("action field {key} has no value")))?;
        match key {
            ":parameters" => params = parse_params(val)?,
            ":precondition" => {
                let set: BTreeSet<String> = params.iter().cloned().collect();
                preconditions = parse_gd(val, preds, Some(&set))?;
            }
            ":effect" => {
                let set: BTreeSet<String> = params.iter().cloned().collect();
                let (a, d) = parse_effects(val, preds, Some(&set))?;
                adds = a;
                dels = d;
                seen_effect = true;
            }
            other => return Err(unsupported(format!("action field {other}"))),
        }
        i += 2;
    }
    if !seen_effect {
        return Err(bad(format!("action {name} has no :effect")));
    }
    for a in &adds {
        if dels.contains(a) {
            return Err(bad(format!("action {name} both adds and deletes {}", a)));
        }
    }
    Ok(Action {
        name,
        params,
        preconditions,
        adds,
        dels,
    })
}

pub fn parse_domain(input: &str) -> Result<Domain, PddlError> {
    let root = Sexp::parse(input).map_err(|e| bad(e.to_string()))?;
    let xs = list(&root, "domain")?;
    if head(xs, "domain")? != "define" {
        return Err(bad("domain must start with (define ...)"));
    }
    let header = xs
        .get(1)
        .ok_or_else(|| bad("domain has no header"))
        .and_then(|x| list(x, "domain header"))?;
    if head(header, "domain header")? != "domain" {
        return Err(bad("missing (domain name) header"));
    }
    let name = header
        .get(1)
        .ok_or_else(|| bad("domain has no name"))
        .and_then(|x| atom(x, "domain name"))?
        .to_string();

    let mut predicates = BTreeMap::new();
    let mut constants = BTreeSet::new();
    let mut actions = Vec::new();
    for field in &xs[2..] {
        let fs = list(field, "domain field")?;
        let key = head(fs, "domain field")?;
        match key {
            ":requirements" => {
                for r in &fs[1..] {
                    let r = atom(r, "requirement")?;
                    match r {
                        ":strips" | ":negative-preconditions" => {}
                        ":typing" => return Err(unsupported("typed PDDL")),
                        other => return Err(unsupported(format!("requirement {other}"))),
                    }
                }
            }
            ":types" => return Err(unsupported("typed PDDL")),
            ":predicates" => predicates = parse_predicates(&Sexp::List(fs[1..].to_vec()))?,
            ":constants" => {
                for n in untyped_names(&fs[1..], "constant")? {
                    constants.insert(n);
                }
            }
            ":action" => actions.push(parse_action(field, &predicates)?),
            other => return Err(unsupported(format!("domain field {other}"))),
        }
    }
    Ok(Domain {
        name,
        predicates,
        constants,
        actions,
    })
}

fn parse_problem_with(input: &str, preds: &BTreeMap<String, usize>) -> Result<Problem, PddlError> {
    let root = Sexp::parse(input).map_err(|e| bad(e.to_string()))?;
    let xs = list(&root, "problem")?;
    if head(xs, "problem")? != "define" {
        return Err(bad("problem must start with (define ...)"));
    }
    let header = xs
        .get(1)
        .ok_or_else(|| bad("problem has no header"))
        .and_then(|x| list(x, "problem header"))?;
    if head(header, "problem header")? != "problem" {
        return Err(bad("missing (problem name) header"));
    }
    let name = header
        .get(1)
        .ok_or_else(|| bad("problem has no name"))
        .and_then(|x| atom(x, "problem name"))?
        .to_string();

    let mut domain = String::new();
    let mut objects = BTreeSet::new();
    let mut init = BTreeSet::new();
    let mut goal = Vec::new();
    let mut has_goal = false;
    for field in &xs[2..] {
        let fs = list(field, "problem field")?;
        let key = head(fs, "problem field")?;
        match key {
            ":domain" => {
                domain = fs
                    .get(1)
                    .ok_or_else(|| bad(":domain has no value"))
                    .and_then(|x| atom(x, "domain name"))?
                    .to_string();
            }
            ":objects" => {
                for n in untyped_names(&fs[1..], "object")? {
                    objects.insert(n);
                }
            }
            ":init" => {
                for a in &fs[1..] {
                    let atom = parse_atom(a, preds, None)?;
                    init.insert(atom);
                }
            }
            ":goal" => {
                has_goal = true;
                let val = fs.get(1).ok_or_else(|| bad(":goal has no value"))?;
                goal = parse_gd(val, preds, None)?;
            }
            other => return Err(unsupported(format!("problem field {other}"))),
        }
    }
    if !has_goal {
        return Err(bad("problem has no :goal"));
    }
    Ok(Problem {
        name,
        domain,
        objects,
        init,
        goal,
    })
}

/// Parse a problem against a domain so predicates, arities, objects and the goal
/// are checked together. `parse_problem` intentionally stays domain-free; this
/// function is the checked entry point used by the engine.
pub fn parse_task(domain_src: &str, problem_src: &str) -> Result<PlanningTask, PddlError> {
    let domain = parse_domain(domain_src)?;
    let problem = parse_problem_with(problem_src, &domain.predicates)?;
    if !problem.domain.is_empty() && problem.domain != domain.name {
        return Err(bad(format!(
            "problem names domain {}, but domain is {}",
            problem.domain, domain.name
        )));
    }
    let mut objects = domain.constants.clone();
    objects.extend(problem.objects.iter().cloned());
    for a in &problem.init {
        for arg in &a.args {
            if !objects.contains(arg) {
                return Err(bad(format!("init atom {a} uses unknown object {arg}")));
            }
        }
    }
    for l in &problem.goal {
        for arg in &l.atom.args {
            if !objects.contains(arg) {
                return Err(bad(format!(
                    "goal atom {} uses unknown object {arg}",
                    l.atom
                )));
            }
        }
    }
    for action in &domain.actions {
        for l in &action.preconditions {
            for arg in &l.atom.args {
                if !arg.starts_with('?') && !objects.contains(arg) {
                    return Err(bad(format!(
                        "action {} uses unknown object constant {arg}",
                        action.name
                    )));
                }
            }
        }
        for a in action.adds.iter().chain(action.dels.iter()) {
            for arg in &a.args {
                if !arg.starts_with('?') && !objects.contains(arg) {
                    return Err(bad(format!(
                        "action {} uses unknown object constant {arg}",
                        action.name
                    )));
                }
            }
        }
    }
    Ok(PlanningTask {
        domain,
        problem,
        objects,
        init: problem.init.clone(),
        goal: problem.goal.clone(),
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlanningTask {
    pub domain: Domain,
    pub problem: Problem,
    pub objects: BTreeSet<String>,
    pub init: BTreeSet<FAtom>,
    pub goal: Vec<PLiteral>,
}

#[cfg(test)]
mod tests {
    use super::*;

    const DOMAIN: &str = r#"
        (define (domain move)
          (:requirements :strips :negative-preconditions)
          (:predicates (at ?x ?y) (connected ?x ?y))
          (:constants item)
          (:action move
            :parameters (?from ?to)
            :precondition (and (at item ?from) (connected ?from ?to))
            :effect (and (not (at item ?from)) (at item ?to))))
    "#;

    const PROBLEM: &str = r#"
        (define (problem p)
          (:domain move)
          (:objects a b)
          (:init (at item a) (connected a b))
          (:goal (at item b)))
    "#;

    #[test]
    fn parses_untyped_strips() {
        let task = parse_task(DOMAIN, PROBLEM).unwrap();
        assert_eq!(task.domain.actions.len(), 1);
        assert_eq!(task.goal.len(), 1);
        assert!(task.objects.contains("a"));
    }

    #[test]
    fn typing_is_rejected() {
        let d = "(define (domain d) (:requirements :typing) (:predicates (p ?x)))";
        assert!(matches!(parse_domain(d), Err(PddlError::Unsupported(_))));
    }

    #[test]
    fn missing_goal_is_an_error() {
        let p = "(define (problem p) (:domain move) (:objects a))";
        assert!(parse_task(DOMAIN, p).is_err());
    }
}
