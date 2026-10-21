//! Finite grounding over the Herbrand universe of constants.
//!
//! The implementation is intentionally unsophisticated: every safe variable is
//! assigned every constant, and each resulting ground rule is retained. A real
//! ASP grounder performs joins, projection and simplification; this one is
//! correct for the finite fragment and bounded in work, not competitive.

use crate::syntax::{Atom, Literal, Program, Statement, Term};
use axiom::Budget;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// Hard caps that keep a hostile or accidental input from allocating without
/// bound. Exceeding them is a resource result, never a partial model.
pub const MAX_GROUND_RULES: usize = 200_000;
pub const MAX_UNIVERSE: usize = 22;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GAtom {
    pub predicate: String,
    pub args: Vec<String>,
}

impl GAtom {
    pub fn new(predicate: impl Into<String>, args: Vec<String>) -> Self {
        GAtom {
            predicate: predicate.into(),
            args,
        }
    }
}

impl fmt::Display for GAtom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.args.is_empty() {
            return f.write_str(&self.predicate);
        }
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

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GLit {
    pub negated: bool,
    pub atom: GAtom,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RuleKind {
    Normal,
    Choice,
    Constraint,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GroundRule {
    pub kind: RuleKind,
    pub heads: Vec<GAtom>,
    pub body: Vec<GLit>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct GroundProgram {
    pub facts: BTreeSet<GAtom>,
    pub rules: Vec<GroundRule>,
    pub universe: BTreeSet<GAtom>,
    pub constants: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GroundError {
    Limit(String),
    Budget(String),
    Unsafe(String),
}

impl fmt::Display for GroundError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GroundError::Limit(m) => write!(f, "grounding limit: {m}"),
            GroundError::Budget(m) => write!(f, "grounding stopped: {m}"),
            GroundError::Unsafe(m) => write!(f, "unsafe program: {m}"),
        }
    }
}

impl std::error::Error for GroundError {}

#[derive(Clone, Default)]
struct Assignment(BTreeMap<String, String>);

impl Assignment {
    fn term(&self, t: &Term) -> Result<String, GroundError> {
        match t {
            Term::Const(c) => Ok(c.clone()),
            Term::Var(v) => self
                .0
                .get(v)
                .cloned()
                .ok_or_else(|| GroundError::Unsafe(format!("unbound variable {v}"))),
        }
    }

    fn atom(&self, a: &Atom) -> Result<GAtom, GroundError> {
        let args = a
            .args
            .iter()
            .map(|t| self.term(t))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(GAtom::new(a.predicate.clone(), args))
    }

    fn literal(&self, l: &Literal) -> Result<GLit, GroundError> {
        Ok(GLit {
            negated: l.negated,
            atom: self.atom(&l.atom)?,
        })
    }
}

fn collect_constants(program: &Program) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut collect_atom = |a: &Atom| {
        for t in &a.args {
            if let Term::Const(c) = t {
                out.insert(c.clone());
            }
        }
    };
    for stmt in &program.statements {
        match stmt {
            Statement::Fact(a) => collect_atom(a),
            Statement::Rule(r) => {
                collect_atom(&r.head);
                for l in &r.body {
                    collect_atom(&l.atom);
                }
            }
            Statement::Choice(c) => {
                for h in &c.heads {
                    collect_atom(h);
                }
                for l in &c.body {
                    collect_atom(&l.atom);
                }
            }
            Statement::Constraint(b) => {
                for l in b {
                    collect_atom(&l.atom);
                }
            }
        }
    }
    out
}

fn variables_in(atom: &Atom) -> BTreeSet<String> {
    atom.variables()
}

fn variables_of_stmt(stmt: &Statement) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    match stmt {
        Statement::Fact(a) => out.extend(variables_in(a)),
        Statement::Rule(r) => {
            out.extend(variables_in(&r.head));
            for l in &r.body {
                out.extend(variables_in(&l.atom));
            }
        }
        Statement::Choice(c) => {
            for h in &c.heads {
                out.extend(variables_in(h));
            }
            for l in &c.body {
                out.extend(variables_in(&l.atom));
            }
        }
        Statement::Constraint(b) => {
            for l in b {
                out.extend(variables_in(&l.atom));
            }
        }
    }
    out
}

fn check_safe_ground(stmt: &Statement, vars: &BTreeSet<String>) -> Result<(), GroundError> {
    let (heads, body): (Vec<&Atom>, &[Literal]) = match stmt {
        Statement::Fact(_) => return Ok(()),
        Statement::Rule(r) => (vec![&r.head], &r.body),
        Statement::Choice(c) => (c.heads.iter().collect(), &c.body),
        Statement::Constraint(b) => (Vec::new(), b),
    };
    let mut positive = BTreeSet::new();
    for l in body {
        if !l.negated {
            positive.extend(l.atom.variables());
        }
    }
    for h in heads {
        for v in h.variables() {
            if !positive.contains(&v) && vars.contains(&v) {
                return Err(GroundError::Unsafe(format!(
                    "head variable {v} has no positive binding"
                )));
            }
        }
    }
    for l in body {
        if l.negated {
            for v in l.atom.variables() {
                if !positive.contains(&v) {
                    return Err(GroundError::Unsafe(format!(
                        "negative variable {v} has no positive binding"
                    )));
                }
            }
        }
    }
    Ok(())
}

fn for_each_assignment<F>(
    vars: &[String],
    constants: &[String],
    budget: &mut Budget,
    f: &mut F,
) -> Result<(), GroundError>
where
    F: FnMut(&Assignment) -> Result<bool, GroundError>,
{
    fn go<F>(
        vars: &[String],
        constants: &[String],
        depth: usize,
        current: &mut Assignment,
        budget: &mut Budget,
        f: &mut F,
    ) -> Result<bool, GroundError>
    where
        F: FnMut(&Assignment) -> Result<bool, GroundError>,
    {
        if depth == vars.len() {
            budget
                .charge(1)
                .map_err(|e| GroundError::Budget(e.to_string()))?;
            return f(current);
        }
        for c in constants {
            current.0.insert(vars[depth].clone(), c.clone());
            if !go(vars, constants, depth + 1, current, budget, f)? {
                return Ok(false);
            }
        }
        current.0.remove(&vars[depth]);
        Ok(true)
    }
    if vars.is_empty() {
        budget
            .charge(1)
            .map_err(|e| GroundError::Budget(e.to_string()))?;
        let empty = Assignment::default();
        f(&empty)?;
        return Ok(());
    }
    let mut current = Assignment::default();
    go(vars, constants, 0, &mut current, budget, f)?;
    Ok(())
}

/// Ground every statement over `constants`.
pub fn ground(program: &Program, budget: &mut Budget) -> Result<GroundProgram, GroundError> {
    let constants_set = collect_constants(program);
    let constants: Vec<String> = constants_set.iter().cloned().collect();
    let mut facts = BTreeSet::new();
    let mut rules: BTreeSet<GroundRule> = BTreeSet::new();
    for stmt in &program.statements {
        let vars = variables_of_stmt(stmt);
        check_safe_ground(stmt, &vars)?;
        let ordered: Vec<String> = vars.into_iter().collect();
        for_each_assignment(&ordered, &constants, budget, &mut |asg| {
            match stmt {
                Statement::Fact(a) => {
                    facts.insert(asg.atom(a)?);
                }
                Statement::Rule(r) => {
                    let head = asg.atom(&r.head)?;
                    let body = r
                        .body
                        .iter()
                        .map(|l| asg.literal(l))
                        .collect::<Result<Vec<_>, _>>()?;
                    rules.insert(GroundRule {
                        kind: RuleKind::Normal,
                        heads: vec![head],
                        body,
                    });
                }
                Statement::Choice(c) => {
                    let heads = c
                        .heads
                        .iter()
                        .map(|h| asg.atom(h))
                        .collect::<Result<Vec<_>, _>>()?;
                    let body = c
                        .body
                        .iter()
                        .map(|l| asg.literal(l))
                        .collect::<Result<Vec<_>, _>>()?;
                    rules.insert(GroundRule {
                        kind: RuleKind::Choice,
                        heads,
                        body,
                    });
                }
                Statement::Constraint(b) => {
                    let body = b
                        .iter()
                        .map(|l| asg.literal(l))
                        .collect::<Result<Vec<_>, _>>()?;
                    rules.insert(GroundRule {
                        kind: RuleKind::Constraint,
                        heads: Vec::new(),
                        body,
                    });
                }
            }
            if rules.len() > MAX_GROUND_RULES {
                return Err(GroundError::Limit(format!(
                    "more than {MAX_GROUND_RULES} ground rules"
                )));
            }
            Ok(true)
        })?;
    }
    let mut universe = BTreeSet::new();
    universe.extend(facts.iter().cloned());
    for r in &rules {
        universe.extend(r.heads.iter().cloned());
        for l in &r.body {
            universe.insert(l.atom.clone());
        }
    }
    if universe.len() > MAX_UNIVERSE {
        return Err(GroundError::Limit(format!(
            "ground universe has {} atoms; exhaustive enumeration is capped at {MAX_UNIVERSE}",
            universe.len()
        )));
    }
    Ok(GroundProgram {
        facts,
        rules: rules.into_iter().collect(),
        universe,
        constants: constants_set,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax;

    fn gp(src: &str) -> GroundProgram {
        let p = syntax::parse(src).unwrap();
        ground(&p, &mut Budget::steps(1_000_000)).unwrap()
    }

    #[test]
    fn safe_variables_are_grounded_over_constants() {
        let g = gp("dom(a). dom(b). p(X) :- dom(X).");
        assert_eq!(g.facts.len(), 2);
        assert_eq!(
            g.rules
                .iter()
                .filter(|r| r.kind == RuleKind::Normal)
                .count(),
            2
        );
    }

    #[test]
    fn duplicate_ground_rules_are_removed() {
        let g = gp("dom(a). p(a) :- dom(a). p(a) :- dom(a).");
        assert_eq!(g.rules.len(), 1);
    }

    #[test]
    fn ground_universe_is_bounded() {
        let mut src = String::from("p(a). ");
        for _ in 0..30 {
            src.push_str("q(a). ");
        }
        let p = syntax::parse(&src).unwrap();
        assert!(ground(&p, &mut Budget::steps(1_000_000)).is_err());
    }
}
