//! Negation normal form, Skolemisation, CNF, and clause freshening.
//!
//! This module is prover-side, not kernel-side. The kernel checks the resulting
//! resolution refutation; the transformation from formulas to clauses is part
//! of the prover's trust boundary and is tested on small formulas.

use crate::fol::{FolError, Formula};
use axiom_proof::{Atom, Clause, Literal, Subst, Term};
use std::collections::{BTreeMap, BTreeSet};

const MAX_CLAUSES: usize = 8192;
const MAX_CLAUSE_LITERALS: usize = 512;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CnfError {
    Formula(String),
    TooLarge(String),
    Internal(String),
}

impl std::fmt::Display for CnfError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CnfError::Formula(m) => f.write_str(m),
            CnfError::TooLarge(m) => f.write_str(m),
            CnfError::Internal(m) => f.write_str(m),
        }
    }
}

impl std::error::Error for CnfError {}

impl From<FolError> for CnfError {
    fn from(e: FolError) -> Self {
        CnfError::Formula(e.to_string())
    }
}

fn rename_term(t: &Term, env: &BTreeMap<String, String>) -> Term {
    match t {
        Term::Var(v) => Term::Var(env.get(v).cloned().unwrap_or_else(|| v.clone())),
        Term::Const(_) => t.clone(),
        Term::App(f, args) => Term::App(
            f.clone(),
            args.iter().map(|a| rename_term(a, env)).collect(),
        ),
    }
}

fn rename_atom(a: &Atom, env: &BTreeMap<String, String>) -> Atom {
    Atom::new(
        a.predicate.clone(),
        a.args.iter().map(|t| rename_term(t, env)).collect(),
    )
}

fn eliminate_iff(f: &Formula) -> Formula {
    match f {
        Formula::Iff(a, b) => {
            let a1 = eliminate_iff(a);
            let b1 = eliminate_iff(b);
            Formula::And(vec![
                Formula::Implies(Box::new(a1.clone()), Box::new(b1.clone())),
                Formula::Implies(Box::new(b1), Box::new(a1)),
            ])
        }
        Formula::Not(x) => Formula::Not(Box::new(eliminate_iff(x))),
        Formula::And(xs) => Formula::And(xs.iter().map(eliminate_iff).collect()),
        Formula::Or(xs) => Formula::Or(xs.iter().map(eliminate_iff).collect()),
        Formula::Implies(a, b) => {
            Formula::Implies(Box::new(eliminate_iff(a)), Box::new(eliminate_iff(b)))
        }
        Formula::Forall(v, x) => Formula::Forall(v.clone(), Box::new(eliminate_iff(x))),
        Formula::Exists(v, x) => Formula::Exists(v.clone(), Box::new(eliminate_iff(x))),
        _ => f.clone(),
    }
}

fn nnf(f: &Formula, negated: bool, counter: &mut usize, env: &BTreeMap<String, String>) -> Formula {
    match f {
        Formula::True => {
            if negated {
                Formula::False
            } else {
                Formula::True
            }
        }
        Formula::False => {
            if negated {
                Formula::True
            } else {
                Formula::False
            }
        }
        Formula::Atom(a) => {
            let atom = Formula::Atom(rename_atom(a, env));
            if negated {
                Formula::Not(Box::new(atom))
            } else {
                atom
            }
        }
        Formula::Not(x) => nnf(x, !negated, counter, env),
        Formula::And(xs) => {
            let parts = xs
                .iter()
                .map(|x| nnf(x, negated, counter, env))
                .collect::<Vec<_>>();
            if negated {
                Formula::Or(parts)
            } else {
                Formula::And(parts)
            }
        }
        Formula::Or(xs) => {
            let parts = xs
                .iter()
                .map(|x| nnf(x, negated, counter, env))
                .collect::<Vec<_>>();
            if negated {
                Formula::And(parts)
            } else {
                Formula::Or(parts)
            }
        }
        Formula::Implies(a, b) => {
            // a -> b  ==  !a | b ; its negation is a & !b.
            if negated {
                Formula::And(vec![
                    nnf(a, false, counter, env),
                    nnf(b, true, counter, env),
                ])
            } else {
                Formula::Or(vec![
                    nnf(a, true, counter, env),
                    nnf(b, false, counter, env),
                ])
            }
        }
        Formula::Iff(_, _) => {
            // eliminate_iff runs first; this is an internal invariant.
            let e = eliminate_iff(f);
            nnf(&e, negated, counter, env)
        }
        Formula::Forall(vars, body) | Formula::Exists(vars, body) => {
            let is_forall = matches!(f, Formula::Forall(_, _));
            let mut inner = env.clone();
            let mut fresh = Vec::new();
            for v in vars {
                let name = format!("v{}", *counter);
                *counter += 1;
                inner.insert(v.clone(), name.clone());
                fresh.push(name);
            }
            let body = nnf(body, negated, counter, &inner);
            if is_forall != negated {
                Formula::Forall(fresh, Box::new(body))
            } else {
                Formula::Exists(fresh, Box::new(body))
            }
        }
    }
}

fn subst_term(t: &Term, subst: &Subst) -> Term {
    t.apply(subst)
}

fn subst_formula(f: &Formula, subst: &Subst) -> Formula {
    match f {
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Atom(a) => Formula::Atom(Atom::new(
            a.predicate.clone(),
            a.args.iter().map(|t| subst_term(t, subst)).collect(),
        )),
        Formula::Not(x) => Formula::Not(Box::new(subst_formula(x, subst))),
        Formula::And(xs) => Formula::And(xs.iter().map(|x| subst_formula(x, subst)).collect()),
        Formula::Or(xs) => Formula::Or(xs.iter().map(|x| subst_formula(x, subst)).collect()),
        Formula::Implies(a, b) => Formula::Implies(
            Box::new(subst_formula(a, subst)),
            Box::new(subst_formula(b, subst)),
        ),
        Formula::Iff(a, b) => Formula::Iff(
            Box::new(subst_formula(a, subst)),
            Box::new(subst_formula(b, subst)),
        ),
        Formula::Forall(vars, body) => {
            let mut s = subst.clone();
            for v in vars {
                s.remove(v);
            }
            Formula::Forall(vars.clone(), Box::new(subst_formula(body, &s)))
        }
        Formula::Exists(vars, body) => {
            let mut s = subst.clone();
            for v in vars {
                s.remove(v);
            }
            Formula::Exists(vars.clone(), Box::new(subst_formula(body, &s)))
        }
    }
}

fn skolem(f: &Formula, universals: &[String], counter: &mut usize) -> Formula {
    match f {
        Formula::Forall(vars, body) => {
            let mut u = universals.to_vec();
            u.extend(vars.iter().cloned());
            skolem(body, &u, counter)
        }
        Formula::Exists(vars, body) => {
            let mut subst = Subst::new();
            for v in vars {
                let name = format!("sk{}", *counter);
                *counter += 1;
                let term = if universals.is_empty() {
                    Term::constant(name)
                } else {
                    Term::app(
                        name,
                        universals.iter().map(|u| Term::var(u.clone())).collect(),
                    )
                };
                subst.insert(v.clone(), term);
            }
            let body = subst_formula(body, &subst);
            skolem(&body, universals, counter)
        }
        Formula::And(xs) => {
            Formula::And(xs.iter().map(|x| skolem(x, universals, counter)).collect())
        }
        Formula::Or(xs) => Formula::Or(xs.iter().map(|x| skolem(x, universals, counter)).collect()),
        Formula::Not(x) => Formula::Not(Box::new(skolem(x, universals, counter))),
        Formula::True => Formula::True,
        Formula::False => Formula::False,
        Formula::Atom(_) => f.clone(),
        Formula::Implies(_, _) | Formula::Iff(_, _) => {
            // NNF and eliminate_iff should have removed these.
            Formula::False
        }
    }
}

fn cnf(f: &Formula) -> Result<Vec<Clause>, CnfError> {
    match f {
        Formula::True => Ok(Vec::new()),
        Formula::False => Ok(vec![Clause::empty()]),
        Formula::Atom(a) => Ok(vec![Clause::new(vec![Literal::positive(a.clone())])]),
        Formula::Not(x) => match x.as_ref() {
            Formula::Atom(a) => Ok(vec![Clause::new(vec![Literal::negative(a.clone())])]),
            _ => Err(CnfError::Internal(
                "non-literal negation reached CNF".into(),
            )),
        },
        Formula::And(xs) => {
            let mut out = Vec::new();
            for x in xs {
                out.extend(cnf(x)?);
                if out.len() > MAX_CLAUSES {
                    return Err(CnfError::TooLarge(format!(
                        "CNF exceeds {MAX_CLAUSES} clauses"
                    )));
                }
            }
            Ok(out)
        }
        Formula::Or(xs) => {
            let mut acc: Vec<Vec<Literal>> = vec![Vec::new()];
            for x in xs {
                let child = cnf(x)?;
                let mut next = Vec::new();
                for a in &acc {
                    for b in &child {
                        let mut lits = a.clone();
                        lits.extend(b.literals.iter().cloned());
                        if lits.len() > MAX_CLAUSE_LITERALS {
                            return Err(CnfError::TooLarge(format!(
                                "CNF clause exceeds {MAX_CLAUSE_LITERALS} literals"
                            )));
                        }
                        next.push(lits);
                        if next.len() > MAX_CLAUSES {
                            return Err(CnfError::TooLarge(format!(
                                "CNF exceeds {MAX_CLAUSES} clauses"
                            )));
                        }
                    }
                }
                acc = next;
            }
            Ok(acc.into_iter().map(Clause::new).collect())
        }
        Formula::Forall(_, _) | Formula::Exists(_, _) => {
            Err(CnfError::Internal("quantifier reached CNF".into()))
        }
        Formula::Implies(_, _) | Formula::Iff(_, _) => {
            Err(CnfError::Internal("connective reached CNF".into()))
        }
    }
}

fn is_tautology(c: &Clause) -> bool {
    let mut pos = BTreeSet::new();
    let mut neg = BTreeSet::new();
    for l in &c.literals {
        if l.positive {
            pos.insert(&l.atom);
        } else {
            neg.insert(&l.atom);
        }
    }
    pos.iter().any(|a| neg.contains(a))
}

fn freshen(c: &Clause, index: usize) -> Clause {
    let mut vars = BTreeSet::new();
    for t in c.literals.iter().flat_map(|l| l.atom.args.iter()) {
        t.vars(&mut vars);
    }
    let mut subst = Subst::new();
    for (n, v) in vars.into_iter().enumerate() {
        subst.insert(v, Term::var(format!("x{index}_{n}")));
    }
    Clause::new(c.literals.iter().map(|l| l.apply(&subst)).collect())
}

/// Convert axioms plus the negation of the goal into a freshened clausal form.
/// Tautologies are removed; duplicate clauses are removed.
pub fn clausal_form(axioms: &[Formula], goal: &Formula) -> Result<Vec<Clause>, CnfError> {
    let mut counter = 0usize;
    let mut clauses = Vec::new();
    for f in axioms {
        let f = eliminate_iff(f);
        let f = nnf(&f, false, &mut counter, &BTreeMap::new());
        let f = skolem(&f, &[], &mut counter);
        clauses.extend(cnf(&f)?);
    }
    let f = eliminate_iff(goal);
    let f = Formula::Not(Box::new(f));
    let f = nnf(&f, false, &mut counter, &BTreeMap::new());
    let f = skolem(&f, &[], &mut counter);
    clauses.extend(cnf(&f)?);
    let mut out = Vec::new();
    let mut seen = BTreeSet::new();
    for (i, c) in clauses.into_iter().enumerate() {
        if is_tautology(&c) {
            continue;
        }
        let c = freshen(&c, i);
        if seen.insert(c.clone()) {
            out.push(c);
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fol::parse_formula;

    fn cf(src: &str) -> Vec<Clause> {
        clausal_form(&[], &parse_formula(src).unwrap()).unwrap()
    }

    #[test]
    fn negation_is_pushed() {
        let cs = cf("P(a) & Q(a)");
        // Negation of a conjunction is a disjunction.
        assert_eq!(cs.len(), 1);
        assert_eq!(cs[0].literals.len(), 2);
    }

    #[test]
    fn implication_negation_is_a_conjunction() {
        let cs = cf("P(a) -> Q(a)");
        assert_eq!(cs.len(), 2);
    }

    #[test]
    fn universal_goal_is_negated_to_an_existential_and_skolemised() {
        let cs = cf("forall x. P(x)");
        assert_eq!(cs.len(), 1);
        assert_eq!(cs[0].literals.len(), 1);
        let lit = &cs[0].literals[0];
        assert!(!lit.positive);
        assert!(matches!(&lit.atom.args[0], Term::Const(c) if c.starts_with("sk")));
    }

    #[test]
    fn existential_under_universal_uses_a_skolem_function() {
        let cs = cf("exists y. forall x. P(x, y)");
        assert_eq!(cs.len(), 1);
        assert!(cs[0].literals[0]
            .atom
            .args
            .iter()
            .any(|t| matches!(t, Term::App(_, args) if args.len() == 1)));
    }

    #[test]
    fn clauses_are_freshened() {
        let cs = cf("exists x. P(x) -> Q(x)");
        assert_eq!(cs.len(), 2);
        let vars: Vec<_> = cs
            .iter()
            .flat_map(|c| c.literals.iter())
            .flat_map(|l| l.atom.args.iter())
            .filter_map(|t| match t {
                Term::Var(v) => Some(v.clone()),
                _ => None,
            })
            .collect();
        assert_ne!(vars[0], vars[1]);
    }

    #[test]
    fn tautologies_are_dropped() {
        let axiom = parse_formula("P(a) | not P(a)").unwrap();
        let goal = parse_formula("P(a)").unwrap();
        let cs = clausal_form(&[axiom], &goal).unwrap();
        assert_eq!(cs.len(), 1);
    }
}
