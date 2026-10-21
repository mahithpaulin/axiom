//! Fair, bounded given-clause resolution with factoring.
//!
//! The search is intentionally conservative: it returns `Saturated` when no new
//! clauses can be generated and `Limit` when a deterministic cap is reached.
//! Neither is reported as a refutation. Only an empty clause, checked by the
//! kernel, yields `Proved`.

use axiom::Budget;
use axiom_proof::{unify_atoms, Clause, Literal, ProofClause, ResolutionProof, StepRule, Subst};
use std::collections::{BTreeSet, HashSet};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SearchStatus {
    Proved,
    Saturated,
    Limit(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SearchResult {
    pub proof: Option<ResolutionProof>,
    pub status: SearchStatus,
    pub selected: u64,
    pub generated: u64,
}

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub max_clauses: usize,
    pub max_selected: usize,
    pub max_generated: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            max_clauses: 4096,
            max_selected: 2048,
            max_generated: 8192,
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

fn subsumes(a: &Clause, b: &Clause) -> bool {
    a.literals.iter().all(|l| b.literals.contains(l))
}

fn factor(parent: &Clause, first: usize, second: usize) -> Option<Clause> {
    let a = parent.literals.get(first)?;
    let b = parent.literals.get(second)?;
    if a.positive != b.positive {
        return None;
    }
    let subst = unify_atoms(&a.atom, &b.atom)?;
    Some(Clause::new(
        parent.literals.iter().map(|l| l.apply(&subst)).collect(),
    ))
}

fn resolve(
    left: &Clause,
    right: &Clause,
    left_lit: usize,
    right_lit: usize,
) -> Option<(Clause, Subst)> {
    let ll = left.literals.get(left_lit)?;
    let rl = right.literals.get(right_lit)?;
    if ll.positive == rl.positive {
        return None;
    }
    let subst = unify_atoms(&ll.atom, &rl.atom)?;
    let mut literals: Vec<Literal> = Vec::new();
    for (i, l) in left.literals.iter().enumerate() {
        if i != left_lit {
            literals.push(l.apply(&subst));
        }
    }
    for (i, l) in right.literals.iter().enumerate() {
        if i != right_lit {
            literals.push(l.apply(&subst));
        }
    }
    Some((Clause::new(literals), subst))
}

pub fn search(input: Vec<Clause>, budget: &mut Budget, limits: Limits) -> SearchResult {
    let mut proof = ResolutionProof {
        clauses: input
            .iter()
            .cloned()
            .map(|clause| ProofClause {
                clause,
                rule: StepRule::Input,
            })
            .collect(),
    };
    let mut selected = 0u64;
    let mut generated = 0u64;

    // An empty input clause is already a refutation. Put it last so the proof
    // contract (last clause is empty) holds.
    if let Some(empty) = input.iter().find(|c| c.is_empty()).cloned() {
        proof.clauses = vec![ProofClause {
            clause: empty,
            rule: StepRule::Input,
        }];
        return SearchResult {
            proof: Some(proof),
            status: SearchStatus::Proved,
            selected,
            generated,
        };
    }

    let mut seen: HashSet<Clause> = input.iter().cloned().collect();
    let mut passive: BTreeSet<(usize, usize)> = proof
        .clauses
        .iter()
        .enumerate()
        .map(|(i, c)| (c.clause.literals.len(), i))
        .collect();
    let mut active: Vec<usize> = Vec::new();
    let mut all: Vec<Clause> = input;

    loop {
        if passive.is_empty() {
            return SearchResult {
                proof: None,
                status: SearchStatus::Saturated,
                selected,
                generated,
            };
        }
        if selected as usize >= limits.max_selected {
            return SearchResult {
                proof: None,
                status: SearchStatus::Limit(format!(
                    "selected clause cap {} reached",
                    limits.max_selected
                )),
                selected,
                generated,
            };
        }
        let (_, current) = passive.pop_first().expect("passive is non-empty");
        selected += 1;
        if budget.charge(1).is_err() {
            return SearchResult {
                proof: None,
                status: SearchStatus::Limit("proof budget exhausted".into()),
                selected,
                generated,
            };
        }

        let current_clause = proof.clauses[current].clause.clone();
        if current_clause.is_empty() {
            return SearchResult {
                proof: Some(proof),
                status: SearchStatus::Proved,
                selected,
                generated,
            };
        }

        // Factoring the selected clause.
        for i in 0..current_clause.literals.len() {
            for j in (i + 1)..current_clause.literals.len() {
                let Some(c) = factor(&current_clause, i, j) else {
                    continue;
                };
                if c == current_clause || c.is_empty() || is_tautology(&c) {
                    continue;
                }
                if seen.contains(&c) || all.iter().any(|x| subsumes(x, &c)) {
                    continue;
                }
                if proof.clauses.len() >= limits.max_clauses
                    || generated as usize >= limits.max_generated
                {
                    return SearchResult {
                        proof: None,
                        status: SearchStatus::Limit("generated clause cap reached".into()),
                        selected,
                        generated,
                    };
                }
                if budget.charge(1).is_err() {
                    return SearchResult {
                        proof: None,
                        status: SearchStatus::Limit("proof budget exhausted".into()),
                        selected,
                        generated,
                    };
                }
                generated += 1;
                seen.insert(c.clone());
                all.push(c.clone());
                proof.clauses.push(ProofClause {
                    clause: c,
                    rule: StepRule::Factor {
                        parent: current,
                        first: i,
                        second: j,
                    },
                });
                let id = proof.clauses.len() - 1;
                passive.insert((proof.clauses[id].clause.literals.len(), id));
            }
        }

        // Binary resolution against every active clause.
        for &other in &active {
            let other_clause = proof.clauses[other].clause.clone();
            for i in 0..current_clause.literals.len() {
                for j in 0..other_clause.literals.len() {
                    let Some((c, _)) = resolve(&current_clause, &other_clause, i, j) else {
                        continue;
                    };
                    if c.is_empty() {
                        if proof.clauses.len() >= limits.max_clauses {
                            return SearchResult {
                                proof: None,
                                status: SearchStatus::Limit("generated clause cap reached".into()),
                                selected,
                                generated,
                            };
                        }
                        generated += 1;
                        proof.clauses.push(ProofClause {
                            clause: c,
                            rule: StepRule::Resolve {
                                left: current,
                                right: other,
                                left_lit: i,
                                right_lit: j,
                            },
                        });
                        return SearchResult {
                            proof: Some(proof),
                            status: SearchStatus::Proved,
                            selected,
                            generated,
                        };
                    }
                    if is_tautology(&c) || seen.contains(&c) {
                        continue;
                    }
                    if all.iter().any(|x| subsumes(x, &c)) {
                        continue;
                    }
                    if proof.clauses.len() >= limits.max_clauses
                        || generated as usize >= limits.max_generated
                    {
                        return SearchResult {
                            proof: None,
                            status: SearchStatus::Limit("generated clause cap reached".into()),
                            selected,
                            generated,
                        };
                    }
                    if budget.charge(1).is_err() {
                        return SearchResult {
                            proof: None,
                            status: SearchStatus::Limit("proof budget exhausted".into()),
                            selected,
                            generated,
                        };
                    }
                    generated += 1;
                    seen.insert(c.clone());
                    all.push(c.clone());
                    proof.clauses.push(ProofClause {
                        clause: c,
                        rule: StepRule::Resolve {
                            left: current,
                            right: other,
                            left_lit: i,
                            right_lit: j,
                        },
                    });
                    let id = proof.clauses.len() - 1;
                    passive.insert((proof.clauses[id].clause.literals.len(), id));
                }
            }
        }

        active.push(current);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axiom_proof::{check_resolution, Atom, Term};

    fn atom(name: &str) -> Atom {
        Atom::new(name, vec![Term::constant("a")])
    }

    fn pos(name: &str) -> Literal {
        Literal::positive(atom(name))
    }

    fn neg(name: &str) -> Literal {
        Literal::negative(atom(name))
    }

    #[test]
    fn modus_ponens_is_proved_and_checked() {
        let input = vec![
            Clause::new(vec![neg("P"), pos("Q")]),
            Clause::new(vec![pos("P")]),
            Clause::new(vec![neg("Q")]),
        ];
        let mut budget = Budget::steps(100_000);
        let r = search(input, &mut budget, Limits::default());
        assert_eq!(r.status, SearchStatus::Proved);
        check_resolution(r.proof.as_ref().unwrap()).unwrap();
    }

    #[test]
    fn satisfiable_problem_does_not_claim_a_refutation() {
        let input = vec![Clause::new(vec![pos("P")])];
        let mut budget = Budget::steps(100_000);
        let r = search(input, &mut budget, Limits::default());
        assert_ne!(r.status, SearchStatus::Proved);
        assert!(r.proof.is_none());
    }

    #[test]
    fn equality_style_factoring_is_searched() {
        // P(x) | P(a), !P(a)  -> refutation needs factoring.
        let x = Term::var("x");
        let input = vec![
            Clause::new(vec![Literal::positive(Atom::new("P", vec![x])), pos("P")]),
            Clause::new(vec![neg("P")]),
        ];
        let mut budget = Budget::steps(100_000);
        let r = search(input, &mut budget, Limits::default());
        assert_eq!(r.status, SearchStatus::Proved);
        check_resolution(r.proof.as_ref().unwrap()).unwrap();
    }

    #[test]
    fn budget_exhaustion_is_not_proved() {
        let input = vec![
            Clause::new(vec![neg("P"), pos("Q")]),
            Clause::new(vec![pos("P")]),
            Clause::new(vec![neg("Q")]),
        ];
        let mut budget = Budget::steps(0);
        let r = search(input, &mut budget, Limits::default());
        assert_eq!(
            r.status,
            SearchStatus::Limit("proof budget exhausted".into())
        );
        assert!(r.proof.is_none());
    }
}
