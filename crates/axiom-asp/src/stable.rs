//! Stable-model checking and exhaustive enumeration.
//!
//! The candidate universe is the finite set of ground atoms occurring in the
//! grounded program. Enumeration is exhaustive and therefore complete for that
//! universe, but exponential; callers must supply a budget and the crate caps the
//! universe before enumeration. A result that stops at the model cap is reported
//! as incomplete, not as an exhaustive answer.

use crate::ground::{GAtom, GLit, GroundProgram, RuleKind, MAX_UNIVERSE};
use axiom::Budget;
use std::collections::{BTreeMap, BTreeSet};

/// Upper bound used when the caller asks for "all" models with `max_models = 0`.
pub const DEFAULT_MODEL_CAP: usize = 1024;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EnumError {
    TooLarge(usize),
    Budget(String),
}

impl std::fmt::Display for EnumError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EnumError::TooLarge(n) => write!(
                f,
                "ground universe has {n} atoms; exhaustive enumeration is capped at {MAX_UNIVERSE}"
            ),
            EnumError::Budget(m) => write!(f, "enumeration stopped: {m}"),
        }
    }
}

impl std::error::Error for EnumError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Enumeration {
    pub models: Vec<BTreeSet<GAtom>>,
    pub complete: bool,
    pub candidates_checked: u64,
    pub stable_checks: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModelError(pub String);

impl std::fmt::Display for ModelError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for ModelError {}

struct Index {
    atoms: Vec<GAtom>,
    pos: BTreeMap<GAtom, usize>,
}

impl Index {
    fn new(universe: &BTreeSet<GAtom>) -> Self {
        let atoms: Vec<GAtom> = universe.iter().cloned().collect();
        let pos = atoms
            .iter()
            .enumerate()
            .map(|(i, a)| (a.clone(), i))
            .collect();
        Index { atoms, pos }
    }

    fn get(&self, a: &GAtom) -> usize {
        self.pos[a]
    }
}

fn body_true(body: &[GLit], selected: &[bool], index: &Index) -> bool {
    body.iter().all(|l| {
        let s = selected[index.get(&l.atom)];
        if l.negated {
            !s
        } else {
            s
        }
    })
}

/// The stable-model test used by both search and the independent validator.
///
/// For a candidate `X`, seed the reduct with facts plus selected choice atoms
/// whose bodies are true in `X`; remove normal rules with a negative body literal
/// in `X`; close under the remaining positive rule bodies; require the least model
/// to equal `X`; and reject if any integrity constraint is satisfied in `X`.
fn is_stable(gp: &GroundProgram, selected: &[bool], index: &Index) -> bool {
    let n = index.atoms.len();
    let mut closure = vec![false; n];

    // Facts are forced.
    for f in &gp.facts {
        let i = index.get(f);
        if !selected[i] {
            return false;
        }
        closure[i] = true;
    }

    // Choice rules do not derive atoms. They may seed an atom that is selected
    // and whose body is true in the candidate. A selected choice atom whose body
    // is false is still allowed if a normal rule derives it, so it is not
    // rejected here.
    for r in &gp.rules {
        if r.kind != RuleKind::Choice || !body_true(&r.body, selected, index) {
            continue;
        }
        for h in &r.heads {
            let i = index.get(h);
            if selected[i] {
                closure[i] = true;
            }
        }
    }

    // Reduct of the normal rules: drop a rule whose negative body is true in X.
    loop {
        let mut changed = false;
        for r in &gp.rules {
            if r.kind != RuleKind::Normal {
                continue;
            }
            let active = r
                .body
                .iter()
                .all(|l| !l.negated || !selected[index.get(&l.atom)]);
            if !active {
                continue;
            }
            let positives = r
                .body
                .iter()
                .filter(|l| !l.negated)
                .all(|l| closure[index.get(&l.atom)]);
            if positives {
                for h in &r.heads {
                    let i = index.get(h);
                    if !closure[i] {
                        closure[i] = true;
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    if closure != selected {
        return false;
    }

    for r in &gp.rules {
        if r.kind == RuleKind::Constraint && body_true(&r.body, selected, index) {
            return false;
        }
    }
    true
}

fn set_to_model(set: &[bool], index: &Index) -> BTreeSet<GAtom> {
    let mut out = BTreeSet::new();
    for (i, on) in set.iter().enumerate() {
        if *on {
            out.insert(index.atoms[i].clone());
        }
    }
    out
}

fn model_to_set(model: &BTreeSet<GAtom>, index: &Index) -> Result<Vec<bool>, ModelError> {
    let mut selected = vec![false; index.atoms.len()];
    for a in model {
        let Some(&i) = index.pos.get(a) else {
            return Err(ModelError(format!(
                "model contains atom outside universe: {a}"
            )));
        };
        selected[i] = true;
    }
    Ok(selected)
}

/// Check one model against the grounded program independently of the search.
pub fn validate_model(gp: &GroundProgram, model: &BTreeSet<GAtom>) -> Result<(), ModelError> {
    let index = Index::new(&gp.universe);
    let selected = model_to_set(model, &index)?;
    if is_stable(gp, &selected, &index) {
        Ok(())
    } else {
        Err(ModelError("candidate is not a stable model".into()))
    }
}

/// Enumerate stable models in deterministic atom/mask order.
pub fn enumerate(
    gp: &GroundProgram,
    max_models: usize,
    budget: &mut Budget,
) -> Result<Enumeration, EnumError> {
    let n = gp.universe.len();
    if n > MAX_UNIVERSE {
        return Err(EnumError::TooLarge(n));
    }
    let cap = if max_models == 0 {
        DEFAULT_MODEL_CAP
    } else {
        max_models
    };
    let index = Index::new(&gp.universe);
    let total: u64 = 1u64 << n;
    let mut fact_mask = 0u64;
    for f in &gp.facts {
        fact_mask |= 1u64 << index.get(f);
    }
    let mut models = Vec::new();
    let mut candidates_checked = 0u64;
    let mut stable_checks = 0u64;
    let mut complete = true;
    for mask in 0..total {
        budget
            .charge(1)
            .map_err(|e| EnumError::Budget(e.to_string()))?;
        candidates_checked += 1;
        if mask & fact_mask != fact_mask {
            continue;
        }
        let mut selected = vec![false; n];
        for (i, s) in selected.iter_mut().enumerate() {
            *s = mask & (1u64 << i) != 0;
        }
        stable_checks += 1;
        if is_stable(gp, &selected, &index) {
            models.push(set_to_model(&selected, &index));
            if models.len() >= cap {
                complete = mask + 1 == total;
                if !complete {
                    break;
                }
            }
        }
    }
    Ok(Enumeration {
        models,
        complete,
        candidates_checked,
        stable_checks,
    })
}

/// Render a model in the canonical ASP syntax used by evidence.
pub fn model_text(model: &BTreeSet<GAtom>) -> String {
    if model.is_empty() {
        return "{}".to_string();
    }
    model
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join(" ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ground;
    use crate::syntax;

    fn solve(src: &str, max: usize) -> Enumeration {
        let p = syntax::parse(src).unwrap();
        let g = ground::ground(&p, &mut Budget::steps(10_000_000)).unwrap();
        enumerate(&g, max, &mut Budget::steps(10_000_000)).unwrap()
    }

    #[test]
    fn normal_positive_program_has_its_least_model() {
        let e = solve("p(a). q(X) :- p(X).", 0);
        assert!(e.complete);
        assert_eq!(e.models.len(), 1);
        assert!(e.models[0].iter().any(|a| a.to_string() == "q(a)"));
    }

    #[test]
    fn negation_splits_into_two_stable_models() {
        let e = solve("p :- not q. q :- not p.", 0);
        assert!(e.complete);
        assert_eq!(e.models.len(), 2);
    }

    #[test]
    fn positive_loop_does_not_support_its_head() {
        // The empty set is the (only) stable model: the loop cannot derive p,
        // and it does not get to assume p merely because p is in the candidate.
        let e = solve("p :- p.", 0);
        assert!(e.complete);
        assert_eq!(e.models.len(), 1);
        assert!(e.models[0].is_empty());
    }

    #[test]
    fn choice_is_optional() {
        let e = solve("{p}.", 0);
        assert!(e.complete);
        assert_eq!(e.models.len(), 2);
        assert!(e.models.iter().any(|m| m.is_empty()));
        assert!(e.models.iter().any(|m| m.len() == 1));
    }

    #[test]
    fn integrity_constraint_eliminates_the_bad_model() {
        let e = solve("{p}. :- p.", 0);
        assert!(e.complete);
        assert_eq!(e.models.len(), 1);
        assert!(e.models[0].is_empty());
    }

    #[test]
    fn model_cap_marks_enumeration_incomplete() {
        let e = solve("{a; b}.", 1);
        assert!(!e.complete);
        assert_eq!(e.models.len(), 1);
    }

    #[test]
    fn validator_rejects_a_non_model() {
        let p = syntax::parse("p :- not q.").unwrap();
        let g = ground::ground(&p, &mut Budget::steps(1000)).unwrap();
        let mut bad = BTreeSet::new();
        bad.insert(GAtom::new("q", vec![]));
        assert!(validate_model(&g, &bad).is_err());
    }
}
