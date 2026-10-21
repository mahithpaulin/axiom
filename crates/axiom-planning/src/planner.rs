//! Grounding, deterministic breadth-first search, and plan validation.
//!
//! BFS makes plans shortest in number of actions. The search is exhaustive up to
//! explicit state/action caps; exhaustion therefore licenses `Impossible`, while
//! a cap hit is only `ResourceLimit`.

use crate::pddl::{FAtom, PLiteral, PlanningTask};
use axiom::Budget;
use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

pub const MAX_GROUND_ACTIONS: usize = 100_000;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GroundAction {
    pub name: String,
    pub args: Vec<String>,
    pub preconditions: Vec<PLiteral>,
    pub adds: Vec<FAtom>,
    pub dels: Vec<FAtom>,
}

impl GroundAction {
    pub fn text(&self) -> String {
        format!("{}({})", self.name, self.args.join(","))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Plan {
    pub actions: Vec<GroundAction>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PlanStatus {
    Found(Plan),
    Impossible,
    Limit(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlanResult {
    pub status: PlanStatus,
    pub expanded: u64,
    pub states: usize,
    pub ground_actions: usize,
}

#[derive(Clone, Copy, Debug)]
pub struct Limits {
    pub max_states: usize,
    pub max_expanded: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Limits {
            max_states: 50_000,
            max_expanded: 100_000,
        }
    }
}

fn subst_atom(atom: &FAtom, subst: &BTreeMap<String, String>) -> Option<FAtom> {
    let mut args = Vec::new();
    for a in &atom.args {
        if a.starts_with('?') {
            args.push(subst.get(a)?.clone());
        } else {
            args.push(a.clone());
        }
    }
    Some(FAtom::new(atom.predicate.clone(), args))
}

fn subst_literal(l: &PLiteral, subst: &BTreeMap<String, String>) -> Option<PLiteral> {
    Some(PLiteral {
        positive: l.positive,
        atom: subst_atom(&l.atom, subst)?,
    })
}

fn ground_action(
    task: &PlanningTask,
    action_index: usize,
    subst: &BTreeMap<String, String>,
) -> Option<GroundAction> {
    let action = &task.domain.actions[action_index];
    let args = action
        .params
        .iter()
        .map(|p| subst.get(p).cloned())
        .collect::<Option<Vec<_>>>()?;
    let preconditions = action
        .preconditions
        .iter()
        .map(|l| subst_literal(l, subst))
        .collect::<Option<Vec<_>>>()?;
    let mut adds = Vec::new();
    let mut dels = Vec::new();
    for a in &action.adds {
        adds.push(subst_atom(a, subst)?);
    }
    for a in &action.dels {
        dels.push(subst_atom(a, subst)?);
    }
    adds.sort();
    adds.dedup();
    dels.sort();
    dels.dedup();
    Some(GroundAction {
        name: action.name.clone(),
        args,
        preconditions,
        adds,
        dels,
    })
}

pub fn ground_actions(task: &PlanningTask) -> Result<Vec<GroundAction>, String> {
    let objects: Vec<String> = task.objects.iter().cloned().collect();
    let mut out = Vec::new();
    for (i, action) in task.domain.actions.iter().enumerate() {
        let mut subst = BTreeMap::new();
        fn go(
            task: &PlanningTask,
            action_index: usize,
            params: &[String],
            n: usize,
            objects: &[String],
            subst: &mut BTreeMap<String, String>,
            out: &mut Vec<GroundAction>,
        ) -> Result<(), String> {
            if out.len() > MAX_GROUND_ACTIONS {
                return Err(format!(
                    "grounding exceeds {MAX_GROUND_ACTIONS} actions"
                ));
            }
            if n == params.len() {
                let a = ground_action(task, action_index, subst)
                    .ok_or_else(|| "internal grounding error".to_string())?;
                out.push(a);
                return Ok(());
            }
            for o in objects {
                subst.insert(params[n].clone(), o.clone());
                go(task, action_index, params, n + 1, objects, subst, out)?;
            }
            subst.remove(&params[n]);
            Ok(())
        }
        go(
            task,
            i,
            &action.params,
            0,
            &objects,
            &mut subst,
            &mut out,
        )?;
    }
    out.sort();
    out.dedup();
    Ok(out)
}

fn applicable(action: &GroundAction, state: &BTreeSet<FAtom>) -> bool {
    action.preconditions.iter().all(|l| {
        let present = state.contains(&l.atom);
        present == l.positive
    })
}

fn apply_action(action: &GroundAction, state: &BTreeSet<FAtom>) -> BTreeSet<FAtom> {
    let mut next = state.clone();
    for a in &action.dels {
        next.remove(a);
    }
    for a in &action.adds {
        next.insert(a.clone());
    }
    next
}

fn goal_reached(goal: &[PLiteral], state: &BTreeSet<FAtom>) -> bool {
    goal.iter().all(|l| {
        let present = state.contains(&l.atom);
        present == l.positive
    })
}

pub fn plan(task: &PlanningTask, budget: &mut Budget, limits: Limits) -> PlanResult {
    let actions = match ground_actions(task) {
        Ok(a) => a,
        Err(m) => {
            return PlanResult {
                status: PlanStatus::Limit(m),
                expanded: 0,
                states: 0,
                ground_actions: 0,
            }
        }
    };
    let initial = task.init.clone();
    if goal_reached(&task.goal, &initial) {
        return PlanResult {
            status: PlanStatus::Found(Plan {
                actions: Vec::new(),
            }),
            expanded: 0,
            states: 1,
            ground_actions: actions.len(),
        };
    }
    let mut parent: HashMap<BTreeSet<FAtom>, (BTreeSet<FAtom>, Option<usize>)> = HashMap::new();
    parent.insert(initial.clone(), (BTreeSet::new(), None));
    let mut queue = VecDeque::new();
    queue.push_back(initial);
    let mut expanded = 0u64;

    while let Some(state) = queue.pop_front() {
        if expanded as usize >= limits.max_expanded {
            return PlanResult {
                status: PlanStatus::Limit(format!(
                    "expanded-state cap {} reached",
                    limits.max_expanded
                )),
                expanded,
                states: parent.len(),
                ground_actions: actions.len(),
            };
        }
        if budget.charge(1).is_err() {
            return PlanResult {
                status: PlanStatus::Limit("planning budget exhausted".into()),
                expanded,
                states: parent.len(),
                ground_actions: actions.len(),
            };
        }
        expanded += 1;
        if goal_reached(&task.goal, &state) {
            let mut plan = Vec::new();
            let mut cur = &state;
            while let Some((prev, Some(idx))) = parent.get(cur) {
                plan.push(actions[*idx].clone());
                cur = prev;
            }
            plan.reverse();
            return PlanResult {
                status: PlanStatus::Found(Plan { actions: plan }),
                expanded,
                states: parent.len(),
                ground_actions: actions.len(),
            };
        }
        for (idx, action) in actions.iter().enumerate() {
            if !applicable(action, &state) {
                continue;
            }
            let next = apply_action(action, &state);
            if parent.contains_key(&next) {
                continue;
            }
            if parent.len() >= limits.max_states {
                return PlanResult {
                    status: PlanStatus::Limit(format!("state cap {} reached", limits.max_states)),
                    expanded,
                    states: parent.len(),
                    ground_actions: actions.len(),
                };
            }
            parent.insert(next.clone(), (state.clone(), Some(idx)));
            queue.push_back(next);
        }
    }
    PlanResult {
        status: PlanStatus::Impossible,
        expanded,
        states: parent.len(),
        ground_actions: actions.len(),
    }
}

pub fn validate_actions(
    task: &PlanningTask,
    names: &[(String, Vec<String>)],
) -> Result<(), String> {
    let actions = ground_actions(task)?;
    let map: BTreeMap<(String, Vec<String>), &GroundAction> = actions
        .iter()
        .map(|a| ((a.name.clone(), a.args.clone()), a))
        .collect();
    let mut state = task.init.clone();
    for (name, args) in names {
        let action = map
            .get(&(name.clone(), args.clone()))
            .ok_or_else(|| format!("plan uses unknown action {name}({})", args.join(",")))?;
        if !applicable(action, &state) {
            return Err(format!(
                "precondition of {} is not satisfied at this step",
                action.text()
            ));
        }
        state = apply_action(action, &state);
    }
    if !goal_reached(&task.goal, &state) {
        return Err("plan does not reach the goal".into());
    }
    Ok(())
}

/// Parse `move(a,b)|load(a)|...`. An empty string is the empty plan.
pub fn parse_plan_text(text: &str) -> Result<Vec<(String, Vec<String>)>, String> {
    if text.trim().is_empty() {
        return Ok(Vec::new());
    }
    let mut out = Vec::new();
    for item in text.split('|') {
        let item = item.trim();
        let (name, rest) = item
            .split_once('(')
            .ok_or_else(|| format!("bad plan action {item:?}"))?;
        if !rest.ends_with(')') {
            return Err(format!("bad plan action {item:?}"));
        }
        let inner = &rest[..rest.len() - 1];
        let args = if inner.trim().is_empty() {
            Vec::new()
        } else {
            inner.split(',').map(|a| a.trim().to_string()).collect()
        };
        if name.is_empty() || args.iter().any(|a| a.is_empty()) {
            return Err(format!("bad plan action {item:?}"));
        }
        out.push((name.to_string(), args));
    }
    Ok(out)
}

pub fn plan_text(plan: &Plan) -> String {
    plan.actions
        .iter()
        .map(GroundAction::text)
        .collect::<Vec<_>>()
        .join("|")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pddl::parse_task;

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
    fn finds_and_validates_a_plan() {
        let task = parse_task(DOMAIN, PROBLEM).unwrap();
        let mut b = Budget::steps(1_000_000);
        let r = plan(&task, &mut b, Limits::default());
        let PlanStatus::Found(plan) = r.status else {
            panic!("no plan: {r:?}");
        };
        assert_eq!(plan.actions.len(), 1);
        validate_actions(
            &task,
            &[("move".into(), vec!["a".into(), "b".into()])],
        )
        .unwrap();
    }

    #[test]
    fn impossible_is_exhaustive() {
        let p = r#"
            (define (problem p)
              (:domain move)
              (:objects a b c)
              (:init (at item a) (connected a b))
              (:goal (at item c)))
        "#;
        let task = parse_task(DOMAIN, p).unwrap();
        let mut b = Budget::steps(1_000_000);
        let r = plan(&task, &mut b, Limits::default());
        assert_eq!(r.status, PlanStatus::Impossible);
    }

    #[test]
    fn invalid_plan_is_rejected() {
        let task = parse_task(DOMAIN, PROBLEM).unwrap();
        assert!(validate_actions(
            &task,
            &[("move".into(), vec!["b".into(), "a".into()])]
        )
        .is_err());
    }
}
