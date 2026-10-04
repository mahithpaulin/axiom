//! State-transition systems (V2 R5, ROADMAP II4 first cut).
//!
//! A planning problem or turn-based game position is a graph: numbered states,
//! named actions with costs, one initial state, and goal states. Two
//! operations are provided, sharing one certificate shape (the action
//! sequence, replayed by [`verify_plan`]):
//!
//! * [`shortest_plan`] — Dijkstra over the explicit graph. Optimal for
//!   non-negative costs; `Impossible` only after the reachable set is
//!   exhausted.
//! * [`bmc_clauses`] — bounded-model-checking lowering onto the clause IR
//!   (V2 R5 → R2): `bound` time steps, one boolean per (state, step). The
//!   encoding is exact reachability in *exactly* `bound` steps; the SAT core
//!   from V1 decides it, so planning answers reuse the RUP machinery.

use crate::budget::Budget;
use crate::status::{Exhausted, Status};

/// One directed, named, costed transition.
#[derive(Clone, Debug)]
pub struct Action {
    pub name: String,
    pub from: u32,
    pub to: u32,
    pub cost: i64,
}

/// States are `0..num_states`; actions name the edges.
#[derive(Clone, Debug, Default)]
pub struct StateGraph {
    pub num_states: u32,
    pub actions: Vec<Action>,
    pub initial: u32,
    pub goals: Vec<u32>,
}

impl StateGraph {
    pub fn new(num_states: u32, initial: u32) -> Self {
        StateGraph {
            num_states,
            actions: Vec::new(),
            initial,
            goals: Vec::new(),
        }
    }

    pub fn action(&mut self, name: &str, from: u32, to: u32, cost: i64) {
        self.actions.push(Action {
            name: name.to_string(),
            from,
            to,
            cost,
        });
    }

    pub fn goal(&mut self, s: u32) {
        if !self.goals.contains(&s) {
            self.goals.push(s);
        }
    }

    /// Structural validation: state ids in range, non-negative costs.
    pub fn validate(&self) -> Result<(), String> {
        if self.initial >= self.num_states {
            return Err(format!(
                "initial state {} out of {} states",
                self.initial, self.num_states
            ));
        }
        for g in &self.goals {
            if *g >= self.num_states {
                return Err(format!("goal state {g} out of range"));
            }
        }
        for a in &self.actions {
            if a.from >= self.num_states || a.to >= self.num_states {
                return Err(format!("action {} leaves the state range", a.name));
            }
            if a.cost < 0 {
                return Err(format!("action {} has negative cost", a.name));
            }
        }
        Ok(())
    }

    fn adjacency(&self) -> Vec<Vec<usize>> {
        let mut adj = vec![Vec::new(); self.num_states as usize];
        for (i, a) in self.actions.iter().enumerate() {
            adj[a.from as usize].push(i);
        }
        adj
    }
}

/// Outcome of [`shortest_plan`].
#[derive(Clone, Debug)]
pub struct PlanOutcome {
    pub status: Status,
    /// Action names from the initial state, in order. Present on `Found`.
    pub plan: Vec<String>,
    pub cost: i64,
    /// States removed from the frontier. Present on `Impossible`.
    pub explored: u64,
}

/// Independent checker: replays the plan from the initial state and requires
/// it to end in a goal state with matching step costs.
pub fn verify_plan(g: &StateGraph, plan: &[String], cost: i64) -> bool {
    let mut at = g.initial;
    let mut total = 0i64;
    for name in plan {
        match g.actions.iter().find(|a| a.from == at && a.name == *name) {
            Some(a) => {
                at = a.to;
                total += a.cost;
            }
            None => return false,
        }
    }
    total == cost && g.goals.contains(&at)
}

/// Dijkstra over the explicit graph (BFS when all costs are 1). Optimal for
/// non-negative costs. `Impossible` is reported only after the whole
/// reachable set is explored; budget exhaustion is `Err(Exhausted)`.
pub fn shortest_plan(g: &StateGraph, budget: &mut Budget) -> Result<PlanOutcome, Exhausted> {
    g.validate().map_err(|_| Exhausted::Malformed)?;
    let n = g.num_states as usize;
    let adj = g.adjacency();
    let mut dist = vec![i64::MAX; n];
    let mut prev: Vec<Option<(u32, usize)>> = vec![None; n];
    let mut done = vec![false; n];
    dist[g.initial as usize] = 0;
    let mut explored = 0u64;
    loop {
        budget.charge(1)?;
        let next = (0..n)
            .filter(|s| !done[*s] && dist[*s] != i64::MAX)
            .min_by_key(|s| (dist[*s], *s));
        let Some(u) = next else {
            return Ok(PlanOutcome {
                status: Status::Impossible,
                plan: Vec::new(),
                cost: 0,
                explored,
            });
        };
        done[u] = true;
        explored += 1;
        if g.goals.contains(&(u as u32)) {
            let mut steps: Vec<String> = Vec::new();
            let mut at = u;
            while let Some((from, ai)) = prev[at] {
                steps.push(g.actions[ai].name.clone());
                at = from as usize;
            }
            steps.reverse();
            let outcome = PlanOutcome {
                status: Status::Found,
                plan: steps,
                cost: dist[u],
                explored,
            };
            debug_assert!(verify_plan(g, &outcome.plan, outcome.cost));
            return Ok(outcome);
        }
        for ai in &adj[u] {
            let a = &g.actions[*ai];
            let v = a.to as usize;
            let nd = dist[u].saturating_add(a.cost);
            if nd < dist[v] {
                dist[v] = nd;
                prev[v] = Some((u as u32, *ai));
            }
        }
    }
}

/// Ground CNF for "a goal is reachable in exactly `bound` steps".
/// Variable `x[s][t]` (1-based DIMACS) is true iff the system is in state `s`
/// at time `t`. Clauses: initial unit, exactly-one state per time step, goal
/// disjunction at time `bound`, and both directions of the transition
/// relation between consecutive steps.
#[derive(Clone, Debug)]
pub struct BmcCnf {
    pub num_vars: u32,
    pub clauses: Vec<Vec<i32>>,
}

fn bmc_var(num_states: u32, state: u32, step: u32) -> i32 {
    (step * num_states + state + 1) as i32
}

pub fn bmc_clauses(g: &StateGraph, bound: u32) -> Result<BmcCnf, String> {
    g.validate()?;
    if g.goals.is_empty() {
        return Err("no goal states".to_string());
    }
    let n = g.num_states;
    let num_vars = n * (bound + 1);
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    clauses.push(vec![bmc_var(n, g.initial, 0)]);
    let mut succ: Vec<Vec<u32>> = vec![Vec::new(); n as usize];
    let mut pred: Vec<Vec<u32>> = vec![Vec::new(); n as usize];
    for a in &g.actions {
        if !succ[a.from as usize].contains(&a.to) {
            succ[a.from as usize].push(a.to);
        }
        if !pred[a.to as usize].contains(&a.from) {
            pred[a.to as usize].push(a.from);
        }
    }
    for t in 0..=bound {
        // At least one state per step.
        clauses.push((0..n).map(|s| bmc_var(n, s, t)).collect());
        // At most one state per step (pairwise; small graphs only).
        for a in 0..n {
            for b in (a + 1)..n {
                clauses.push(vec![-bmc_var(n, a, t), -bmc_var(n, b, t)]);
            }
        }
    }
    // Goal at the final step.
    clauses.push(g.goals.iter().map(|s| bmc_var(n, *s, bound)).collect());
    for t in 0..bound {
        for s in 0..n {
            // Forward: being in s at t forces a successor at t+1. With no
            // successors this is the unit clause `-x[s][t]` (s is a dead end
            // before the final step), which is exactly right.
            let mut fwd = vec![-bmc_var(n, s, t)];
            for ns in &succ[s as usize] {
                fwd.push(bmc_var(n, *ns, t + 1));
            }
            clauses.push(fwd);
            // Backward: being in s at t+1 forces a predecessor at t. With no
            // predecessors this is the unit `-x[s][t+1]`: nothing enters s.
            // Sound for every t+1 >= 1, which is all we emit (the initial
            // state is pinned at t=0 by the unit clause above).
            let mut bwd = vec![-bmc_var(n, s, t + 1)];
            for ps in &pred[s as usize] {
                bwd.push(bmc_var(n, *ps, t));
            }
            clauses.push(bwd);
        }
    }
    Ok(BmcCnf { num_vars, clauses })
}
