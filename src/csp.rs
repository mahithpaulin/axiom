//! Finite-domain constraint problems (V2 R4, ROADMAP II3 first cut).
//!
//! A puzzle is a set of variables with small finite domains plus constraints.
//! The solver is deliberately simple — propagation to a fixpoint, then
//! depth-first search with the minimum-remaining-values order — because V2
//! optimises for capability first. What is *not* simple is the proof
//! discipline: every value a propagator removes records *which constraint did
//! it and why*, so an `Impossible` answer carries the pruning trace, and every
//! `Found` assignment is re-checkable by [`verify_csp`], which evaluates the
//! constraints directly and shares no code with the propagators.
//!
//! Bounds: domains are explicit value lists (not intervals), so this layer
//! suits puzzles and word problems with small domains. Large or continuous
//! domains belong to the theory layer (`crate::theory`), not here.

use crate::budget::Budget;
use crate::status::{Exhausted, Status};

/// Variable id: index into [`CspProblem::vars`].
pub type VarId = u32;

/// One finite-domain variable.
#[derive(Clone, Debug)]
pub struct CspVar {
    pub name: String,
    pub domain: Vec<i32>,
}

/// Constraints. Each documents its own propagation rule; a propagator that
/// cannot explain itself (see `docs/V2.md` §5) does not belong here.
#[derive(Clone, Debug)]
pub enum Constraint {
    /// Pairwise distinct. Propagates: a singleton value is removed everywhere
    /// else; reports impossible when the union of domains is smaller than the
    /// number of variables.
    AllDifferent(Vec<VarId>),
    /// Same value. Propagates by domain intersection.
    Equal(VarId, VarId),
    /// Different values. Propagates singletons against each other.
    NotEqual(VarId, VarId),
    /// Strict `a < b`. Prunes `a` values with no greater `b` value and `b`
    /// values with no smaller `a` value.
    LessThan(VarId, VarId),
    /// `v == c`.
    ValueEq(VarId, i32),
    /// `v != c`.
    ValueNe(VarId, i32),
    /// `sum(coeff[i] * var[i]) <= bound`. Interval propagation over current
    /// minima/maxima; exact on the small domains this layer targets.
    LinearLe {
        coeffs: Vec<(VarId, i64)>,
        bound: i64,
    },
}

/// A puzzle: variables plus constraints.
#[derive(Clone, Debug, Default)]
pub struct CspProblem {
    pub vars: Vec<CspVar>,
    pub constraints: Vec<Constraint>,
}

impl CspProblem {
    pub fn new() -> Self {
        CspProblem {
            vars: Vec::new(),
            constraints: Vec::new(),
        }
    }

    /// Add a variable with an explicit finite domain. Returns its id.
    /// An empty domain is kept (not rejected): the problem is then trivially
    /// impossible and the solver says so with a trace.
    pub fn var(&mut self, name: &str, mut domain: Vec<i32>) -> VarId {
        domain.sort_unstable();
        domain.dedup();
        let id = self.vars.len() as VarId;
        self.vars.push(CspVar {
            name: name.to_string(),
            domain,
        });
        id
    }

    pub fn constrain(&mut self, c: Constraint) {
        self.constraints.push(c);
    }

    pub fn nvars(&self) -> usize {
        self.vars.len()
    }
}

/// Deterministic counters: propagator rounds, values pruned, search nodes.
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct CspStats {
    pub rounds: u64,
    pub pruned: u64,
    pub nodes: u64,
}

/// Outcome of [`solve_csp`].
#[derive(Clone, Debug)]
pub struct CspOutcome {
    pub status: Status,
    /// Present on `Found`: one value per variable, in variable order.
    pub assignment: Vec<i32>,
    /// Present on `Impossible`: the pruning trace, oldest first.
    pub explanation: Vec<String>,
    pub stats: CspStats,
}

fn var_name(prob: &CspProblem, v: VarId) -> &str {
    &prob.vars[v as usize].name
}

/// Independent checker: evaluates every constraint against a full assignment.
/// Shares no code with the propagators, so agreement is evidence.
pub fn verify_csp(prob: &CspProblem, assignment: &[i32]) -> bool {
    if assignment.len() != prob.vars.len() {
        return false;
    }
    let inadmissible = assignment
        .iter()
        .zip(prob.vars.iter())
        .any(|(val, var)| !var.domain.contains(val));
    if inadmissible {
        return false;
    }
    let at = |v: VarId| assignment[v as usize];
    prob.constraints.iter().all(|c| match c {
        Constraint::AllDifferent(vs) => {
            let mut seen = Vec::with_capacity(vs.len());
            vs.iter().all(|v| {
                let val = at(*v);
                if seen.contains(&val) {
                    false
                } else {
                    seen.push(val);
                    true
                }
            })
        }
        Constraint::Equal(a, b) => at(*a) == at(*b),
        Constraint::NotEqual(a, b) => at(*a) != at(*b),
        Constraint::LessThan(a, b) => at(*a) < at(*b),
        Constraint::ValueEq(v, c) => at(*v) == *c,
        Constraint::ValueNe(v, c) => at(*v) != *c,
        Constraint::LinearLe { coeffs, bound } => {
            coeffs.iter().map(|(v, k)| *k * at(*v) as i64).sum::<i64>() <= *bound
        }
    })
}

/// Remove `val` from `domains[v]`; records the reason. Returns true when the
/// domain changed.
fn remove(
    domains: &mut [Vec<i32>],
    trace: &mut Vec<String>,
    prob: &CspProblem,
    v: VarId,
    val: i32,
    why: &str,
    pruned: &mut u64,
) -> bool {
    let d = &mut domains[v as usize];
    if let Some(pos) = d.iter().position(|x| *x == val) {
        d.remove(pos);
        *pruned += 1;
        if trace.len() < 1024 {
            trace.push(format!("{} != {val} by {why}", var_name(prob, v)));
        }
        true
    } else {
        false
    }
}

/// What propagation stopped on: a real conflict, or the budget.
enum PropErr {
    Conflict(String),
    Budget(Exhausted),
}

fn conflict_msg(trace: &mut Vec<String>, msg: String) {
    if trace.len() < 1024 {
        trace.push(msg);
    }
}

/// One pass over every constraint. Returns the net change, or the reason the
/// problem just became impossible.
fn propagate_once(
    prob: &CspProblem,
    domains: &mut [Vec<i32>],
    trace: &mut Vec<String>,
    pruned: &mut u64,
) -> Result<bool, String> {
    let mut changed = false;
    for (ci, c) in prob.constraints.iter().enumerate() {
        let tag = |kind: &str| format!("constraint {ci} ({kind})");
        match c {
            Constraint::ValueEq(v, c) => {
                let keep = *c;
                let stale: Vec<i32> = domains[*v as usize]
                    .iter()
                    .copied()
                    .filter(|x| *x != keep)
                    .collect();
                if !stale.is_empty() && !domains[*v as usize].contains(&keep) {
                    return Err(format!(
                        "{}: {} has no {keep}",
                        tag("value-eq"),
                        var_name(prob, *v)
                    ));
                }
                for x in stale {
                    changed |= remove(domains, trace, prob, *v, x, &tag("value-eq"), pruned);
                }
            }
            Constraint::ValueNe(v, c) => {
                changed |= remove(domains, trace, prob, *v, *c, &tag("value-ne"), pruned);
            }
            Constraint::Equal(a, b) => {
                let (da, db) = (domains[*a as usize].clone(), domains[*b as usize].clone());
                for x in da {
                    if !db.contains(&x) {
                        changed |= remove(domains, trace, prob, *a, x, &tag("equal"), pruned);
                    }
                }
                let (da, db) = (domains[*a as usize].clone(), domains[*b as usize].clone());
                for x in db {
                    if !da.contains(&x) {
                        changed |= remove(domains, trace, prob, *b, x, &tag("equal"), pruned);
                    }
                }
            }
            Constraint::NotEqual(a, b) => {
                if domains[*a as usize].len() == 1 && domains[*b as usize].len() == 1 {
                    if domains[*a as usize][0] == domains[*b as usize][0] {
                        return Err(format!(
                            "{}: {} and {} both forced to {}",
                            tag("not-equal"),
                            var_name(prob, *a),
                            var_name(prob, *b),
                            domains[*a as usize][0]
                        ));
                    }
                }
                if domains[*a as usize].len() == 1 {
                    let x = domains[*a as usize][0];
                    changed |= remove(domains, trace, prob, *b, x, &tag("not-equal"), pruned);
                }
                if domains[*b as usize].len() == 1 {
                    let x = domains[*b as usize][0];
                    changed |= remove(domains, trace, prob, *a, x, &tag("not-equal"), pruned);
                }
            }
            Constraint::LessThan(a, b) => {
                if domains[*a as usize].is_empty() || domains[*b as usize].is_empty() {
                    continue;
                }
                let max_b = *domains[*b as usize].iter().max().unwrap_or(&i32::MIN);
                let min_a = *domains[*a as usize].iter().min().unwrap_or(&i32::MAX);
                let bad_a: Vec<i32> = domains[*a as usize]
                    .iter()
                    .copied()
                    .filter(|x| *x >= max_b)
                    .collect();
                for x in bad_a {
                    changed |= remove(domains, trace, prob, *a, x, &tag("less-than"), pruned);
                }
                let bad_b: Vec<i32> = domains[*b as usize]
                    .iter()
                    .copied()
                    .filter(|x| *x <= min_a)
                    .collect();
                for x in bad_b {
                    changed |= remove(domains, trace, prob, *b, x, &tag("less-than"), pruned);
                }
            }
            Constraint::AllDifferent(vs) => {
                let mut union: Vec<i32> = Vec::new();
                for v in vs {
                    for x in &domains[*v as usize] {
                        if !union.contains(x) {
                            union.push(*x);
                        }
                    }
                }
                if union.len() < vs.len() {
                    return Err(format!(
                        "{}: {} variables share {} values",
                        tag("all-different"),
                        vs.len(),
                        union.len()
                    ));
                }
                let singletons: Vec<(VarId, i32)> = vs
                    .iter()
                    .filter_map(|v| {
                        if domains[*v as usize].len() == 1 {
                            Some((*v, domains[*v as usize][0]))
                        } else {
                            None
                        }
                    })
                    .collect();
                for (sv, x) in &singletons {
                    for v in vs {
                        if *v != *sv {
                            changed |=
                                remove(domains, trace, prob, *v, *x, &tag("all-different"), pruned);
                        }
                    }
                }
            }
            Constraint::LinearLe { coeffs, bound } => {
                // Per-variable min/max contribution under the current domains.
                let mut contrib: Vec<(VarId, i64, i64, i64)> = Vec::new();
                for (v, k) in coeffs {
                    let d = &domains[*v as usize];
                    if d.is_empty() {
                        continue;
                    }
                    let (lo, hi) = (
                        *d.iter().min().unwrap_or(&0) as i64,
                        *d.iter().max().unwrap_or(&0) as i64,
                    );
                    if *k >= 0 {
                        contrib.push((*v, *k, *k * lo, *k * hi));
                    } else {
                        contrib.push((*v, *k, *k * hi, *k * lo));
                    }
                }
                let min_sum: i64 = contrib.iter().map(|(_, _, lo, _)| *lo).sum();
                if min_sum > *bound {
                    return Err(format!(
                        "{}: minimum sum {min_sum} exceeds {bound}",
                        tag("linear-le")
                    ));
                }
                for (v, k, lo, _) in &contrib {
                    if *k == 0 {
                        continue;
                    }
                    let others_min = min_sum - *lo;
                    let bad: Vec<i32> = domains[*v as usize]
                        .iter()
                        .copied()
                        .filter(|x| others_min + *k * *x as i64 > *bound)
                        .collect();
                    for x in bad {
                        changed |= remove(domains, trace, prob, *v, x, &tag("linear-le"), pruned);
                    }
                }
            }
        }
        for (i, d) in domains.iter().enumerate() {
            if d.is_empty() {
                return Err(format!(
                    "{}: {} ran out of values",
                    tag("domain-wipeout"),
                    var_name(prob, i as VarId)
                ));
            }
        }
    }
    Ok(changed)
}

/// Propagate to a fixpoint. Charges one step per round.
fn propagate(
    prob: &CspProblem,
    domains: &mut Vec<Vec<i32>>,
    trace: &mut Vec<String>,
    stats: &mut CspStats,
    budget: &mut Budget,
) -> Result<(), PropErr> {
    loop {
        budget.charge(1).map_err(PropErr::Budget)?;
        stats.rounds += 1;
        let changed =
            propagate_once(prob, domains, trace, &mut stats.pruned).map_err(PropErr::Conflict)?;
        if !changed {
            return Ok(());
        }
    }
}

fn dfs(
    prob: &CspProblem,
    domains: Vec<Vec<i32>>,
    trace: Vec<String>,
    stats: &mut CspStats,
    budget: &mut Budget,
) -> Result<CspOutcome, Exhausted> {
    budget.charge(1)?;
    stats.nodes += 1;
    let mut domains = domains;
    let mut trace = trace;
    match propagate(prob, &mut domains, &mut trace, stats, budget) {
        Ok(()) => {}
        Err(PropErr::Budget(e)) => return Err(e),
        Err(PropErr::Conflict(reason)) => {
            conflict_msg(&mut trace, reason);
            return Ok(CspOutcome {
                status: Status::Impossible,
                assignment: Vec::new(),
                explanation: trace,
                stats: *stats,
            });
        }
    }
    if domains.iter().all(|d| d.len() == 1) {
        let assignment: Vec<i32> = domains.iter().map(|d| d[0]).collect();
        debug_assert!(verify_csp(prob, &assignment));
        return Ok(CspOutcome {
            status: Status::Found,
            assignment,
            explanation: Vec::new(),
            stats: *stats,
        });
    }
    // Minimum-remaining-values, ties broken by lowest variable id.
    let next = domains
        .iter()
        .enumerate()
        .filter(|(_, d)| d.len() > 1)
        .min_by_key(|(i, d)| (d.len(), *i))
        .map(|(i, _)| i)
        .expect("a non-singleton domain exists");
    let mut first_impossible: Option<CspOutcome> = None;
    for val in domains[next].clone() {
        let mut child = domains.clone();
        child[next] = vec![val];
        let mut child_trace = trace.clone();
        if child_trace.len() < 1024 {
            child_trace.push(format!("branch {} = {val}", var_name(prob, next as VarId)));
        }
        match dfs(prob, child, child_trace, stats, budget)? {
            out @ CspOutcome {
                status: Status::Found,
                ..
            } => return Ok(out),
            out @ CspOutcome {
                status: Status::Impossible,
                ..
            } => {
                if first_impossible.is_none() {
                    first_impossible = Some(out);
                }
            }
            out => return Ok(out),
        }
    }
    Ok(first_impossible.unwrap_or(CspOutcome {
        status: Status::Impossible,
        assignment: Vec::new(),
        explanation: trace,
        stats: *stats,
    }))
}

/// Solve a finite-domain problem. Returns `Found` with a checked assignment,
/// `Impossible` with the pruning trace, or `Err(Exhausted)` when the budget
/// runs out (which says nothing about satisfiability).
pub fn solve_csp(prob: &CspProblem, budget: &mut Budget) -> Result<CspOutcome, Exhausted> {
    let mut stats = CspStats::default();
    let domains: Vec<Vec<i32>> = prob.vars.iter().map(|v| v.domain.clone()).collect();
    for (i, d) in domains.iter().enumerate() {
        if d.is_empty() {
            return Ok(CspOutcome {
                status: Status::Impossible,
                assignment: Vec::new(),
                explanation: vec![format!(
                    "{} starts with an empty domain",
                    var_name(prob, i as VarId)
                )],
                stats,
            });
        }
    }
    dfs(prob, domains, Vec::new(), &mut stats, budget)
}
