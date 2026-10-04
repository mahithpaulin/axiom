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
use std::rc::Rc;

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
    /// `|a - b| != k`. The queens diagonal (`k` = column distance) and any
    /// separation requirement. Prunes a value with no surviving partner.
    AbsDiffNe(VarId, VarId, i32),
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
        Constraint::AbsDiffNe(a, b, k) => (at(*a) as i64 - at(*b) as i64).abs() != *k as i64,
    })
}

/// Undo stack for domain removals: backtracking pops entries and restores
/// values instead of cloning whole domains per node. Domains stay sorted at
/// all times (removals shift, restores binary-search the slot back), so the
/// branching order — and therefore the search — is exactly as before.
#[derive(Default)]
struct Trail {
    entries: Vec<(VarId, i32)>,
}

impl Trail {
    fn mark(&self) -> usize {
        self.entries.len()
    }

    fn undo_to(&mut self, domains: &mut [Vec<i32>], mark: usize) {
        while self.entries.len() > mark {
            let (v, val) = self.entries.pop().expect("mark is within the trail");
            let d = &mut domains[v as usize];
            match d.binary_search(&val) {
                Err(pos) => d.insert(pos, val),
                Ok(_) => {}
            }
        }
    }
}

/// Persistent explanation list: pushing is one `Rc` allocation and branching
/// shares the parent tail with zero copying (the old `Vec<String>` clone per
/// node dominated hard searches). Flattened oldest-first on `Impossible`.
#[derive(Clone, Default)]
struct Trace {
    top: Option<Rc<TraceNode>>,
    len: usize,
}

struct TraceNode {
    msg: String,
    parent: Trace,
}

impl Trace {
    fn push(&mut self, msg: String) {
        if self.len >= 1024 {
            return;
        }
        let parent = std::mem::take(self);
        let len = parent.len + 1;
        self.top = Some(Rc::new(TraceNode { msg, parent }));
        self.len = len;
    }

    fn flatten(&self) -> Vec<String> {
        let mut out = Vec::new();
        let mut cur = self;
        while let Some(rc) = &cur.top {
            out.push(rc.msg.clone());
            cur = &rc.parent;
        }
        out.reverse();
        out
    }
}

/// Remove `val` from `domains[v]`; records the trail entry and the reason.
/// Returns true when the domain changed. Order-preserving (`Vec::remove`),
/// so branching order is untouched.
#[allow(clippy::too_many_arguments)]
fn remove(
    domains: &mut [Vec<i32>],
    trail: &mut Trail,
    trace: &mut Trace,
    prob: &CspProblem,
    v: VarId,
    val: i32,
    why: &str,
    pruned: &mut u64,
) -> bool {
    let d = &mut domains[v as usize];
    if let Some(pos) = d.iter().position(|x| *x == val) {
        d.remove(pos);
        trail.entries.push((v, val));
        *pruned += 1;
        trace.push(format!("{} != {val} by {why}", var_name(prob, v)));
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

/// Kuhn DFS for bipartite matching (one augmenting-path search). Domains are
/// tiny, so the textbook O(VE) version beats fancier ones; order is scope
/// order over first-seen values, hence deterministic.
fn kuhn(
    i: usize,
    adj: &[Vec<usize>],
    match_var: &mut [Option<usize>],
    match_val: &mut [Option<usize>],
    seen: &mut [bool],
) -> bool {
    for xi in &adj[i] {
        let xi = *xi;
        if seen[xi] {
            continue;
        }
        seen[xi] = true;
        if match_val[xi].is_none()
            || kuhn(
                match_val[xi].expect("matched value"),
                adj,
                match_var,
                match_val,
                seen,
            )
        {
            match_var[i] = Some(xi);
            match_val[xi] = Some(i);
            return true;
        }
    }
    false
}

/// Strongly connected components by Kosaraju (iterative, deterministic in
/// stored edge order). Returns one component id per node.
fn scc(n: usize, edges: &[Vec<usize>]) -> Vec<usize> {
    let mut rev: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (a, outs) in edges.iter().enumerate() {
        for b in outs {
            rev[*b].push(a);
        }
    }
    let mut visited = vec![false; n];
    let mut order = Vec::with_capacity(n);
    for s in 0..n {
        if visited[s] {
            continue;
        }
        let mut stack = vec![(s, false)];
        while let Some((u, done)) = stack.pop() {
            if done {
                order.push(u);
                continue;
            }
            if visited[u] {
                continue;
            }
            visited[u] = true;
            stack.push((u, true));
            for v in edges[u].iter().rev() {
                if !visited[*v] {
                    stack.push((*v, false));
                }
            }
        }
    }
    let mut comp = vec![usize::MAX; n];
    let mut ncomps = 0usize;
    for s in order.iter().rev() {
        if comp[*s] != usize::MAX {
            continue;
        }
        let mut stack = vec![*s];
        while let Some(u) = stack.pop() {
            if comp[u] != usize::MAX {
                continue;
            }
            comp[u] = ncomps;
            for v in &rev[u] {
                if comp[*v] == usize::MAX {
                    stack.push(*v);
                }
            }
        }
        ncomps += 1;
    }
    comp
}

/// One pass over every constraint. Returns the net change, or the reason the
/// problem just became impossible.
fn propagate_once(
    prob: &CspProblem,
    domains: &mut [Vec<i32>],
    trail: &mut Trail,
    trace: &mut Trace,
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
                    changed |= remove(domains, trail, trace, prob, *v, x, &tag("value-eq"), pruned);
                }
            }
            Constraint::ValueNe(v, c) => {
                changed |= remove(
                    domains,
                    trail,
                    trace,
                    prob,
                    *v,
                    *c,
                    &tag("value-ne"),
                    pruned,
                );
            }
            Constraint::Equal(a, b) => {
                // Intersect without cloning: collect owned values under
                // shared borrows, then remove.
                let bad_a: Vec<i32> = domains[*a as usize]
                    .iter()
                    .copied()
                    .filter(|x| !domains[*b as usize].contains(x))
                    .collect();
                for x in bad_a {
                    changed |= remove(domains, trail, trace, prob, *a, x, &tag("equal"), pruned);
                }
                let bad_b: Vec<i32> = domains[*b as usize]
                    .iter()
                    .copied()
                    .filter(|x| !domains[*a as usize].contains(x))
                    .collect();
                for x in bad_b {
                    changed |= remove(domains, trail, trace, prob, *b, x, &tag("equal"), pruned);
                }
            }
            Constraint::NotEqual(a, b) => {
                if domains[*a as usize].len() == 1
                    && domains[*b as usize].len() == 1
                    && domains[*a as usize][0] == domains[*b as usize][0]
                {
                    return Err(format!(
                        "{}: {} and {} both forced to {}",
                        tag("not-equal"),
                        var_name(prob, *a),
                        var_name(prob, *b),
                        domains[*a as usize][0]
                    ));
                }
                if domains[*a as usize].len() == 1 {
                    let x = domains[*a as usize][0];
                    changed |= remove(
                        domains,
                        trail,
                        trace,
                        prob,
                        *b,
                        x,
                        &tag("not-equal"),
                        pruned,
                    );
                }
                if domains[*b as usize].len() == 1 {
                    let x = domains[*b as usize][0];
                    changed |= remove(
                        domains,
                        trail,
                        trace,
                        prob,
                        *a,
                        x,
                        &tag("not-equal"),
                        pruned,
                    );
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
                    changed |= remove(
                        domains,
                        trail,
                        trace,
                        prob,
                        *a,
                        x,
                        &tag("less-than"),
                        pruned,
                    );
                }
                let bad_b: Vec<i32> = domains[*b as usize]
                    .iter()
                    .copied()
                    .filter(|x| *x <= min_a)
                    .collect();
                for x in bad_b {
                    changed |= remove(
                        domains,
                        trail,
                        trace,
                        prob,
                        *b,
                        x,
                        &tag("less-than"),
                        pruned,
                    );
                }
            }
            Constraint::AllDifferent(vs) => {
                // Régin-style GAC: a value stays only if some maximum
                // matching uses it. Strictly stronger than the old
                // singleton rule (which it subsumes) and the union check.
                let mut vals: Vec<i32> = Vec::new();
                for v in vs {
                    for x in &domains[*v as usize] {
                        if !vals.contains(x) {
                            vals.push(*x);
                        }
                    }
                }
                let k = vs.len();
                let adj: Vec<Vec<usize>> = vs
                    .iter()
                    .map(|v| {
                        domains[*v as usize]
                            .iter()
                            .map(|x| vals.iter().position(|y| y == x).expect("in universe"))
                            .collect()
                    })
                    .collect();
                let mut match_var: Vec<Option<usize>> = vec![None; k];
                let mut match_val: Vec<Option<usize>> = vec![None; vals.len()];
                let mut matched = 0usize;
                for i in 0..k {
                    let mut seen = vec![false; vals.len()];
                    if kuhn(i, &adj, &mut match_var, &mut match_val, &mut seen) {
                        matched += 1;
                    }
                }
                if matched < k {
                    return Err(format!(
                        "{}: only {matched} of {} variables placeable",
                        tag("all-different"),
                        k
                    ));
                }
                // Alternating digraph: matched edges var -> value, the rest
                // value -> var. Values prunable exactly when their edge is
                // unmatched and crosses components.
                let total = k + vals.len();
                let mut edges: Vec<Vec<usize>> = vec![Vec::new(); total];
                for (i, outs) in adj.iter().enumerate() {
                    for xi in outs {
                        if match_var[i] == Some(*xi) {
                            edges[i].push(k + xi);
                        } else {
                            edges[k + xi].push(i);
                        }
                    }
                }
                let comp = scc(total, &edges);
                for (i, v) in vs.iter().enumerate() {
                    let doomed: Vec<i32> = domains[*v as usize]
                        .iter()
                        .copied()
                        .filter(|x| {
                            let xi = vals.iter().position(|y| y == x).expect("in universe");
                            match_var[i] != Some(xi) && comp[i] != comp[k + xi]
                        })
                        .collect();
                    for x in doomed {
                        changed |= remove(
                            domains,
                            trail,
                            trace,
                            prob,
                            *v,
                            x,
                            &tag("all-different"),
                            pruned,
                        );
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
                        changed |= remove(
                            domains,
                            trail,
                            trace,
                            prob,
                            *v,
                            x,
                            &tag("linear-le"),
                            pruned,
                        );
                    }
                }
            }
            Constraint::AbsDiffNe(a, b, k) => {
                let sep = *k as i64;
                let close = |x: i32, y: i32| (x as i64 - y as i64).abs() == sep;
                let bad_a: Vec<i32> = domains[*a as usize]
                    .iter()
                    .copied()
                    .filter(|x| domains[*b as usize].iter().all(|y| close(*x, *y)))
                    .collect();
                for x in bad_a {
                    changed |= remove(
                        domains,
                        trail,
                        trace,
                        prob,
                        *a,
                        x,
                        &tag("absdiff-ne"),
                        pruned,
                    );
                }
                let bad_b: Vec<i32> = domains[*b as usize]
                    .iter()
                    .copied()
                    .filter(|y| domains[*a as usize].iter().all(|x| close(*x, *y)))
                    .collect();
                for y in bad_b {
                    changed |= remove(
                        domains,
                        trail,
                        trace,
                        prob,
                        *b,
                        y,
                        &tag("absdiff-ne"),
                        pruned,
                    );
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
    domains: &mut [Vec<i32>],
    trail: &mut Trail,
    trace: &mut Trace,
    stats: &mut CspStats,
    budget: &mut Budget,
) -> Result<(), PropErr> {
    loop {
        budget.charge(1).map_err(PropErr::Budget)?;
        stats.rounds += 1;
        let changed = propagate_once(prob, domains, trail, trace, &mut stats.pruned)
            .map_err(PropErr::Conflict)?;
        if !changed {
            return Ok(());
        }
    }
}

fn dfs(
    prob: &CspProblem,
    domains: &mut Vec<Vec<i32>>,
    trail: &mut Trail,
    trace: Trace,
    stats: &mut CspStats,
    budget: &mut Budget,
) -> Result<CspOutcome, Exhausted> {
    budget.charge(1)?;
    stats.nodes += 1;
    let mark = trail.mark();
    let mut trace = trace;
    match propagate(prob, domains, trail, &mut trace, stats, budget) {
        Ok(()) => {}
        Err(PropErr::Budget(e)) => {
            trail.undo_to(domains, mark);
            return Err(e);
        }
        Err(PropErr::Conflict(reason)) => {
            trace.push(reason);
            let out = CspOutcome {
                status: Status::Impossible,
                assignment: Vec::new(),
                explanation: trace.flatten(),
                stats: *stats,
            };
            trail.undo_to(domains, mark);
            return Ok(out);
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
    // Minimum-remaining-values, ties broken by lowest variable id. The trail
    // preserves domain order, so the value order matches the old solver.
    let next = domains
        .iter()
        .enumerate()
        .filter(|(_, d)| d.len() > 1)
        .min_by_key(|(i, d)| (d.len(), *i))
        .map(|(i, _)| i)
        .expect("a non-singleton domain exists");
    let mut first_impossible: Option<CspOutcome> = None;
    for val in domains[next].clone() {
        let child_mark = trail.mark();
        let mut child_trace = trace.clone();
        let others: Vec<i32> = domains[next]
            .iter()
            .copied()
            .filter(|x| *x != val)
            .collect();
        for x in others {
            remove(
                domains,
                trail,
                &mut child_trace,
                prob,
                next as VarId,
                x,
                "branch",
                &mut stats.pruned,
            );
        }
        child_trace.push(format!("branch {} = {val}", var_name(prob, next as VarId)));
        match dfs(prob, domains, trail, child_trace, stats, budget)? {
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
            out => {
                trail.undo_to(domains, mark);
                return Ok(out);
            }
        }
        trail.undo_to(domains, child_mark);
    }
    trail.undo_to(domains, mark);
    Ok(first_impossible.unwrap_or(CspOutcome {
        status: Status::Impossible,
        assignment: Vec::new(),
        explanation: trace.flatten(),
        stats: *stats,
    }))
}

/// Solve a finite-domain problem. Returns `Found` with a checked assignment,
/// `Impossible` with the pruning trace, or `Err(Exhausted)` when the budget
/// runs out (which says nothing about satisfiability).
pub fn solve_csp(prob: &CspProblem, budget: &mut Budget) -> Result<CspOutcome, Exhausted> {
    let mut stats = CspStats::default();
    let mut domains: Vec<Vec<i32>> = prob.vars.iter().map(|v| v.domain.clone()).collect();
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
    let mut trail = Trail::default();
    dfs(
        prob,
        &mut domains,
        &mut trail,
        Trace::default(),
        &mut stats,
        budget,
    )
}
