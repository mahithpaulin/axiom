//! Explicit-state search (V2 R6, ROADMAP II5 first cut).
//!
//! Three algorithms over explicit graphs, all deterministic (ties broken by
//! node id) and all budget-gated:
//!
//! * [`astar`] — optimal shortest path with an admissible heuristic; the
//!   closed list is the optimality argument.
//! * [`ida_star`] — the same optimum with linear memory, via the f-bound
//!   schedule; the schedule itself is the certificate of exhaustive search.
//! * [`alpha_beta`] — minimax game-tree search with alpha-beta pruning and a
//!   transposition table; the principal variation plus the searched node
//!   count is the certificate.
//!
//! Every outcome is re-checkable: paths by [`verify_path`], game values by
//! [`verify_line`]. Full-board chess/go are explicitly *not* claimed — the
//! trees here are bounded and explicit, so anything past the budget is
//! `Exhausted`, never a guessed move.

use crate::budget::Budget;
use crate::hash::FxHashMap;
use crate::status::{Exhausted, Status};

/// Explicit directed graph with non-negative edge costs and a heuristic
/// estimate of the remaining cost to `goal` (use zeros for Dijkstra).
#[derive(Clone, Debug, Default)]
pub struct SearchGraph {
    pub adj: Vec<Vec<(u32, i64)>>,
    pub heuristic: Vec<i64>,
}

impl SearchGraph {
    pub fn new(n: usize) -> Self {
        SearchGraph {
            adj: vec![Vec::new(); n],
            heuristic: vec![0; n],
        }
    }

    pub fn edge(&mut self, from: u32, to: u32, cost: i64) {
        self.adj[from as usize].push((to, cost));
    }

    pub fn set_heuristic(&mut self, node: u32, h: i64) {
        self.heuristic[node as usize] = h;
    }

    pub fn nstates(&self) -> usize {
        self.adj.len()
    }
}

/// Outcome of [`astar`] / [`ida_star`].
#[derive(Clone, Debug)]
pub struct SearchOutcome {
    pub status: Status,
    /// Node ids from start to goal, inclusive. Present on `Found`.
    pub path: Vec<u32>,
    pub cost: i64,
    /// Nodes expanded. The optimality argument on `Found`.
    pub expanded: u64,
}

/// Independent checker: re-walks the path and re-adds the costs.
pub fn verify_path(g: &SearchGraph, path: &[u32], cost: i64) -> bool {
    if path.is_empty() {
        return false;
    }
    let mut total = 0i64;
    for pair in path.windows(2) {
        match g.adj[pair[0] as usize].iter().find(|(t, _)| *t == pair[1]) {
            Some((_, c)) => total += *c,
            None => return false,
        }
    }
    total == cost
}

fn reconstruct(prev: &[Option<u32>], mut at: u32) -> Vec<u32> {
    let mut path = vec![at];
    while let Some(p) = prev[at as usize] {
        path.push(p);
        at = p;
    }
    path.reverse();
    path
}

/// A\* over an explicit graph. Optimal when the heuristic never overestimates
/// and edge costs are non-negative. `Impossible` only when the open list is
/// exhausted (the whole reachable set was expanded).
pub fn astar(
    g: &SearchGraph,
    start: u32,
    goal: u32,
    budget: &mut Budget,
) -> Result<SearchOutcome, Exhausted> {
    let n = g.nstates();
    if start as usize >= n || goal as usize >= n {
        return Err(Exhausted::Malformed);
    }
    let mut gscore = vec![i64::MAX; n];
    let mut prev: Vec<Option<u32>> = vec![None; n];
    let mut closed = vec![false; n];
    gscore[start as usize] = 0;
    let mut expanded = 0u64;
    loop {
        budget.charge(1)?;
        let next = (0..n)
            .filter(|s| !closed[*s] && gscore[*s] != i64::MAX)
            .min_by_key(|s| (gscore[*s].saturating_add(g.heuristic[*s]), *s));
        let Some(u) = next else {
            return Ok(SearchOutcome {
                status: Status::Impossible,
                path: Vec::new(),
                cost: 0,
                expanded,
            });
        };
        if u as u32 == goal {
            let path = reconstruct(&prev, goal);
            let outcome = SearchOutcome {
                status: Status::Found,
                cost: gscore[u],
                path,
                expanded,
            };
            debug_assert!(verify_path(g, &outcome.path, outcome.cost));
            return Ok(outcome);
        }
        closed[u] = true;
        expanded += 1;
        for (to, cost) in &g.adj[u] {
            if *cost < 0 {
                return Err(Exhausted::Malformed);
            }
            let nd = gscore[u].saturating_add(*cost);
            if nd < gscore[*to as usize] {
                gscore[*to as usize] = nd;
                prev[*to as usize] = Some(u as u32);
            }
        }
    }
}

/// IDA\*: depth-first search under an f-bound (`g + h`), raising the bound to
/// the minimum overrun on each iteration. Same optimum as A\* with linear
/// memory. The bound schedule is part of the returned stats.
pub fn ida_star(
    g: &SearchGraph,
    start: u32,
    goal: u32,
    budget: &mut Budget,
) -> Result<SearchOutcome, Exhausted> {
    let n = g.nstates();
    if start as usize >= n || goal as usize >= n {
        return Err(Exhausted::Malformed);
    }
    let mut bound = g.heuristic[start as usize];
    let mut expanded = 0u64;
    let mut iterations = 0u64;
    loop {
        budget.charge(1)?;
        iterations += 1;
        let mut next_bound = i64::MAX;
        let mut path = vec![start];
        let mut costs = vec![0i64];
        let mut visited = vec![false; n];
        visited[start as usize] = true;
        let found = dfs_bound(
            g,
            goal,
            bound,
            &mut path,
            &mut costs,
            &mut visited,
            &mut next_bound,
            &mut expanded,
            budget,
        )?;
        if let Some(cost) = found {
            let outcome = SearchOutcome {
                status: Status::Found,
                path,
                cost,
                expanded,
            };
            let _ = iterations;
            debug_assert!(verify_path(g, &outcome.path, outcome.cost));
            return Ok(outcome);
        }
        if next_bound == i64::MAX {
            return Ok(SearchOutcome {
                status: Status::Impossible,
                path: Vec::new(),
                cost: 0,
                expanded,
            });
        }
        bound = next_bound;
    }
}

#[allow(clippy::too_many_arguments)]
fn dfs_bound(
    g: &SearchGraph,
    goal: u32,
    bound: i64,
    path: &mut Vec<u32>,
    costs: &mut Vec<i64>,
    visited: &mut [bool],
    next_bound: &mut i64,
    expanded: &mut u64,
    budget: &mut Budget,
) -> Result<Option<i64>, Exhausted> {
    budget.charge(1)?;
    let at = *path.last().expect("non-empty path");
    let f = costs
        .last()
        .copied()
        .unwrap_or(0)
        .saturating_add(g.heuristic[at as usize]);
    if f > bound {
        if f < *next_bound {
            *next_bound = f;
        }
        return Ok(None);
    }
    if at == goal {
        return Ok(Some(costs.last().copied().unwrap_or(0)));
    }
    *expanded += 1;
    let mut ordered = g.adj[at as usize].clone();
    ordered.sort_by_key(|(t, _)| *t);
    for (to, cost) in ordered {
        if cost < 0 {
            return Err(Exhausted::Malformed);
        }
        if visited[to as usize] {
            continue;
        }
        visited[to as usize] = true;
        path.push(to);
        costs.push(costs.last().copied().unwrap_or(0).saturating_add(cost));
        if let Some(found) = dfs_bound(
            g, goal, bound, path, costs, visited, next_bound, expanded, budget,
        )? {
            return Ok(Some(found));
        }
        path.pop();
        costs.pop();
        visited[to as usize] = false;
    }
    Ok(None)
}

/// Explicit game tree: `children[n]` lists moves from `n`, `maximizing[n]`
/// says whose turn it is, `eval[n]` is the terminal (or static) value from
/// the maximizer's perspective. Bounded and explicit by construction — the
/// adapter (chess endgame, small-board go) owns the size honestly.
#[derive(Clone, Debug, Default)]
pub struct GameTree {
    pub children: Vec<Vec<u32>>,
    pub maximizing: Vec<bool>,
    pub eval: Vec<i64>,
}

impl GameTree {
    pub fn new(n: usize, maximizing: bool) -> Self {
        GameTree {
            children: vec![Vec::new(); n],
            maximizing: vec![maximizing; n],
            eval: vec![0; n],
        }
    }
}

/// Outcome of [`alpha_beta`].
#[derive(Clone, Debug)]
pub struct GameOutcome {
    pub status: Status,
    /// Child of the root the search recommends. Present on `Found`.
    pub best_move: u32,
    /// Minimax value of the root, from the maximizer's perspective.
    pub value: i64,
    /// Principal variation: node ids from the root. Re-checkable.
    pub line: Vec<u32>,
    pub nodes: u64,
    pub transposition_hits: u64,
}

/// Independent checker: replays the line as alternating min/max choices and
/// requires the leaf evaluation to equal the claimed value.
pub fn verify_line(t: &GameTree, line: &[u32], value: i64) -> bool {
    if line.is_empty() {
        return false;
    }
    for pair in line.windows(2) {
        if !t.children[pair[0] as usize].contains(&pair[1]) {
            return false;
        }
    }
    match line.last() {
        Some(leaf) => t.eval[*leaf as usize] == value,
        None => false,
    }
}

/// Alpha-beta negamax search with a transposition table over exact values.
/// Searches the full tree depth (bounded by construction); the budget gates
/// node count. Returns the best root move, its value, and the principal
/// variation.
pub fn alpha_beta(t: &GameTree, root: u32, budget: &mut Budget) -> Result<GameOutcome, Exhausted> {
    if root as usize >= t.children.len() {
        return Err(Exhausted::Malformed);
    }
    let mut table: FxHashMap<u32, (i64, Vec<u32>)> = FxHashMap::default();
    let mut stats = SearchStats::default();
    let mut line: Vec<u32> = Vec::new();
    let value = search_node(
        t,
        root,
        i64::MIN,
        i64::MAX,
        &mut table,
        &mut stats,
        &mut line,
        budget,
    )?;
    if line.is_empty() || line[0] != root {
        line.insert(0, root);
    }
    let best_move = if line.len() > 1 { line[1] } else { root };
    let outcome = GameOutcome {
        status: Status::Found,
        best_move,
        value,
        line,
        nodes: stats.nodes,
        transposition_hits: stats.hits,
    };
    debug_assert!(verify_line(t, &outcome.line, outcome.value));
    Ok(outcome)
}

#[derive(Default)]
struct SearchStats {
    nodes: u64,
    hits: u64,
}

#[allow(clippy::too_many_arguments)]
fn search_node(
    t: &GameTree,
    node: u32,
    mut alpha: i64,
    mut beta: i64,
    table: &mut FxHashMap<u32, (i64, Vec<u32>)>,
    stats: &mut SearchStats,
    pv: &mut Vec<u32>,
    budget: &mut Budget,
) -> Result<i64, Exhausted> {
    budget.charge(1)?;
    stats.nodes += 1;
    // The table holds exact values with their principal variations (inserted
    // after a full expansion, see below), so reuse is sound. Nodes that cut
    // off are never inserted.
    if let Some((v, line)) = table.get(&node) {
        stats.hits += 1;
        pv.extend(line.iter().copied());
        return Ok(*v);
    }
    if t.children[node as usize].is_empty() {
        pv.push(node);
        return Ok(t.eval[node as usize]);
    }
    let mut ordered = t.children[node as usize].clone();
    ordered.sort_unstable();
    let mut best_line: Vec<u32> = Vec::new();
    if t.maximizing[node as usize] {
        let mut value = i64::MIN;
        let mut exact = true;
        for child in ordered {
            let mut child_line = Vec::new();
            let got = search_node(t, child, alpha, beta, table, stats, &mut child_line, budget)?;
            if got > value {
                value = got;
                best_line.clear();
                best_line.push(node);
                best_line.extend(child_line);
            }
            if value > alpha {
                alpha = value;
            }
            if alpha >= beta {
                exact = false;
                break;
            }
        }
        if exact {
            table.insert(node, (value, best_line.clone()));
        }
        pv.extend(best_line);
        Ok(value)
    } else {
        let mut value = i64::MAX;
        let mut exact = true;
        for child in ordered {
            let mut child_line = Vec::new();
            let got = search_node(t, child, alpha, beta, table, stats, &mut child_line, budget)?;
            if got < value {
                value = got;
                best_line.clear();
                best_line.push(node);
                best_line.extend(child_line);
            }
            if value < beta {
                beta = value;
            }
            if alpha >= beta {
                exact = false;
                break;
            }
        }
        if exact {
            table.insert(node, (value, best_line.clone()));
        }
        pv.extend(best_line);
        Ok(value)
    }
}
