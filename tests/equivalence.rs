//! Optimization-equivalence regressions for the v2.5 merge.
//!
//! Each test pins that an optimized implementation agrees with an independent
//! reference on the answer (not just the cost): a naive scan A\* against the
//! heap A\*, a pairwise BMC encoding against the Sinz encoding, and
//! double-solve determinism for the trail CSP solver. All under fixed step
//! budgets with explicit `Status` asserts.

use axiom::bench::Rng;
use axiom::csp::{solve_csp, verify_csp};
use axiom::puzzle::nqueens;
use axiom::sat::{verify_sat, SatOutcome, SatSolver};
use axiom::search::{astar, verify_path, SearchGraph, SearchOutcome};
use axiom::state::{bmc_clauses, stacking_3, StateGraph};
use axiom::status::Exhausted;
use axiom::{Budget, Status};

// ---- 1. Scan-reference A* vs the heap A* ----------------------------------

/// Textbook naive A\*: full scan for the minimum open node every iteration.
/// Slow and obviously right; the heap version must agree path-for-path.
fn astar_scan(
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
            let mut path = vec![goal];
            let mut at = goal;
            while let Some(p) = prev[at as usize] {
                path.push(p);
                at = p;
            }
            path.reverse();
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

/// Seeded DAG: backbone chain plus ~20% forward shortcuts, zero heuristics
/// (Dijkstra, admissible by construction).
fn seeded_graph() -> SearchGraph {
    let mut rng = Rng::new(0xC10C_4C0C_5EED_2026);
    let n = 40u32;
    let mut g = SearchGraph::new(n as usize);
    for s in 0..n - 1 {
        g.edge(s, s + 1, 1 + rng.below(9) as i64);
    }
    for i in 0..n {
        for j in (i + 2)..n {
            if rng.below(100) < 20 {
                g.edge(i, j, 1 + rng.below(9) as i64);
            }
        }
    }
    g
}

#[test]
fn heap_astar_matches_scan() {
    let g = seeded_graph();
    let mut b = Budget::steps(100_000);
    let scan = astar_scan(&g, 0, 39, &mut b).expect("scan within budget");
    assert_eq!(scan.status, Status::Found);
    let mut b = Budget::steps(100_000);
    let heap = astar(&g, 0, 39, &mut b).expect("heap within budget");
    assert_eq!(heap.status, Status::Found);
    assert_eq!(scan.cost, heap.cost);
    assert_eq!(scan.path, heap.path);
    assert!(verify_path(&g, &heap.path, heap.cost));
}

#[test]
fn heap_astar_matches_scan_on_impossible() {
    let g = SearchGraph::new(2);
    let mut b = Budget::steps(10_000);
    let scan = astar_scan(&g, 0, 1, &mut b).expect("scan within budget");
    assert_eq!(scan.status, Status::Impossible);
    let mut b = Budget::steps(10_000);
    let heap = astar(&g, 0, 1, &mut b).expect("heap within budget");
    assert_eq!(heap.status, Status::Impossible);
}

// ---- 2. Pairwise BMC vs the Sinz BMC -------------------------------------

/// Reference BMC with pairwise at-most-one (quadratic, obviously right).
/// Same state-var numbering as `state.rs`: `x[s][t] = t*n + s + 1`.
fn bmc_clauses_pairwise(g: &StateGraph, bound: u32) -> (u32, Vec<Vec<i32>>) {
    let n = g.num_states;
    assert!(!g.goals.is_empty());
    let var = |s: u32, t: u32| (t * n + s + 1) as i32;
    let mut succ = vec![Vec::<u32>::new(); n as usize];
    let mut pred = vec![Vec::<u32>::new(); n as usize];
    for a in &g.actions {
        if !succ[a.from as usize].contains(&a.to) {
            succ[a.from as usize].push(a.to);
        }
        if !pred[a.to as usize].contains(&a.from) {
            pred[a.to as usize].push(a.from);
        }
    }
    let mut clauses = vec![vec![var(g.initial, 0)]];
    for t in 0..=bound {
        clauses.push((0..n).map(|s| var(s, t)).collect());
        for a in 0..n {
            for b in (a + 1)..n {
                clauses.push(vec![-var(a, t), -var(b, t)]);
            }
        }
    }
    clauses.push(g.goals.iter().map(|s| var(*s, bound)).collect());
    for t in 0..bound {
        for s in 0..n {
            let mut fwd = vec![-var(s, t)];
            for ns in &succ[s as usize] {
                fwd.push(var(*ns, t + 1));
            }
            clauses.push(fwd);
            let mut bwd = vec![-var(s, t + 1)];
            for ps in &pred[s as usize] {
                bwd.push(var(*ps, t));
            }
            clauses.push(bwd);
        }
    }
    (n * (bound + 1), clauses)
}

fn solve_cnf_status(num_vars: u32, clauses: &[Vec<i32>], steps: u64) -> Status {
    let mut solver = SatSolver::new();
    for _ in 0..num_vars {
        solver.new_var();
    }
    for c in clauses {
        solver.add_clause(c);
    }
    let mut budget = Budget::steps(steps);
    match solver.solve(&mut budget).expect("cnf within budget") {
        SatOutcome::Sat { model } => {
            assert!(verify_sat(clauses, &model));
            Status::Found
        }
        SatOutcome::Unsat { .. } => Status::Impossible,
    }
}

#[test]
fn sinz_matches_pairwise_on_stacking() {
    let g = stacking_3();
    for (bound, want) in [(3u32, Status::Found), (2u32, Status::Impossible)] {
        let (nv, pc) = bmc_clauses_pairwise(&g, bound);
        assert_eq!(solve_cnf_status(nv, &pc, 10_000_000), want);
        let cnf = bmc_clauses(&g, bound).expect("valid graph");
        assert_eq!(
            solve_cnf_status(cnf.num_vars, &cnf.clauses, 10_000_000),
            want
        );
    }
}

// ---- 3. Trail CSP determinism --------------------------------------------

#[test]
fn csp_double_solve_agrees() {
    let p = nqueens(8).expect("valid board");
    let mut b = Budget::steps(50_000_000);
    let first = solve_csp(&p, &mut b).expect("within budget");
    assert_eq!(first.status, Status::Found);
    assert!(verify_csp(&p, &first.assignment));
    let mut b = Budget::steps(50_000_000);
    let second = solve_csp(&p, &mut b).expect("within budget");
    assert_eq!(second.status, Status::Found);
    assert_eq!(first.assignment, second.assignment);
}
