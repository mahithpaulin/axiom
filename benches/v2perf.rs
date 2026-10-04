//! V2 performance bench: one row per capability, deterministic work
//! counters as `ops` plus wall time. `PERF:` lines are machine-readable for
//! `.github/workflows/perf.yml`, which runs this file against the branch and
//! against `main` and prints the comparison. Correctness lives in
//! `tests/v2.rs`; this measures cost. Run with `cargo bench --bench v2perf`.
//!
//! This file must keep compiling against `main` (perf.yml copies it onto a
//! `main` checkout): use only stable public API, no experimental items.

use axiom::bench::Bench;
use axiom::puzzle::{nqueens, sudoku9};
use axiom::sat::{SatOutcome, SatSolver};
use axiom::search::{alpha_beta, astar, ida_star};
use axiom::state::{bmc_clauses, shortest_plan};
use axiom::{Budget, Goban, Position, StateGraph, Status, WordModel, BLACK, WHITE};

fn main() {
    let mut b = Bench::new("axiom -- V2 capability costs (branch vs main)");
    b.note("single-threaded; step budgets bound work, time is measured");
    b.note("PERF lines: name wall_ms ops (parsed by perf.yml)");

    // 1. Classic sudoku through CSP.
    let mut perf = |name: &str, wall: f64, ops: u64| {
        println!("PERF {name} wall={wall:.2} ops={ops}");
    };
    b.run_once("csp_sudoku", |_| {
        let t0 = std::time::Instant::now();
        let p = sudoku9(
            "53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79",
        )
        .expect("valid puzzle");
        let mut budget = Budget::steps(500_000_000);
        let out = axiom::solve_csp(&p, &mut budget).expect("within budget");
        assert_eq!(out.status, Status::Found);
        let ops = out.stats.nodes + out.stats.pruned;
        perf("csp_sudoku", t0.elapsed().as_secs_f64() * 1000.0, ops);
        ops
    });

    // 2. 8-queens.
    b.run_once("csp_queens8", |_| {
        let t0 = std::time::Instant::now();
        let p = nqueens(8).expect("valid board");
        let mut budget = Budget::steps(500_000_000);
        let out = axiom::solve_csp(&p, &mut budget).expect("within budget");
        assert_eq!(out.status, Status::Found);
        let ops = out.stats.nodes + out.stats.pruned;
        perf("csp_queens8", t0.elapsed().as_secs_f64() * 1000.0, ops);
        ops
    });

    // 3. Word coins problem.
    b.run_once("word_coins", |_| {
        let t0 = std::time::Instant::now();
        let mut m = WordModel::new();
        m.quantity("nickels", 0, 30).unwrap();
        m.quantity("dimes", 0, 30).unwrap();
        m.quantity("quarters", 0, 30).unwrap();
        m.sum_eq(&[("nickels", 1), ("dimes", 1), ("quarters", 1)], 30)
            .unwrap();
        m.sum_eq(&[("nickels", 5), ("dimes", 10), ("quarters", 25)], 500)
            .unwrap();
        let mut budget = Budget::steps(100_000_000);
        let out = m.solve(&mut budget).expect("within budget");
        assert_eq!(out.status, Status::Found);
        let ops = out.stats.nodes + out.stats.pruned;
        perf("word_coins", t0.elapsed().as_secs_f64() * 1000.0, ops);
        ops
    });

    // 4. BMC lowering solved by the SAT core.
    b.run_once("sat_bmc_stacking", |_| {
        let t0 = std::time::Instant::now();
        let cnf = bmc_clauses(&axiom::stacking_3(), 3).expect("valid graph");
        let mut s = SatSolver::new();
        for _ in 0..cnf.num_vars {
            s.new_var();
        }
        for c in &cnf.clauses {
            s.add_clause(c);
        }
        let mut budget = Budget::steps(100_000_000);
        let ops = match s.solve(&mut budget).expect("within budget") {
            SatOutcome::Sat { .. } => s.stats.propagations + s.stats.conflicts + s.stats.decisions,
            SatOutcome::Unsat { .. } => panic!("bound 3 reaches the goal"),
        };
        perf("sat_bmc_stacking", t0.elapsed().as_secs_f64() * 1000.0, ops);
        ops
    });

    // 5. A* + IDA* on a 45x45 open grid (2025 nodes).
    b.run_once("search_grid2025", |_| {
        let t0 = std::time::Instant::now();
        let n = 45usize;
        let mut g = axiom::SearchGraph::new(n * n);
        for r in 0..n {
            for c in 0..n {
                let id = (r * n + c) as u32;
                if c + 1 < n {
                    g.edge(id, id + 1, 1);
                    g.edge(id + 1, id, 1);
                }
                if r + 1 < n {
                    g.edge(id, id + n as u32, 1);
                    g.edge(id + n as u32, id, 1);
                }
                g.set_heuristic(id, ((n - 1 - r) + (n - 1 - c)) as i64);
            }
        }
        let mut budget = Budget::steps(500_000_000);
        let a = astar(&g, 0, (n * n - 1) as u32, &mut budget).expect("within budget");
        assert_eq!(a.status, Status::Found);
        let mut budget = Budget::steps(500_000_000);
        let d = ida_star(&g, 0, (n * n - 1) as u32, &mut budget).expect("within budget");
        assert_eq!((d.status, d.cost), (Status::Found, a.cost));
        let ops = a.expanded + d.expanded;
        perf("search_grid2025", t0.elapsed().as_secs_f64() * 1000.0, ops);
        ops
    });

    // 6. Chess perft(3) from startpos.
    b.run_once("chess_perft3", |_| {
        let t0 = std::time::Instant::now();
        let nodes = axiom::perft(&Position::startpos(), 3);
        assert_eq!(nodes, 8902);
        perf("chess_perft3", t0.elapsed().as_secs_f64() * 1000.0, nodes);
        nodes
    });

    // 7. Mate tree export + alpha-beta.
    b.run_once("chess_mate_tree", |_| {
        let t0 = std::time::Instant::now();
        let pos = Position::from_fen("6k1/5ppp/8/8/8/8/5PPP/4R1K1 w - - 0 1").expect("valid fen");
        let mut budget = Budget::steps(100_000_000);
        let tree = axiom::endgame_tree(&pos, 3, &mut budget).expect("within budget");
        let treenodes = tree.children.len() as u64;
        let mut budget = Budget::steps(100_000_000);
        let out = alpha_beta(&tree, 0, &mut budget).expect("within budget");
        assert_eq!(out.status, Status::Found);
        let ops = treenodes + out.nodes;
        perf("chess_mate_tree", t0.elapsed().as_secs_f64() * 1000.0, ops);
        ops
    });

    // 8. Go capture scan on a busy 9x9 board.
    b.run_once("go_capture_scan", |_| {
        let t0 = std::time::Instant::now();
        let mut g = Goban::new(9).unwrap();
        for i in (0..81).step_by(3) {
            g.set(i, BLACK);
        }
        for i in (1..81).step_by(7) {
            g.set(i, WHITE);
        }
        let mut budget = Budget::steps(10_000_000);
        let found = g.capture_in_one(&mut budget).expect("within budget");
        let _ = found;
        let ops = 81u64;
        perf("go_capture_scan", t0.elapsed().as_secs_f64() * 1000.0, ops);
        ops
    });

    // 9. Dijkstra over a 2000-node chain.
    b.run_once("plan_chain2000", |_| {
        let t0 = std::time::Instant::now();
        let mut graph = StateGraph::new(2000, 0);
        for s in 0..1999 {
            graph.action("step", s, s + 1, 1);
        }
        graph.goal(1999);
        let mut budget = Budget::steps(100_000_000);
        let out = shortest_plan(&graph, &mut budget).expect("within budget");
        assert_eq!(out.status, Status::Found);
        let ops = out.explored;
        perf("plan_chain2000", t0.elapsed().as_secs_f64() * 1000.0, ops);
        ops
    });

    b.report();
}
