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
use axiom::{Budget, Goban, Position, StateGraph, Status, WordModel};

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

    // 2b. Hard sudoku (AI Escargot): exercises propagation strength.
    b.run_once("csp_sudoku_hard", |_| {
        let t0 = std::time::Instant::now();
        let src = "1....7.9..3..2...8..96..5....53..9...1..8...26....1...2..9..4....5....7..7...43";
        let p = sudoku9(src).expect("81-cell puzzle");
        let mut budget = Budget::steps(5_000_000_000);
        let out = axiom::solve_csp(&p, &mut budget).expect("within budget");
        assert_eq!(out.status, Status::Found);
        assert!(axiom::verify_csp(&p, &out.assignment));
        let ops = out.stats.nodes + out.stats.pruned;
        perf("csp_sudoku_hard", t0.elapsed().as_secs_f64() * 1000.0, ops);
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

    // 4. BMC lowering solved by the SAT core: 60-state chain, bound 60.
    b.run_once("sat_bmc_chain60", |_| {
        let t0 = std::time::Instant::now();
        let mut graph = StateGraph::new(60, 0);
        for s in 0..59 {
            graph.action("step", s, s + 1, 1);
        }
        graph.goal(59);
        let cnf = bmc_clauses(&graph, 60 - 1).expect("valid graph");
        let mut s = SatSolver::new();
        for _ in 0..cnf.num_vars {
            s.new_var();
        }
        for c in &cnf.clauses {
            s.add_clause(c);
        }
        let mut budget = Budget::steps(2_000_000_000);
        let ops = match s.solve(&mut budget).expect("within budget") {
            SatOutcome::Sat { .. } => s.stats.propagations + s.stats.conflicts + s.stats.decisions,
            SatOutcome::Unsat { .. } => panic!("bound 59 reaches state 59"),
        };
        perf("sat_bmc_chain60", t0.elapsed().as_secs_f64() * 1000.0, ops);
        ops
    });

    // 5. A* + IDA* on a 150x150 open grid (22500 nodes).
    b.run_once("search_grid22500", |_| {
        let t0 = std::time::Instant::now();
        let n = 150usize;
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
        let mut budget = Budget::steps(5_000_000_000);
        let a = astar(&g, 0, (n * n - 1) as u32, &mut budget).expect("within budget");
        assert_eq!(a.status, Status::Found);
        let mut budget = Budget::steps(5_000_000_000);
        let d = ida_star(&g, 0, (n * n - 1) as u32, &mut budget).expect("within budget");
        assert_eq!((d.status, d.cost), (Status::Found, a.cost));
        let ops = a.expanded + d.expanded;
        perf("search_grid22500", t0.elapsed().as_secs_f64() * 1000.0, ops);
        ops
    });

    // 6. Chess perft(4) from startpos.
    b.run_once("chess_perft4", |_| {
        let t0 = std::time::Instant::now();
        let nodes = axiom::perft(&Position::startpos(), 4);
        assert_eq!(nodes, 197_281);
        perf("chess_perft4", t0.elapsed().as_secs_f64() * 1000.0, nodes);
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

    // 8. Scripted 9x9 game: row-major alternating stones (81 attempts,
    //    illegal ones skipped). Stresses liberty computation.
    b.run_once("go_scripted_game", |_| {
        let t0 = std::time::Instant::now();
        let mut g = Goban::new(9).unwrap();
        let mut placed = 0u64;
        for i in 0..81 {
            if g.play(i).is_ok() {
                placed += 1;
            }
        }
        assert!(placed > 60, "most opening points are legal");
        perf(
            "go_scripted_game",
            t0.elapsed().as_secs_f64() * 1000.0,
            placed,
        );
        placed
    });

    // 9. Dijkstra over a 20000-node chain.
    b.run_once("plan_chain20000", |_| {
        let t0 = std::time::Instant::now();
        let mut graph = StateGraph::new(20000, 0);
        for s in 0..19999 {
            graph.action("step", s, s + 1, 1);
        }
        graph.goal(19999);
        let mut budget = Budget::steps(5_000_000_000);
        let out = shortest_plan(&graph, &mut budget).expect("within budget");
        assert_eq!(out.status, Status::Found);
        let ops = out.explored;
        perf("plan_chain20000", t0.elapsed().as_secs_f64() * 1000.0, ops);
        ops
    });

    b.report();
}
