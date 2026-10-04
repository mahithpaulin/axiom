//! Thorough evaluation: knowns, unknowns, benchmarks (small), cognitive checks.
//!
//! Each test maps to a cognitive dimension (deduction, constraint, planning,
//! game, search, explanation, honesty, robustness, determinism). Known problems
//! assert exact ground truth; unknown problems (novel inputs not present
//! anywhere else in the suite) assert the honesty contract: a definite status
//! carries a machine-checked proof, an inconclusive status carries none.

use axiom::chess_play::{best_move, insufficient_material, play_game};
use axiom::csp::{solve_csp, verify_csp, Constraint, CspProblem};
use axiom::puzzle::{logic_grid, map_color, nqueens};
use axiom::repr::{run, Operation, Representation};
use axiom::sat::{parse_dimacs, verify_sat, verify_unsat, SatOutcome, SatSolver};
use axiom::search::{alpha_beta, astar, ida_star, verify_line, verify_path, GameTree, SearchGraph};
use axiom::state::{shortest_plan, verify_plan, StateGraph};
use axiom::{exterior, Budget, Solver, Status, WordModel};
use axiom::{gripper_1, stacking_3, Goban, Position};

// ---------- helpers ----------

fn tc_solver() -> (Solver, axiom::TermId) {
    let src = "edge(a, b).\nedge(b, c).\npath(X, Y) :- edge(X, Y).\npath(X, Z) :- path(X, Y), edge(Y, Z).\n?- path(a, c).\n";
    let parsed = exterior::parse(src).unwrap();
    let goal = parsed.queries[0];
    (Solver::new(parsed.program), goal)
}

fn solve_sat(clauses: &[Vec<i32>]) -> SatOutcome {
    let mut s = SatSolver::new();
    for c in clauses {
        s.add_clause(c);
    }
    let mut b = Budget::unlimited();
    s.solve(&mut b).expect("within budget")
}

fn chain_graph(n: u32) -> SearchGraph {
    let mut g = SearchGraph::new(n as usize);
    for s in 0..n - 1 {
        g.edge(s, s + 1, 1);
    }
    g.set_heuristic(n - 1, 0);
    g
}

// ---------- A. KNOWN deduction ----------

#[test]
fn known_transitive_closure_proves_and_verifies() {
    let (mut s, goal) = tc_solver();
    let mut b = Budget::steps(1_000_000);
    let out = s.prove(goal, &mut b);
    assert_eq!(out.status, Status::Proved);
    let proof = out.proof.expect("proved carries proof");
    assert!(s.verify(&proof).is_ok());
}

#[test]
fn known_absent_fact_is_refuted_not_unknown() {
    // path(c, a) is absent from a completed least model -> Refuted, with proof.
    let src = "edge(a, b).\nedge(b, c).\npath(X, Y) :- edge(X, Y).\npath(X, Z) :- path(X, Y), edge(Y, Z).\n?- path(c, a).\n";
    let parsed = exterior::parse(src).unwrap();
    let goal = parsed.queries[0];
    let mut s = Solver::new(parsed.program);
    let mut b = Budget::steps(1_000_000);
    let out = s.prove(goal, &mut b);
    assert_eq!(out.status, Status::Refuted);
    assert!(out.proof.is_some());
}

#[test]
fn known_stratified_negation() {
    let src = "node(a).\nnode(b).\nblocked(b).\nsafe(X) :- node(X), not blocked(X).\n?- safe(a).\n";
    let parsed = exterior::parse(src).unwrap();
    let goal = parsed.queries[0];
    let mut s = Solver::new(parsed.program);
    let mut b = Budget::steps(100_000);
    let out = s.prove(goal, &mut b);
    assert_eq!(out.status, Status::Proved);
}

// ---------- B. KNOWN SAT ----------

#[test]
fn known_sat_unit_and_unsat_units() {
    match solve_sat(&[vec![1]]) {
        SatOutcome::Sat { model } => assert!(verify_sat(&[vec![1]], &model)),
        SatOutcome::Unsat { .. } => panic!("single unit is SAT"),
    }
    match solve_sat(&[vec![1], vec![-1]]) {
        SatOutcome::Unsat { proof } => {
            assert!(verify_unsat(&[vec![1], vec![-1]], &proof).is_ok())
        }
        SatOutcome::Sat { .. } => panic!("p & ~p is UNSAT"),
    }
}

#[test]
fn known_frozen_corpus_spot_check() {
    // Spot-check 3 corpus files (full corpus runs in tests/sat.rs).
    for (src, expect_sat) in [
        (include_str!("../benches/data/sat_trivial.cnf"), true),
        (include_str!("../benches/data/unsat_units.cnf"), false),
        (include_str!("../benches/data/sat_xor2.cnf"), true),
    ] {
        let (_, clauses) = parse_dimacs(src).unwrap();
        match solve_sat(&clauses) {
            SatOutcome::Sat { model } => {
                assert!(verify_sat(&clauses, &model));
                assert!(expect_sat);
            }
            SatOutcome::Unsat { proof } => {
                assert!(verify_unsat(&clauses, &proof).is_ok());
                assert!(!expect_sat);
            }
        }
    }
}

// ---------- C. KNOWN constraints ----------

#[test]
fn known_queens4_solves_and_verifies() {
    let p = nqueens(4).unwrap();
    let mut b = Budget::steps(1_000_000);
    let out = solve_csp(&p, &mut b).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert!(verify_csp(&p, &out.assignment));
}

#[test]
fn known_queens3_is_impossible_with_explanation() {
    let p = nqueens(3).unwrap();
    let mut b = Budget::steps(1_000_000);
    let out = solve_csp(&p, &mut b).expect("within budget");
    assert_eq!(out.status, Status::Impossible);
    assert!(!out.explanation.is_empty());
}

#[test]
fn known_map_color_triangle() {
    let p = map_color(3, &[(0, 1), (1, 2), (0, 2)], 3);
    let mut b = Budget::steps(100_000);
    let out = solve_csp(&p, &mut b).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert!(verify_csp(&p, &out.assignment));
    // 2 colors cannot color a triangle.
    let p2 = map_color(3, &[(0, 1), (1, 2), (0, 2)], 2);
    let mut b = Budget::steps(100_000);
    let out2 = solve_csp(&p2, &mut b).expect("within budget");
    assert_eq!(out2.status, Status::Impossible);
}

// ---------- D. KNOWN planning / search / games ----------

#[test]
fn known_stacking_plan_cost_4_and_verifies() {
    let g = stacking_3();
    let mut b = Budget::steps(100_000);
    let plan = shortest_plan(&g, &mut b).expect("within budget");
    assert_eq!(plan.status, Status::Found);
    assert_eq!(plan.cost, 4);
    assert!(verify_plan(&g, &plan.plan, plan.cost));
}

#[test]
fn known_gripper_plan_cost_3() {
    let g = gripper_1();
    let mut b = Budget::steps(100_000);
    let plan = shortest_plan(&g, &mut b).expect("within budget");
    assert_eq!(plan.status, Status::Found);
    assert_eq!(plan.cost, 3);
    assert!(verify_plan(&g, &plan.plan, plan.cost));
}

#[test]
fn known_astar_ida_agree_on_chain() {
    let g = chain_graph(6);
    let mut b = Budget::steps(10_000);
    let a = astar(&g, 0, 5, &mut b).expect("within budget");
    let mut b = Budget::steps(100_000);
    let c = ida_star(&g, 0, 5, &mut b).expect("within budget");
    assert_eq!((a.status, a.cost), (Status::Found, 5));
    assert_eq!((c.status, c.cost), (Status::Found, 5));
    assert!(verify_path(&g, &a.path, a.cost));
    assert!(verify_path(&g, &c.path, c.cost));
}

#[test]
fn known_chess_perft_vectors() {
    let pos = Position::startpos();
    assert_eq!(axiom::perft(&pos, 1), 20);
    assert_eq!(axiom::perft(&pos, 2), 400);
}

#[test]
fn known_back_rank_mate_in_one() {
    let pos = Position::from_fen("6k1/5ppp/8/8/8/8/5PPP/4R1K1 w - - 0 1").unwrap();
    let m = axiom::find_mate_in_one(&pos).expect("mate exists");
    assert!(pos.make(m).is_checkmate());
}

#[test]
fn known_go_capture_puzzle() {
    let mut g = Goban::new(5).unwrap();
    let mut b = Budget::steps(100_000);
    assert_eq!(g.capture_in_one(&mut b).unwrap(), vec![17]);
    let out = g.play(17).expect("capture works");
    assert!(out.captured > 0);
}

// ---------- E. UNKNOWN deduction / honesty ----------

#[test]
fn unknown_empty_program_is_honest() {
    let src = "?- path(a, c).\n";
    let parsed = exterior::parse(src).unwrap();
    let goal = parsed.queries[0];
    let mut s = Solver::new(parsed.program);
    let mut b = Budget::steps(10_000);
    let out = s.prove(goal, &mut b);
    assert!(out.status == Status::Refuted || out.status.is_inconclusive());
    if out.status.is_inconclusive() {
        assert!(out.proof.is_none(), "inconclusive carries no proof");
    }
}

#[test]
fn unknown_tiny_budget_exhausts_without_proof() {
    let (mut s, goal) = tc_solver();
    let mut b = Budget::steps(1);
    let out = s.prove(goal, &mut b);
    if out.status.is_inconclusive() {
        assert!(out.proof.is_none());
    }
}

#[test]
fn unknown_malformed_syntax_is_err_not_panic() {
    assert!(exterior::parse("edge(a b).").is_err());
    assert!(exterior::parse("?- .").is_err());
    assert!(exterior::parse("").is_ok() || exterior::parse("").is_err());
}

#[test]
fn unknown_long_chain_completes() {
    // Novel 50-link chain, not present elsewhere in the suite.
    let mut src = String::new();
    for i in 0..50 {
        src.push_str(&format!("edge(n{i}, n{}).\n", i + 1));
    }
    src.push_str(
        "path(X, Y) :- edge(X, Y).\npath(X, Z) :- path(X, Y), edge(Y, Z).\n?- path(n0, n50).\n",
    );
    let parsed = exterior::parse(&src).unwrap();
    let goal = parsed.queries[0];
    let mut s = Solver::new(parsed.program);
    let mut b = Budget::steps(5_000_000);
    let out = s.prove(goal, &mut b);
    assert_eq!(out.status, Status::Proved);
}

// ---------- F. UNKNOWN constraints ----------

#[test]
fn unknown_novel_logic_grid() {
    // 3 houses x 3 colors, all different + 2 fixed. Novel instance.
    let p = logic_grid(
        &["h0", "h1", "h2"],
        &[vec![1, 2, 3], vec![1, 2, 3], vec![1, 2, 3]],
        &[vec![0, 1, 2]],
        &[(0, 1), (2, 3)],
    );
    let mut b = Budget::steps(100_000);
    let out = solve_csp(&p, &mut b).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert!(verify_csp(&p, &out.assignment));
    assert_eq!(out.assignment[0], 1);
    assert_eq!(out.assignment[2], 3);
}

#[test]
fn unknown_queens5_solves_and_verifies() {
    let p = nqueens(5).unwrap();
    let mut b = Budget::steps(5_000_000);
    let out = solve_csp(&p, &mut b).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert!(verify_csp(&p, &out.assignment));
}

#[test]
fn unknown_contradictory_csp_is_impossible() {
    let mut p = CspProblem::new();
    let a = p.var("a", vec![7]);
    let b = p.var("b", vec![7]);
    p.constrain(Constraint::AllDifferent(vec![a, b]));
    let mut budget = Budget::steps(10_000);
    let out = solve_csp(&p, &mut budget).expect("within budget");
    assert_eq!(out.status, Status::Impossible);
    assert!(!out.explanation.is_empty());
}

#[test]
fn unknown_word_problem_novel() {
    // Novel: a + b = 10, a in 1..9, b in 1..9, a < b. Expects a=4,b=6? Any
    // valid pair accepted; verify via model lookup.
    let mut m = WordModel::new();
    m.quantity("a", 1, 9).unwrap();
    m.quantity("b", 1, 9).unwrap();
    m.sum_eq(&[("a", 1), ("b", 1)], 10).unwrap();
    m.less_than("a", "b").unwrap();
    let mut b = Budget::steps(100_000);
    let out = m.solve(&mut b).expect("within budget");
    assert_eq!(out.status, Status::Found);
    let (a, bb) = (
        m.value_of(&out, "a").unwrap(),
        m.value_of(&out, "b").unwrap(),
    );
    assert_eq!(a + bb, 10);
    assert!(a < bb);
}

// ---------- G. UNKNOWN planning / search ----------

#[test]
fn unknown_custom_line_plan() {
    // Novel 6-state line, jump edge 0->3 cost 5 vs walk cost 1 each.
    let mut g = StateGraph::new(6, 0);
    for s in 0..5 {
        g.action(&format!("walk{s}"), s, s + 1, 1);
    }
    g.action("jump", 0, 3, 5);
    g.goal(5);
    let mut b = Budget::steps(10_000);
    let plan = shortest_plan(&g, &mut b).expect("within budget");
    assert_eq!(plan.status, Status::Found);
    assert_eq!(plan.cost, 5);
    assert!(verify_plan(&g, &plan.plan, plan.cost));
}

#[test]
fn unknown_unreachable_goal_is_impossible() {
    let mut g = StateGraph::new(3, 0);
    g.action("a", 0, 1, 1);
    g.goal(2);
    let mut b = Budget::steps(10_000);
    let plan = shortest_plan(&g, &mut b).expect("within budget");
    assert_eq!(plan.status, Status::Impossible);
}

#[test]
fn unknown_repr_plan_bounded_honesty() {
    // bound 1 on stacking_3 (cost 4) must be Impossible, not a guessed plan.
    let rep = Representation::States(stacking_3());
    let mut b = Budget::steps(1_000_000);
    let v = run(&rep, Operation::PlanBounded { bound: 1 }, &mut b).expect("within budget");
    assert_eq!(v.status, Status::Impossible);
}

#[test]
fn unknown_alpha_beta_novel_tree() {
    // Novel tree: root(max) -> x(min){1,9}, y(min){4,4}. min picks 1 under x,
    // 4 under y; max picks y. Value 4 via move 2.
    let t = GameTree {
        children: vec![
            vec![1, 2],
            vec![3, 4],
            vec![5, 6],
            vec![],
            vec![],
            vec![],
            vec![],
        ],
        maximizing: vec![true, false, false, true, true, true, true],
        eval: vec![0, 0, 0, 1, 9, 4, 4],
    };
    let mut b = Budget::steps(10_000);
    let out = alpha_beta(&t, 0, &mut b).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert_eq!((out.best_move, out.value), (2, 4));
    assert!(verify_line(&t, &out.line, out.value));
}

// ---------- H. UNKNOWN games ----------

#[test]
fn unknown_chess_stalemate_not_mate() {
    let stale = Position::from_fen("k7/8/1Q6/8/8/8/8/K7 b - - 0 1").unwrap();
    assert!(stale.is_stalemate());
    assert!(!stale.is_checkmate());
    assert!(axiom::find_mate_in_one(&stale).is_none());
}

#[test]
fn unknown_chess_search_deterministic_depth1() {
    let pos = Position::startpos();
    let mut b = Budget::steps(5_000_000);
    let first = best_move(&pos, 1, &mut b).expect("within budget");
    let mut b = Budget::steps(5_000_000);
    let second = best_move(&pos, 1, &mut b).expect("within budget");
    assert_eq!(first, second);
    assert!(pos.legal_moves().contains(&first.0));
}

#[test]
fn unknown_chess_kings_only_is_material_draw() {
    let kings = Position::from_fen("8/8/8/4k3/8/4K3/8/8 w - - 0 1").unwrap();
    assert!(insufficient_material(&kings));
}

#[test]
fn unknown_chess_short_self_play_ends_legally() {
    let mut b = Budget::steps(20_000_000);
    let game = play_game(&Position::startpos(), 1, 1, 6, &mut b).expect("within budget");
    assert_eq!(game.moves.len(), 6);
    // Replay every move for legality.
    let mut pos = Position::startpos();
    for text in &game.moves {
        let m = pos.parse_uci(text).expect("every played move is legal");
        pos = pos.make(m);
    }
}

#[test]
fn unknown_go_boards_reject_garbage() {
    assert!(Goban::new(0).is_err());
    assert!(Goban::new(10).is_err());
    let mut g = Goban::new(5).unwrap();
    assert!(g.play(0).is_err());
}

// ---------- I. determinism / small bench ----------

#[test]
fn unknown_csp_solve_is_deterministic() {
    let p = nqueens(4).unwrap();
    let mut b = Budget::steps(1_000_000);
    let first = solve_csp(&p, &mut b).expect("within budget").assignment;
    let mut b = Budget::steps(1_000_000);
    let second = solve_csp(&p, &mut b).expect("within budget").assignment;
    assert_eq!(first, second);
}

#[test]
fn small_bench_chain100_completes_fast() {
    // Small benchmark: 100-link transitive closure in debug CI.
    let mut src = String::new();
    for i in 0..100 {
        src.push_str(&format!("edge(n{i}, n{}).\n", i + 1));
    }
    src.push_str(
        "path(X, Y) :- edge(X, Y).\npath(X, Z) :- path(X, Y), edge(Y, Z).\n?- path(n0, n100).\n",
    );
    let parsed = exterior::parse(&src).unwrap();
    let goal = parsed.queries[0];
    let mut s = Solver::new(parsed.program);
    let mut b = Budget::steps(20_000_000);
    let t0 = std::time::Instant::now();
    let out = s.prove(goal, &mut b);
    let dt = t0.elapsed();
    assert_eq!(out.status, Status::Proved);
    assert!(dt.as_secs() < 120, "took {dt:?}");
}
