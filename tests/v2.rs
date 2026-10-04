//! V2 representation tests: each representation solves something real, and
//! every definite answer passes its independent checker. The cross-engine
//! agreements (A\* vs IDA\*, plan vs BMC-vs-SAT) are the regression net.

use axiom::csp::{solve_csp, verify_csp, Constraint, CspProblem};
use axiom::puzzle::{logic_grid, map_color, nqueens, sudoku9};
use axiom::repr::{run, Operation, Representation};
use axiom::search::{alpha_beta, astar, ida_star, verify_line, verify_path, GameTree, SearchGraph};
use axiom::state::{bmc_clauses, shortest_plan, verify_plan, StateGraph};
use axiom::{Budget, Status};

fn sudoku4() -> CspProblem {
    let mut p = CspProblem::new();
    let cell = |r: usize, c: usize| (r * 4 + c) as u32;
    for r in 0..4 {
        for c in 0..4 {
            p.var(&format!("r{r}c{c}"), vec![1, 2, 3, 4]);
        }
    }
    for r in 0..4 {
        p.constrain(Constraint::AllDifferent(
            (0..4).map(|c| cell(r, c)).collect(),
        ));
        p.constrain(Constraint::AllDifferent(
            (0..4).map(|rr| cell(rr, r)).collect(),
        ));
    }
    for (br, bc) in [(0, 0), (0, 2), (2, 0), (2, 2)] {
        let mut box_cells = Vec::new();
        for r in br..br + 2 {
            for c in bc..bc + 2 {
                box_cells.push(cell(r, c));
            }
        }
        p.constrain(Constraint::AllDifferent(box_cells));
    }
    // One valid grid with four blanks removed (0,0) (1,1) (2,2) (3,3).
    let grid = [[1, 2, 3, 4], [3, 4, 1, 2], [2, 1, 4, 3], [4, 3, 2, 1]];
    for (r, row) in grid.iter().enumerate() {
        for (c, val) in row.iter().enumerate() {
            if (r, c) != (0, 0) && (r, c) != (1, 1) && (r, c) != (2, 2) && (r, c) != (3, 3) {
                p.constrain(Constraint::ValueEq(cell(r, c), *val));
            }
        }
    }
    p
}

#[test]
fn sudoku_solves_and_verifies() {
    let p = sudoku4();
    let mut budget = Budget::steps(1_000_000);
    let out = solve_csp(&p, &mut budget).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert!(verify_csp(&p, &out.assignment));
    assert_eq!(out.assignment.len(), 16);
}

#[test]
fn impossible_carries_an_explanation() {
    let mut p = CspProblem::new();
    let a = p.var("a", vec![1]);
    let b = p.var("b", vec![1]);
    p.constrain(Constraint::AllDifferent(vec![a, b]));
    let mut budget = Budget::steps(10_000);
    let out = solve_csp(&p, &mut budget).expect("within budget");
    assert_eq!(out.status, Status::Impossible);
    assert!(!out.explanation.is_empty());
}

#[test]
fn word_arithmetic_twice_as_old() {
    // x is twice y; both in 1..12; x <= 9; x + y <= 15.
    let mut p = CspProblem::new();
    let x = p.var("x", (1..=12).collect());
    let y = p.var("y", (1..=12).collect());
    p.constrain(Constraint::LinearLe {
        coeffs: vec![(x, 1), (y, -2)],
        bound: 0,
    });
    p.constrain(Constraint::LinearLe {
        coeffs: vec![(x, -1), (y, 2)],
        bound: 0,
    });
    p.constrain(Constraint::LinearLe {
        coeffs: vec![(x, 1)],
        bound: 9,
    });
    p.constrain(Constraint::LinearLe {
        coeffs: vec![(x, 1), (y, 1)],
        bound: 15,
    });
    let mut budget = Budget::steps(100_000);
    let out = solve_csp(&p, &mut budget).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert!(verify_csp(&p, &out.assignment));
    assert_eq!(out.assignment[x as usize], 2 * out.assignment[y as usize]);
}

#[test]
fn exhausted_budget_says_nothing() {
    let p = sudoku4();
    let mut budget = Budget::steps(0);
    assert!(solve_csp(&p, &mut budget).is_err());
}

fn chain3() -> StateGraph {
    let mut g = StateGraph::new(3, 0);
    g.action("a01", 0, 1, 1);
    g.action("a12", 1, 2, 1);
    g.goal(2);
    g
}

#[test]
fn shortest_plan_replays() {
    let g = chain3();
    let mut budget = Budget::steps(10_000);
    let out = shortest_plan(&g, &mut budget).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert_eq!(out.plan, vec!["a01".to_string(), "a12".to_string()]);
    assert!(verify_plan(&g, &out.plan, out.cost));
    assert!(!verify_plan(&g, &out.plan, out.cost + 1));
    assert!(!verify_plan(&g, &["a12".to_string()], 1));
}

#[test]
fn bmc_agrees_with_the_plan() {
    let g = chain3();
    // Reachable in exactly 2 steps, unreachable in exactly 1.
    let cnf2 = bmc_clauses(&g, 2).expect("valid graph");
    let rep2 = Representation::Clauses {
        num_vars: cnf2.num_vars,
        clauses: cnf2.clauses,
    };
    let mut budget = Budget::steps(1_000_000);
    let found = run(&rep2, Operation::Solve, &mut budget).expect("within budget");
    assert_eq!(found.status, Status::Found);

    let cnf1 = bmc_clauses(&g, 1).expect("valid graph");
    let rep1 = Representation::Clauses {
        num_vars: cnf1.num_vars,
        clauses: cnf1.clauses,
    };
    let mut budget = Budget::steps(1_000_000);
    let impossible = run(&rep1, Operation::Solve, &mut budget).expect("within budget");
    assert_eq!(impossible.status, Status::Impossible);
}

#[test]
fn disconnected_graph_is_impossible_both_ways() {
    let mut g = StateGraph::new(2, 0);
    g.goal(1);
    let mut budget = Budget::steps(10_000);
    let out = shortest_plan(&g, &mut budget).expect("within budget");
    assert_eq!(out.status, Status::Impossible);
}

fn route_graph() -> SearchGraph {
    // 0 ->1 (1), 0 ->2 (4), 1 ->2 (1), 1 ->3 (5), 2 ->3 (1).
    let mut g = SearchGraph::new(4);
    g.edge(0, 1, 1);
    g.edge(0, 2, 4);
    g.edge(1, 2, 1);
    g.edge(1, 3, 5);
    g.edge(2, 3, 1);
    g.set_heuristic(0, 3);
    g.set_heuristic(1, 2);
    g.set_heuristic(2, 1);
    g.set_heuristic(3, 0);
    g
}

#[test]
fn astar_and_ida_star_agree() {
    let g = route_graph();
    let mut budget = Budget::steps(10_000);
    let a = astar(&g, 0, 3, &mut budget).expect("within budget");
    assert_eq!(a.status, Status::Found);
    assert_eq!(a.cost, 3);
    assert!(verify_path(&g, &a.path, a.cost));
    let mut budget = Budget::steps(10_000);
    let b = ida_star(&g, 0, 3, &mut budget).expect("within budget");
    assert_eq!(b.status, Status::Found);
    assert_eq!(b.cost, a.cost);
    assert!(verify_path(&g, &b.path, b.cost));
}

fn mate_in_one() -> (GameTree, u32) {
    // root(max) -> a(min) -> {a1: 5, a2: 1}; root -> b(min) -> {b1: 7}.
    // min picks 1 under a and 7 under b; max picks b. Value 7 via b1.
    let (root, a, b, a1, a2, b1) = (0, 1, 2, 3, 4, 5);
    let t = GameTree {
        children: vec![vec![a, b], vec![a1, a2], vec![b1], vec![], vec![], vec![]],
        maximizing: vec![true, false, false, true, true, true],
        eval: vec![0, 0, 0, 5, 1, 7],
    };
    (t, root)
}

#[test]
fn alpha_beta_finds_the_winning_move() {
    let (t, root) = mate_in_one();
    let mut budget = Budget::steps(10_000);
    let out = alpha_beta(&t, root, &mut budget).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert_eq!(out.best_move, 2);
    assert_eq!(out.value, 7);
    assert!(verify_line(&t, &out.line, out.value));
}

#[test]
fn repr_dispatch_covers_every_pair() {
    let mut budget = Budget::steps(1_000_000);
    let puzzle = Representation::Puzzle(sudoku4());
    let v = run(&puzzle, Operation::Solve, &mut budget).expect("within budget");
    assert_eq!(v.status, Status::Found);

    let states = Representation::States(chain3());
    let v = run(&states, Operation::Plan, &mut budget).expect("within budget");
    assert_eq!(v.status, Status::Found);
    let v = run(&states, Operation::PlanBounded { bound: 2 }, &mut budget).expect("within budget");
    assert_eq!(v.status, Status::Found);

    let graph = Representation::Graph {
        graph: route_graph(),
        start: 0,
        goal: 3,
    };
    let v = run(&graph, Operation::ShortestPath, &mut budget).expect("within budget");
    assert_eq!(v.status, Status::Found);

    let (tree, root) = mate_in_one();
    let game = Representation::Game { tree, root };
    let v = run(&game, Operation::Play, &mut budget).expect("within budget");
    assert_eq!(v.status, Status::Found);

    // A mismatched pair is Unknown, never a wrong definite answer.
    let v = run(&graph, Operation::Play, &mut budget).expect("within budget");
    assert_eq!(v.status, Status::Unknown);
}

#[test]
fn queens_scales_and_small_boards_refuse() {
    for impossible in [2, 3] {
        let p = nqueens(impossible).expect("valid board");
        let mut budget = Budget::steps(1_000_000);
        let out = solve_csp(&p, &mut budget).expect("within budget");
        assert_eq!(out.status, Status::Impossible, "n={impossible}");
    }
    for solvable in [4, 8] {
        let p = nqueens(solvable).expect("valid board");
        let mut budget = Budget::steps(50_000_000);
        let out = solve_csp(&p, &mut budget).expect("within budget");
        assert_eq!(out.status, Status::Found, "n={solvable}");
        assert!(verify_csp(&p, &out.assignment));
    }
}

#[test]
fn classic_sudoku_solves() {
    let src = "53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79";
    let p = sudoku9(src).expect("valid puzzle");
    let mut budget = Budget::steps(50_000_000);
    let out = solve_csp(&p, &mut budget).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert!(verify_csp(&p, &out.assignment));
    assert!(sudoku9(src).is_ok());
    assert!(sudoku9("too short").is_err());
}

#[test]
fn map_coloring_counts_colors_honestly() {
    // Triangle: impossible in 2 colors, trivial in 3.
    let borders = [(0, 1), (1, 2), (0, 2)];
    let p2 = map_color(3, &borders, 2);
    let mut budget = Budget::steps(10_000);
    let out = solve_csp(&p2, &mut budget).expect("within budget");
    assert_eq!(out.status, Status::Impossible);
    let p3 = map_color(3, &borders, 3);
    let mut budget = Budget::steps(10_000);
    let out = solve_csp(&p3, &mut budget).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert!(verify_csp(&p3, &out.assignment));
}

#[test]
fn tiny_logic_grid_deduces() {
    let p = logic_grid(
        &["alice", "bob"],
        &[vec![1, 2], vec![1, 2]],
        &[vec![0, 1]],
        &[(0, 1)],
    );
    let mut budget = Budget::steps(10_000);
    let out = solve_csp(&p, &mut budget).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert_eq!(out.assignment, vec![1, 2]);
}

#[test]
fn word_coins_problem() {
    use axiom::WordModel;
    // 30 coins, nickels(5) + dimes(10) + quarters(25) = 500 cents.
    let mut m = WordModel::new();
    m.quantity("nickels", 0, 30).unwrap();
    m.quantity("dimes", 0, 30).unwrap();
    m.quantity("quarters", 0, 30).unwrap();
    m.sum_eq(&[("nickels", 1), ("dimes", 1), ("quarters", 1)], 30)
        .unwrap();
    m.sum_eq(&[("nickels", 5), ("dimes", 10), ("quarters", 25)], 500)
        .unwrap();
    let mut budget = Budget::steps(1_000_000);
    let out = m.solve(&mut budget).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert!(axiom::verify_csp(m.problem(), &out.assignment));
    let total: i32 = ["nickels", "dimes", "quarters"]
        .iter()
        .map(|q| m.value_of(&out, q).unwrap())
        .sum();
    assert_eq!(total, 30);
    assert!(m.value_of(&out, "pennies").is_none());
}

#[test]
fn word_model_rejects_bad_input() {
    use axiom::WordModel;
    let mut m = WordModel::new();
    m.quantity("x", 1, 6).unwrap();
    assert!(m.quantity("x", 1, 6).is_err());
    assert!(m.quantity("wide", 0, 100_001).is_err());
    assert!(m.quantity("empty", 5, 4).is_err());
    assert!(m.sum_le(&[("ghost", 1)], 3).is_err());
}

#[test]
fn chess_perft_startpos() {
    use axiom::{perft, Position};
    let start = Position::startpos();
    assert_eq!(perft(&start, 1), 20);
    assert_eq!(perft(&start, 2), 400);
    assert_eq!(perft(&start, 3), 8902);
}

#[test]
fn chess_back_rank_mate_in_one() {
    use axiom::{find_mate_in_one, move_to_string, Position};
    let pos = Position::from_fen("6k1/5ppp/8/8/8/8/5PPP/4R1K1 w - - 0 1").unwrap();
    assert!(!pos.is_checkmate());
    let m = find_mate_in_one(&pos).expect("Re8 is mate");
    assert_eq!(move_to_string(m), "e1e8");
    assert!(pos.make(m).is_checkmate());
    assert!(Position::startpos().legal_moves().len() == 20);
    assert!(find_mate_in_one(&Position::startpos()).is_none());
    assert!(Position::from_fen("nonsense").is_err());
}

#[test]
fn chess_endgame_tree_plays_mate() {
    use axiom::{alpha_beta, chess::MATE_SCORE, endgame_tree, Position};
    let pos = Position::from_fen("6k1/5ppp/8/8/8/8/5PPP/4R1K1 w - - 0 1").unwrap();
    let mut budget = Budget::steps(1_000_000);
    let tree = endgame_tree(&pos, 2, &mut budget).expect("within budget");
    let mut budget = Budget::steps(1_000_000);
    let out = alpha_beta(&tree, 0, &mut budget).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert_eq!(out.value, MATE_SCORE);
    assert!(axiom::verify_line(&tree, &out.line, out.value));
}

#[test]
fn go_capture_in_one() {
    use axiom::{Goban, BLACK, WHITE};
    // White c3 ringed on three sides; the only liberty is c4.
    let mut g = Goban::new(5).unwrap();
    g.set(12, WHITE);
    for s in [11, 13, 7] {
        g.set(s, BLACK);
    }
    assert_eq!(g.side_to_move(), BLACK);
    let mut budget = Budget::steps(10_000);
    assert_eq!(g.capture_in_one(&mut budget).unwrap(), vec![17]);
    let out = g.play(17).expect("c4 captures");
    assert_eq!(out.captured, 1);
    assert_eq!(g.at(12), axiom::EMPTY);
}

#[test]
fn go_suicide_is_refused() {
    use axiom::{Goban, WHITE};
    let mut g = Goban::new(5).unwrap();
    g.set(1, WHITE);
    g.set(5, WHITE);
    assert!(g.play(0).is_err());
    assert!(g.play(1).is_err());
    assert!(Goban::new(0).is_err());
    assert!(Goban::new(10).is_err());
}

#[test]
fn go_simple_ko_is_refused() {
    use axiom::{Goban, BLACK, WHITE};
    let mut g = Goban::new(5).unwrap();
    for s in [6, 10, 12, 16] {
        g.set(s, WHITE);
    }
    for s in [5, 7, 1] {
        g.set(s, BLACK);
    }
    g.set_side(true);
    let out = g.play(11).expect("b3 captures b2");
    assert_eq!(out.captured, 1);
    assert_eq!(g.at(6), axiom::EMPTY);
    assert!(g.play(6).is_err(), "immediate recapture repeats: ko");
    g.play(24).expect("playing elsewhere is fine");
}

#[test]
fn planning_domains_plan_and_bmc_agree() {
    use axiom::{gripper_1, stacking_3};
    for (graph, cost, bound) in [(stacking_3(), 4, 3), (gripper_1(), 3, 3)] {
        let mut budget = Budget::steps(100_000);
        let plan = shortest_plan(&graph, &mut budget).expect("within budget");
        assert_eq!(plan.status, Status::Found);
        assert_eq!(plan.cost, cost);
        assert!(verify_plan(&graph, &plan.plan, plan.cost));
        for (b, want) in [(bound, Status::Found), (bound - 1, Status::Impossible)] {
            let rep = Representation::States(graph.clone());
            let mut budget = Budget::steps(1_000_000);
            let v =
                run(&rep, Operation::PlanBounded { bound: b }, &mut budget).expect("within budget");
            assert_eq!(v.status, want, "bound {b}");
        }
    }
    let stacking = stacking_3();
    let mut budget = Budget::steps(10_000);
    let plan = shortest_plan(&stacking, &mut budget).expect("within budget");
    assert_eq!(plan.plan, vec!["stack-a", "stack-b", "finish"]);
}

#[test]
fn chooser_is_deterministic_and_honest() {
    use axiom::{choose, features, stacking_3, Operation};
    let rep = Representation::States(stacking_3());
    assert_eq!(choose(&rep), choose(&rep));
    let f = features(&rep);
    assert_eq!((f.states, f.actions), (5, 5));
    let choice = choose(&rep);
    assert_eq!(choice.operation, Operation::Plan);
    let mut budget = Budget::steps(choice.budget_hint);
    let v = run(&rep, choice.operation, &mut budget).expect("within budget");
    assert_eq!(v.status, Status::Found);
}

#[test]
fn chooser_sends_large_graphs_to_bounded_sat() {
    use axiom::{choose, Operation, StateGraph};
    let mut g = StateGraph::new(100, 0);
    for s in 0..99 {
        g.action(&format!("step{s}"), s, s + 1, 1);
    }
    g.goal(99);
    let rep = Representation::States(g);
    let choice = choose(&rep);
    assert_eq!(choice.operation, Operation::PlanBounded { bound: 64 });
    let mut budget = Budget::steps(choice.budget_hint);
    let v = run(&rep, choice.operation, &mut budget).expect("within budget");
    assert_eq!(
        v.status,
        Status::Impossible,
        "goal is 99 steps out, bound 64"
    );
}
