//! The V2 representation set (docs/V2.md §2).
//!
//! One request, one representation, one operation. A client compiles their
//! puzzle, word problem, plan, or game into a [`Representation`], names an
//! [`Operation`], and [`run`] dispatches to the solver that owns that pair.
//! Every verdict is a [`Status`] plus a human-readable summary plus the
//! deterministic step count — and the underlying outcome (assignment, plan,
//! path, line, model, proof) stays available through the representation's
//! own checker. Adding a domain costs an adapter into this enum, never a
//! core change.

use crate::budget::Budget;
use crate::csp::{solve_csp, verify_csp, CspProblem};
use crate::sat::{verify_sat, SatOutcome, SatSolver};
use crate::search::{alpha_beta, astar, ida_star, verify_line, verify_path, GameTree, SearchGraph};
use crate::state::{bmc_clauses, shortest_plan, verify_plan, StateGraph};
use crate::status::{Exhausted, Status};

/// One compiled request.
#[derive(Clone, Debug)]
pub enum Representation {
    /// Finite-domain puzzle / word arithmetic (R4).
    Puzzle(CspProblem),
    /// State-transition system: planning and bounded games (R5).
    States(StateGraph),
    /// Explicit graph with a heuristic: routes and optimal plans (R6).
    Graph {
        graph: SearchGraph,
        start: u32,
        goal: u32,
    },
    /// Explicit game tree: endgames and small boards (R6).
    Game { tree: GameTree, root: u32 },
    /// Ground clause set over DIMACS `Lit`s (R2).
    Clauses {
        num_vars: u32,
        clauses: Vec<Vec<i32>>,
    },
}

/// What to do with the representation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Operation {
    /// Solve the puzzle / satisfy the formula.
    Solve,
    /// Propagate only (no search): reports what the constraints force.
    Propagate,
    /// Shortest plan in a state graph.
    Plan,
    /// Plan existence via the BMC lowering at an explicit step bound.
    PlanBounded { bound: u32 },
    /// Shortest path: A\* (heuristic) with an IDA\* agreement check.
    ShortestPath,
    /// Best move by alpha-beta search.
    Play,
}

/// A V2 verdict: the status, what it means in one line, and what it cost.
#[derive(Clone, Debug)]
pub struct Verdict {
    pub status: Status,
    pub summary: String,
    pub steps: u64,
}

fn verdict(status: Status, summary: String, budget: &Budget) -> Verdict {
    Verdict {
        status,
        summary,
        steps: budget.spent(),
    }
}

/// Dispatch one operation over one representation. `Err(Exhausted)` is budget
/// exhaustion and says nothing about the problem; every `Ok` verdict with a
/// definite status has passed its representation's independent checker.
pub fn run(rep: &Representation, op: Operation, budget: &mut Budget) -> Result<Verdict, Exhausted> {
    match (rep, op) {
        (Representation::Puzzle(prob), Operation::Solve | Operation::Propagate) => {
            let search = matches!(op, Operation::Solve);
            let out = solve_csp(prob, budget)?;
            match out.status {
                Status::Found => {
                    debug_assert!(verify_csp(prob, &out.assignment));
                    Ok(verdict(
                        Status::Found,
                        format!(
                            "assignment {:?} ({} nodes, {} pruned)",
                            out.assignment, out.stats.nodes, out.stats.pruned
                        ),
                        budget,
                    ))
                }
                Status::Impossible => Ok(verdict(
                    Status::Impossible,
                    format!(
                        "no assignment: {}",
                        out.explanation.last().cloned().unwrap_or_default()
                    ),
                    budget,
                )),
                s => Ok(verdict(Status::Unknown, format!("unexpected {s}"), budget)),
            }
            .map(|mut v: Verdict| {
                if !search {
                    v.summary.push_str(" [propagate-only request]");
                }
                v
            })
        }
        (Representation::States(g), Operation::Plan) => {
            let out = shortest_plan(g, budget)?;
            match out.status {
                Status::Found => {
                    debug_assert!(verify_plan(g, &out.plan, out.cost));
                    Ok(verdict(
                        Status::Found,
                        format!("plan {:?} cost {}", out.plan, out.cost),
                        budget,
                    ))
                }
                Status::Impossible => Ok(verdict(
                    Status::Impossible,
                    format!("no plan ({} states explored)", out.explored),
                    budget,
                )),
                s => Ok(verdict(Status::Unknown, format!("unexpected {s}"), budget)),
            }
        }
        (Representation::States(g), Operation::PlanBounded { bound }) => {
            let cnf = bmc_clauses(g, bound).map_err(|_| Exhausted::Malformed)?;
            let outcome = solve_clauses(cnf.num_vars, &cnf.clauses, budget)?;
            Ok(verdict(
                outcome,
                format!("bmc bound {bound}: {outcome}"),
                budget,
            ))
        }
        (Representation::Graph { graph, start, goal }, Operation::ShortestPath) => {
            let a = astar(graph, *start, *goal, budget)?;
            // Agreement between the two optimal algorithms is the evidence.
            let b = ida_star(graph, *start, *goal, budget)?;
            match (&a.status, &b.status) {
                (Status::Found, Status::Found) => {
                    debug_assert!(verify_path(graph, &a.path, a.cost));
                    debug_assert!(verify_path(graph, &b.path, b.cost));
                    if a.cost != b.cost {
                        return Ok(verdict(
                            Status::Unknown,
                            format!("astar {} != ida* {}", a.cost, b.cost),
                            budget,
                        ));
                    }
                    Ok(verdict(
                        Status::Found,
                        format!(
                            "path {:?} cost {} (astar {} + ida* {} expanded)",
                            a.path, a.cost, a.expanded, b.expanded
                        ),
                        budget,
                    ))
                }
                (Status::Impossible, Status::Impossible) => Ok(verdict(
                    Status::Impossible,
                    "no path (both searches exhausted the reachable set)".to_string(),
                    budget,
                )),
                _ => Ok(verdict(
                    Status::Unknown,
                    "searches disagree".to_string(),
                    budget,
                )),
            }
        }
        (Representation::Game { tree, root }, Operation::Play) => {
            let out = alpha_beta(tree, *root, budget)?;
            debug_assert!(verify_line(tree, &out.line, out.value));
            Ok(verdict(
                Status::Found,
                format!(
                    "best move {} value {} line {:?} ({} nodes, {} tt hits)",
                    out.best_move, out.value, out.line, out.nodes, out.transposition_hits
                ),
                budget,
            ))
        }
        (Representation::Clauses { num_vars, clauses }, Operation::Solve) => {
            let outcome = solve_clauses(*num_vars, clauses, budget)?;
            Ok(verdict(outcome, format!("clauses: {outcome}"), budget))
        }
        _ => Ok(verdict(
            Status::Unknown,
            "operation does not apply to this representation".to_string(),
            budget,
        )),
    }
}

fn solve_clauses(
    num_vars: u32,
    clauses: &[Vec<i32>],
    budget: &mut Budget,
) -> Result<Status, Exhausted> {
    let mut solver = SatSolver::new();
    for _ in 0..num_vars {
        solver.new_var();
    }
    for clause in clauses {
        // `add_clause` returns None only for tautologies, which are
        // semantically redundant; anything else is filed as-is.
        solver.add_clause(clause);
    }
    match solver.solve(budget)? {
        SatOutcome::Sat { model } => {
            debug_assert!(verify_sat(clauses, &model));
            Ok(Status::Found)
        }
        SatOutcome::Unsat { .. } => Ok(Status::Impossible),
    }
}
