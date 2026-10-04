//! Planning domains (V2 R5 instances, ROADMAP II4).
//!
//! Small classical-planning instances as explicit [`StateGraph`]s: a
//! three-block stacking problem with a tempting dead end, and a two-room
//! gripper carry. Both are tiny on purpose — they exist to prove the
//! plan-vs-BMC agreement (`shortest_plan` vs `bmc_clauses` + SAT), not to
//! benchmark a planner. Larger instances grow the same builders.

use crate::state::StateGraph;

/// Three blocks, one dead end. Optimal plan costs 4 (`s0 -a-> s1 -b->
/// s2 -c-> s3`); the `bad` move from `s0` strands the search in `s4`.
pub fn stacking_3() -> StateGraph {
    let mut g = StateGraph::new(5, 0);
    g.action("stack-a", 0, 1, 1);
    g.action("bad", 0, 4, 1);
    g.action("stack-b", 1, 2, 2);
    g.action("unstack", 1, 0, 1);
    g.action("finish", 2, 3, 1);
    g.goal(3);
    g
}

/// Gripper with one ball and two rooms. `carry` then `drop` delivers the
/// ball; wandering back is allowed but never optimal.
pub fn gripper_1() -> StateGraph {
    // 0: robot at A, ball at A. 1: robot at A carrying. 2: robot at B
    // carrying. 3: robot at B, ball delivered (goal).
    let mut g = StateGraph::new(4, 0);
    g.action("pickup", 0, 1, 1);
    g.action("move-ab", 1, 2, 1);
    g.action("drop", 2, 3, 1);
    g.action("wander", 0, 0, 1);
    g.action("back", 2, 1, 1);
    g.goal(3);
    g
}
