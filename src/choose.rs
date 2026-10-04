//! Deterministic strategy selection (V2 chooser, ROADMAP II6 first cut).
//!
//! Given a representation, [`choose`] names the operation and a budget hint.
//! It is a **pure function of measured input features** (counts, not timings),
//! so the same problem always gets the same choice — asserted by
//! `chooser_is_deterministic`. It never changes an answer, only which engine
//! and parameters produce it: every verdict still carries its own proof.
//!
//! The one genuine choice today is plans: small state graphs go to optimal
//! Dijkstra (`Plan`); larger ones go to bounded SAT (`PlanBounded`) with a
//! bound derived from the state count. Everything else maps to its
//! representation's canonical operation. As more engines land, their measured
//! win regions extend [`choose`], never branch it.

use crate::repr::{Operation, Representation};

/// Measured input features. Counts only — never timings.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Features {
    pub vars: u64,
    pub constraints: u64,
    pub states: u64,
    pub actions: u64,
    pub graph_nodes: u64,
    pub game_nodes: u64,
    pub clauses: u64,
}

/// What to run and roughly how much to spend.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Choice {
    pub operation: Operation,
    pub budget_hint: u64,
}

pub fn features(rep: &Representation) -> Features {
    match rep {
        Representation::Puzzle(p) => Features {
            vars: p.vars.len() as u64,
            constraints: p.constraints.len() as u64,
            states: 0,
            actions: 0,
            graph_nodes: 0,
            game_nodes: 0,
            clauses: 0,
        },
        Representation::States(g) => Features {
            vars: 0,
            constraints: 0,
            states: g.num_states as u64,
            actions: g.actions.len() as u64,
            graph_nodes: 0,
            game_nodes: 0,
            clauses: 0,
        },
        Representation::Graph { graph, .. } => Features {
            vars: 0,
            constraints: 0,
            states: 0,
            actions: 0,
            graph_nodes: graph.nstates() as u64,
            game_nodes: 0,
            clauses: 0,
        },
        Representation::Game { tree, .. } => Features {
            vars: 0,
            constraints: 0,
            states: 0,
            actions: 0,
            graph_nodes: 0,
            game_nodes: tree.children.len() as u64,
            clauses: 0,
        },
        Representation::Clauses { num_vars, clauses } => Features {
            vars: *num_vars as u64,
            constraints: 0,
            states: 0,
            actions: 0,
            graph_nodes: 0,
            game_nodes: 0,
            clauses: clauses.len() as u64,
        },
    }
}

pub fn choose(rep: &Representation) -> Choice {
    let f = features(rep);
    match rep {
        Representation::Puzzle(_) => Choice {
            operation: Operation::Solve,
            budget_hint: f
                .vars
                .saturating_mul(f.constraints.max(1))
                .saturating_mul(1000)
                .max(10_000),
        },
        Representation::States(_) => {
            if f.states <= 64 && f.actions <= 256 {
                Choice {
                    operation: Operation::Plan,
                    budget_hint: f
                        .states
                        .saturating_mul(f.actions.max(1))
                        .saturating_mul(100)
                        .max(10_000),
                }
            } else {
                Choice {
                    // Bounded SAT with a bound that covers any simple path.
                    operation: Operation::PlanBounded {
                        bound: f.states.saturating_sub(1).min(64) as u32,
                    },
                    budget_hint: 10_000_000,
                }
            }
        }
        Representation::Graph { .. } => Choice {
            operation: Operation::ShortestPath,
            budget_hint: f.graph_nodes.saturating_mul(1000).max(10_000),
        },
        Representation::Game { .. } => Choice {
            operation: Operation::Play,
            budget_hint: f.game_nodes.saturating_mul(100).max(10_000),
        },
        Representation::Clauses { .. } => Choice {
            operation: Operation::Solve,
            budget_hint: f
                .vars
                .saturating_add(f.clauses)
                .saturating_mul(1000)
                .max(100_000),
        },
    }
}
