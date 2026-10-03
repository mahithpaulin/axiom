//! Backward resolution and the public `prove` / `query` entry points.
//!
//! ## Why a second engine at all
//!
//! Bottom-up saturation is complete for stratified Datalog and *cannot* handle
//! `reach(succ(x))`, because that relation has an infinite domain. Rather than
//! pushing those rules into an ad-hoc special case, the same rules are handled by
//! goal-directed resolution, which searches the rule space instead of the tuple
//! space. This is the concrete example behind the charter's generality test: a
//! new problem family costs an exterior adapter, not a core change.
//!
//! ## What is and is not implemented
//!
//! Implemented: depth-bounded SLD for **ground** goals, positive body literals,
//! rule reuse across recursive calls, and failure memoisation keyed by
//! (goal, remaining depth).
//!
//! Not implemented, deliberately: negation in backward mode, and non-ground
//! goals. Both are recorded in KNOWN_LIMITATIONS.md. Negation-as-failure would
//! make the "proved" status unfalsifiable, and non-ground backward search
//! requires tabling to be *complete*; offering an incomplete version under the
//! same status enum would be worse than not offering it. `prove` therefore
//! returns `Unknown` rather than pretending, when only backward search could
//! apply and the ground restriction bites.
//!
//! ## Status honesty
//!
//! `Refuted` means exactly one thing here: *the goal is absent from the least
//! model, and the least model was computed to completion*. If saturation was cut
//! short by a budget, the answer is `Exhausted`, never `Refuted`. The
//! distinction is enforced by construction: the saturation certificate is only
//! attached when `saturate` returned `Ok`.

use crate::budget::Budget;
use crate::hash::FxHashMap;
use crate::program::{Literal, RuleId};
use crate::proof::{Proof, ResolutionStep};
use crate::solver::{Answer, Outcome, ProofMode, QueryOutcome, Solver};
use crate::status::{Exhausted, Status};
use crate::term::TermId;

const DEFAULT_MAX_DEPTH: u32 = 64;

/// Why SLD stopped, as distinct from whether the goal was provable.
///
/// The distinction is load-bearing. "No rule derives this goal" and "I did not
/// look" both used to surface as `Refuted`, which is a definite claim that the
/// goal is not derivable. Backward resolution declines for several reasons that
/// are *not* such a claim: the depth bound, a negated body literal, a non-ground
/// subgoal. Those must reach the caller as a decline, so `prove` can answer
/// `Unknown` instead of asserting something it never established.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SldOutcome {
    /// Proved, and `steps` holds the derivation.
    Proved,
    /// Exhaustively declined: every candidate rule was tried and failed.
    NotProvable,
    /// Declined without establishing anything.
    Declined(DeclineReason),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DeclineReason {
    Depth,
    NegatedBody,
    NonGroundSubgoal,
    Budget,
}

impl DeclineReason {
    pub fn as_str(self) -> &'static str {
        match self {
            DeclineReason::Depth => "resolution depth bound reached",
            DeclineReason::NegatedBody => "negation is not implemented in backward resolution",
            DeclineReason::NonGroundSubgoal => "backward resolution is restricted to ground goals",
            DeclineReason::Budget => "budget exhausted during resolution",
        }
    }
    pub fn exhausted(self) -> Option<Exhausted> {
        match self {
            DeclineReason::Budget => Some(Exhausted::Steps),
            _ => None,
        }
    }
}

impl Solver {
    /// Depth-bounded SLD for a ground goal.
    ///
    /// Returns true with the proof trace in `trace` when the goal is provable.
    #[allow(clippy::type_complexity)]
    // 8 args: goal, depths, budget, trace and two memo tables. Bundling them
    // into a context struct is churn; the arity is the honest signature.
    #[allow(clippy::too_many_arguments)]
    fn sld_ground(
        &mut self,
        goal: TermId,
        depth: u32,
        max_depth: u32,
        budget: &mut Budget,
        trace: &mut Vec<ResolutionStep>,
        failed: &mut FxHashMap<(TermId, u32), ()>,
        declined: &mut FxHashMap<(TermId, u32), DeclineReason>,
    ) -> Result<SldOutcome, Exhausted> {
        if depth > max_depth {
            return Ok(SldOutcome::Declined(DeclineReason::Depth));
        }
        if let Some(r) = declined.get(&(goal, depth)) {
            return Ok(SldOutcome::Declined(*r));
        }
        budget.charge(1)?;
        self.stats.sld_steps += 1;
        self.stats.max_depth = self.stats.max_depth.max(depth as u64);

        if failed.contains_key(&(goal, depth)) {
            return Ok(SldOutcome::NotProvable);
        }
        // Already known bottom-up: the forward derivations carry the proof.
        if self.db.contains(goal) {
            return Ok(SldOutcome::Proved);
        }

        let pred = self.prog.store.sym(goal);
        let mut saw_unsupported = false;
        let candidates: Vec<RuleId> = match self.rules_by_pred.get(pred as usize) {
            Some(v) => v.clone(),
            None => Vec::new(),
        };
        for rule in candidates {
            self.ensure_renamed(rule);
            let mark = self.subst.mark();
            let mut ok = true;

            if self
                .subst
                .unify(&self.prog.store, self.ren_head(rule), goal)
                .is_err()
            {
                self.subst.undo_to(mark);
                continue;
            }
            // Resolve the body left to right. A negated body literal has no
            // backward semantics yet, so such a rule is skipped rather than
            // approximated.
            let blen = self.ren_len(rule);
            let mut sub_trace: Vec<ResolutionStep> = Vec::new();
            for i in 0..blen {
                let lit = self.ren_lit(rule, i);
                if !lit.pos {
                    // No backward semantics for negation: record that this rule
                    // was not usable rather than treating it as a failure.
                    ok = false;
                    saw_unsupported = true;
                    break;
                }
                let sub = self.subst.resolve(&mut self.prog.store, lit.atom);
                if !self.prog.store.is_ground(sub) {
                    // Non-ground subgoal: outside the implemented fragment.
                    ok = false;
                    saw_unsupported = true;
                    break;
                }
                let r = self.sld_ground(
                    sub,
                    depth + 1,
                    max_depth,
                    budget,
                    &mut sub_trace,
                    failed,
                    declined,
                );
                if r.is_err() {
                    self.subst.undo_to(mark);
                    return r;
                }
                match r.unwrap() {
                    SldOutcome::Proved => {}
                    SldOutcome::NotProvable => {
                        ok = false;
                        break;
                    }
                    SldOutcome::Declined(reason) => {
                        ok = false;
                        saw_unsupported = true;
                        let _ = reason;
                        break;
                    }
                }
            }

            if ok {
                let h = self.ren_head(rule);
                let concl = self.subst.resolve(&mut self.prog.store, h);
                let inst = self.instantiation(rule);
                let premises: Vec<u32> = Vec::new();
                trace.append(&mut sub_trace);
                trace.push(ResolutionStep {
                    rule,
                    goal: Literal::pos(goal),
                    concl: Literal::pos(concl),
                    inst,
                    premises,
                });
                self.subst.undo_to(mark);
                return Ok(SldOutcome::Proved);
            }
            self.subst.undo_to(mark);
        }
        if saw_unsupported {
            declined.insert((goal, depth), DeclineReason::NegatedBody);
            Ok(SldOutcome::Declined(DeclineReason::NegatedBody))
        } else {
            failed.insert((goal, depth), ());
            Ok(SldOutcome::NotProvable)
        }
    }

    /// Current binding of a rule's local variables, as ground terms.
    fn instantiation(&mut self, rule: RuleId) -> Vec<(u32, TermId)> {
        let nvars = self.prog.rules[rule as usize].local_vars.len();
        let mut out = Vec::with_capacity(nvars);
        for i in 0..nvars {
            let (local, g) = self.ren_map_at(rule, i);
            let r = self.subst.find(g);
            out.push((local, r));
        }
        out
    }

    /// Decide a ground goal.
    ///
    /// Tries bottom-up first (cheap and complete for Datalog), then goal-directed
    /// resolution for rules saturation cannot enumerate.
    pub fn prove(&mut self, goal: TermId, budget: &mut Budget) -> Outcome {
        self.prove_with_depth(goal, budget, DEFAULT_MAX_DEPTH)
    }

    pub fn prove_with_depth(
        &mut self,
        goal: TermId,
        budget: &mut Budget,
        max_depth: u32,
    ) -> Outcome {
        let before = self.stats;
        if !self.goal_in_range(goal) {
            // A TermId from a different TermStore is a caller error, not an
            // engine error, but it must not be an index-out-of-bounds panic.
            return Outcome::inconclusive(Status::Unknown, Exhausted::Malformed, before)
                .note("goal id does not belong to this program's term store");
        }
        self.seed_facts();
        let mut note_forward_exhausted: Option<Exhausted> = None;

        let sat = match self.saturate(budget) {
            Ok(s) => Some(s),
            Err(e) => {
                note_forward_exhausted = Some(e);
                None
            }
        };

        if self.db.contains(goal) {
            // Without recorded derivations there is nothing to check, so the
            // honest status is `Found`, not `Proved`. See `ProofMode`.
            if self.proof_mode == ProofMode::Off {
                return Outcome::definite(Status::Found, None, self.stats.delta(&before))
                    .note("derivations not recorded; no proof attached");
            }
            let proof = Proof {
                goal,
                root: self.deriv_of.get(&goal).copied(),
                steps: Vec::new(),
                saturation: None,
            };
            return Outcome::definite(Status::Proved, Some(proof), self.stats.delta(&before));
        }

        // Not in the closure. Try goal-directed resolution before concluding.
        //
        // The outcome is tri-state on purpose. Only `NotProvable` licenses the
        // definite claim `Refuted`; a decline means the backward engine never
        // established anything, and saturation's success does not license the
        // claim either because saturation skips `backward_only` rules.
        let mut trace = Vec::new();
        let mut failed = FxHashMap::default();
        let mut declined = FxHashMap::default();
        let sld = match self.sld_ground(
            goal,
            0,
            max_depth,
            budget,
            &mut trace,
            &mut failed,
            &mut declined,
        ) {
            Ok(v) => v,
            Err(e) => {
                return Outcome::inconclusive(Status::Exhausted, e, self.stats.delta(&before))
            }
        };
        match sld {
            SldOutcome::Proved => {
                let proof = Proof {
                    goal,
                    root: None,
                    steps: trace,
                    saturation: None,
                };
                Outcome::definite(Status::Proved, Some(proof), self.stats.delta(&before))
                    .note("proved by backward resolution; the proof is a rule-resolution trace")
            }
            SldOutcome::NotProvable => match sat {
                Some(s) => {
                    // Bottom-up completed and the backward engine exhausted its
                    // options: the atom is absent from the least model.
                    let proof = Proof {
                        goal,
                        root: None,
                        steps: Vec::new(),
                        saturation: Some(s),
                    };
                    let mut o =
                        Outcome::definite(Status::Refuted, Some(proof), self.stats.delta(&before));
                    o.notes.push(
                        "bottom-up saturation completed; goal absent from the least model"
                            .to_string(),
                    );
                    o
                }
                None => {
                    let e = note_forward_exhausted.unwrap_or(Exhausted::Steps);
                    Outcome::inconclusive(Status::Exhausted, e, self.stats.delta(&before))
                }
            },
            SldOutcome::Declined(reason) => {
                // An inconclusive result must not carry a proof, and must say
                // why. `Unknown` is the honest status: the engine did not
                // establish either answer.
                let mut o = Outcome::inconclusive(
                    Status::Unknown,
                    reason.exhausted().unwrap_or(Exhausted::Depth),
                    self.stats.delta(&before),
                );
                o.notes.push(format!(
                    "backward resolution declined: {}; a negative answer is not established",
                    reason.as_str()
                ));
                o
            }
        }
    }

    /// Answer a possibly non-ground goal by matching it against the least model.
    ///
    /// Complete for Datalog: every answer is a tuple in the saturated closure,
    /// and if the closure is complete then an empty answer set is a proof that
    /// there are no answers.
    pub fn query(&mut self, goal: TermId, budget: &mut Budget) -> QueryOutcome {
        let before = self.stats;
        if !self.goal_in_range(goal) {
            return QueryOutcome::inconclusive(Status::Unknown, Exhausted::Malformed, before);
        }
        self.seed_facts();
        let sat = match self.saturate(budget) {
            Ok(s) => s,
            Err(e) => {
                return QueryOutcome::inconclusive(Status::Exhausted, e, self.stats.delta(&before))
            }
        };
        let pred = self.prog.store.sym(goal);
        let facts: Vec<TermId> = self
            .db
            .by_pred
            .get(pred as usize)
            .cloned()
            .unwrap_or_default();
        let mut answers = Vec::new();
        for f in facts {
            let mark = self.subst.mark();
            if self.subst.match_into(&self.prog.store, goal, f).is_ok() {
                let mut subst = Vec::new();
                let n = self.prog.store.arity(goal);
                for i in 0..n {
                    let a = self.prog.store.child(goal, i);
                    if self.prog.store.var_id(a).is_some() {
                        let r = self.subst.find(a);
                        subst.push((a, r));
                    }
                }
                let proof = Proof {
                    goal: f,
                    root: self.deriv_of.get(&f).copied(),
                    steps: Vec::new(),
                    saturation: None,
                };
                answers.push(Answer { subst, proof });
            }
            self.subst.undo_to(mark);
            if let Err(e) = budget.charge(1) {
                return QueryOutcome::inconclusive(Status::Exhausted, e, self.stats.delta(&before));
            }
        }
        QueryOutcome {
            status: if answers.is_empty() {
                Status::Refuted
            } else {
                Status::Found
            },
            answers,
            stats: self.stats.delta(&before),
            reason: None,
            saturation: Some(sat),
        }
    }

    /// Saturate only, exposing the certificate. Useful for benchmarks that want
    /// the closure without a goal.
    pub fn least_model(
        &mut self,
        budget: &mut Budget,
    ) -> Result<crate::proof::Saturation, Exhausted> {
        self.saturate(budget)
    }
}
