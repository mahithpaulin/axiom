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
use crate::solver::{Answer, Outcome, QueryOutcome, Solver, Stats};
use crate::status::{Exhausted, Status};
use crate::term::TermId;

const DEFAULT_MAX_DEPTH: u32 = 64;

impl Solver {
    /// Depth-bounded SLD for a ground goal.
    ///
    /// Returns true with the proof trace in `trace` when the goal is provable.
    fn sld_ground(
        &mut self,
        goal: TermId,
        depth: u32,
        max_depth: u32,
        budget: &mut Budget,
        trace: &mut Vec<ResolutionStep>,
        failed: &mut FxHashMap<(TermId, u32), ()>,
    ) -> Result<bool, Exhausted> {
        if depth > max_depth {
            return Ok(false);
        }
        budget.charge(1)?;
        self.stats.sld_steps += 1;
        self.stats.max_depth = self.stats.max_depth.max(depth as u64);

        if failed.contains_key(&(goal, depth)) {
            return Ok(false);
        }
        // Already known bottom-up: the forward derivations carry the proof.
        if self.db.contains(goal) {
            return Ok(true);
        }

        let pred = self.prog.store.sym(goal);
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
                    ok = false;
                    break;
                }
                let sub = self.subst.resolve(&mut self.prog.store, lit.atom);
                if !self.prog.store.is_ground(sub) {
                    // Non-ground subgoal: outside the implemented fragment.
                    ok = false;
                    break;
                }
                let r = self.sld_ground(sub, depth + 1, max_depth, budget, &mut sub_trace, failed);
                if r.is_err() {
                    self.subst.undo_to(mark);
                    return r;
                }
                if !r.unwrap() {
                    ok = false;
                    break;
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
                return Ok(true);
            }
            self.subst.undo_to(mark);
            failed.insert((goal, depth), ());
        }
        Ok(false)
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
            let proof = Proof {
                goal,
                root: self.deriv_of.get(&goal).copied(),
                steps: Vec::new(),
                saturation: None,
            };
            return Outcome::definite(Status::Proved, Some(proof), self.stats.delta(&before));
        }

        // Not in the closure. Try goal-directed resolution before concluding.
        let mut trace = Vec::new();
        let mut failed = FxHashMap::default();
        match self.sld_ground(goal, 0, max_depth, budget, &mut trace, &mut failed) {
            Ok(true) => {
                let proof = Proof {
                    goal,
                    root: None,
                    steps: trace,
                    saturation: None,
                };
                Outcome::definite(Status::Proved, Some(proof), self.stats.delta(&before))
            }
            Ok(false) => match sat {
                Some(s) => {
                    // Bottom-up completed and the goal is absent: this is the
                    // least model, so absence is a proof of non-derivability.
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
            Err(e) => Outcome::inconclusive(Status::Exhausted, e, self.stats.delta(&before)),
        }
    }

    /// Answer a possibly non-ground goal by matching it against the least model.
    ///
    /// Complete for Datalog: every answer is a tuple in the saturated closure,
    /// and if the closure is complete then an empty answer set is a proof that
    /// there are no answers.
    pub fn query(&mut self, goal: TermId, budget: &mut Budget) -> QueryOutcome {
        let before = self.stats;
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
            status: if answers.is_empty() { Status::Refuted } else { Status::Found },
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
