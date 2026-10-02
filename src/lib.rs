//! Forward chaining: semi-naive bottom-up evaluation.
//!
//! ## The algorithm and its correctness conditions
//!
//! A naive fixpoint re-runs every rule on every round, so its cost is
//! quadratic in the number of derivations. Semi-naive evaluation computes only
//! derivations whose body includes at least one *new* fact, which is linear in
//! the number of intermediate tuples for the acyclic cases that matter. This is
//! the single most important algorithmic choice for Datalog performance;
//! `bench_semi_naive_vs_fixpoint` measures the gap rather than asserting it.
//!
//! Three variants exist: all-old, all-new, and mixed. This implementation uses
//! **mixed** -- seed each body position in turn with the delta and join the rest
//! against the full relation. Mixed is the most robust to rule shape, at the
//! cost of `|body|` firings per rule per round.
//!
//! ## Completeness boundary
//!
//! Bottom-up evaluation is **complete for stratified Datalog** and *incomplete
//! for everything else*. Two cases are excluded and reported rather than
//! silently mishandled:
//!
//! 1. Function symbols in the head (`reach(succ(x))`). The relation has an
//!    infinite domain, so saturation cannot enumerate it. Such rules are marked
//!    `backward_only` and deferred to the backward engine.
//! 2. A body predicate that is neither seed nor IDB: the join finds nothing,
//!    which is the correct answer, not a bug.
//!
//! ## Negated literals
//!
//! A negated literal blocks the derivation if it matches a stored fact, *or* if
//! it is not fully instantiated. The second clause is a soundness requirement,
//! not an optimisation: treating a partially instantiated `not q(X)` as
//! satisfied would derive facts classical negation does not license. The cost is
//! incompleteness for programs whose negations never become ground, recorded in
//! KNOWN_LIMITATIONS.md.
//!
//! ## Cost accounting
//!
//! `Stats::candidates` counts tuples examined by the join -- the number the
//! index and join-order experiments are judged on. `derivations` counts
//! productive firings, `rounds` counts fixpoint iterations, and
//! `non_ground_heads` is a canary that must stay 0. All are deterministic, so
//! they can be asserted in tests, not just printed.

use crate::budget::Budget;
use crate::program::RuleId;
use crate::proof::{DerivId, Derivation, Saturation};
use crate::program::Literal;
use crate::solver::Solver;
use crate::status::Exhausted;
use crate::symbol::SymId;
use crate::term::{TermId, T_VAR};

/// The `k`-th body position that is not `skip`. Avoids materialising a `rem`
/// vector, which would alias the solver's own borrow.
#[inline]
fn nth_other(n_body: usize, skip: Option<usize>, k: usize) -> Option<usize> {
    let mut c = 0usize;
    for i in 0..n_body {
        if Some(i) == skip {
            continue;
        }
        if c == k {
            return Some(i);
        }
        c += 1;
    }
    None
}

impl Solver {
    #[inline]
    fn is_idb_in_stratum(&self, pred: SymId, stratum: u32) -> bool {
        self.prog
            .pred_idb
            .get(pred as usize)
            .copied()
            .unwrap_or(false)
            && self
                .prog
                .pred_stratum
                .get(pred as usize)
                .copied()
                .unwrap_or(0)
                == stratum
    }

    pub(crate) fn ensure_pred_slots(&mut self, pred: SymId) {
        let n = pred as usize + 1;
        if self.delta.len() < n {
            self.delta.resize(n, Vec::new());
            self.work.resize(n, Vec::new());
        }
    }

    /// Is every negated body literal false under the current substitution?
    fn negatives_hold(&mut self, rule: RuleId) -> bool {
        let n = self.ren_len(rule);
        for i in 0..n {
            let lit = self.ren_lit(rule, i);
            if lit.pos {
                continue;
            }
            let a = self.subst.resolve(&mut self.prog.store, lit.atom);
            // Soundness: a negation that is not fully instantiated cannot be
            // evaluated, and must not be assumed true.
            if !self.prog.store.is_ground(a) {
                return false;
            }
            if self.db.contains(a) {
                return false;
            }
        }
        true
    }

    /// Resolve the first argument of `atom` if it is already determined. Returns
    /// the resolved term, which indexes the database directly.
    #[inline]
    fn first_bound(&mut self, atom: TermId) -> Option<TermId> {
        let n = self.prog.store.arity(atom);
        for i in 0..n {
            let a = self.prog.store.child(atom, i);
            let r = self.subst.find(a);
            if self.prog.store.kind(r) != T_VAR {
                return Some(self.subst.resolve(&mut self.prog.store, r));
            }
        }
        None
    }

    /// Produce the *next* complete solution for every body position except
    /// `skip`, leaving the substitution bound on success.
    ///
    /// This is a resumable generator, and being resumable is the whole point.
    /// An earlier version ran the whole enumeration inside one call and returned
    /// with only the *final* solution still bound, so each rule firing derived a
    /// single fact. Saturation then needed one round per derived fact and the
    /// least model was badly incomplete -- visible in the benchmarks as
    /// semi-naive being 350x *slower* than the naive baseline, which was the
    /// tell that something was wrong rather than something being slow.
    ///
    /// The cursor and trail-mark stacks live in the solver, so successive calls
    /// resume where the previous one stopped and allocate nothing. Depth is
    /// bounded by the body length, so no input can reach the native stack.
    fn next_solution(
        &mut self,
        rule: RuleId,
        skip: Option<usize>,
        budget: &mut Budget,
    ) -> Result<bool, Exhausted> {
        let n_body = self.ren_len(rule);
        let levels = n_body - usize::from(skip.is_some());
        if levels == 0 {
            // The seed already covers every body position, so there is exactly
            // one solution for this seed and no cursor to advance. Yielding
            // `true` unconditionally would spin forever, because the caller
            // asks for the next solution until exhausted.
            if self.jc.is_empty() {
                self.jc.push(0);
                self.jm.push(0);
                return Ok(self.negatives_hold(rule));
            }
            return Ok(false);
        }
        // Resuming: drop the previous solution's bindings before rescanning
        // level 0 from its saved cursor.
        if !self.jc.is_empty() {
            self.subst.undo_to(self.jm[0]);
        }
        let mut depth = 0usize;
        loop {
            if depth == levels {
                if self.negatives_hold(rule) {
                    return Ok(true);
                }
                // This solution violates a negation; keep searching.
            } else {
                let i = match nth_other(n_body, skip, depth) {
                    Some(i) => i,
                    None => return Ok(false),
                };
                let lit = self.ren_lit(rule, i);
                let pred = self.prog.store.sym(lit.atom);
                // A negated position is never seeded by the delta; it is checked
                // by `negatives_hold` once the positive positions have matched.
                let bound = if lit.pos { self.first_bound(lit.atom) } else { None };
                if depth == self.jc.len() {
                    self.jc.push(0);
                    self.jm.push(self.subst.mark());
                }
                let list = self.db.candidates(pred, bound);
                let mut cursor = self.jc[depth];
                let mut advanced = false;
                while cursor < list.len() {
                    let t = list[cursor];
                    cursor += 1;
                    budget.charge(1)?;
                    self.stats.candidates += 1;
                    let mark = self.subst.mark();
                    match self.subst.match_into(&self.prog.store, lit.atom, t) {
                        Ok(()) => {
                            advanced = true;
                            break;
                        }
                        Err(_) => self.subst.undo_to(mark),
                    }
                }
                self.jc[depth] = cursor;
                if advanced {
                    self.stats.join_levels += 1;
                    depth += 1;
                    continue;
                }
            }
            // No viable continuation here: back out one level and retry it.
            if depth == 0 {
                return Ok(false);
            }
            depth -= 1;
            self.subst.undo_to(self.jm[depth]);
        }
    }

    /// Fire one rule, optionally with one body position already matched to a new
    /// fact. The whole firing is enclosed in a trail mark.
    fn eval_rule(
        &mut self,
        rule: RuleId,
        seed: Option<(usize, TermId)>,
        budget: &mut Budget,
    ) -> Result<(), Exhausted> {
        self.ensure_renamed(rule);
        // The union-find table is indexed by node id, so it must cover the
        // whole arena before any `find`. A static (all-extensional) rule reaches
        // `first_bound` -> `find` without ever calling `match_into`, which is
        // where the `ensure` used to live. Found by the benchmark suite.
        self.subst.ensure(self.prog.store.node_count());
        let mark = self.subst.mark();
        let r = self.eval_rule_inner(rule, seed, budget);
        self.subst.undo_to(mark);
        r
    }

    fn eval_rule_inner(
        &mut self,
        rule: RuleId,
        seed: Option<(usize, TermId)>,
        budget: &mut Budget,
    ) -> Result<(), Exhausted> {
        let mark = self.subst.mark();
        if let Some((i, t)) = seed {
            let lit = self.ren_lit(rule, i);
            if self.subst.match_into(&self.prog.store, lit.atom, t).is_err() {
                self.subst.undo_to(mark);
                return Ok(());
            }
            if !self.negatives_hold(rule) {
                self.subst.undo_to(mark);
                return Ok(());
            }
        }

        let head = self.ren_head(rule);
        self.jc.clear();
        self.jm.clear();
        loop {
            match self.next_solution(rule, seed.map(|(i, _)| i), budget) {
                Err(e) => {
                    self.subst.undo_to(mark);
                    self.jc.clear();
                    self.jm.clear();
                    return Err(e);
                }
                Ok(false) => break,
                Ok(true) => {
                    let concl = self.subst.resolve(&mut self.prog.store, head);
                    if !self.prog.store.is_ground(concl) {
                        // Cannot happen for a well-formed Datalog rule: every head
                        // variable is bound by matching against ground premises.
                        // Counted rather than stored, so the condition stays
                        // visible if it ever does.
                        self.stats.non_ground_heads += 1;
                    } else {
                        let pred = self.prog.store.sym(concl);
                        self.ensure_pred_slots(pred);
                        if self.db.insert(&self.prog.store, concl, false) {
                            self.delta[pred as usize].push(concl);
                            self.stats.new_facts += 1;
                            self.stats.derivations += 1;
                            self.record_derivation(rule, concl);
                        }
                    }
                    self.subst.undo_to(mark);
                }
            }
        }
        self.jc.clear();
        self.jm.clear();
        self.subst.undo_to(mark);
        Ok(())
    }

    fn record_derivation(&mut self, rule: RuleId, concl: TermId) {
        let nvars = self.prog.rules[rule as usize].local_vars.len();
        let mut inst = Vec::with_capacity(nvars);
        for i in 0..nvars {
            let (local, g) = self.ren_map_at(rule, i);
            let r = self.subst.find(g);
            let t = if self.prog.store.kind(r) == T_VAR {
                // Unbound. `negatives_hold` guarantees this cannot reach the
                // proof log for a well-formed program; record it truthfully so
                // the checker rejects it rather than accepting a bad proof.
                r
            } else {
                self.subst.resolve(&mut self.prog.store, r)
            };
            inst.push((local, t));
        }
        let blen = self.ren_len(rule);
        let mut body = Vec::with_capacity(blen);
        for i in 0..blen {
            let lit = self.ren_lit(rule, i);
            let a = self.subst.resolve(&mut self.prog.store, lit.atom);
            body.push(Literal {
                pos: lit.pos,
                atom: a,
            });
        }
        let id = self.derivs.len() as DerivId;
        self.derivs.push(Derivation {
            rule,
            concl,
            body,
            inst,
        });
        self.deriv_of.insert(concl, id);
    }

    /// Compute the least model. Returns a certificate checkable by
    /// recomputation (see `check::verify_saturation`).
    pub fn saturate(&mut self, budget: &mut Budget) -> Result<Saturation, Exhausted> {
        self.seed_facts();
        self.subst.ensure(self.prog.store.node_count());
        let np = self.prog.num_preds();
        for v in self.delta.iter_mut() {
            v.clear();
        }

        // Seed the delta with the program's own facts, per stratum.
        for i in 0..self.prog.rules.len() {
            let head = self.prog.rules[i].head;
            if self.prog.rules[i].body.is_empty() && self.db.contains(head) {
                let p = self.prog.store.sym(head);
                self.ensure_pred_slots(p);
                self.delta[p as usize].push(head);
            }
        }

        let mut rounds = 0u32;
        for stratum in 0..self.prog.num_strata {
            loop {
                let mut any = false;
                for p in 0..np.min(self.delta.len()) {
                    if self.prog.pred_stratum[p] == stratum && !self.delta[p].is_empty() {
                        any = true;
                        break;
                    }
                }
                if !any {
                    break;
                }
                rounds += 1;
                self.stats.rounds += 1;
                budget.charge(1)?;

                for v in self.work.iter_mut() {
                    v.clear();
                }
                for p in 0..np.min(self.delta.len()) {
                    if self.prog.pred_stratum[p] == stratum && !self.delta[p].is_empty() {
                        std::mem::swap(&mut self.work[p], &mut self.delta[p]);
                    }
                }

                let rules = self.prog.by_stratum[stratum as usize].clone();
                for rule_id in rules {
                    if self.prog.rules[rule_id as usize].backward_only {
                        continue;
                    }
                    self.ensure_renamed(rule_id);
                    let blen = self.ren_len(rule_id);
                    let mut seeds = Vec::new();
                    for i in 0..blen {
                        let lit = self.ren_lit(rule_id, i);
                        if !lit.pos {
                            continue;
                        }
                        let p = self.prog.store.sym(lit.atom);
                        if self.is_idb_in_stratum(p, stratum) {
                            seeds.push(i);
                        }
                    }
                    if seeds.is_empty() {
                        if !self.static_done[rule_id as usize] {
                            self.static_done[rule_id as usize] = true;
                            self.eval_rule(rule_id, None, budget)?;
                        }
                    } else {
                        for i in seeds {
                            let lit = self.ren_lit(rule_id, i);
                            let p = self.prog.store.sym(lit.atom) as usize;
                            let facts = std::mem::take(&mut self.work[p]);
                            for k in 0..facts.len() {
                                let t = facts[k];
                                self.eval_rule(rule_id, Some((i, t)), budget)?;
                            }
                            self.work[p] = facts;
                        }
                    }
                }
            }
        }
        Ok(Saturation {
            rounds,
            idb_facts: self.idb_fact_count(),
            closure_hash: self.closure_hash(),
        })
    }

    /// Naive full-recomputation fixpoint. Retained **only** as the benchmark
    /// baseline for `bench_semi_naive_vs_fixpoint`; no solver path calls it.
    pub fn saturate_naive(&mut self, budget: &mut Budget) -> Result<Saturation, Exhausted> {
        self.seed_facts();
        self.subst.ensure(self.prog.store.node_count());
        let rules: Vec<RuleId> = self
            .prog
            .rules
            .iter()
            .filter(|r| !r.backward_only)
            .map(|r| r.id)
            .collect();
        let mut rounds = 0u32;
        loop {
            let before = self.stats.new_facts;
            for &rule_id in &rules {
                if self.prog.rules[rule_id as usize].body.is_empty() {
                    continue;
                }
                self.eval_rule(rule_id, None, budget)?;
            }
            rounds += 1;
            if self.stats.new_facts == before {
                break;
            }
        }
        Ok(Saturation {
            rounds,
            idb_facts: self.idb_fact_count(),
            closure_hash: self.closure_hash(),
        })
    }
}

#[cfg(test)]
mod regressions {
    use super::*;

    /// A one-literal rule whose predicate is itself defined by facts. The
    /// bottom-up evaluator treats that predicate as IDB, so the delta seeds the
    /// only body position and the join has zero levels. This must yield exactly
    /// one solution per seed rather than spinning.
    #[test]
    fn single_literal_rule_terminates_and_derives() {
        let mut b = Builder::new();
        b.fact_n("edge", &["a", "b"]);
        b.fact_n("edge", &["b", "c"]);
        b.fact_n("edge", &["c", "d"]);
        let x = b.var("X");
        let y = b.var("Y");
        let h = b.atom("path", 2, &[x, y]);
        let l = b.pos("edge", 2, &[x, y]);
        b.rule(h, vec![l]);
        let prog = b.build().unwrap();
        let mut s = Solver::new(prog);
        let mut budget = Budget::steps(100_000);
        let sat = s.saturate(&mut budget).expect("must terminate");
        // 3 edge facts + 3 path facts.
        assert_eq!(sat.idb_facts, 6);
    }

    /// The join must enumerate *all* solutions for a seed, not just the last.
    #[test]
    fn every_solution_for_a_seed_is_derived() {
        let (prog, _) = super::tests_fixtures::transitive_closure_program();
        let mut s = Solver::new(prog);
        let mut budget = Budget::steps(100_000);
        let sat = s.saturate(&mut budget).expect("within budget");
        // path(a,b), path(b,c), path(a,c) plus the two edge facts.
        assert_eq!(sat.idb_facts, 5);
        assert_eq!(s.stats.rounds, 2, "path(a,c) needs exactly one extra round");
    }
}

#[cfg(test)]
mod regressions {
    use super::*;

    /// A one-literal rule whose predicate is itself defined by facts. The
    /// bottom-up evaluator treats that predicate as IDB, so the delta seeds the
    /// only body position and the join has zero levels. This must yield exactly
    /// one solution per seed rather than spinning forever.
    #[test]
    fn single_literal_rule_terminates_and_derives() {
        let mut b = Builder::new();
        b.fact_n("edge", &["a", "b"]);
        b.fact_n("edge", &["b", "c"]);
        b.fact_n("edge", &["c", "d"]);
        let x = b.var("X");
        let y = b.var("Y");
        let h = b.atom("path", 2, &[x, y]);
        let l = b.pos("edge", 2, &[x, y]);
        b.rule(h, vec![l]);
        let prog = b.build().unwrap();
        let mut s = Solver::new(prog);
        let mut budget = Budget::steps(100_000);
        let sat = s.saturate(&mut budget).expect("must terminate");
        // 3 edge facts + 3 path facts.
        assert_eq!(sat.idb_facts, 6);
    }

    /// The join must enumerate *all* solutions for a seed, not just the last.
    #[test]
    fn every_solution_for_a_seed_is_derived() {
        let (prog, _) = super::tests_fixtures::transitive_closure_program();
        let mut s = Solver::new(prog);
        let mut budget = Budget::steps(100_000);
        let sat = s.saturate(&mut budget).expect("within budget");
        // path(a,b), path(b,c), path(a,c) plus the two edge facts.
        assert_eq!(sat.idb_facts, 5);
        assert_eq!(s.stats.rounds, 2, "path(a,c) needs exactly one extra round");
    }
}
