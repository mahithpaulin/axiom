//! CDCL SAT core (ROADMAP II1).
//!
//! A conflict-driven clause-learning solver over its own flat literal array.
//! Per DD-0001 the rule IR is the interchange format, not the executable form:
//! this core lowers its input (ground rules, DIMACS) into clauses and never
//! touches terms, arenas or substitutions. Certificates are checked by code
//! that shares no search state with the solver (DD-0010): satisfying models by
//! direct satisfaction, unsatisfiability by replaying the recorded resolution
//! chain with a duplicated five-line resolver.
//!
//! Scope: two-watched-literal propagation, first-UIP learning, VSIDS
//! decisions, phase saving, Luby restarts, activity-based learned-clause
//! detachment. Detachment keeps storage (tombstones) so proof references stay
//! stable; a compacting collector is future work and is stated as such rather
//! than implied. Input is ground: rule grounding covers the negation-free
//! forward fragment (`ground_positive_program`); general CNF arrives as DIMACS.
//!
//! [`Lit`] is DIMACS-style: `+(v+1)` is positive over variable `v` (0-based),
//! `-(v+1)` negative. `0` is never a literal (it terminates DIMACS lines).

use crate::budget::Budget;
use crate::hash::FxHashMap;
use crate::program::Program;
use crate::status::Exhausted;
use crate::term::{T_CONST, T_FUN};
use std::collections::{HashMap, HashSet};

/// Variable id, 0-based.
pub type Var = u32;
/// Literal, DIMACS-style: `+(v+1)` positive, `-(v+1)` negative. Never 0.
pub type Lit = i32;

#[inline]
fn var_of(l: Lit) -> usize {
    debug_assert_ne!(l, 0);
    (l.unsigned_abs() as usize) - 1
}

#[inline]
fn is_pos(l: Lit) -> bool {
    l > 0
}

/// Watch-list index: positive and negative polarities watch separately.
#[inline]
fn lit_index(l: Lit) -> usize {
    var_of(l) * 2 + if is_pos(l) { 0 } else { 1 }
}

#[inline]
fn negate(l: Lit) -> Lit {
    debug_assert_ne!(l, 0);
    -l
}

#[inline]
fn lit_var(l: Lit) -> Var {
    var_of(l) as Var
}

/// Current value: 1 true, -1 false, 0 unassigned.
#[inline]
fn lit_value(assign: &[i8], l: Lit) -> i8 {
    let a = assign[var_of(l)];
    if a == 0 {
        0
    } else if (a == 1) == is_pos(l) {
        1
    } else {
        -1
    }
}

#[derive(Clone, Debug)]
struct Clause {
    lits: Vec<Lit>,
    learnt: bool,
    activity: f64,
    detached: bool,
}

#[derive(Clone, Copy)]
struct Watcher {
    clause: usize,
    blocker: Lit,
}

/// Structural term for theory proofs: names, not arena ids, so a proof
/// survives the arena that made it. Rendered from terms at emission,
/// rebuilt into a fresh store by the checker.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum STerm {
    Var(String),
    Const(String),
    App(String, Vec<STerm>),
}

/// Meaning of one theory SAT variable, structurally.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum AtomDesc {
    Rdl { x: STerm, y: STerm, c: i64 },
    Eq(STerm, STerm),
    Neq(STerm, STerm),
}

/// One theory lemma: `hyps => concl` (`None` = conflict), with the emitted
/// `clause` (negated hypotheses, plus the conclusion literal when present).
/// Checked by asserting the hypotheses in a fresh theory state, never by unit
/// propagation (which is incomplete for theory reasoning).
#[derive(Clone, Debug)]
pub struct TheoryLemma {
    pub clause: Vec<Lit>,
    pub hyps: Vec<Lit>,
    pub concl: Option<Lit>,
}

/// Theory solver plug-in for DPLL(T). Implemented by `theory.rs`; the core
/// only sees literal vectors and justification clauses, never terms.
///
/// The single entry point keeps the protocol small: `full=false` after each
/// propagation fixpoint (partial assignment: propagate, report conflict, or
/// stay silent), `full=true` on complete assignments (confirm or conflict).
/// Every returned lemma is recorded by the handler itself; the solver only
/// files its clause.
pub trait TheoryHandler {
    fn theory_step(
        &mut self,
        store: &crate::term::TermStore,
        assign: &[i8],
        full: bool,
    ) -> TheoryResponse;
    /// Move recorded lemmas out (proof assembly).
    fn take_lemmas(&mut self) -> Vec<TheoryLemma>;
    /// (rounds, conflicts, propagations, lemmas) — see [`TheoryStats`].
    fn stats(&self) -> TheoryStats;
}

/// Handler response for one theory call.
pub enum TheoryResponse {
    /// Implied literals with justifying lemmas. Each lemma's clause is
    /// added; unassigned literals are enqueued with it as reason.
    Implications(Vec<(Lit, TheoryLemma)>),
    /// Inconsistent under the current assignment; the lemma explains why.
    Conflict(TheoryLemma),
    /// Nothing to report.
    Consistent,
}

/// Theory-side counters: solver rounds entered, conflicts, implications, and
/// lemmas emitted through this channel.
#[derive(Clone, Copy, Default, Debug)]
pub struct TheoryStats {
    pub rounds: u64,
    pub conflicts: u64,
    pub propagations: u64,
    pub lemmas: u64,
}

/// An unsatisfiability proof: learnt clauses in learning order. Each one is
/// verified by reverse unit propagation (RUP) against the input plus earlier
/// learnts, and the whole set together must propagate to conflict. Clause
/// detachment never removes proof material (tombstones stay stored), so the
/// order recorded here is always checkable.
#[derive(Clone, Debug, Default)]
pub struct UnsatProof {
    pub learnts: Vec<Vec<Lit>>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SatCheckErr {
    /// A learnt clause is not implied (RUP check failed).
    NotImplied { index: usize },
    /// The full set does not propagate to conflict.
    NotEmpty,
}

impl core::fmt::Display for SatCheckErr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SatCheckErr::NotImplied { index } => {
                write!(f, "learnt clause {index} is not reverse-unit-propagated")
            }
            SatCheckErr::NotEmpty => write!(f, "clauses do not propagate to conflict"),
        }
    }
}

impl core::error::Error for SatCheckErr {}

#[derive(Clone, Debug)]
pub enum SatOutcome {
    /// Satisfiable; `model[v]` is 1/-1 for every variable.
    Sat { model: Vec<i8> },
    /// Unsatisfiable; `proof` replays to the empty clause.
    Unsat { proof: UnsatProof },
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct SatStats {
    pub decisions: u64,
    pub propagations: u64,
    pub conflicts: u64,
    pub learned: u64,
    pub restarts: u64,
    pub deleted: u64,
}

pub struct SatSolver {
    nvars: usize,
    clauses: Vec<Clause>,
    /// Sorted literal vectors of stored non-tautological clauses, for
    /// duplicate suppression. Learnt clauses go through the same filter.
    seen: HashSet<Vec<Lit>>,
    watches: Vec<Vec<Watcher>>,
    assign: Vec<i8>,
    level: Vec<u32>,
    reason: Vec<Option<usize>>,
    /// Saved phase per variable (phase saving).
    polarity: Vec<bool>,
    activity: Vec<f64>,
    trail: Vec<Lit>,
    trail_lim: Vec<usize>,
    qhead: usize,
    cur_level: u32,
    var_inc: f64,
    conflicts: u64,
    conflicts_since_restart: u64,
    luby_idx: u64,
    has_empty: bool,
    ok: bool,
    /// Learnt clauses in learning order: the RUP proof under construction.
    proof_learnts: Vec<Vec<Lit>>,
    /// Optional DPLL(T) plug-in. `None` (plain SAT) costs one branch per
    /// loop iteration and nothing else.
    pub theory: Option<Box<dyn TheoryHandler>>,
    pub stats: SatStats,
}

impl Default for SatSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl SatSolver {
    pub fn new() -> Self {
        SatSolver {
            nvars: 0,
            clauses: Vec::new(),
            seen: HashSet::new(),
            watches: Vec::new(),
            assign: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            polarity: Vec::new(),
            activity: Vec::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            cur_level: 0,
            var_inc: 1.0,
            conflicts: 0,
            conflicts_since_restart: 0,
            luby_idx: 1,
            has_empty: false,
            ok: true,
            proof_learnts: Vec::new(),
            theory: None,
            stats: SatStats::default(),
        }
    }

    pub fn nvars(&self) -> usize {
        self.nvars
    }

    pub fn nclauses(&self) -> usize {
        self.clauses.len()
    }

    fn ensure_vars(&mut self, n: usize) {
        while self.nvars < n {
            self.assign.push(0);
            self.level.push(0);
            self.reason.push(None);
            self.polarity.push(false);
            self.activity.push(0.0);
            self.watches.push(Vec::new());
            self.watches.push(Vec::new());
            self.nvars += 1;
        }
    }

    pub fn new_var(&mut self) -> Var {
        self.ensure_vars(self.nvars + 1);
        (self.nvars - 1) as Var
    }

    /// Add a clause. Tautologies and duplicates are skipped (both sound: a
    /// tautology never constrains, a duplicate adds nothing). Returns the
    /// arena index, or `None` when skipped.
    pub fn add_clause(&mut self, lits: &[Lit]) -> Option<usize> {
        // Order-preserving dedup; tautology scan.
        let mut norm: Vec<Lit> = Vec::with_capacity(lits.len());
        for &l in lits {
            debug_assert_ne!(l, 0);
            if norm.contains(&negate(l)) {
                return None;
            }
            if !norm.contains(&l) {
                norm.push(l);
            }
        }
        for &l in &norm {
            let need = var_of(l) + 1;
            self.ensure_vars(need);
        }
        if norm.is_empty() {
            self.has_empty = true;
            self.ok = false;
            self.clauses.push(Clause {
                lits: Vec::new(),
                learnt: false,
                activity: 0.0,
                detached: false,
            });
            return Some(self.clauses.len() - 1);
        }
        let mut key = norm.clone();
        key.sort_unstable();
        if !self.seen.insert(key) {
            return None;
        }
        self.clauses.push(Clause {
            lits: norm,
            learnt: false,
            activity: 0.0,
            detached: false,
        });
        let cid = self.clauses.len() - 1;
        // Units are enqueued explicitly during preprocessing; only longer
        // clauses need watches.
        if self.clauses[cid].lits.len() >= 2 {
            self.attach(cid);
        }
        Some(cid)
    }

    /// Attach two watches. Unit clauses are never attached: they are enqueued
    /// explicitly during preprocessing (input) or after learning.
    fn attach(&mut self, cid: usize) {
        debug_assert!(self.clauses[cid].lits.len() >= 2);
        let (a, b) = (self.clauses[cid].lits[0], self.clauses[cid].lits[1]);
        self.watches[lit_index(a)].push(Watcher {
            clause: cid,
            blocker: b,
        });
        self.watches[lit_index(b)].push(Watcher {
            clause: cid,
            blocker: a,
        });
    }

    fn enqueue(&mut self, l: Lit, reason: Option<usize>) {
        let v = var_of(l);
        debug_assert_eq!(self.assign[v], 0);
        self.assign[v] = if is_pos(l) { 1 } else { -1 };
        self.level[v] = self.cur_level;
        self.reason[v] = reason;
        self.polarity[v] = is_pos(l);
        self.trail.push(l);
    }

    fn backtrack(&mut self, level: u32) {
        while self.cur_level > level {
            let lim = self.trail_lim.pop().expect("level stack underflow");
            while self.trail.len() > lim {
                let l = self.trail.pop().expect("trail underflow");
                let v = var_of(l);
                self.assign[v] = 0;
                self.reason[v] = None;
                // Polarity is deliberately kept: phase saving.
            }
            self.cur_level -= 1;
        }
        self.qhead = self.trail.len();
    }

    /// Unit propagation with two watched literals and blocker literals.
    /// Returns the conflicting clause id, if any.
    fn propagate(&mut self, budget: &mut Budget) -> Result<Option<usize>, Exhausted> {
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            self.stats.propagations += 1;
            if self.stats.propagations & 0xFFF == 0 {
                budget.charge(64)?;
            }
            let falsified = negate(p);
            let idx = lit_index(falsified);
            let mut ws = std::mem::take(&mut self.watches[idx]);
            let mut i = 0;
            let mut conflict = None;
            while i < ws.len() {
                let cid = ws[i].clause;
                let blocker = ws[i].blocker;
                if self.clauses[cid].detached {
                    i += 1;
                    continue;
                }
                if lit_value(&self.assign, blocker) == 1 {
                    i += 1;
                    continue;
                }
                // Invariant: the falsified literal is watched at position 0
                // or 1. Detached clauses keep their literals, so the
                // invariant survives detachment.
                let fpos = if self.clauses[cid].lits[0] == falsified {
                    0
                } else {
                    debug_assert_eq!(self.clauses[cid].lits[1], falsified);
                    1
                };
                let other = self.clauses[cid].lits[1 - fpos];
                if lit_value(&self.assign, other) == 1 {
                    ws[i].blocker = other;
                    i += 1;
                    continue;
                }
                let mut found = None;
                for (k, &lk) in self.clauses[cid].lits.iter().enumerate().skip(2) {
                    if lit_value(&self.assign, lk) != -1 {
                        found = Some(k);
                        break;
                    }
                }
                if let Some(k) = found {
                    self.clauses[cid].lits.swap(fpos, k);
                    let new_other = self.clauses[cid].lits[1 - fpos];
                    ws.swap_remove(i);
                    // Watch the new literal: notify when *it* is falsified.
                    let new_idx = lit_index(self.clauses[cid].lits[fpos]);
                    self.watches[new_idx].push(Watcher {
                        clause: cid,
                        blocker: new_other,
                    });
                } else if lit_value(&self.assign, other) == -1 {
                    conflict = Some(cid);
                    break;
                } else {
                    self.enqueue(other, Some(cid));
                    i += 1;
                }
            }
            self.watches[idx].append(&mut ws);
            if let Some(c) = conflict {
                return Ok(Some(c));
            }
        }
        Ok(None)
    }

    /// First-UIP conflict analysis. Returns the learnt clause (empty when the
    /// conflict stands at level 0, i.e. unsatisfiable) and the backjump level.
    /// The learnt clause is recorded by the caller for the RUP proof.
    fn analyze(&mut self, confl: usize) -> (Vec<Lit>, u32) {
        let mut learnt = vec![0];
        let mut seen = vec![false; self.nvars];
        let mut path_c = 0usize;
        let mut p: Option<Lit> = None;
        if self.clauses[confl].lits.is_empty() {
            return (Vec::new(), 0);
        }
        let mut cur_lits = self.clauses[confl].lits.clone();
        let mut idx = self.trail.len();
        loop {
            for &q in &cur_lits {
                if Some(q) == p {
                    continue;
                }
                let v = var_of(q);
                if !seen[v] {
                    seen[v] = true;
                    if self.level[v] == self.cur_level {
                        path_c += 1;
                    } else {
                        learnt.push(q);
                    }
                }
            }
            // Last assigned seen variable. Infallible: every marked literal
            // is falsified hence assigned, so all marked vars sit on the
            // trail. An underflow here would be an engine bug, and it is
            // allowed to be loud rather than silently wrong.
            loop {
                idx -= 1;
                if seen[var_of(self.trail[idx])] {
                    p = Some(self.trail[idx]);
                    break;
                }
            }
            let pl = p.expect("selected literal");
            self.bump_activity(var_of(pl));
            match self.reason[var_of(pl)] {
                None => {
                    // Decision variable: the unique current-level literal,
                    // i.e. the first UIP.
                    debug_assert_eq!(path_c, 1);
                    learnt[0] = negate(pl);
                    break;
                }
                Some(rc) => {
                    cur_lits = resolvent(&cur_lits, &self.clauses[rc].lits, lit_var(pl))
                        .expect("1UIP resolvent exists");
                    if cur_lits.is_empty() {
                        return (Vec::new(), 0);
                    }
                    if self.level[var_of(pl)] == self.cur_level {
                        path_c -= 1;
                    }
                }
            }
        }
        let mut bt = 0;
        for &l in &learnt[1..] {
            bt = bt.max(self.level[var_of(l)]);
        }
        (learnt, bt)
    }

    fn bump_activity(&mut self, v: usize) {
        self.activity[v] += self.var_inc;
        if self.activity[v] > 1e100 {
            for a in self.activity.iter_mut() {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
    }

    /// VSIDS decision: highest-activity unassigned variable, saved phase.
    fn decide(&mut self) {
        let mut best: Option<usize> = None;
        let mut best_act = -1.0f64;
        for v in 0..self.nvars {
            if self.assign[v] == 0 && self.activity[v] > best_act {
                best_act = self.activity[v];
                best = Some(v);
            }
        }
        let v = best.expect("decide called with no unassigned variable");
        self.cur_level += 1;
        self.trail_lim.push(self.trail.len());
        let lit = if self.polarity[v] {
            v as Lit + 1
        } else {
            -((v as Lit) + 1)
        };
        self.enqueue(lit, None);
        self.stats.decisions += 1;
    }

    /// Luby restart sequence (1-based): 1,1,2,1,1,2,4,... Iterative: each
    /// step strips the leading complete block.
    fn luby(i: u64) -> u64 {
        debug_assert!(i >= 1);
        let mut i = i;
        loop {
            let mut k = 1u32;
            while (1u64 << k) - 1 < i {
                k += 1;
            }
            if (1u64 << k) - 1 == i {
                return 1 << (k - 1);
            }
            i = i - (1u64 << (k - 1)) + 1;
        }
    }

    /// Detach the weaker half of non-locked learned clauses longer than two
    /// literals. Storage is kept (tombstones) so proof references stay stable;
    /// detached clauses are skipped by propagation. Locked clauses — reasons
    /// of current assignments — are never detached.
    fn delete_learned(&mut self) {
        let mut locked = vec![false; self.clauses.len()];
        for v in 0..self.nvars {
            if self.assign[v] != 0 {
                if let Some(c) = self.reason[v] {
                    locked[c] = true;
                }
            }
        }
        let mut cands: Vec<(usize, f64)> = Vec::new();
        for (cid, c) in self.clauses.iter().enumerate() {
            if c.learnt && !c.detached && !locked[cid] && c.lits.len() > 2 {
                cands.push((cid, c.activity));
            }
        }
        if cands.len() <= 4 {
            return;
        }
        cands.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(core::cmp::Ordering::Equal));
        let drop = cands.len() / 2;
        for (cid, _) in cands.into_iter().take(drop) {
            self.clauses[cid].detached = true;
            self.stats.deleted += 1;
        }
    }

    fn store_learnt(&mut self, lits: Vec<Lit>) -> usize {
        self.proof_learnts.push(lits.clone());
        self.push_learnt(lits)
    }

    /// Add a theory lemma: watched, stored and deletable like a learnt clause
    /// (it participates in propagation, reasons and deletion), but recorded in
    /// the theory proof channel instead of the RUP stream — its justification
    /// is theory reasoning, which unit propagation cannot replay.
    pub fn add_theory_lemma(&mut self, lits: Vec<Lit>) -> usize {
        self.push_learnt(lits)
    }

    fn push_learnt(&mut self, lits: Vec<Lit>) -> usize {
        self.clauses.push(Clause {
            lits,
            learnt: true,
            activity: self.var_inc,
            detached: false,
        });
        let cid = self.clauses.len() - 1;
        if self.clauses[cid].lits.len() >= 2 {
            self.attach(cid);
        }
        cid
    }

    /// Move the accumulated learnt clauses out as the RUP proof.
    pub(crate) fn take_proof(&mut self) -> UnsatProof {
        UnsatProof {
            learnts: std::mem::take(&mut self.proof_learnts),
        }
    }

    pub fn solve(&mut self, budget: &mut Budget) -> Result<SatOutcome, Exhausted> {
        // No theory configured: the store is unused. It exists so the
        // theory-enabled path shares one implementation below.
        let store = crate::term::TermStore::new();
        self.solve_inner(budget, &store)
    }

    /// Solve with theory hooks enabled. Requires `self.theory` to be `Some`;
    /// without it this behaves exactly like [`SatSolver::solve`].
    pub fn solve_theory(
        &mut self,
        budget: &mut Budget,
        store: &crate::term::TermStore,
    ) -> Result<SatOutcome, Exhausted> {
        self.solve_inner(budget, store)
    }

    fn solve_inner(
        &mut self,
        budget: &mut Budget,
        store: &crate::term::TermStore,
    ) -> Result<SatOutcome, Exhausted> {
        if self.has_empty {
            return Ok(SatOutcome::Unsat {
                proof: UnsatProof::default(),
            });
        }
        // Level-0 units. They carry no watches (nothing to watch on a
        // singleton), so a unit contradicted by an earlier one must be
        // caught here, not in propagation.
        let units: Vec<(Lit, usize)> = self
            .clauses
            .iter()
            .enumerate()
            .filter(|(_, c)| c.lits.len() == 1 && !c.detached)
            .map(|(cid, c)| (c.lits[0], cid))
            .collect();
        for (l, cid) in units {
            match lit_value(&self.assign, l) {
                0 => self.enqueue(l, Some(cid)),
                -1 => {
                    let _ = self.analyze(cid);
                    return Ok(SatOutcome::Unsat {
                        proof: self.take_proof(),
                    });
                }
                _ => {}
            }
        }
        if let Some(confl) = self.propagate(budget)? {
            let _ = self.analyze(confl);
            return Ok(SatOutcome::Unsat {
                proof: self.take_proof(),
            });
        }
        loop {
            match self.propagate(budget)? {
                Some(confl) => {
                    self.stats.conflicts += 1;
                    budget.charge(1)?;
                    self.conflicts += 1;
                    self.conflicts_since_restart += 1;
                    let (learnt, bt) = self.analyze(confl);
                    self.var_inc *= 1.0 / 0.95;
                    if learnt.is_empty() {
                        return Ok(SatOutcome::Unsat {
                            proof: self.take_proof(),
                        });
                    }
                    let cid = self.store_learnt(learnt);
                    self.stats.learned += 1;
                    self.backtrack(bt);
                    let asserting = self.clauses[cid].lits[0];
                    self.enqueue(asserting, Some(cid));
                    if self.conflicts % 2000 == 0 {
                        self.delete_learned();
                    }
                    let limit = Self::luby(self.luby_idx) * 100;
                    if self.conflicts_since_restart >= limit {
                        self.luby_idx += 1;
                        self.conflicts_since_restart = 0;
                        self.stats.restarts += 1;
                        self.backtrack(0);
                    }
                }
                None => {
                    if self.assign.iter().all(|&a| a != 0) {
                        // Theory verdict on full models; plain SAT returns here.
                        if self.theory.is_some() {
                            let mut h = self.theory.take().expect("present");
                            let resp = h.theory_step(store, &self.assign, true);
                            self.theory = Some(h);
                            match resp {
                                TheoryResponse::Conflict(lemma) => {
                                    self.add_theory_lemma(lemma.clause.clone());
                                    self.backtrack(0);
                                    continue;
                                }
                                _ => {}
                            }
                        }
                        return Ok(SatOutcome::Sat {
                            model: self.assign.clone(),
                        });
                    }
                    // Theory propagation hook: implied literals arrive with
                    // justifying lemmas and re-enter propagation as clauses.
                    // With no theory configured this is one branch, nothing more.
                    if self.theory.is_some() {
                        let mut h = self.theory.take().expect("present");
                        let resp = h.theory_step(store, &self.assign, false);
                        self.theory = Some(h);
                        match resp {
                            TheoryResponse::Implications(items) => {
                                // Progress accounting: an implication whose
                                // literal is already true adds nothing —
                                // re-adding its lemma every round would spin
                                // forever on duplicates.
                                let mut added = false;
                                for (lit, lemma) in items {
                                    if lit_value(&self.assign, lit) != 1 {
                                        let cid =
                                            self.add_theory_lemma(lemma.clause.clone());
                                        if lit_value(&self.assign, lit) == 0 {
                                            self.enqueue(lit, Some(cid));
                                        }
                                        added = true;
                                    }
                                }
                                if added {
                                    continue;
                                }
                            }
                            TheoryResponse::Conflict(lemma) => {
                                self.add_theory_lemma(lemma.clause.clone());
                                self.backtrack(0);
                                continue;
                            }
                            TheoryResponse::Consistent => {}
                        }
                    }
                    self.decide();
                    budget.charge(1)?;
                }
            }
        }
    }
}

/// One resolution step, used only inside conflict analysis to continue the
/// search after recording. Proof checking does not use resolution at all:
/// learnt clauses are verified by reverse unit propagation below, which needs
/// no shared search code (DD-0010).
fn resolvent(a: &[Lit], b: &[Lit], pivot: Var) -> Option<Vec<Lit>> {
    let p = pivot as Lit + 1;
    let n = -p;
    let (big, small, drop_big, drop_small) = if a.contains(&p) && b.contains(&n) {
        (a, b, p, n)
    } else if a.contains(&n) && b.contains(&p) {
        (a, b, n, p)
    } else {
        return None;
    };
    let mut out = Vec::with_capacity(big.len() + small.len());
    for &l in big {
        if l != drop_big && !out.contains(&l) {
            out.push(l);
        }
    }
    for &l in small {
        if l != drop_small && !out.contains(&l) {
            out.push(l);
        }
    }
    Some(out)
}

/// Does the model satisfy every clause?
pub fn verify_sat(clauses: &[Vec<Lit>], model: &[i8]) -> bool {
    clauses.iter().all(|c| {
        c.iter().any(|&l| {
            let v = var_of(l);
            v < model.len() && ((model[v] == 1) == is_pos(l))
        })
    })
}

/// Naive unit propagation to conflict-or-fixpoint. Returns true on conflict.
/// Deliberately simple (quadratic scan, no watches): it is the checker's
/// independent engine, not the solver's, and corpus sizes make it instant.
fn up_conflict(clauses: &[Vec<Lit>], assumps: &[Lit]) -> bool {
    let mut max_v = 0usize;
    for c in clauses {
        for &l in c {
            max_v = max_v.max(var_of(l));
        }
    }
    for &l in assumps {
        max_v = max_v.max(var_of(l));
    }
    let mut assign = vec![0i8; max_v + 1];
    for &l in assumps {
        let v = var_of(l);
        let val = if is_pos(l) { 1 } else { -1 };
        if assign[v] == -val {
            return true;
        }
        assign[v] = val;
    }
    loop {
        let mut unit: Option<Lit> = None;
        for c in clauses {
            let mut open: Option<Lit> = None;
            let mut satisfied = false;
            for &l in c {
                match lit_value(&assign, l) {
                    1 => {
                        satisfied = true;
                        break;
                    }
                    0 => {
                        if open.is_some() {
                            open = Some(0);
                            break;
                        }
                        open = Some(l);
                    }
                    _ => {}
                }
            }
            if satisfied {
                continue;
            }
            match open {
                None => return true, // every literal false: conflict
                Some(0) => {}        // two or more open: not unit
                Some(l) => {
                    unit = Some(l);
                    break;
                }
            }
        }
        match unit {
            None => return false,
            Some(l) => {
                let v = var_of(l);
                let val = if is_pos(l) { 1 } else { -1 };
                if assign[v] == -val {
                    return true;
                }
                assign[v] = val;
            }
        }
    }
}

/// Verify an unsatisfiability proof by reverse unit propagation: every learnt
/// clause, negated, must propagate to conflict against the input plus earlier
/// learnts, and the whole set together must propagate to conflict with no
/// assumptions. Tautologies and duplicates in the input are harmless (never
/// unit, never conflicting), so no canonicalisation is shared with the solver.
pub fn verify_unsat(input: &[Vec<Lit>], proof: &UnsatProof) -> Result<(), SatCheckErr> {
    let mut db: Vec<Vec<Lit>> = input.to_vec();
    for (i, c) in proof.learnts.iter().enumerate() {
        let assumps: Vec<Lit> = c.iter().map(|&l| negate(l)).collect();
        if !up_conflict(&db, &assumps) {
            return Err(SatCheckErr::NotImplied { index: i });
        }
        db.push(c.clone());
    }
    if up_conflict(&db, &[]) {
        Ok(())
    } else {
        Err(SatCheckErr::NotEmpty)
    }
}

/// Parse DIMACS CNF. Strict: requires the `p cnf` header, rejects
/// unterminated clauses and out-of-range variables with positions.
pub fn parse_dimacs(src: &str) -> Result<(usize, Vec<Vec<Lit>>), String> {
    let mut nvars: Option<usize> = None;
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    let mut cur: Vec<Lit> = Vec::new();
    for (ln, line) in src.lines().enumerate() {
        let t = line.trim();
        if t.is_empty() || t.starts_with('c') {
            continue;
        }
        if t.starts_with('p') {
            let parts: Vec<&str> = t.split_whitespace().collect();
            if parts.len() != 4 || parts[1] != "cnf" {
                return Err(format!("line {}: bad header {t:?}", ln + 1));
            }
            nvars = Some(
                parts[2]
                    .parse::<usize>()
                    .map_err(|_| format!("line {}: bad var count", ln + 1))?,
            );
            continue;
        }
        for tok in t.split_whitespace() {
            let l: Lit = tok
                .parse::<Lit>()
                .map_err(|_| format!("line {}: bad literal {tok:?}", ln + 1))?;
            if l == 0 {
                clauses.push(std::mem::take(&mut cur));
            } else {
                cur.push(l);
            }
        }
    }
    if !cur.is_empty() {
        return Err("unterminated final clause (missing 0)".to_string());
    }
    let nvars = nvars.ok_or_else(|| "missing `p cnf` header".to_string())?;
    for c in &clauses {
        for &l in c {
            if var_of(l) >= nvars {
                return Err(format!(
                    "variable {} exceeds header count {nvars}",
                    var_of(l) + 1
                ));
            }
        }
    }
    Ok((nvars, clauses))
}

/// Grounding of the negation-free forward fragment into clauses: one
/// variable per ground atom, one clause `(¬b1 ∨ … ∨ ¬bn ∨ h)` per ground rule
/// instance, one unit clause per fact. Rules with function-symbol heads
/// (`backward_only`) and rules with negated bodies are skipped and counted —
/// their instances are infinite or need completion semantics, respectively.
/// Only constant-domain programs ground finitely; a fact containing a function
/// term makes the grounding incomplete and is counted in `skipped_facts`.
pub struct Grounding {
    pub nvars: usize,
    pub clauses: Vec<Vec<Lit>>,
    /// Ground atom per variable, for answers.
    pub atoms: Vec<crate::term::TermId>,
    pub skipped_rules: usize,
    pub skipped_facts: usize,
}

pub fn ground_positive_program(prog: &mut Program) -> Grounding {
    use crate::term::TermId;
    // Constant domain: every constant symbol occurring in any rule.
    let mut consts: Vec<crate::symbol::SymId> = Vec::new();
    {
        let mut seen = HashSet::new();
        for r in &prog.rules {
            let mut stack = vec![r.head];
            stack.extend(r.body.iter().map(|l| l.atom));
            while let Some(t) = stack.pop() {
                if prog.store.kind(t) == T_CONST {
                    if seen.insert(prog.store.sym(t)) {
                        consts.push(prog.store.sym(t));
                    }
                } else {
                    stack.extend(prog.store.args(t).iter().copied());
                }
            }
        }
    }
    let mut domain: Vec<TermId> = Vec::with_capacity(consts.len());
    for s in consts {
        domain.push(prog.store.constant(s));
    }
    let mut atom_var: HashMap<TermId, Var> = HashMap::new();
    let mut atoms: Vec<TermId> = Vec::new();
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    let mut skipped_rules = 0usize;
    let mut skipped_facts = 0usize;
    let var_of_atom =
        |t: TermId, atom_var: &mut HashMap<TermId, Var>, atoms: &mut Vec<TermId>| -> Var {
            if let Some(&v) = atom_var.get(&t) {
                return v;
            }
            let v = atoms.len() as Var;
            atom_var.insert(t, v);
            atoms.push(t);
            v
        };
    for ri in 0..prog.rules.len() {
        let rule = prog.rules[ri].clone();
        if rule.body.is_empty() {
            // Fact: must be a constant-only ground atom to join the domain.
            let mut bad = false;
            let mut stack = vec![rule.head];
            while let Some(t) = stack.pop() {
                let k = prog.store.kind(t);
                if k == T_FUN {
                    bad = true;
                    break;
                }
                stack.extend(prog.store.args(t).iter().copied());
            }
            if bad || !prog.store.is_ground(rule.head) {
                skipped_facts += 1;
                continue;
            }
            let v = var_of_atom(rule.head, &mut atom_var, &mut atoms);
            clauses.push(vec![v as Lit + 1]);
            continue;
        }
        if prog.rules[ri].backward_only || rule.body.iter().any(|l| !l.pos) {
            skipped_rules += 1;
            continue;
        }
        // Cartesian product over the domain, odometer-style (no recursion).
        let k = rule.local_vars.len();
        if domain.is_empty() && k > 0 {
            skipped_rules += 1;
            continue;
        }
        let mut idx = vec![0usize; k];
        loop {
            let mut env = FxHashMap::with_capacity_and_hasher(k, Default::default());
            for (j, &local) in rule.local_vars.iter().enumerate() {
                env.insert(local, domain[idx[j]]);
            }
            let head = prog.store.rename(rule.head, &env, 0);
            if prog.store.is_ground(head) {
                let mut clause = Vec::with_capacity(rule.body.len() + 1);
                let mut ok = true;
                for l in &rule.body {
                    let a = prog.store.rename(l.atom, &env, 0);
                    if !prog.store.is_ground(a) {
                        ok = false;
                        break;
                    }
                    let v = var_of_atom(a, &mut atom_var, &mut atoms);
                    clause.push(-((v as Lit) + 1));
                }
                if ok {
                    let v = var_of_atom(head, &mut atom_var, &mut atoms);
                    clause.push(v as Lit + 1);
                    clauses.push(clause);
                }
            }
            // Odometer advance.
            let mut j = 0;
            while j < k {
                idx[j] += 1;
                if idx[j] < domain.len() {
                    break;
                }
                idx[j] = 0;
                j += 1;
            }
            if j == k {
                break;
            }
        }
    }
    let nvars = atoms.len();
    Grounding {
        nvars,
        clauses,
        atoms,
        skipped_rules,
        skipped_facts,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn solve_all(clauses: &[Vec<Lit>]) -> SatOutcome {
        let mut s = SatSolver::new();
        for c in clauses {
            s.add_clause(c);
        }
        let mut b = Budget::unlimited();
        s.solve(&mut b).expect("within budget")
    }

    #[test]
    fn unit_conflict_is_unsat() {
        match solve_all(&[vec![1], vec![-1]]) {
            SatOutcome::Unsat { proof } => {
                assert!(verify_unsat(&[vec![1], vec![-1]], &proof).is_ok());
            }
            SatOutcome::Sat { .. } => panic!("must be unsat"),
        }
    }

    #[test]
    fn empty_clause_is_unsat() {
        match solve_all(&[vec![1, 2], vec![]]) {
            SatOutcome::Unsat { proof } => {
                assert!(verify_unsat(&[vec![1, 2], vec![]], &proof).is_ok());
            }
            SatOutcome::Sat { .. } => panic!("must be unsat"),
        }
    }

    #[test]
    fn xor_chain_is_sat_with_verified_model() {
        // x1 != x2, x2 != x3: satisfiable, two models.
        let clauses = vec![vec![1, 2], vec![-1, -2], vec![2, 3], vec![-2, -3]];
        match solve_all(&clauses) {
            SatOutcome::Sat { model } => assert!(verify_sat(&clauses, &model)),
            SatOutcome::Unsat { .. } => panic!("must be sat"),
        }
    }

    #[test]
    fn pigeonhole_2_1_is_unsat_with_proof() {
        // Two pigeons, one hole: p1, p2, -(p1&p2).
        let clauses = vec![vec![1], vec![2], vec![-1, -2]];
        match solve_all(&clauses) {
            SatOutcome::Unsat { proof } => {
                assert!(verify_unsat(&clauses, &proof).is_ok());
            }
            SatOutcome::Sat { .. } => panic!("must be unsat"),
        }
    }

    #[test]
    fn tautology_and_duplicates_are_absorbed() {
        let mut s = SatSolver::new();
        assert!(s.add_clause(&[1, -1, 2]).is_none());
        assert!(s.add_clause(&[1, 2]).is_some());
        assert!(s.add_clause(&[2, 1, 1]).is_none());
        assert_eq!(s.nclauses(), 1);
    }

    #[test]
    fn luby_sequence_starts_1_1_2() {
        assert_eq!(SatSolver::luby(1), 1);
        assert_eq!(SatSolver::luby(2), 1);
        assert_eq!(SatSolver::luby(3), 2);
        assert_eq!(SatSolver::luby(4), 1);
    }
}
