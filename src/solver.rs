//! The solver: everything the core owns, and the only public entry point.
//!
//! ## Ownership
//!
//! One `Solver` owns the program, the substitution, the fact database and the
//! derivation log. Nothing else in the crate mutates them. That is what makes
//! the independent checker possible: `&Solver` is enough to check a proof, and
//! the checker never touches the substitution the solver used.
//!
//! ## Rule caching
//!
//! Each rule is renamed to fresh global variables exactly once, lazily, and the
//! result is reused for every subsequent derivation. Sound only because each
//! firing is enclosed in a trail mark that is undone when it finishes, so no
//! binding survives into the next firing.
//! `tests/soundness.rs::no_binding_leaks_across_derivations` guards this.
//!
//! ## Borrowing discipline
//!
//! Inference needs `&mut` on the substitution, the store, the database and the
//! derivation log simultaneously. Rather than threading eight parameters through
//! every helper, the inference routines take `&mut self` and read rule data
//! through `ren_*` accessors that return `Copy` values. Holding a `&Renamed`
//! across a `&mut self` call would not compile; copying a 4-byte `TermId` or an
//! 8-byte `Literal` does. This is a deliberate choice for the whole inference
//! layer and is the reason those accessors exist.

use crate::budget::Budget;
use crate::check;
use crate::db::Db;
use crate::hash::FxHashMap;
use crate::program::{Literal, Program, RuleId};
use crate::proof::{CheckErr, DerivId, Derivation, Proof, Saturation};
use crate::status::{Exhausted, Status};
use crate::subst::Subst;
use crate::term::TermId;

/// Whether to record derivations.
///
/// This is not a cosmetic switch. Measured cost of `Full` on transitive closure
/// is roughly an order of magnitude more memory than the facts themselves
/// (see docs/PERFORMANCE.md, `memory_breakdown`): every derived fact stores a
/// `Derivation` with two `Vec`s, and each `Vec` is a separate heap block. On a
/// 7 GB machine that is the difference between solving and not solving.
///
/// The status contract is preserved either way. With `Off` the engine cannot
/// support a `Proved` claim, so it reports `Found` -- "a witness exists, no
/// proof attached" -- rather than a definite status with nothing behind it.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum ProofMode {
    /// Least model only. No derivations recorded.
    Off,
    /// Every derivation recorded; proofs available and independently checkable.
    #[default]
    Full,
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub struct Stats {
    /// Semi-naive rounds executed.
    pub rounds: u64,
    /// Rule firings that produced a new fact.
    pub derivations: u64,
    /// Join levels entered.
    pub join_levels: u64,
    /// Candidate tuples examined. The primary cost proxy.
    pub candidates: u64,
    pub new_facts: u64,
    /// Backward resolution rule applications.
    pub sld_steps: u64,
    pub max_depth: u64,
    /// Heads that were not ground after a successful join. Must stay 0; it is a
    /// canary for a soundness bug in the join, and is asserted in tests.
    pub non_ground_heads: u64,
}

impl Stats {
    pub fn delta(&self, prev: &Stats) -> Stats {
        Stats {
            rounds: self.rounds.wrapping_sub(prev.rounds),
            derivations: self.derivations.wrapping_sub(prev.derivations),
            join_levels: self.join_levels.wrapping_sub(prev.join_levels),
            candidates: self.candidates.wrapping_sub(prev.candidates),
            new_facts: self.new_facts.wrapping_sub(prev.new_facts),
            sld_steps: self.sld_steps.wrapping_sub(prev.sld_steps),
            max_depth: self.max_depth.max(prev.max_depth),
            non_ground_heads: self.non_ground_heads.wrapping_sub(prev.non_ground_heads),
        }
    }
}

/// A rule with its local variables replaced by fresh global variables.
pub struct Renamed {
    pub head: TermId,
    pub body: Vec<Literal>,
    /// `(local var id, global var node)`, same order as `rule.local_vars`.
    pub map: Vec<(u32, TermId)>,
}

pub struct Solver {
    pub prog: Program,
    pub subst: Subst,
    pub db: Db,
    pub derivs: Vec<Derivation>,
    pub deriv_of: FxHashMap<TermId, DerivId>,
    pub stats: Stats,
    /// Whether derivations are being recorded. See [`ProofMode`].
    pub proof_mode: ProofMode,
    renamed: Vec<Option<Renamed>>,
    /// Rules whose body is entirely extensional: evaluated once per stratum.
    pub(crate) static_done: Vec<bool>,
    /// New facts since the last round, per predicate.
    pub(crate) delta: Vec<Vec<TermId>>,
    /// Snapshot of the delta for the round in progress, per predicate.
    pub(crate) work: Vec<Vec<TermId>>,
    /// Join backtracking stacks, reused to keep the join allocation-free.
    pub(crate) jc: Vec<usize>,
    pub(crate) jm: Vec<usize>,
    /// Diagnostic only: tuples examined by (rule, body position) as
    /// (bound, unbound). Never cleared per eval; read it off a fresh solver
    /// per measurement (ROADMAP I1). Not part of `Stats` because it is keyed,
    /// not scalar.
    pub(crate) scan_attr: FxHashMap<(RuleId, usize), (u64, u64)>,
    /// Rules bucketed by head predicate, for goal-directed resolution.
    pub rules_by_pred: Vec<Vec<RuleId>>,
}

impl Solver {
    pub fn new(prog: Program) -> Self {
        let n = prog.rules.len();
        let np = prog.num_preds();
        let mut rules_by_pred: Vec<Vec<RuleId>> = vec![Vec::new(); np];
        for r in &prog.rules {
            let h = prog.store.sym(r.head) as usize;
            if rules_by_pred.len() <= h {
                rules_by_pred.resize(h + 1, Vec::new());
            }
            rules_by_pred[h].push(r.id);
        }
        Solver {
            prog,
            subst: Subst::new(),
            db: Db::new(),
            derivs: Vec::new(),
            deriv_of: FxHashMap::default(),
            stats: Stats::default(),
            proof_mode: ProofMode::Full,
            renamed: (0..n).map(|_| None).collect(),
            static_done: vec![false; n],
            delta: vec![Vec::new(); np],
            work: vec![Vec::new(); np],
            jc: Vec::new(),
            jm: Vec::new(),
            scan_attr: FxHashMap::default(),
            rules_by_pred,
        }
    }

    /// Stop recording derivations. Existing derivations are kept, so this must
    /// be called before solving to have any memory effect.
    pub fn set_proof_mode(&mut self, m: ProofMode) {
        self.proof_mode = m;
    }

    // ---- rule renaming ----------------------------------------------------

    /// Build the once-and-reused fresh-variable copy of a rule.
    pub fn ensure_renamed(&mut self, rule: RuleId) {
        if self.renamed[rule as usize].is_some() {
            return;
        }
        let r = self.prog.rules[rule as usize].clone();
        let mut env: FxHashMap<u32, TermId> =
            FxHashMap::with_capacity_and_hasher(r.local_vars.len(), Default::default());
        let mut map = Vec::with_capacity(r.local_vars.len());
        for &v in &r.local_vars {
            let (g, _) = self.prog.store.fresh_var();
            env.insert(v, g);
            map.push((v, g));
        }
        let head = self.prog.store.rename(r.head, &env, 0);
        let mut body = Vec::with_capacity(r.body.len());
        for l in &r.body {
            body.push(Literal {
                pos: l.pos,
                atom: self.prog.store.rename(l.atom, &env, 0),
            });
        }
        self.renamed[rule as usize] = Some(Renamed { head, body, map });
    }

    #[inline]
    pub fn ren_head(&self, r: RuleId) -> TermId {
        self.renamed[r as usize]
            .as_ref()
            .expect("rule not renamed")
            .head
    }
    #[inline]
    pub fn ren_lit(&self, r: RuleId, i: usize) -> Literal {
        self.renamed[r as usize]
            .as_ref()
            .expect("rule not renamed")
            .body[i]
    }
    #[inline]
    pub fn ren_len(&self, r: RuleId) -> usize {
        self.renamed[r as usize]
            .as_ref()
            .expect("rule not renamed")
            .body
            .len()
    }
    #[inline]
    pub fn ren_map_at(&self, r: RuleId, i: usize) -> (u32, TermId) {
        self.renamed[r as usize]
            .as_ref()
            .expect("rule not renamed")
            .map[i]
    }

    // ---- database ---------------------------------------------------------

    /// Assert every empty-body rule as a seed fact.
    pub fn seed_facts(&mut self) {
        for i in 0..self.prog.rules.len() {
            let head = self.prog.rules[i].head;
            if self.prog.rules[i].body.is_empty() && !self.prog.store.contains_var(head) {
                self.db.insert(&self.prog.store, head, true);
            }
        }
    }

    /// Order-independent fingerprint of the whole IDB closure.
    ///
    /// Additive rather than sequential, so the value cannot depend on iteration
    /// order anywhere. This is what a negative answer's certificate commits to.
    pub fn closure_hash(&self) -> u64 {
        let mut acc: u64 = 0;
        for (p, list) in self.db.by_pred.iter().enumerate() {
            if self.prog.pred_idb.get(p).copied().unwrap_or(false) {
                for &t in list {
                    acc = acc.wrapping_add(crate::hash::mix(0xC0_FFEE, t as u64));
                }
            }
        }
        acc
    }

    pub fn idb_fact_count(&self) -> u64 {
        let mut n = 0u64;
        for (p, list) in self.db.by_pred.iter().enumerate() {
            if self.prog.pred_idb.get(p).copied().unwrap_or(false) {
                n += list.len() as u64;
            }
        }
        n
    }

    // ---- checking ---------------------------------------------------------

    /// Strong check: re-derive the goal from program facts and rules alone.
    ///
    /// A proof carrying a saturation certificate (a `Refuted` outcome) is
    /// checked by recomputing the closure from scratch and comparing
    /// fingerprints (KNOWN_LIMITATIONS A3). Recomputation is a full re-solve,
    /// so verification costs a bounded multiple of solve time, not a constant.
    pub fn verify(&self, proof: &Proof) -> Result<(), CheckErr> {
        if let Some(recorded) = &proof.saturation {
            let recomputed = recompute_saturation(&self.prog)
                .map_err(|_| CheckErr::Unsupported { atom: proof.goal })?;
            return check::verify_saturation(recorded, &recomputed);
        }
        check::verify(&self.prog, &self.db, &self.derivs, &self.deriv_of, proof)
    }

    /// Cheap check: goal is in the fact database. Trusts the forward chainer.
    pub fn verify_shallow(&self, proof: &Proof) -> Result<(), CheckErr> {
        check::verify_shallow(&self.db, proof)
    }

    pub fn proof_size(&self, proof: &Proof) -> usize {
        check::proof_size(&self.derivs, &self.deriv_of, proof.goal)
    }

    pub fn derivations_for(&self, proof: &Proof) -> Vec<DerivId> {
        check::derivations_for(&self.derivs, &self.deriv_of, proof.goal)
    }

    /// Tuples examined by (rule, body position) as (bound, unbound),
    /// sorted by unbound descending. Diagnostic surface for ROADMAP I1.
    pub fn scan_attribution(&self) -> Vec<(RuleId, usize, u64, u64)> {
        let mut v: Vec<(RuleId, usize, u64, u64)> = self
            .scan_attr
            .iter()
            .map(|(&(r, i), &(b, u))| (r, i, b, u))
            .collect();
        v.sort_by_key(|x| std::cmp::Reverse(x.3));
        v
    }

    /// Every atom in the database for a predicate, for inspection and tests.
    pub fn facts_of(&self, pred: u32) -> Vec<TermId> {
        self.db
            .by_pred
            .get(pred as usize)
            .cloned()
            .unwrap_or_default()
    }

    pub fn fact_count(&self, pred: u32) -> usize {
        self.db.count(pred)
    }

    /// Is `t` a valid node id in this program's arena?
    ///
    /// `TermId` is a `u32` index into `Program::store`. Nothing stops a caller
    /// passing an id produced by a *different* `Program` -- building the goal in
    /// a separate `exterior::parse` call is an easy mistake, and it produced
    /// index-out-of-bounds panics in the test suite rather than a diagnostic.
    #[inline]
    pub fn goal_in_range(&self, t: TermId) -> bool {
        (t as usize) < self.prog.store.node_count()
            && self.prog.store.kind(t) == crate::term::T_ATOM
    }

    /// Clear the database and derivation log, keeping the program. Used to run
    /// a second independent experiment on the same program.
    pub fn reset_db(&mut self) {
        self.db = Db::new();
        self.derivs.clear();
        self.deriv_of.clear();
        self.stats = Stats::default();
        self.subst.clear(self.prog.store.node_count());
        for d in self.static_done.iter_mut() {
            *d = false;
        }
        self.seed_facts();
    }
}

/// Result of a `prove`/`refute` call.
pub struct Outcome {
    pub status: Status,
    pub proof: Option<Proof>,
    pub stats: Stats,
    /// Set when the search was inconclusive: which budget stopped it.
    pub reason: Option<Exhausted>,
    /// Human-readable notes, e.g. that a program needed backward resolution
    /// because a head contains function symbols.
    pub notes: Vec<String>,
}

impl Outcome {
    pub fn inconclusive(status: Status, reason: Exhausted, stats: Stats) -> Self {
        Outcome {
            status,
            proof: None,
            stats,
            reason: Some(reason),
            notes: Vec::new(),
        }
    }
    pub fn note(mut self, n: impl Into<String>) -> Self {
        self.notes.push(n.into());
        self
    }
    pub fn definite(status: Status, proof: Option<Proof>, stats: Stats) -> Self {
        Outcome {
            status,
            proof,
            stats,
            reason: None,
            notes: Vec::new(),
        }
    }
}

#[derive(Clone)]
pub struct Answer {
    pub subst: Vec<(TermId, TermId)>,
    pub proof: Proof,
}

pub struct QueryOutcome {
    pub status: Status,
    pub answers: Vec<Answer>,
    pub stats: Stats,
    pub reason: Option<Exhausted>,
    /// Closure certificate, present iff bottom-up saturation ran to completion.
    /// A `Refuted` status without one would be an unbacked claim, so the two
    /// always travel together.
    pub saturation: Option<Saturation>,
}

impl QueryOutcome {
    pub fn inconclusive(status: Status, reason: Exhausted, stats: Stats) -> Self {
        QueryOutcome {
            status,
            answers: Vec::new(),
            stats,
            reason: Some(reason),
            saturation: None,
        }
    }
}

/// Re-run saturation from scratch on a clone of the solver. Used to verify a
/// negative answer's certificate without disturbing the original.
pub fn recompute_saturation(prog: &Program) -> Result<Saturation, Exhausted> {
    let mut s = Solver::new(prog.clone());
    s.seed_facts();
    let mut b = Budget::unlimited();
    s.saturate(&mut b)
}
