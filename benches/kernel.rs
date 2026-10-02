//! The Stage-1 benchmark suite.
//!
//! Run with `cargo bench --bench kernel`, or `cargo bench --bench kernel -- quick`
//! for the fast subset.
//!
//! ## What each benchmark is testing
//!
//! | Benchmark | Hypothesis under test |
//! |---|---|
//! | `hash_cons_*` | Interning is O(1) with structural sharing; duplicates allocate nothing |
//! | `unify_pairs` | Union-find unification sustains millions of unifications/second |
//! | `occurs_check` | The occurs check is not the dominant cost on realistic terms |
//! | `index_selectivity` | The first-argument index examines far fewer tuples than a scan |
//! | `semi_naive_vs_fixpoint[A\|B]` | Semi-naive evaluation is asymptotically better than naive fixpoint |
//! | `tc_path_n*` | Transitive closure on a path graph is linear in the number of pairs |
//! | `tc_random_n2000` | The join degrades gracefully on non-path graphs |
//! | `proof_check_strong` | Independent verification costs a bounded multiple of solve time |
//! | `parse_program` | The exterior compiles rather than interprets |
//! | `end_to_end_tc_prove` | The whole pipeline, problem to verified proof |
//!
//! Work counters (`candidates`, `derivations`, `rounds`) are deterministic and
//! are printed alongside the timings. An algorithmic change shows up there
//! first; a constant-factor change shows up only in the time columns.

use axiom::bench::{allocated_bytes, peak_rss_kb, rss_kb, Bench, Rng};
use axiom::{exterior, Budget, Builder, Db, Literal, Program, Solver, Status, TermId};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let quick = args.iter().any(|a| a == "quick");

    let mut b = Bench::new("axiom -- Stage 1 kernel benchmarks");
    b.note("single-threaded, one core; wall and CPU time reported separately");
    b.note("work bounded by deterministic step budgets; time measured, never used as a limit");
    b.note("allocator: counting global allocator over std::alloc::System");

    representation(&mut b, quick);
    unification(&mut b, quick);
    indexing(&mut b, quick);
    algorithms(&mut b, quick);
    checking(&mut b, quick);
    exterior_and_end_to_end(&mut b, quick);

    b.report();
    scaling_table(quick);
}

// ---- representation ------------------------------------------------------

fn representation(b: &mut Bench, quick: bool) {
    b.note("");
    b.note("-- representation --");

    // H: interning a term is O(arity) and duplicate interning allocates nothing.
    b.run_once("hash_cons_1000_terms", |_| {
        let mut s = Builder::new();
        let f2 = s.symbols.func("f", 2);
        let g1 = s.symbols.func("g", 1);
        let mut ts = axiom::TermStore::new();
        let a = ts.constant(s.symbols.constant("a"));
        let c = ts.constant(s.symbols.constant("b"));
        let mut built = 0u64;
        for i in 0..1000u32 {
            let k = ts.constant(s.symbols.constant(&format!("k{i}")));
            let y = ts.func(f2, &[k, c]);
            let z = ts.func(g1, &[y]);
            let w = ts.func(f2, &[a, z]);
            built += 1;
            std::hint::black_box(w);
        }
        ts.assert_no_dead_children();
        assert_eq!(
            ts.node_count(),
            built as usize * 4 + 3,
            "no duplicate nodes"
        );

        // Same terms again: every intern must hit the existing node.
        let before_nodes = ts.node_count();
        let before_bytes = allocated_bytes();
        let mut dups = 0u64;
        for i in 0..1000u32 {
            let k = ts.constant(s.symbols.constant(&format!("k{i}")));
            let y = ts.func(f2, &[k, c]);
            let z = ts.func(g1, &[y]);
            let w = ts.func(f2, &[a, z]);
            dups += 1;
            std::hint::black_box(w);
        }
        assert_eq!(
            ts.node_count(),
            before_nodes,
            "duplicates must not grow the arena"
        );
        assert_eq!(
            allocated_bytes(),
            before_bytes,
            "duplicate interning must not allocate"
        );
        built
    });

    // Structural sharing across rules: the same subterm is one node.
    b.run_once("hash_cons_sharing", |_| {
        let mut s = Builder::new();
        let f2 = s.symbols.func("f", 2);
        let mut ts = axiom::TermStore::new();
        let a = ts.constant(s.symbols.constant("a"));
        let bb = ts.constant(s.symbols.constant("b"));
        let shared = ts.func(f2, &[a, bb]);
        let g = s.symbols.func("g", 1);
        let mut n = 0u64;
        for _ in 0..1000 {
            // 1000 distinct wrappers over one shared subterm.
            let w = ts.func(g, &[shared]);
            n += 1;
            std::hint::black_box(w);
        }
        n
    });

    if quick {
        return;
    }

    // Deep terms: walking and resolving must not touch the native stack.
    b.run_once("deep_term_walk_100k", |_| {
        let mut s = Builder::new();
        let cons = s.symbols.func("cons", 2);
        let nil = s.symbols.constant("nil");
        let mut ts = axiom::TermStore::new();
        let n = ts.constant(nil);
        let mut t = n;
        for _ in 0..100_000 {
            t = ts.func(cons, &[n, t]);
        }
        let mut count = 0u64;
        ts.walk(t, &mut |_| count += 1);
        count
    });
}

// ---- unification ---------------------------------------------------------

fn unification(b: &mut Bench, quick: bool) {
    b.note("");
    b.note("-- unification --");

    let mut prog = term_program(4000, 0x5EED);
    // Build the pattern once, outside the timed region: the closure captures
    // `prog` immutably and cannot intern new nodes.
    let pat_pred = prog.symbols.predicate("t", 1);
    let px = prog.store.fresh_var().0;
    let py = prog.store.fresh_var().0;
    let pat2 = prog.store.atom(pat_pred, &[px, py]);

    b.run("unify_ground_pairs", 4000, |_| {
        let mut sub = axiom::Subst::new();
        let heads: Vec<TermId> = prog.rules.iter().map(|r| r.head).collect();
        let mut ok = 0u64;
        for i in 0..heads.len() {
            let a = heads[i];
            let c = heads[(i + 13) % heads.len()];
            if sub.unify(&prog.store, a, c).is_ok() {
                ok += 1;
            }
            sub.undo_to(0);
        }
        ok
    });

    // Matching a variable-bearing pattern against a ground tuple is the hot
    // path in forward chaining, so it is measured on its own.
    b.run("match_pattern_vs_fact", 4000, |_| {
        let mut sub = axiom::Subst::new();
        let mut ok = 0u64;
        for r in &prog.rules {
            if sub.match_into(&prog.store, pat2, r.head).is_ok() {
                ok += 1;
            }
            sub.undo_to(0);
        }
        ok
    });

    // H: the occurs check must not dominate on realistic terms.
    b.run("occurs_check_cost", 4000, |_| {
        let mut sub = axiom::Subst::new();
        let mut n = 0u64;
        for r in &prog.rules {
            if sub.occurs(&prog.store, px as u32, r.head) {
                n += 1;
            }
            sub.undo_to(0);
        }
        n
    });

    if quick {
        return;
    }

    // Wide terms: a single literal with many arguments.
    b.run_once("unify_wide_terms", |_| {
        let mut s = Builder::new();
        let wide = s.symbols.func("w", 64);
        let mut ts = axiom::TermStore::new();
        let mut args = Vec::new();
        for i in 0..64 {
            args.push(ts.constant(s.symbols.constant(&format!("c{i}"))));
        }
        let a = ts.func(wide, &args);
        let mut args2 = Vec::new();
        for i in 0..64 {
            args2.push(ts.constant(s.symbols.constant(&format!("c{}", 63 - i))));
        }
        let bb = ts.func(wide, &args2);
        let mut sub = axiom::Subst::new();
        let mut iters = 0u64;
        for _ in 0..10_000 {
            if sub.unify(&ts, a, bb).is_err() {
                break;
            }
            sub.undo_to(0);
            iters += 1;
        }
        iters
    });
}

// ---- indexing ------------------------------------------------------------

fn indexing(b: &mut Bench, _quick: bool) {
    b.note("");
    b.note("-- indexing --");

    // H1: a first-argument index examines far fewer tuples than a full scan.
    // H2: the ratio is roughly the average degree of the relation.
    const N: usize = 50_000;
    const DISTINCT: usize = 500;
    let (prog, pred) = rel_program(N, DISTINCT, 7);
    let mut db = Db::new();
    for r in &prog.rules {
        db.insert(&prog.store, r.head, true);
    }
    let keys: Vec<TermId> = prog
        .rules
        .iter()
        .map(|r| prog.store.child(r.head, 0))
        .collect();

    let scan_total: usize = (0..keys.len())
        .map(|_| db.candidates(pred, None).len())
        .sum();
    let index_total: usize = (0..keys.len())
        .map(|i| db.candidates(pred, Some(keys[i])).len())
        .sum();

    println!("\n  index_selectivity: {N} tuples, {DISTINCT} distinct first arguments");
    println!("    scan   examines {scan_total} tuples total");
    println!("    index  examines {index_total} tuples total");
    println!(
        "    ratio  {:.2}x fewer (average degree {:.1})",
        scan_total as f64 / index_total.max(1) as f64,
        scan_total as f64 / keys.len() as f64
    );

    b.run("db_index_lookup", 50_000, |_| {
        let mut n = 0u64;
        for i in 0..keys.len() {
            n += db.candidates(pred, Some(keys[i])).len() as u64;
        }
        n
    });

    b.run("db_scan_lookup", 50_000, |_| {
        let mut n = 0u64;
        for _ in 0..keys.len() {
            n += db.candidates(pred, None).len() as u64;
        }
        n
    });
}

// ---- algorithms ----------------------------------------------------------

fn algorithms(b: &mut Bench, quick: bool) {
    b.note("");
    b.note("-- inference algorithms --");

    // A: semi-naive. B: naive fixpoint. Same program, same answer.
    b.compare("semi_naive_vs_fixpoint_n600", 3, |mode| {
        let prog = path_graph(600);
        let mut s = Solver::new(prog);
        s.seed_facts();
        let mut budget = Budget::steps(200_000_000);
        let sat = if mode == 0 {
            s.saturate(&mut budget)
        } else {
            s.saturate_naive(&mut budget)
        };
        let n = sat.map(|x| x.idb_facts).unwrap_or(0);
        std::hint::black_box(&s);
        n
    });

    let sizes: &[usize] = if quick {
        &[200, 1_000]
    } else {
        &[200, 1_000, 5_000, 20_000]
    };
    for n in sizes {
        b.run_once(&format!("tc_path_n{n}"), |_| {
            let prog = path_graph(*n);
            let mut s = Solver::new(prog);
            let mut budget = Budget::steps(4_000_000_000);
            match s.least_model(&mut budget) {
                Ok(sat) => sat.idb_facts,
                Err(_) => 0,
            }
        });
    }

    b.run_once("tc_random_n3000", |_| {
        let prog = random_graph(3000, 10, 11);
        let mut s = Solver::new(prog);
        let mut budget = Budget::steps(4_000_000_000);
        match s.least_model(&mut budget) {
            Ok(sat) => sat.idb_facts,
            Err(_) => 0,
        }
    });

    // Stratified negation: the extra stratum must not cost much.
    b.run_once("stratified_negation_5000", |_| {
        let mut bld = Builder::new();
        for i in 0..5_000 {
            let x = bld.constant(&format!("n{i}"));
            let h = bld.atom("base", 1, &[x]);
            bld.fact(h);
        }
        for i in 0..5_000 {
            let x = bld.constant(&format!("n{i}"));
            let h = bld.atom("blocked", 1, &[x]);
            bld.fact(h);
        }
        let x = bld.var("X");
        let h = bld.atom("safe", 1, &[x]);
        let l1 = bld.pos("base", 1, &[x]);
        let blocked = bld.atom("blocked", 1, &[]);
        let _ = blocked;
        // `not blocked(X)` reuses the same variable slot.
        let x2 = bld.var("X");
        let l2 = bld.neg("blocked", 1, &[x2]);
        bld.rule(h, vec![l1, l2]);
        let prog = bld.build().unwrap();
        let mut s = Solver::new(prog);
        let mut budget = Budget::steps(100_000_000);
        match s.least_model(&mut budget) {
            Ok(sat) => sat.idb_facts,
            Err(_) => 0,
        }
    });
}

// ---- checking ------------------------------------------------------------

fn checking(b: &mut Bench, quick: bool) {
    b.note("");
    b.note("-- proof checking --");

    let (prog, goal) = tc_program(if quick { 100 } else { 400 });
    let mut s = Solver::new(prog);
    s.seed_facts();
    let mut budget = Budget::steps(100_000_000);
    s.saturate(&mut budget).ok();
    let proof = axiom::Proof {
        goal,
        root: s.deriv_of.get(&goal).copied(),
        ..Default::default()
    };
    let size = s.proof_size(&proof);
    println!("\n  proof_check_strong: goal proof contains {size} derivations");
    println!("    verify() ok = {}", s.verify(&proof).is_ok());

    b.run("proof_verify_strong", 200, |_| {
        if s.verify(&proof).is_ok() {
            1
        } else {
            0
        }
    });
    b.run("proof_verify_shallow", 200, |_| {
        if s.verify_shallow(&proof).is_ok() {
            1
        } else {
            0
        }
    });
}

// ---- exterior and end to end --------------------------------------------

fn exterior_and_end_to_end(b: &mut Bench, quick: bool) {
    b.note("");
    b.note("-- exterior and end to end --");

    let mut src = String::new();
    for i in 0..if quick { 100 } else { 800 } {
        src.push_str(&format!("edge(n{i},n{}).\n", i + 1));
    }
    src.push_str("path(X, Y) :- edge(X, Y).\npath(X, Z) :- path(X, Y), edge(Y, Z).\n");

    b.run("parse_program", 20, |_| match exterior::parse(&src) {
        Ok(p) => p.program.rules.len() as u64,
        Err(_) => 0,
    });

    let (prog, goal) = tc_program(if quick { 100 } else { 300 });
    b.run("end_to_end_prove", 50, |_| {
        let mut s = Solver::new(prog.clone());
        let mut budget = Budget::steps(100_000_000);
        let out = s.prove(goal, &mut budget);
        if out.status == Status::Proved {
            if let Some(p) = &out.proof {
                std::hint::black_box(s.verify(p).is_ok());
            }
            1
        } else {
            0
        }
    });
}

// ---- scaling table -------------------------------------------------------

fn scaling_table(quick: bool) {
    println!("\n{}", "=".repeat(78));
    println!("scaling: transitive closure on a path graph (semi-naive)");
    println!("{}", "=".repeat(78));
    println!(
        "{:>8}  {:>12}  {:>10}  {:>12}  {:>10}  {:>12}  {:>12}",
        "n", "idb facts", "wall ms", "us/fact", "rss kB", "bytes/fact", "candidates"
    );
    let sizes: &[usize] = if quick {
        &[1_000, 5_000]
    } else {
        &[500, 1_000, 2_000, 5_000, 10_000, 20_000]
    };
    for n in sizes {
        let prog = path_graph(*n);
        let mut s = Solver::new(prog);
        let mut budget = Budget::steps(8_000_000_000);
        let bytes_before = s.prog.payload_bytes();
        let t0 = std::time::Instant::now();
        let sat = s.least_model(&mut budget);
        let ms = t0.elapsed().as_secs_f64() * 1000.0;
        let facts = sat.map(|x| x.idb_facts).unwrap_or(0);
        let us = if facts > 0 {
            ms * 1000.0 / facts as f64
        } else {
            0.0
        };
        let bytes = s.prog.payload_bytes().saturating_sub(bytes_before);
        let per_fact = if facts > 0 { bytes / facts as usize } else { 0 };
        println!(
            "{:>8}  {:>12}  {:>10.2}  {:>12.3}  {:>10}  {:>12}  {:>12}",
            n,
            facts,
            ms,
            us,
            rss_kb(),
            per_fact,
            s.stats.candidates
        );
        std::hint::black_box(peak_rss_kb());
    }
}

// ---- programs ------------------------------------------------------------

fn path_graph(n: usize) -> Program {
    let mut b = Builder::new();
    let names: Vec<String> = (0..=n).map(|i| format!("n{i}")).collect();
    for i in 0..n {
        let x = b.constant(&names[i]);
        let y = b.constant(&names[i + 1]);
        let h = b.atom("edge", 2, &[x, y]);
        b.fact(h);
    }
    add_tc_rules(&mut b);
    b.build().unwrap()
}

fn add_tc_rules(b: &mut Builder) {
    let x = b.var("X");
    let y = b.var("Y");
    let z = b.var("Z");
    let h1 = b.atom("path", 2, &[x, y]);
    let l1 = b.pos("edge", 2, &[x, y]);
    b.rule(h1, vec![l1]);
    let h2 = b.atom("path", 2, &[x, z]);
    let p1 = b.pos("path", 2, &[x, y]);
    let e1 = b.pos("edge", 2, &[y, z]);
    b.rule(h2, vec![p1, e1]);
}

fn random_graph(n: usize, degree: usize, seed: u64) -> Program {
    let mut b = Builder::new();
    let mut rng = Rng::new(seed);
    let names: Vec<String> = (0..n).map(|i| format!("n{i}")).collect();
    for i in 0..n {
        for _ in 0..degree {
            let j = rng.below(n as u64) as usize;
            let x = b.constant(&names[i]);
            let y = b.constant(&names[j]);
            let h = b.atom("edge", 2, &[x, y]);
            b.fact(h);
        }
    }
    add_tc_rules(&mut b);
    b.build().unwrap()
}

fn tc_program(n: usize) -> (Program, TermId) {
    let mut b = Builder::new();
    for i in 0..n {
        let x = b.constant(&format!("n{i}"));
        let y = b.constant(&format!("n{}", i + 1));
        let h = b.atom("edge", 2, &[x, y]);
        b.fact(h);
    }
    add_tc_rules(&mut b);
    let goal = b.goal_n("path", &[&format!("n0"), &format!("n{n}")]);
    let prog = b.build().unwrap();
    (prog, goal)
}

/// `n` ground facts whose arguments are random shallow terms.
fn term_program(n: usize, seed: u64) -> Program {
    let mut b = Builder::new();
    let mut rng = Rng::new(seed);
    for _ in 0..n {
        let t = random_term(&mut b, &mut rng, 0);
        let h = b.atom("t", 1, &[t]);
        b.fact(h);
    }
    b.build().unwrap()
}

fn random_term(b: &mut Builder, rng: &mut Rng, depth: usize) -> TermId {
    if depth >= 2 {
        return b.constant(&format!("c{}", rng.below(16)));
    }
    match rng.below(4) {
        0 => b.constant(&format!("c{}", rng.below(16))),
        1 => {
            let a = random_term(b, rng, depth + 1);
            let s = b.symbols.func("f", 1);
            b.store.func(s, &[a])
        }
        2 => {
            let a = random_term(b, rng, depth + 1);
            let c = random_term(b, rng, depth + 1);
            let s = b.symbols.func("g", 2);
            b.store.func(s, &[a, c])
        }
        _ => {
            let a = random_term(b, rng, depth + 1);
            let s = b.symbols.func("h", 1);
            b.store.func(s, &[a])
        }
    }
}

/// A binary relation with `n` tuples over `distinct` first-argument values.
fn rel_program(n: usize, distinct: usize, seed: u64) -> (Program, u32) {
    let mut b = Builder::new();
    let mut rng = Rng::new(seed);
    for i in 0..distinct {
        let x = b.constant(&format!("k{i}"));
        let y = b.constant(&format!("v{i}"));
        let h = b.atom("rel", 2, &[x, y]);
        b.fact(h);
    }
    for _ in 0..n {
        let x = b.constant(&format!("k{}", rng.below(distinct as u64)));
        let y = b.constant(&format!("v{}", rng.below(distinct as u64)));
        let h = b.atom("rel", 2, &[x, y]);
        b.fact(h);
    }
    let pred = b.symbols.predicate("rel", 2);
    let prog = b.build().unwrap();
    (prog, pred)
}

const _: fn() = || {
    // Keep `Literal` referenced so the import documents the rule shape used.
    let _ = Literal::pos(0);
};
