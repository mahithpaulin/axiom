//! Theory benchmarks: small RDL/UF problems through the DPLL(T) driver at a
//! fixed step budget, with driver counters alongside the timings. Labels and
//! certificates are asserted in `tests/theory.rs`, not here; this measures
//! cost. Run with `cargo bench --bench theory`.

use axiom::bench::Bench;
use axiom::theory::{
    verify_theory_sat, verify_theory_unsat, Diff, TheoryAtom, TheoryDriver, TheoryOutcome,
};
use axiom::{Budget, Builder, TermId};

fn consts(b: &mut Builder, prefix: &str, n: usize) -> Vec<TermId> {
    (0..n)
        .map(|i| b.constant(&format!("{prefix}{i}")))
        .collect()
}

fn main() {
    let mut b = Bench::new("axiom -- theories through the DPLL(T) driver");
    b.note("single-threaded; work bounded by deterministic step budgets");
    b.note("labels and certificates asserted in tests/theory.rs");

    // Unsat: 50 unit-time steps with an impossible deadline.
    b.run_once("rdl_chain_unsat", |_| {
        let mut bd = Builder::new();
        let xs = consts(&mut bd, "x", 51);
        let mut d = TheoryDriver::new();
        let mut vs = Vec::new();
        for i in 0..50 {
            let v = d
                .theory_var(
                    &bd.store,
                    TheoryAtom::Rdl(Diff {
                        x: xs[i],
                        y: xs[i + 1],
                        c: -1,
                    }),
                )
                .unwrap();
            d.add_clause(&[v as i32 + 1]);
            vs.push(v);
        }
        let vd = d
            .theory_var(
                &bd.store,
                TheoryAtom::Rdl(Diff {
                    x: xs[50],
                    y: xs[0],
                    c: 49,
                }),
            )
            .unwrap();
        d.add_clause(&[vd as i32 + 1]);
        vs.push(vd);
        let mut budget = Budget::steps(100_000_000);
        match d.solve(&bd.store, &bd.symbols, &mut budget) {
            Ok(TheoryOutcome::Unsat { sat, theory }) => {
                let input: Vec<Vec<i32>> =
                    vs.iter().map(|&v| vec![v as i32 + 1]).collect();
                assert!(verify_theory_unsat(&input, &sat, &theory).is_ok());
                let st = d.stats();
                assert!(st.theory_conflicts > 0);
                st.theory_conflicts + st.lemmas
            }
            Ok(_) => panic!("rdl chain with deadline must be unsat"),
            Err(_) => 0,
        }
    });

    // Sat: the same steps without the deadline; model re-checks.
    b.run_once("rdl_chain_sat", |_| {
        let mut bd = Builder::new();
        let xs = consts(&mut bd, "x", 51);
        let mut d = TheoryDriver::new();
        for i in 0..50 {
            let v = d
                .theory_var(
                    &bd.store,
                    TheoryAtom::Rdl(Diff {
                        x: xs[i],
                        y: xs[i + 1],
                        c: -1,
                    }),
                )
                .unwrap();
            d.add_clause(&[v as i32 + 1]);
        }
        let mut budget = Budget::steps(100_000_000);
        match d.solve(&bd.store, &bd.symbols, &mut budget) {
            Ok(TheoryOutcome::Sat { model, theory }) => {
                assert!(verify_theory_sat(&model, &theory));
                1
            }
            Ok(_) => panic!("steps alone are satisfiable"),
            Err(_) => 0,
        }
    });

    // UF: a 30-link congruence chain, asserted links, propagated conclusion.
    b.run_once("uf_cong_propagate", |_| {
        let mut bd = Builder::new();
        let xs = consts(&mut bd, "a", 31);
        let f = bd.symbols.func("f", 1);
        let mut d = TheoryDriver::new();
        for i in 0..30 {
            let v = d
                .theory_var(&bd.store, TheoryAtom::Eq(xs[i], xs[i + 1]))
                .unwrap();
            d.add_clause(&[v as i32 + 1]);
        }
        let (mut fa, mut fb) = (xs[0], xs[30]);
        for _ in 0..5 {
            fa = bd.store.func(f, &[fa]);
            fb = bd.store.func(f, &[fb]);
        }
        let vq = d.theory_var(&bd.store, TheoryAtom::Eq(fa, fb)).unwrap();
        let mut budget = Budget::steps(100_000_000);
        match d.solve(&bd.store, &bd.symbols, &mut budget) {
            Ok(TheoryOutcome::Sat { model, theory }) => {
                assert!(verify_theory_sat(&model, &theory));
                assert_eq!(model[vq as usize], 1, "must propagate, not decide");
                d.stats().propagations
            }
            Ok(_) => panic!("must be sat"),
            Err(_) => 0,
        }
    });

    b.report();
}
