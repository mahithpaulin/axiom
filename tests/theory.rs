//! DPLL(T) driver tests: boolean abstraction over difference constraints and
//! equalities, with every certificate re-checked — models by re-assertion,
//! unsatisfiability by RUP plus theory-lemma replay.

use axiom::sat::UnsatProof;
use axiom::theory::{
    verify_theory_sat, verify_theory_unsat, Diff, TheoryAtom, TheoryDriver, TheoryOutcome,
    TheoryProof,
};
use axiom::{Budget, Builder, TermId};

fn consts(b: &mut Builder, names: &[&str]) -> Vec<TermId> {
    names.iter().map(|n| b.constant(n)).collect()
}

fn check_unsat(
    sat_input: &[Vec<i32>],
    sat_proof: &UnsatProof,
    theory: &TheoryProof,
) {
    assert!(
        verify_theory_unsat(sat_input, sat_proof, theory).is_ok(),
        "theory unsat proof must verify"
    );
}

#[test]
fn rdl_conflict_is_unsat_with_proof() {
    // x - y <= 0 and y - x <= -1: jointly unsatisfiable.
    let mut b = Builder::new();
    let v = consts(&mut b, &["x", "y"]);
    let (x, y) = (v[0], v[1]);
    let mut d = TheoryDriver::new();
    let v1 = d
        .theory_var(&b.store, TheoryAtom::Rdl(Diff { x, y, c: 0 }))
        .unwrap();
    let v2 = d
        .theory_var(&b.store, TheoryAtom::Rdl(Diff {
            x: y,
            y: x,
            c: -1,
        }))
        .unwrap();
    d.add_clause(&[v1 as i32 + 1]);
    d.add_clause(&[v2 as i32 + 1]);
    let mut budget = Budget::unlimited();
    match d.solve(&b.store, &b.symbols, &mut budget) {
        Ok(TheoryOutcome::Unsat { sat, theory }) => {
            check_unsat(&[[v1 as i32 + 1], [v2 as i32 + 1]], &sat, &theory)
        }
        Ok(TheoryOutcome::Sat { .. }) => panic!("must be unsat"),
        Err(_) => panic!("within budget"),
    }
}

#[test]
fn rdl_chain_is_sat_with_verified_model() {
    // x - y <= 5, y - z <= 2: satisfiable; the model re-checks.
    let mut b = Builder::new();
    let v = consts(&mut b, &["x", "y", "z"]);
    let (x, y, z) = (v[0], v[1], v[2]);
    let mut d = TheoryDriver::new();
    let v1 = d
        .theory_var(&b.store, TheoryAtom::Rdl(Diff { x, y, c: 5 }))
        .unwrap();
    let v2 = d
        .theory_var(&b.store, TheoryAtom::Rdl(Diff {
            x: y,
            y: z,
            c: 2,
        }))
        .unwrap();
    d.add_clause(&[v1 as i32 + 1]);
    d.add_clause(&[v2 as i32 + 1]);
    let mut budget = Budget::unlimited();
    match d.solve(&b.store, &b.symbols, &mut budget) {
        Ok(TheoryOutcome::Sat { model, theory }) => {
            assert!(verify_theory_sat(&model, &theory));
        }
        Ok(_) => panic!("must be sat"),
        Err(_) => panic!("within budget"),
    }
}

#[test]
fn uf_propagates_congruence_through_lemmas() {
    // a ≈ b asserted; f(a) ≈ f(b) is entailed, so the solver must derive it
    // by theory propagation (no decision on it).
    let mut b = Builder::new();
    let v = consts(&mut b, &["a", "c"]);
    let (a, c) = (v[0], v[1]);
    let f = b.symbols.func("f", 1);
    let (fa, fb) = (b.store.func(f, &[a]), b.store.func(f, &[c]));
    let mut d = TheoryDriver::new();
    let v1 = d
        .theory_var(&b.store, TheoryAtom::Eq(a, c))
        .unwrap();
    let v2 = d
        .theory_var(&b.store, TheoryAtom::Eq(fa, fb))
        .unwrap();
    d.add_clause(&[v1 as i32 + 1]);
    // v2 constrained to false would conflict; here it is free to propagate.
    let mut budget = Budget::unlimited();
    match d.solve(&b.store, &b.symbols, &mut budget) {
        Ok(TheoryOutcome::Sat { model, theory }) => {
            assert_eq!(
                model[v2 as usize], 1,
                "entailed equality must propagate, not decide"
            );
            assert!(verify_theory_sat(&model, &theory));
            assert!(d.stats().propagations > 0);
        }
        Ok(_) => panic!("must be sat"),
        Err(_) => panic!("within budget"),
    }
}

#[test]
fn disequality_against_merge_is_unsat() {
    // a ≈ b but a ≠ b: direct UF conflict.
    let mut b = Builder::new();
    let v = consts(&mut b, &["a", "c"]);
    let (a, c) = (v[0], v[1]);
    let mut d = TheoryDriver::new();
    let v1 = d
        .theory_var(&b.store, TheoryAtom::Eq(a, c))
        .unwrap();
    let v2 = d
        .theory_var(&b.store, TheoryAtom::Neq(a, c))
        .unwrap();
    d.add_clause(&[v1 as i32 + 1]);
    d.add_clause(&[v2 as i32 + 1]);
    let mut budget = Budget::unlimited();
    match d.solve(&b.store, &b.symbols, &mut budget) {
        Ok(TheoryOutcome::Unsat { sat, theory }) => {
            check_unsat(&[[v1 as i32 + 1], [v2 as i32 + 1]], &sat, &theory)
        }
        Ok(_) => panic!("must be unsat"),
        Err(_) => panic!("within budget"),
    }
}

#[test]
fn nelson_oppen_exchange_fires() {
    // x - y <= 0, y - x <= 0 entail x ≈ y; x ≠ y then conflicts. Neither
    // theory alone sees it: the equality must cross over.
    let mut b = Builder::new();
    let v = consts(&mut b, &["x", "y"]);
    let (x, y) = (v[0], v[1]);
    let mut d = TheoryDriver::new();
    let v1 = d
        .theory_var(&b.store, TheoryAtom::Rdl(Diff { x, y, c: 0 }))
        .unwrap();
    let v2 = d
        .theory_var(&b.store, TheoryAtom::Rdl(Diff {
            x: y,
            y: x,
            c: 0,
        }))
        .unwrap();
    let v3 = d.theory_var(&b.store, TheoryAtom::Neq(x, y)).unwrap();
    d.add_clause(&[v1 as i32 + 1]);
    d.add_clause(&[v2 as i32 + 1]);
    d.add_clause(&[v3 as i32 + 1]);
    let mut budget = Budget::unlimited();
    match d.solve(&b.store, &b.symbols, &mut budget) {
        Ok(TheoryOutcome::Unsat { sat, theory }) => check_unsat(
            &[[v1 as i32 + 1], [v2 as i32 + 1], [v3 as i32 + 1]],
            &sat,
            &theory,
        ),
        Ok(_) => panic!("must be unsat"),
        Err(_) => panic!("within budget"),
    }
}

#[test]
fn inconsistent_model_does_not_verify() {
    // A model claiming both x - y <= 0 and y - x <= -1 is rejected.
    let mut b = Builder::new();
    let v = consts(&mut b, &["x", "y"]);
    let (x, y) = (v[0], v[1]);
    let mut d = TheoryDriver::new();
    let v1 = d
        .theory_var(&b.store, TheoryAtom::Rdl(Diff { x, y, c: 0 }))
        .unwrap();
    let v2 = d
        .theory_var(&b.store, TheoryAtom::Rdl(Diff {
            x: y,
            y: x,
            c: -1,
        }))
        .unwrap();
    let mut budget = Budget::unlimited();
    // Force both conflicting atoms true so the outcome is unsat.
    d.add_clause(&[v1 as i32 + 1]);
    d.add_clause(&[v2 as i32 + 1]);
    match d.solve(&b.store, &b.symbols, &mut budget) {
        Ok(TheoryOutcome::Unsat { sat, theory }) => {
            check_unsat(&[[v1 as i32 + 1], [v2 as i32 + 1]], &sat, &theory);
            // And a forged all-true model over the same atoms fails:
            let n = (v2 as usize + 1).max(2);
            let mut forged = vec![0i8; n];
            forged[v1 as usize] = 1;
            forged[v2 as usize] = 1;
            assert!(!verify_theory_sat(&forged, &theory));
        }
        Ok(_) => panic!("must be unsat"),
        Err(_) => panic!("within budget"),
    }
}

#[test]
fn predicate_atoms_are_rejected() {
    // Equality over predicate atoms is not a theory term.
    let mut b = Builder::new();
    let x = b.constant("x");
    let p = b.atom("p", 1, &[x]);
    let mut d = TheoryDriver::new();
    assert!(d.theory_var(&b.store, TheoryAtom::Eq(p, x)).is_err());
}
