//! SAT core tests: DIMACS parsing, rule grounding, certificates, and the
//! cross-engine differential — the least model and SAT entailment must agree
//! on positive programs (definite Horn: `q` in the least model iff the
//! clauses entail `q` iff clauses + `¬q` are unsatisfiable).

use axiom::sat::{
    ground_positive_program, parse_dimacs, verify_sat, verify_unsat, SatOutcome, SatSolver,
};
use axiom::{exterior, Budget, Solver, Status};
use std::collections::HashMap;

// ---- DIMACS --------------------------------------------------------------

#[test]
fn dimacs_rejects_malformed_input() {
    assert!(parse_dimacs("c no header\n1 0\n").is_err());
    assert!(parse_dimacs("p cnf 1 1\n1\n").is_err()); // unterminated
    assert!(parse_dimacs("p cnf 1 1\n2 0\n").is_err()); // out of range
    assert!(parse_dimacs("p sat 1 1\n1 0\n").is_err()); // bad header
    let (n, cs) = parse_dimacs("c comment\np cnf 2 2\n1 -2 0\n-1 2 0\n").unwrap();
    assert_eq!((n, cs.len()), (2, 2));
}

// ---- grounding ------------------------------------------------------------

#[test]
fn grounding_covers_facts_and_rules() {
    let src = "edge(a,b).\nedge(b,c).\npath(X,Y) :- edge(X,Y).\n";
    let mut parsed = exterior::parse(src).unwrap();
    let g = ground_positive_program(&mut parsed.program);
    assert_eq!((g.skipped_rules, g.skipped_facts), (0, 0));
    // 2 unit clauses + 3x3 ground instances of the rule (X,Y over {a,b,c}).
    assert_eq!(g.clauses.len(), 2 + 9);
    assert!(g.nvars > 0);
}

#[test]
fn grounding_skips_backward_and_negated_rules() {
    let src = "base(a).\nnum(succ(X)) :- base(X).\nsafe(X) :- node(X), not blocked(X).\nnode(a).\n";
    let mut parsed = exterior::parse(src).unwrap();
    let g = ground_positive_program(&mut parsed.program);
    assert_eq!(g.skipped_rules, 2);
}

// ---- certificates ---------------------------------------------------------

fn solve_all(clauses: &[Vec<i32>]) -> SatOutcome {
    let mut s = SatSolver::new();
    for c in clauses {
        s.add_clause(c);
    }
    let mut b = Budget::unlimited();
    s.solve(&mut b).expect("within budget")
}

#[test]
fn frozen_corpus_labels_hold_with_checked_certs() {
    let corpus: &[(&str, bool)] = &[
        (include_str!("../benches/data/sat_trivial.cnf"), true),
        (include_str!("../benches/data/unsat_units.cnf"), false),
        (include_str!("../benches/data/sat_xor2.cnf"), true),
        (include_str!("../benches/data/unsat_xor01.cnf"), false),
        (include_str!("../benches/data/unsat_php32.cnf"), false),
        (include_str!("../benches/data/sat_chain7.cnf"), true),
        (include_str!("../benches/data/unsat_php43.cnf"), false),
        (include_str!("../benches/data/sat_planted50.cnf"), true),
        (include_str!("../benches/data/sat_planted100.cnf"), true),
    ];
    for (src, expect_sat) in corpus {
        let (_, clauses) = parse_dimacs(src).expect("corpus parses");
        match solve_all(&clauses) {
            SatOutcome::Sat { model } => {
                assert!(verify_sat(&clauses, &model), "model must satisfy");
                assert!(*expect_sat, "expected unsat");
            }
            SatOutcome::Unsat { proof } => {
                assert!(verify_unsat(&clauses, &proof).is_ok(), "proof must replay");
                assert!(!expect_sat, "expected sat");
            }
        }
    }
}

// ---- cross-engine agreement -------------------------------------------------

/// For every ground query in `src`: engine `Proved` iff clauses+¬q are unsat
/// (proof replays); engine `Refuted` iff clauses+¬q are sat (model verifies).
/// Instant on these sizes; the biconditional is the differential.
fn check_agreement(src: &str) {
    let mut parsed = exterior::parse(src).unwrap();
    assert!(!parsed.queries.is_empty(), "agreement needs ground queries");
    let g = ground_positive_program(&mut parsed.program);
    assert_eq!((g.skipped_rules, g.skipped_facts), (0, 0));
    let mut atom_var: HashMap<axiom::TermId, usize> = HashMap::new();
    for (i, &t) in g.atoms.iter().enumerate() {
        atom_var.insert(t, i);
    }
    let program = parsed.program;
    let queries = parsed.queries;
    let mut s = Solver::new(program);
    for &goal in &queries {
        let v = *atom_var.get(&goal).expect("ground query in domain") as i32;
        let mut cls = g.clauses.clone();
        cls.push(vec![-(v + 1)]);
        let mut b = Budget::unlimited();
        match s.prove(goal, &mut b) {
            o if o.status == Status::Proved => {
                match solve_all(&cls) {
                    SatOutcome::Unsat { proof } => {
                        assert!(verify_unsat(&cls, &proof).is_ok())
                    }
                    SatOutcome::Sat { .. } => panic!("entailed goal refuted by SAT"),
                }
                let proof = o.proof.expect("proved carries a proof");
                assert!(s.verify(&proof).is_ok());
            }
            o if o.status == Status::Refuted => match solve_all(&cls) {
                SatOutcome::Sat { model } => {
                    assert!(verify_sat(&cls, &model))
                }
                SatOutcome::Unsat { .. } => panic!("omitted goal entailed by SAT"),
            },
            o => panic!("inconclusive {:?} on a positive program", o.status),
        }
    }
}

#[test]
fn engine_and_sat_agree_on_chains() {
    check_agreement(
        "edge(a,b).\nedge(b,c).\nedge(c,d).\n\
         path(X,Y) :- edge(X,Y).\npath(X,Z) :- path(X,Y), edge(Y,Z).\n\
         ?- path(a,d).\n?- path(d,a).\n?- path(a,c).\n",
    );
}

#[test]
fn engine_and_sat_agree_on_joins() {
    check_agreement(
        "e(a,b).\ne(a,c).\ne(b,d).\ne(c,d).\n\
         p(X) :- e(X,_).\nq(X,Y) :- p(X), e(X,Y).\n\
         ?- q(a,b).\n?- q(b,a).\n?- p(d).\n?- q(a,d).\n",
    );
}

#[test]
fn tiny_budget_reports_exhaustion_not_an_answer() {
    let (_, clauses) = parse_dimacs(include_str!("../benches/data/unsat_php43.cnf")).unwrap();
    let mut s = SatSolver::new();
    for c in &clauses {
        s.add_clause(c);
    }
    let mut b = Budget::steps(5);
    match s.solve(&mut b) {
        Err(_) => {}
        Ok(_) => panic!("5 steps cannot decide php43"),
    }
}
