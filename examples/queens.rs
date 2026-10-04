//! 8-queens through the V2 puzzle layer. Run with `cargo run --example queens`.

use axiom::puzzle::nqueens;
use axiom::{solve_csp, verify_csp, Budget, Status};

fn main() {
    let p = nqueens(8).expect("valid board");
    let mut budget = Budget::steps(50_000_000);
    let out = solve_csp(&p, &mut budget).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert!(verify_csp(&p, &out.assignment));
    for r in 0..8 {
        for c in 0..8 {
            print!(
                "{}",
                if out.assignment[c] as usize == r {
                    "Q "
                } else {
                    ". "
                }
            );
        }
        println!();
    }
}
