//! Solve the classic easy Sudoku through the V2 puzzle layer.
//! Run with `cargo run --example sudoku`.

use axiom::puzzle::sudoku9;
use axiom::{solve_csp, verify_csp, Budget, Status};

fn main() {
    let src = "53..7....6..195....98....6.8...6...34..8.3..17...2...6.6....28....419..5....8..79";
    let p = sudoku9(src).expect("valid puzzle");
    let mut budget = Budget::steps(50_000_000);
    let out = solve_csp(&p, &mut budget).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert!(verify_csp(&p, &out.assignment));
    for (i, v) in out.assignment.iter().enumerate() {
        if i % 9 == 0 {
            println!();
        }
        print!("{v} ");
    }
    println!(
        "\npruned {} values over {} rounds",
        out.stats.pruned, out.stats.rounds
    );
}
