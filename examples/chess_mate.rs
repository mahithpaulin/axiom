//! Back-rank mate through the V2 chess layer. Run with `cargo run --example chess_mate`.

use axiom::{alpha_beta, endgame_tree, find_mate_in_one, move_to_string, verify_line};
use axiom::{Budget, Position, Status};

fn main() {
    let pos = Position::from_fen("6k1/5ppp/8/8/8/8/5PPP/4R1K1 w - - 0 1").unwrap();
    let m = find_mate_in_one(&pos).expect("mate in one exists");
    println!("mate in one: {}", move_to_string(m));
    assert!(pos.make(m).is_checkmate());

    let mut budget = Budget::steps(1_000_000);
    let tree = endgame_tree(&pos, 2, &mut budget).expect("within budget");
    let mut budget = Budget::steps(1_000_000);
    let out = alpha_beta(&tree, 0, &mut budget).expect("within budget");
    assert_eq!(out.status, Status::Found);
    assert!(verify_line(&tree, &out.line, out.value));
    println!("alpha-beta: value {} line {:?}", out.value, out.line);
}
