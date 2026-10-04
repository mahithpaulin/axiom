//! A full self-play chess game through the V2 play layer.
//! Run with `cargo run --example chess_play`.

use axiom::{play_game, Budget, Position};

fn main() {
    let mut budget = Budget::steps(500_000_000);
    let game = play_game(&Position::startpos(), 2, 2, 120, &mut budget).expect("within budget");
    for (i, m) in game.moves.iter().enumerate() {
        if i % 2 == 0 {
            print!("{}. ", i / 2 + 1);
        }
        print!("{m} ");
        if i % 2 == 1 {
            println!();
        }
    }
    if game.moves.len() % 2 == 1 {
        println!();
    }
    println!("end: {:?} ({} plies)", game.end, game.moves.len());
    println!("final: {}", game.final_fen);
}
