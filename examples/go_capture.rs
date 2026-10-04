//! 5x5 Go capture puzzle through the V2 go layer.
//! Run with `cargo run --example go_capture`.

use axiom::{Budget, Goban, BLACK, WHITE};

fn main() {
    let mut g = Goban::new(5).unwrap();
    g.set(12, WHITE);
    for s in [11, 13, 7] {
        g.set(s, BLACK);
    }
    let mut budget = Budget::steps(10_000);
    let targets = g.capture_in_one(&mut budget).expect("within budget");
    println!("capturing points (side to move is black): {targets:?}");
    assert_eq!(targets, vec![17]);
}
