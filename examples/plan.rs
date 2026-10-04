//! Plan the stacking domain through the chooser + representation spine.
//! Run with `cargo run --example plan`.

use axiom::{choose, run, stacking_3, Budget, Representation, Status};

fn main() {
    let rep = Representation::States(stacking_3());
    let choice = choose(&rep);
    println!("chooser: {choice:?}");
    let mut budget = Budget::steps(choice.budget_hint);
    let verdict = run(&rep, choice.operation, &mut budget).expect("within budget");
    assert_eq!(verdict.status, Status::Found);
    println!("verdict: {verdict:?}");
}
