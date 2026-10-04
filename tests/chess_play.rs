//! Full-game chess: search picks real moves, the loop plays real games.
//! Every terminal claim is detected; every move is replayed for legality.

use axiom::chess_play::{best_move, insufficient_material, play_game, threefold_reached};
use axiom::{chess::MATE_SCORE, Budget, Position};

const BACK_RANK: &str = "6k1/5ppp/8/8/8/8/5PPP/4R1K1 w - - 0 1";

#[test]
fn search_finds_mate_at_depth() {
    let pos = Position::from_fen(BACK_RANK).unwrap();
    let mut budget = Budget::steps(10_000_000);
    let (m, value) = best_move(&pos, 2, &mut budget).expect("within budget");
    assert_eq!(axiom::move_to_string(m), "e1e8");
    assert!(value >= MATE_SCORE - 10);
    assert!(pos.make(m).is_checkmate());
}

#[test]
fn search_is_deterministic() {
    let pos = Position::startpos();
    let mut budget = Budget::steps(50_000_000);
    let first = best_move(&pos, 2, &mut budget).expect("within budget");
    let mut budget = Budget::steps(50_000_000);
    let second = best_move(&pos, 2, &mut budget).expect("within budget");
    assert_eq!(first, second);
    assert!(pos.legal_moves().contains(&first.0));
}

#[test]
fn stalemate_and_material_draws_detected() {
    let stale = Position::from_fen("k7/8/1Q6/8/8/8/8/K7 b - - 0 1").unwrap();
    assert!(stale.is_stalemate());
    assert!(!stale.is_checkmate());
    let kings = Position::from_fen("8/8/8/4k3/8/4K3/8/8 w - - 0 1").unwrap();
    assert!(insufficient_material(&kings));
    assert!(!insufficient_material(&Position::startpos()));
    let minor = Position::from_fen("8/8/8/4k3/8/4KB3/8/8 w - - 0 1").unwrap();
    assert!(insufficient_material(&minor));
}

#[test]
fn fifty_and_ply_cap_end_games_honestly() {
    let old = Position::from_fen("8/8/8/4k3/8/4KR2/8/8 w - - 100 90").unwrap();
    let mut budget = Budget::steps(1_000_000);
    let game = play_game(&old, 1, 1, 200, &mut budget).expect("within budget");
    assert_eq!(game.end, axiom::chess_play::GameEnd::DrawFifty);
    let mut budget = Budget::steps(10_000_000);
    let capped = play_game(&Position::startpos(), 1, 1, 4, &mut budget).expect("within budget");
    assert_eq!(capped.end, axiom::chess_play::GameEnd::PlyCap);
    assert_eq!(capped.moves.len(), 4);
}

#[test]
fn threefold_counter_counts_occurrences() {
    // History holds past hashes; reaching `hash` again when it is already
    // there twice is the third occurrence.
    assert!(!threefold_reached(&[7, 9], 7));
    assert!(!threefold_reached(&[7, 9, 7], 9));
    assert!(threefold_reached(&[7, 9, 7], 7));
    assert!(threefold_reached(&[7, 9, 7, 9, 7], 7));
}

#[test]
fn self_play_terminates_with_legal_moves() {
    let mut budget = Budget::steps(200_000_000);
    let game = play_game(&Position::startpos(), 1, 1, 120, &mut budget).expect("within budget");
    assert!(game.moves.len() <= 120);
    // Replay every move for legality from the start position.
    let mut pos = Position::startpos();
    for text in &game.moves {
        let m = pos.parse_uci(text).expect("every played move is legal");
        pos = pos.make(m);
    }
    assert_eq!(pos.to_fen(), game.final_fen);
    // The recorded end matches the replayed position.
    match game.end {
        axiom::chess_play::GameEnd::WhiteWins => assert!(pos.is_checkmate() && !pos.white_to_move),
        axiom::chess_play::GameEnd::BlackWins => assert!(pos.is_checkmate() && pos.white_to_move),
        axiom::chess_play::GameEnd::DrawStalemate => assert!(pos.is_stalemate()),
        _ => {}
    }
}

#[test]
fn fen_round_trips() {
    for fen in [
        "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1",
        "6k1/5ppp/8/8/8/8/5PPP/4R1K1 w - - 0 1",
        "r1bqkbnr/pppp1ppp/2n5/4p3/4P3/5N2/PPPP1PPP/RNBQKB1R b KQkq - 3 3",
        "r1bqkbnr/ppp2ppp/2np4/4p2Q/2B1P3/8/PPPP1PPP/RNB1K1NR w KQkq e6 0 4",
    ] {
        let pos = Position::from_fen(fen).unwrap();
        assert_eq!(pos.to_fen(), fen, "round trip");
    }
}
