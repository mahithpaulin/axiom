//! Playing full chess games (V2 R6, `Play` over real positions).
//!
//! [`best_move`] picks a move by fixed-depth negamax with alpha-beta,
//! transposition table, MVV-LVA move ordering, and a capture-only
//! quiescence search past the horizon. [`play_game`] strings those moves
//! into complete self-play games with real draw rules (stalemate,
//! insufficient material, fifty moves, threefold repetition).
//!
//! The honesty framing matters: this plays *a* game at an explicit depth
//! with an explicit static evaluation — it does not claim optimal play.
//! Depth, evaluation, and every draw rule are inspectable; anything the
//! search cannot decide is a heuristic value, and anything past the budget
//! is `Err(Exhausted)`.

use crate::budget::Budget;
use crate::chess::{Move, Position, BISHOP, EMPTY, KING, KNIGHT, MATE_SCORE, PAWN, QUEEN, ROOK};
use crate::hash::FxHashMap;
use crate::status::Exhausted;

const QDEPTH_MAX: u32 = 8;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Bound {
    Exact,
    Lower,
    Upper,
}

#[derive(Clone, Copy)]
struct TtEntry {
    depth: u32,
    value: i64,
    bound: Bound,
    best: Move,
}

struct Searcher {
    tt: FxHashMap<u64, TtEntry>,
    nodes: u64,
}

fn piece_value(kind: i8) -> i64 {
    match kind {
        PAWN => 100,
        KNIGHT => 320,
        BISHOP => 330,
        ROOK => 500,
        QUEEN => 900,
        KING => 20_000,
        _ => 0,
    }
}

/// Order key: captures by MVV-LVA, promotions next, quiet last; ties broken
/// by coordinates so the order (and the search) is deterministic.
fn order_key(pos: &Position, m: Move) -> (i64, u8, u8, i8) {
    let target = pos.sq[m.to as usize];
    let attacker = pos.sq[m.from as usize].abs();
    let mut score = 0i64;
    if target != EMPTY {
        score += 10 * piece_value(target.abs()) - piece_value(attacker) / 16;
    } else if pos.ep_square() == Some(m.to) {
        score += 10 * piece_value(PAWN) - piece_value(PAWN) / 16;
    }
    if m.promo != EMPTY {
        score += 9_000 + piece_value(m.promo);
    }
    (-score, m.from, m.to, m.promo)
}

/// Side-to-move perspective evaluation (negamax convention).
fn side_eval(pos: &Position) -> i64 {
    let w = pos.evaluate();
    if pos.white_to_move {
        w
    } else {
        -w
    }
}

fn quiesce(
    s: &mut Searcher,
    pos: &Position,
    mut alpha: i64,
    beta: i64,
    qdepth: u32,
    budget: &mut Budget,
) -> Result<i64, Exhausted> {
    budget.charge(1)?;
    s.nodes += 1;
    let stand = side_eval(pos);
    if stand >= beta {
        return Ok(beta);
    }
    if stand > alpha {
        alpha = stand;
    }
    if qdepth == 0 {
        return Ok(alpha);
    }
    let mut moves = pos.legal_moves();
    moves.retain(|m| {
        pos.sq[m.to as usize] != EMPTY || pos.ep_square() == Some(m.to) || m.promo != EMPTY
    });
    moves.sort_by_key(|m| order_key(pos, *m));
    for m in moves {
        let got = -quiesce(s, &pos.make(m), -beta, -alpha, qdepth - 1, budget)?;
        if got >= beta {
            return Ok(beta);
        }
        if got > alpha {
            alpha = got;
        }
    }
    Ok(alpha)
}

#[allow(clippy::too_many_arguments)]
fn negamax(
    s: &mut Searcher,
    pos: &Position,
    depth: u32,
    mut alpha: i64,
    beta: i64,
    ply: u32,
    budget: &mut Budget,
) -> Result<i64, Exhausted> {
    budget.charge(1)?;
    s.nodes += 1;
    let key = pos.repetition_hash();
    let mut tt_move: Option<Move> = None;
    if let Some(e) = s.tt.get(&key) {
        if e.depth >= depth {
            match e.bound {
                Bound::Exact => return Ok(e.value),
                Bound::Lower => {
                    if e.value >= beta {
                        return Ok(e.value);
                    }
                }
                Bound::Upper => {
                    if e.value <= alpha {
                        return Ok(e.value);
                    }
                }
            }
            tt_move = Some(e.best);
        } else {
            tt_move = Some(e.best);
        }
    }
    let mut moves = pos.legal_moves();
    if moves.is_empty() {
        if pos.in_check(pos.white_to_move) {
            return Ok(-MATE_SCORE + ply as i64);
        }
        return Ok(0);
    }
    if depth == 0 {
        return quiesce(s, pos, alpha, beta, QDEPTH_MAX, budget);
    }
    if let Some(tm) = tt_move {
        if let Some(i) = moves.iter().position(|m| *m == tm) {
            moves.swap(0, i);
            moves[1..].sort_by_key(|m| order_key(pos, *m));
        } else {
            moves.sort_by_key(|m| order_key(pos, *m));
        }
    } else {
        moves.sort_by_key(|m| order_key(pos, *m));
    }
    let alpha0 = alpha;
    let mut best = i64::MIN + 1;
    let mut best_move = moves[0];
    for m in moves {
        let got = -negamax(s, &pos.make(m), depth - 1, -beta, -alpha, ply + 1, budget)?;
        if got > best {
            best = got;
            best_move = m;
        }
        if best > alpha {
            alpha = best;
        }
        if alpha >= beta {
            break;
        }
    }
    let bound = if best <= alpha0 {
        Bound::Upper
    } else if best >= beta {
        Bound::Lower
    } else {
        Bound::Exact
    };
    s.tt.insert(
        key,
        TtEntry {
            depth,
            value: best,
            bound,
            best: best_move,
        },
    );
    Ok(best)
}

/// Best move by fixed-depth search. The value is from the side-to-move
/// perspective: positive favours the mover. Deterministic for fixed depth.
pub fn best_move(
    pos: &Position,
    depth: u32,
    budget: &mut Budget,
) -> Result<(Move, i64), Exhausted> {
    let mut moves = pos.legal_moves();
    if moves.is_empty() {
        return Err(Exhausted::Malformed);
    }
    moves.sort_by_key(|m| order_key(pos, *m));
    let mut s = Searcher {
        tt: FxHashMap::default(),
        nodes: 0,
    };
    let mut best_val = i64::MIN + 1;
    let mut best = moves[0];
    for m in moves {
        let got = -negamax(
            &mut s,
            &pos.make(m),
            depth.saturating_sub(1),
            i64::MIN + 1,
            i64::MAX,
            1,
            budget,
        )?;
        if got > best_val {
            best_val = got;
            best = m;
        }
    }
    Ok((best, best_val))
}

/// How a game ended. `PlyCap` is not a rules draw: the move cap was reached,
/// and the string says so.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum GameEnd {
    WhiteWins,
    BlackWins,
    DrawStalemate,
    DrawMaterial,
    DrawFifty,
    DrawThreefold,
    PlyCap,
}

/// A finished (or capped) self-play game.
#[derive(Clone, Debug)]
pub struct PlayedGame {
    pub moves: Vec<String>,
    pub end: GameEnd,
    pub final_fen: String,
}

/// True when neither side can possibly checkmate: bare kings, or one minor
/// piece at most on the whole board.
pub fn insufficient_material(pos: &Position) -> bool {
    let mut minors = 0;
    for p in pos.sq {
        match p.abs() {
            PAWN | ROOK | QUEEN => return false,
            KNIGHT | BISHOP => minors += 1,
            _ => {}
        }
    }
    minors <= 1
}

/// True when `hash` already appears twice in `history` (so playing it again
/// is the third occurrence).
pub fn threefold_reached(history: &[u64], hash: u64) -> bool {
    history.iter().filter(|h| **h == hash).count() >= 2
}

/// Self-play: White searches at `white_depth`, Black at `black_depth`, up to
/// `max_plies`. Every move is a legal move of the position it is played in;
/// every terminal claim (mate, stalemate, draws) is detected, never assumed.
pub fn play_game(
    from: &Position,
    white_depth: u32,
    black_depth: u32,
    max_plies: u32,
    budget: &mut Budget,
) -> Result<PlayedGame, Exhausted> {
    let mut pos = *from;
    let mut moves = Vec::new();
    let mut history = vec![pos.repetition_hash()];
    loop {
        if pos.is_checkmate() {
            return Ok(PlayedGame {
                moves,
                end: if pos.white_to_move {
                    GameEnd::BlackWins
                } else {
                    GameEnd::WhiteWins
                },
                final_fen: pos.to_fen(),
            });
        }
        if pos.is_stalemate() {
            return Ok(PlayedGame {
                moves,
                end: GameEnd::DrawStalemate,
                final_fen: pos.to_fen(),
            });
        }
        if insufficient_material(&pos) {
            return Ok(PlayedGame {
                moves,
                end: GameEnd::DrawMaterial,
                final_fen: pos.to_fen(),
            });
        }
        if pos.halfmove() >= 100 {
            return Ok(PlayedGame {
                moves,
                end: GameEnd::DrawFifty,
                final_fen: pos.to_fen(),
            });
        }
        if moves.len() as u32 >= max_plies {
            return Ok(PlayedGame {
                moves,
                end: GameEnd::PlyCap,
                final_fen: pos.to_fen(),
            });
        }
        let depth = if pos.white_to_move {
            white_depth
        } else {
            black_depth
        };
        let (m, _) = best_move(&pos, depth.max(1), budget)?;
        pos = pos.make(m);
        moves.push(crate::chess::move_to_string(m));
        if threefold_reached(&history, pos.repetition_hash()) {
            return Ok(PlayedGame {
                moves,
                end: GameEnd::DrawThreefold,
                final_fen: pos.to_fen(),
            });
        }
        history.push(pos.repetition_hash());
    }
}
