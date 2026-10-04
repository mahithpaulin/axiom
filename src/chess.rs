//! Chess (V2 R6 game adapter, ROADMAP II4/II5).
//!
//! A complete-enough chess engine for endgame tactics and mate search: full
//! legal move generation (including castling and en passant), FEN parsing,
//! check/checkmate/stalemate detection, perft counting, mate-in-1 search,
//! and a bounded explicit-tree export into [`crate::search::GameTree`] so
//! `Play` (alpha-beta) runs on real positions.
//!
//! Deliberately absent (stated, not hidden): underpromotion below queen in
//! search (generation supports all four). Full-board optimal play is not
//! claimed either: [`crate::chess_play`] searches to a fixed depth with a
//! static evaluation, so anything past the horizon is `Exhausted` or a
//! heuristic value, never a proof.

use crate::budget::Budget;
use crate::search::GameTree;
use crate::status::Exhausted;

pub const EMPTY: i8 = 0;
pub const PAWN: i8 = 1;
pub const KNIGHT: i8 = 2;
pub const BISHOP: i8 = 3;
pub const ROOK: i8 = 4;
pub const QUEEN: i8 = 5;
pub const KING: i8 = 6;

const WK: u8 = 1;
const WQ: u8 = 2;
const BK: u8 = 4;
const BQ: u8 = 8;

pub const MATE_SCORE: i64 = 100_000;

/// A move: `promo` is `EMPTY` or one of KNIGHT/BISHOP/ROOK/QUEEN.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Move {
    pub from: u8,
    pub to: u8,
    pub promo: i8,
}

impl Move {
    pub fn quiet(from: u8, to: u8) -> Self {
        Move {
            from,
            to,
            promo: EMPTY,
        }
    }
}

/// Squares are `0 = a1 .. 63 = h8`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Position {
    pub sq: [i8; 64],
    pub white_to_move: bool,
    castle: u8,
    ep: i8,
    halfmove: u32,
    fullmove: u32,
}

impl Default for Position {
    fn default() -> Self {
        Position {
            sq: [EMPTY; 64],
            white_to_move: true,
            castle: 0,
            ep: -1,
            halfmove: 0,
            fullmove: 1,
        }
    }
}

fn file(s: i8) -> i8 {
    s % 8
}
fn rank(s: i8) -> i8 {
    s / 8
}
fn sq_of(f: i8, r: i8) -> Option<u8> {
    if (0..8).contains(&f) && (0..8).contains(&r) {
        Some((r * 8 + f) as u8)
    } else {
        None
    }
}

fn is_white(p: i8) -> bool {
    p > 0
}

impl Position {
    pub fn king_square(&self, white: bool) -> Option<u8> {
        let want = if white { KING } else { -KING };
        self.sq.iter().position(|p| *p == want).map(|i| i as u8)
    }

    /// Is `s` attacked by `by_white`?
    pub fn attacked(&self, s: u8, by_white: bool) -> bool {
        let (f, r) = (file(s as i8), rank(s as i8));
        // Pawns.
        let pr = if by_white { r - 1 } else { r + 1 };
        for df in [-1, 1] {
            if let Some(t) = sq_of(f + df, pr) {
                let p = self.sq[t as usize];
                if p == if by_white { PAWN } else { -PAWN } {
                    return true;
                }
            }
        }
        // Knights.
        for (df, dr) in [
            (1, 2),
            (2, 1),
            (2, -1),
            (1, -2),
            (-1, -2),
            (-2, -1),
            (-2, 1),
            (-1, 2),
        ] {
            if let Some(t) = sq_of(f + df, r + dr) {
                let p = self.sq[t as usize];
                if p == if by_white { KNIGHT } else { -KNIGHT } {
                    return true;
                }
            }
        }
        // King.
        for df in -1..=1 {
            for dr in -1..=1 {
                if df == 0 && dr == 0 {
                    continue;
                }
                if let Some(t) = sq_of(f + df, r + dr) {
                    let p = self.sq[t as usize];
                    if p == if by_white { KING } else { -KING } {
                        return true;
                    }
                }
            }
        }
        // Sliders.
        for (df, dr, kinds) in [
            (1, 1, [BISHOP, QUEEN]),
            (1, -1, [BISHOP, QUEEN]),
            (-1, 1, [BISHOP, QUEEN]),
            (-1, -1, [BISHOP, QUEEN]),
            (1, 0, [ROOK, QUEEN]),
            (-1, 0, [ROOK, QUEEN]),
            (0, 1, [ROOK, QUEEN]),
            (0, -1, [ROOK, QUEEN]),
        ] {
            let (mut cf, mut cr) = (f + df, r + dr);
            while let Some(t) = sq_of(cf, cr) {
                let p = self.sq[t as usize];
                if p != EMPTY {
                    let kind = p.abs();
                    if is_white(p) == by_white && kinds.contains(&kind) {
                        return true;
                    }
                    break;
                }
                cf += df;
                cr += dr;
            }
        }
        false
    }

    pub fn in_check(&self, white: bool) -> bool {
        match self.king_square(white) {
            Some(k) => self.attacked(k, !white),
            None => false,
        }
    }

    fn pseudo(&self, moves: &mut Vec<Move>) {
        let white = self.white_to_move;
        for s in 0..64 {
            let p = self.sq[s];
            if p == EMPTY || is_white(p) != white {
                continue;
            }
            let (f, r) = (file(s as i8), rank(s as i8));
            match p.abs() {
                PAWN => self.pawn_moves(s as u8, f, r, white, moves),
                KNIGHT => {
                    for (df, dr) in [
                        (1, 2),
                        (2, 1),
                        (2, -1),
                        (1, -2),
                        (-1, -2),
                        (-2, -1),
                        (-2, 1),
                        (-1, 2),
                    ] {
                        self.try_target(s as u8, f + df, r + dr, white, moves, false);
                    }
                }
                KING => {
                    for df in -1..=1 {
                        for dr in -1..=1 {
                            if df == 0 && dr == 0 {
                                continue;
                            }
                            self.try_target(s as u8, f + df, r + dr, white, moves, false);
                        }
                    }
                    self.castle_moves(white, moves);
                }
                BISHOP | ROOK | QUEEN => {
                    let dirs: &[(i8, i8)] = match p.abs() {
                        BISHOP => &[(1, 1), (1, -1), (-1, 1), (-1, -1)],
                        ROOK => &[(1, 0), (-1, 0), (0, 1), (0, -1)],
                        _ => &[
                            (1, 1),
                            (1, -1),
                            (-1, 1),
                            (-1, -1),
                            (1, 0),
                            (-1, 0),
                            (0, 1),
                            (0, -1),
                        ],
                    };
                    for (df, dr) in dirs {
                        let (mut cf, mut cr) = (f + df, r + dr);
                        while let Some(t) = sq_of(cf, cr) {
                            let tpc = self.sq[t as usize];
                            if tpc == EMPTY {
                                moves.push(Move::quiet(s as u8, t));
                            } else {
                                if is_white(tpc) != white {
                                    moves.push(Move::quiet(s as u8, t));
                                }
                                break;
                            }
                            cf += df;
                            cr += dr;
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn try_target(
        &self,
        from: u8,
        f: i8,
        r: i8,
        white: bool,
        moves: &mut Vec<Move>,
        pawn_capture_only: bool,
    ) {
        if let Some(t) = sq_of(f, r) {
            let tpc = self.sq[t as usize];
            if tpc == EMPTY {
                if !pawn_capture_only {
                    moves.push(Move::quiet(from, t));
                }
            } else if is_white(tpc) != white {
                moves.push(Move::quiet(from, t));
            }
        }
    }

    fn pawn_moves(&self, s: u8, f: i8, r: i8, white: bool, moves: &mut Vec<Move>) {
        let dir: i8 = if white { 1 } else { -1 };
        let start = if white { 1 } else { 6 };
        let last = if white { 7 } else { 0 };
        // Pushes.
        if let Some(t) = sq_of(f, r + dir) {
            if self.sq[t as usize] == EMPTY {
                if r + dir == last {
                    for promo in [QUEEN, ROOK, BISHOP, KNIGHT] {
                        moves.push(Move {
                            from: s,
                            to: t,
                            promo,
                        });
                    }
                } else {
                    moves.push(Move::quiet(s, t));
                    if r == start {
                        if let Some(t2) = sq_of(f, r + 2 * dir) {
                            if self.sq[t2 as usize] == EMPTY {
                                moves.push(Move::quiet(s, t2));
                            }
                        }
                    }
                }
            }
        }
        // Captures (including en passant).
        for df in [-1, 1] {
            if let Some(t) = sq_of(f + df, r + dir) {
                let tpc = self.sq[t as usize];
                let is_ep = self.ep >= 0 && t as i8 == self.ep;
                if (tpc != EMPTY && is_white(tpc) != white) || is_ep {
                    if r + dir == last {
                        for promo in [QUEEN, ROOK, BISHOP, KNIGHT] {
                            moves.push(Move {
                                from: s,
                                to: t,
                                promo,
                            });
                        }
                    } else {
                        moves.push(Move::quiet(s, t));
                    }
                }
            }
        }
    }

    fn castle_moves(&self, white: bool, moves: &mut Vec<Move>) {
        let (home, k_side, q_side, k_through, q_through): (u8, u8, u8, [u8; 2], [u8; 3]) = if white
        {
            (4, WK, WQ, [5, 6], [3, 2, 1])
        } else {
            (60, BK, BQ, [61, 62], [59, 58, 57])
        };
        let king_home = if white { 4 } else { 60 };
        let _ = home;
        if self.white_to_move != white {
            return;
        }
        if self.in_check(white) {
            return;
        }
        // Kingside.
        if self.castle & k_side != 0
            && self.sq[k_through[0] as usize] == EMPTY
            && self.sq[k_through[1] as usize] == EMPTY
            && !self.attacked(k_through[0], !white)
            && !self.attacked(k_through[1], !white)
        {
            moves.push(Move::quiet(king_home, k_through[1]));
        }
        // Queenside.
        if self.castle & q_side != 0
            && self.sq[q_through[0] as usize] == EMPTY
            && self.sq[q_through[1] as usize] == EMPTY
            && self.sq[q_through[2] as usize] == EMPTY
            && !self.attacked(q_through[0], !white)
            && !self.attacked(q_through[1], !white)
        {
            moves.push(Move::quiet(king_home, q_through[1]));
        }
    }

    /// Functional make-move: returns the resulting position.
    pub fn make(&self, m: Move) -> Position {
        let mut n = *self;
        let white = self.white_to_move;
        let p = n.sq[m.from as usize];
        n.sq[m.from as usize] = EMPTY;
        // En passant capture removes the pawn beside the landing square.
        if p.abs() == PAWN
            && self.ep >= 0
            && m.to as i8 == self.ep
            && self.sq[m.to as usize] == EMPTY
        {
            let cap = if white {
                m.to as i8 - 8
            } else {
                m.to as i8 + 8
            };
            n.sq[cap as usize] = EMPTY;
        }
        n.sq[m.to as usize] = if m.promo != EMPTY {
            if white {
                m.promo
            } else {
                -m.promo
            }
        } else {
            p
        };
        // Castling rook hop.
        if p.abs() == KING {
            let (kf, kt) = (file(m.from as i8), file(m.to as i8));
            if (kf - kt).abs() == 2 {
                let (rf, rt) = if kt > kf {
                    (m.from + 3, m.from + 1)
                } else {
                    (m.from - 4, m.from - 1)
                };
                n.sq[rt as usize] = n.sq[rf as usize];
                n.sq[rf as usize] = EMPTY;
            }
        }
        // Rights updates.
        match m.from {
            4 => n.castle &= !(WK | WQ),
            60 => n.castle &= !(BK | BQ),
            0 => n.castle &= !WQ,
            7 => n.castle &= !WK,
            56 => n.castle &= !BQ,
            63 => n.castle &= !BK,
            _ => {}
        }
        match m.to {
            0 => n.castle &= !WQ,
            7 => n.castle &= !WK,
            56 => n.castle &= !BQ,
            63 => n.castle &= !BK,
            _ => {}
        }
        // New en passant square on a double push.
        n.ep = -1;
        if p.abs() == PAWN {
            let (fr, tr) = (rank(m.from as i8), rank(m.to as i8));
            if (fr - tr).abs() == 2 {
                n.ep = (m.from as i8 + m.to as i8) / 2;
            }
        }
        // Clocks: reset on any pawn move or capture (including en passant),
        // otherwise tick. Fullmove ticks after Black's move.
        let captured = self.sq[m.to as usize] != EMPTY
            || (p.abs() == PAWN && self.ep >= 0 && m.to as i8 == self.ep);
        if p.abs() == PAWN || captured {
            n.halfmove = 0;
        } else {
            n.halfmove = self.halfmove + 1;
        }
        if !white {
            n.fullmove = self.fullmove + 1;
        } else {
            n.fullmove = self.fullmove;
        }
        n.white_to_move = !white;
        n
    }

    /// All legal moves (pseudo-legal filtered by king safety).
    pub fn legal_moves(&self) -> Vec<Move> {
        let white = self.white_to_move;
        let mut pseudo = Vec::new();
        self.pseudo(&mut pseudo);
        pseudo
            .into_iter()
            .filter(|m| {
                let n = self.make(*m);
                !n.in_check(white)
            })
            .collect()
    }

    pub fn is_checkmate(&self) -> bool {
        self.in_check(self.white_to_move) && self.legal_moves().is_empty()
    }

    pub fn is_stalemate(&self) -> bool {
        !self.in_check(self.white_to_move) && self.legal_moves().is_empty()
    }

    /// Material from White's perspective (centipawns).
    pub fn material(&self) -> i64 {
        self.sq
            .iter()
            .map(|p| {
                let v = match p.abs() {
                    PAWN => 100,
                    KNIGHT => 320,
                    BISHOP => 330,
                    ROOK => 500,
                    QUEEN => 900,
                    _ => 0,
                };
                if *p > 0 {
                    v
                } else if *p < 0 {
                    -v
                } else {
                    0
                }
            })
            .sum()
    }

    /// Parse a FEN string (placement, side, castling, en passant, clocks).
    /// Clocks default to `0 1` when absent.
    pub fn from_fen(fen: &str) -> Result<Position, String> {
        let parts: Vec<&str> = fen.split_whitespace().collect();
        if parts.len() < 4 {
            return Err(format!("fen needs 4+ fields, got {}", parts.len()));
        }
        let mut pos = Position::default();
        let mut s = 56i8;
        for ch in parts[0].chars() {
            match ch {
                '/' => s -= 16,
                '1'..='8' => s += (ch as u8 - b'0') as i8,
                _ => {
                    let kind = match ch.to_ascii_lowercase() {
                        'p' => PAWN,
                        'n' => KNIGHT,
                        'b' => BISHOP,
                        'r' => ROOK,
                        'q' => QUEEN,
                        'k' => KING,
                        _ => return Err(format!("bad fen piece '{ch}'")),
                    };
                    if !(0..64).contains(&s) {
                        return Err("fen placement overflows the board".to_string());
                    }
                    pos.sq[s as usize] = if ch.is_uppercase() { kind } else { -kind };
                    s += 1;
                }
            }
        }
        pos.white_to_move = match parts[1] {
            "w" => true,
            "b" => false,
            _ => return Err(format!("bad fen side '{}'", parts[1])),
        };
        pos.castle = 0;
        if parts[2] != "-" {
            for ch in parts[2].chars() {
                match ch {
                    'K' => pos.castle |= WK,
                    'Q' => pos.castle |= WQ,
                    'k' => pos.castle |= BK,
                    'q' => pos.castle |= BQ,
                    _ => return Err(format!("bad fen castling '{ch}'")),
                }
            }
        }
        pos.ep = if parts[3] == "-" {
            -1
        } else {
            algebraic(parts[3]).ok_or_else(|| format!("bad fen ep '{}'", parts[3]))? as i8
        };
        if parts.len() > 4 {
            pos.halfmove = parts[4]
                .parse()
                .map_err(|_| format!("bad fen halfmove '{}'", parts[4]))?;
        }
        if parts.len() > 5 {
            pos.fullmove = parts[5]
                .parse()
                .map_err(|_| format!("bad fen fullmove '{}'", parts[5]))?;
            if pos.fullmove == 0 {
                return Err("fen fullmove counts from 1".to_string());
            }
        }
        Ok(pos)
    }

    pub fn startpos() -> Position {
        Position::from_fen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1")
            .expect("startpos fen is valid")
    }

    pub fn halfmove(&self) -> u32 {
        self.halfmove
    }
    pub fn fullmove(&self) -> u32 {
        self.fullmove
    }

    /// En passant target square, if the last move was a double pawn push.
    pub fn ep_square(&self) -> Option<u8> {
        if self.ep < 0 {
            None
        } else {
            Some(self.ep as u8)
        }
    }

    /// Serialize back to FEN (placement, side, castling, en passant, clocks).
    pub fn to_fen(&self) -> String {
        let mut out = String::new();
        for r in (0..8).rev() {
            let mut empty = 0;
            for f in 0..8 {
                let p = self.sq[(r * 8 + f) as usize];
                if p == EMPTY {
                    empty += 1;
                } else {
                    if empty > 0 {
                        out.push((b'0' + empty) as char);
                        empty = 0;
                    }
                    let kind = match p.abs() {
                        PAWN => 'p',
                        KNIGHT => 'n',
                        BISHOP => 'b',
                        ROOK => 'r',
                        QUEEN => 'q',
                        _ => 'k',
                    };
                    out.push(if p > 0 {
                        kind.to_ascii_uppercase()
                    } else {
                        kind
                    });
                }
            }
            if empty > 0 {
                out.push((b'0' + empty) as char);
            }
            if r > 0 {
                out.push('/');
            }
        }
        out.push(' ');
        out.push(if self.white_to_move { 'w' } else { 'b' });
        out.push(' ');
        if self.castle == 0 {
            out.push('-');
        } else {
            if self.castle & WK != 0 {
                out.push('K');
            }
            if self.castle & WQ != 0 {
                out.push('Q');
            }
            if self.castle & BK != 0 {
                out.push('k');
            }
            if self.castle & BQ != 0 {
                out.push('q');
            }
        }
        out.push(' ');
        if self.ep < 0 {
            out.push('-');
        } else {
            out.push_str(&square_name(self.ep as u8));
        }
        out.push_str(&format!(" {} {}", self.halfmove, self.fullmove));
        out
    }

    /// Zobrist-style hash over squares, side, castling, and en passant
    /// (clocks excluded: repetition ignores them). Deterministic: the mixer
    /// is splitmix64 over a fixed per-(piece, square) index, no tables.
    pub fn repetition_hash(&self) -> u64 {
        fn mix(mut z: u64) -> u64 {
            z = z.wrapping_add(0x9E37_79B9_7F4A_7C15);
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }
        let mut h = 0u64;
        for (i, p) in self.sq.iter().enumerate() {
            if *p != EMPTY {
                // Piece codes 0..11 (white 0-5, black 6-11), square 0..63.
                let code = if *p > 0 {
                    (*p - 1) as u64
                } else {
                    (*p).unsigned_abs() as u64 + 5
                };
                h ^= mix(code * 64 + i as u64);
            }
        }
        if self.white_to_move {
            h ^= mix(768);
        }
        h ^= mix(769 + self.castle as u64);
        if self.ep >= 0 {
            h ^= mix(774 + self.ep as u64);
        }
        h
    }

    /// Static evaluation from White's perspective (centipawns): material
    /// plus simple midgame piece-square tables.
    pub fn evaluate(&self) -> i64 {
        let mut total = 0i64;
        for (i, p) in self.sq.iter().enumerate() {
            if *p == EMPTY {
                continue;
            }
            let (f, r) = (file(i as i8), rank(i as i8));
            // White reads the table rank-up; Black mirrors it.
            let t = if *p > 0 {
                ((7 - r) * 8 + f) as usize
            } else {
                (r * 8 + f) as usize
            };
            let (base, table): (i64, &[i16; 64]) = match p.abs() {
                PAWN => (100, &PST_PAWN),
                KNIGHT => (320, &PST_KNIGHT),
                BISHOP => (330, &PST_BISHOP),
                ROOK => (500, &PST_ROOK),
                QUEEN => (900, &PST_QUEEN),
                _ => (0, &PST_KING),
            };
            let v = base + table[t] as i64;
            total += if *p > 0 { v } else { -v };
        }
        total
    }

    /// Parse a UCI-coordinate move (`e2e4`, `e7e8q`) against this position.
    /// Returns `None` when the move is not legal here.
    pub fn parse_uci(&self, text: &str) -> Option<Move> {
        let b = text.as_bytes();
        if b.len() != 4 && b.len() != 5 {
            return None;
        }
        let sq = |f: u8, r: u8| {
            if !(b'a'..=b'h').contains(&f) || !(b'1'..=b'8').contains(&r) {
                None
            } else {
                sq_of((f - b'a') as i8, (r - b'1') as i8)
            }
        };
        let (from, to) = (sq(b[0], b[1])?, sq(b[2], b[3])?);
        let promo = if b.len() == 5 {
            match b[4] {
                b'n' => KNIGHT,
                b'b' => BISHOP,
                b'r' => ROOK,
                b'q' => QUEEN,
                _ => return None,
            }
        } else {
            EMPTY
        };
        let m = Move { from, to, promo };
        if self.legal_moves().contains(&m) {
            Some(m)
        } else {
            None
        }
    }
}

fn algebraic(s: &str) -> Option<u8> {
    let b = s.as_bytes();
    if b.len() != 2 {
        return None;
    }
    let (f, r) = (b[0].wrapping_sub(b'a') as i8, b[1].wrapping_sub(b'1') as i8);
    sq_of(f, r)
}

fn square_name(s: u8) -> String {
    const FILES: &[u8] = b"abcdefgh";
    format!(
        "{}{}",
        FILES[file(s as i8) as usize] as char,
        rank(s as i8) + 1
    )
}

// Midgame piece-square tables, rank 8 first (White mirrors by rank).
// Plain, well-known values: centralisation and king safety over subtlety.
const PST_PAWN: [i16; 64] = [
    0, 0, 0, 0, 0, 0, 0, 0, 50, 50, 50, 50, 50, 50, 50, 50, 10, 10, 20, 30, 30, 20, 10, 10, 5, 5,
    10, 25, 25, 10, 5, 5, 0, 0, 0, 20, 20, 0, 0, 0, 5, -5, -10, 0, 0, -10, -5, 5, 5, 10, 10, -20,
    -20, 10, 10, 5, 0, 0, 0, 0, 0, 0, 0, 0,
];
const PST_KNIGHT: [i16; 64] = [
    -50, -40, -30, -30, -30, -30, -40, -50, -40, -20, 0, 0, 0, 0, -20, -40, -30, 0, 10, 15, 15, 10,
    0, -30, -30, 5, 15, 20, 20, 15, 5, -30, -30, 0, 15, 20, 20, 15, 0, -30, -30, 5, 10, 15, 15, 10,
    5, -30, -40, -20, 0, 5, 5, 0, -20, -40, -50, -40, -30, -30, -30, -30, -40, -50,
];
const PST_BISHOP: [i16; 64] = [
    -20, -10, -10, -10, -10, -10, -10, -20, -10, 0, 0, 0, 0, 0, 0, -10, -10, 0, 5, 10, 10, 5, 0,
    -10, -10, 5, 5, 10, 10, 5, 5, -10, -10, 0, 10, 10, 10, 10, 0, -10, -10, 10, 10, 10, 10, 10, 10,
    -10, -10, 5, 0, 0, 0, 0, 5, -10, -20, -10, -10, -10, -10, -10, -10, -20,
];
const PST_ROOK: [i16; 64] = [
    0, 0, 0, 0, 0, 0, 0, 0, 5, 10, 10, 10, 10, 10, 10, 5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0,
    0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, -5, 0, 0, 0, 0, 0, 0, -5, 0, 0,
    0, 5, 5, 0, 0, 0,
];
const PST_QUEEN: [i16; 64] = [
    -20, -10, -10, -5, -5, -10, -10, -20, -10, 0, 0, 0, 0, 0, 0, -10, -10, 0, 5, 5, 5, 5, 0, -10,
    -5, 0, 5, 5, 5, 5, 0, -5, 0, 0, 5, 5, 5, 5, 0, -5, -10, 5, 5, 5, 5, 5, 0, -10, -10, 0, 5, 0, 0,
    0, 0, -10, -20, -10, -10, -5, -5, -10, -10, -20,
];
const PST_KING: [i16; 64] = [
    -30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40, -40, -30, -30, -40, -40,
    -50, -50, -40, -40, -30, -30, -40, -40, -50, -50, -40, -40, -30, -20, -30, -30, -40, -40, -30,
    -30, -20, -10, -20, -20, -20, -20, -20, -20, -10, 20, 20, 0, 0, 0, 0, 20, 20, 20, 30, 10, 0, 0,
    10, 30, 20,
];

pub fn move_to_string(m: Move) -> String {
    const FILES: &[u8] = b"abcdefgh";
    let promo = match m.promo {
        KNIGHT => "n",
        BISHOP => "b",
        ROOK => "r",
        QUEEN => "q",
        _ => "",
    };
    format!(
        "{}{}{}{}",
        FILES[file(m.from as i8) as usize] as char,
        rank(m.from as i8) + 1,
        FILES[file(m.to as i8) as usize] as char,
        rank(m.to as i8) + 1,
    ) + promo
}

/// Perft: leaf nodes at `depth` (depth 0 counts 1). Bulk counting is omitted
/// deliberately — clarity first, per V2's capability-before-speed rule.
pub fn perft(pos: &Position, depth: u32) -> u64 {
    if depth == 0 {
        return 1;
    }
    pos.legal_moves()
        .iter()
        .map(|m| perft(&pos.make(*m), depth - 1))
        .sum()
}

/// Mate in one, if any legal move checkmates.
pub fn find_mate_in_one(pos: &Position) -> Option<Move> {
    pos.legal_moves()
        .into_iter()
        .find(|m| pos.make(*m).is_checkmate())
}

/// Export a bounded explicit tree for `Play`: node per position up to `depth`
/// plies, `maximizing` by White to move, leaves scored by mate (signed by
/// winner), stalemate 0, otherwise material.
pub fn endgame_tree(
    root: &Position,
    depth: u32,
    budget: &mut Budget,
) -> Result<GameTree, Exhausted> {
    let mut tree = GameTree {
        children: vec![Vec::new()],
        maximizing: vec![root.white_to_move],
        eval: vec![0],
    };
    let mut stack = vec![(0u32, *root, depth)];
    while let Some((id, pos, left)) = stack.pop() {
        budget.charge(1)?;
        if left == 0 || pos.is_checkmate() || pos.is_stalemate() {
            tree.eval[id as usize] = if pos.is_checkmate() {
                if pos.white_to_move {
                    -MATE_SCORE
                } else {
                    MATE_SCORE
                }
            } else {
                pos.material()
            };
            continue;
        }
        let moves = pos.legal_moves();
        if moves.is_empty() {
            tree.eval[id as usize] = pos.material();
            continue;
        }
        for m in moves {
            let child = tree.children.len() as u32;
            tree.children.push(Vec::new());
            let next = pos.make(m);
            tree.maximizing.push(next.white_to_move);
            tree.eval.push(0);
            tree.children[id as usize].push(child);
            stack.push((child, next, left - 1));
        }
    }
    Ok(tree)
}
