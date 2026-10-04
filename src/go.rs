//! Go (V2 R6 game adapter, ROADMAP II4/II5).
//!
//! A small-board Go engine with the rules that decide tactics: liberties,
//! capture removal, suicide prohibition, and simple ko (repeating the
//! previous board position is illegal). Board size is `1..=9`; the tests use
//! 5x5 capture puzzles, which is also the honest scope statement — full-board
//! play explodes past any explicit tree, and this module reports `Err` on
//! illegal moves rather than guessing.
//!
//! Scoring is deliberately absent: capture puzzles (`capture_in_one`) and
//! legality are what the search layer consumes. Stone counting can extend the
//! same board later.

use crate::budget::Budget;
use crate::status::Exhausted;

pub const EMPTY: i8 = 0;
pub const BLACK: i8 = 1;
pub const WHITE: i8 = 2;

/// Outcome of one legal play: stones captured and the resulting side to move.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PlayOutcome {
    pub captured: usize,
}

/// A board position with simple-ko memory (hash of the position one move
/// ago; `None` after manual setup, where no repetition is possible yet).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Goban {
    pub n: usize,
    cells: Vec<i8>,
    black_to_move: bool,
    prev_hash: Option<u64>,
}

impl Goban {
    pub fn new(n: usize) -> Result<Self, String> {
        if n == 0 || n > 9 {
            return Err(format!("board size {n} out of 1..=9"));
        }
        Ok(Goban {
            n,
            cells: vec![EMPTY; n * n],
            black_to_move: true,
            prev_hash: None,
        })
    }

    pub fn at(&self, idx: usize) -> i8 {
        self.cells[idx]
    }

    pub fn side_to_move(&self) -> i8 {
        if self.black_to_move {
            BLACK
        } else {
            WHITE
        }
    }

    fn neighbors(&self, idx: usize) -> Vec<usize> {
        let (f, r) = (idx % self.n, idx / self.n);
        let mut out = Vec::new();
        if f > 0 {
            out.push(idx - 1);
        }
        if f + 1 < self.n {
            out.push(idx + 1);
        }
        if r > 0 {
            out.push(idx - self.n);
        }
        if r + 1 < self.n {
            out.push(idx + self.n);
        }
        out
    }

    fn group_and_liberties(&self, start: usize) -> (Vec<usize>, usize) {
        let color = self.cells[start];
        let mut group = Vec::new();
        let mut seen = vec![false; self.cells.len()];
        let mut libs = vec![false; self.cells.len()];
        let mut stack = vec![start];
        seen[start] = true;
        while let Some(i) = stack.pop() {
            group.push(i);
            for nb in self.neighbors(i) {
                if self.cells[nb] == EMPTY {
                    libs[nb] = true;
                } else if self.cells[nb] == color && !seen[nb] {
                    seen[nb] = true;
                    stack.push(nb);
                }
            }
        }
        (group, libs.iter().filter(|x| **x).count())
    }

    fn hash(&self) -> u64 {
        let mut h: u64 = 0x9e37_79b9_7f4a_7c15;
        for c in &self.cells {
            h = h.wrapping_mul(0x1000_0000_01b3).wrapping_add(*c as u64 + 1);
        }
        h = h
            .wrapping_mul(0x1000_0000_01b3)
            .wrapping_add(self.black_to_move as u64);
        h
    }

    /// Place `stones` without any legality check (position setup for puzzles).
    pub fn set(&mut self, idx: usize, stone: i8) {
        self.cells[idx] = stone;
        self.prev_hash = None;
    }

    pub fn set_side(&mut self, black_to_move: bool) {
        self.black_to_move = black_to_move;
        self.prev_hash = None;
    }

    /// Raw placement: occupied and suicide rules only, no ko check. The
    /// suicide restore is exact: captures give the new stone liberties, so a
    /// zero-liberty result implies nothing was removed.
    fn place(&mut self, idx: usize) -> Result<PlayOutcome, String> {
        if idx >= self.cells.len() {
            return Err(format!("point {idx} off a {}x{} board", self.n, self.n));
        }
        if self.cells[idx] != EMPTY {
            return Err(format!("point {idx} occupied"));
        }
        let mine = self.side_to_move();
        let theirs = if mine == BLACK { WHITE } else { BLACK };
        self.cells[idx] = mine;
        let mut captured = 0usize;
        let adj = self.neighbors(idx);
        for nb in adj {
            if self.cells[nb] == theirs {
                let (group, libs) = self.group_and_liberties(nb);
                if libs == 0 {
                    for g in group {
                        self.cells[g] = EMPTY;
                    }
                    captured += 1;
                }
            }
        }
        let (_, libs) = self.group_and_liberties(idx);
        if libs == 0 {
            self.cells[idx] = EMPTY;
            return Err("suicide move".to_string());
        }
        self.black_to_move = !self.black_to_move;
        Ok(PlayOutcome { captured })
    }

    /// Play at `idx`. Illegal (occupied, suicide, ko) is `Err`, always. Ko is
    /// checked by simulation so a repetition is rejected *before* the board
    /// mutates: the candidate position must differ from the one a move ago.
    pub fn play(&mut self, idx: usize) -> Result<PlayOutcome, String> {
        if idx >= self.cells.len() || self.cells[idx] != EMPTY {
            return Err(format!("point {idx} not playable"));
        }
        let mut sim = self.clone();
        let out = sim.place(idx)?;
        if Some(sim.hash()) == self.prev_hash {
            return Err("ko: repeating the previous position".to_string());
        }
        let before = self.hash();
        *self = sim;
        self.prev_hash = Some(before);
        Ok(out)
    }

    /// Empty points where the side to move captures at least one stone.
    pub fn capture_in_one(&self, budget: &mut Budget) -> Result<Vec<usize>, Exhausted> {
        let mut out = Vec::new();
        for idx in 0..self.cells.len() {
            budget.charge(1)?;
            if self.cells[idx] != EMPTY {
                continue;
            }
            let mut sim = self.clone();
            if let Ok(res) = sim.play(idx) {
                if res.captured > 0 {
                    out.push(idx);
                }
            }
        }
        out.sort_unstable();
        Ok(out)
    }
}
