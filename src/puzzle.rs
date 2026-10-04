//! Puzzle adapters (V2 R4 front ends, ROADMAP II3).
//!
//! Each function compiles one familiar puzzle into a [`CspProblem`]: the
//! adapter owns the domain knowledge, the solver sees only variables,
//! domains, and constraints. Fast paths are explicitly out of scope —
//! propagation plus search solves these instances outright, and every
//! solution re-checks through [`verify_csp`].

use crate::csp::{Constraint, CspProblem, VarId};

/// 9x9 Sudoku from an 81-character string: `1`–`9` givens, `.` or `0` blanks.
/// Returns the problem plus the givens vector for solution comparison.
pub fn sudoku9(src: &str) -> Result<CspProblem, String> {
    let chars: Vec<char> = src.chars().filter(|c| !c.is_whitespace()).collect();
    if chars.len() != 81 {
        return Err(format!("sudoku needs 81 cells, got {}", chars.len()));
    }
    let mut p = CspProblem::new();
    let cell = |r: usize, c: usize| (r * 9 + c) as VarId;
    for r in 0..9 {
        for c in 0..9 {
            p.var(&format!("r{r}c{c}"), (1..=9).collect());
        }
    }
    for r in 0..9 {
        p.constrain(Constraint::AllDifferent(
            (0..9).map(|c| cell(r, c)).collect(),
        ));
        p.constrain(Constraint::AllDifferent(
            (0..9).map(|rr| cell(rr, r)).collect(),
        ));
    }
    for (br, bc) in [
        (0, 0),
        (0, 3),
        (0, 6),
        (3, 0),
        (3, 3),
        (3, 6),
        (6, 0),
        (6, 3),
        (6, 6),
    ] {
        let mut box_cells = Vec::new();
        for r in br..br + 3 {
            for c in bc..bc + 3 {
                box_cells.push(cell(r, c));
            }
        }
        p.constrain(Constraint::AllDifferent(box_cells));
    }
    for (i, ch) in chars.iter().enumerate() {
        match ch {
            '1'..='9' => {
                let v = (*ch as u8 - b'0') as i32;
                p.constrain(Constraint::ValueEq(i as VarId, v));
            }
            '.' | '0' => {}
            _ => return Err(format!("bad sudoku character '{ch}' at cell {i}")),
        }
    }
    Ok(p)
}

/// N-queens: `q[c]` is the row of the queen in column `c`. Rows all differ
/// and diagonals differ (`AbsDiffNe` with the column distance).
pub fn nqueens(n: usize) -> Result<CspProblem, String> {
    if n == 0 || n > 32 {
        return Err(format!("queens board {n} out of 1..=32"));
    }
    let mut p = CspProblem::new();
    for c in 0..n {
        p.var(&format!("q{c}"), (0..n as i32).collect());
    }
    let cols: Vec<VarId> = (0..n as VarId).collect();
    p.constrain(Constraint::AllDifferent(cols));
    for a in 0..n {
        for b in (a + 1)..n {
            p.constrain(Constraint::AbsDiffNe(
                a as VarId,
                b as VarId,
                (b - a) as i32,
            ));
        }
    }
    Ok(p)
}

/// Map coloring: one variable per region over `colors` colors, `NotEqual`
/// per border. Regions are `0..num_regions`.
pub fn map_color(num_regions: usize, borders: &[(usize, usize)], colors: i32) -> CspProblem {
    let mut p = CspProblem::new();
    for r in 0..num_regions {
        p.var(&format!("region{r}"), (0..colors).collect());
    }
    for (a, b) in borders {
        p.constrain(Constraint::NotEqual(*a as VarId, *b as VarId));
    }
    p
}

/// Small logic-grid helper: `groups` of variables that must all differ
/// (each group is one attribute across entities) plus fixed equalities as
/// `(var, value)` pairs.
pub fn logic_grid(
    names: &[&str],
    domains: &[Vec<i32>],
    all_different_groups: &[Vec<usize>],
    fixed: &[(usize, i32)],
) -> CspProblem {
    let mut p = CspProblem::new();
    for (name, dom) in names.iter().zip(domains.iter()) {
        p.var(name, dom.clone());
    }
    for group in all_different_groups {
        p.constrain(Constraint::AllDifferent(
            group.iter().map(|v| *v as VarId).collect(),
        ));
    }
    for (v, val) in fixed {
        p.constrain(Constraint::ValueEq(*v as VarId, *val));
    }
    p
}
