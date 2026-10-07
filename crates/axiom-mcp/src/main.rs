//! axiom-mcp: MCP stdio server exposing Axiom as agent tools.
//!
//! Transport: newline-delimited JSON-RPC 2.0 on stdin/stdout (MCP stdio).
//! Std only — no new dependencies, so the `axiom` core stays zero-dep.
//!
//! Tools:
//! - `axiom_prove { program, query_index?, max_steps? }`
//! - `axiom_sat { dimacs, max_steps? }`
//! - `axiom_version {}`
//!
//! Every verdict reports the honest `Status`: `exhausted`/`unknown` never
//! render as negatives, and `proof_present`/`verified` say what backs a
//! definite answer.

use std::io::{BufRead, Write};

use axiom::{Budget, SatSolver, Solver};

const VERSION: &str = env!("CARGO_PKG_VERSION");

fn main() {
    let stdin = std::io::stdin();
    let lock = stdin.lock();
    for line in lock.lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };
        if line.trim().is_empty() {
            continue;
        }
        if let Some(resp) = handle_line(&line) {
            println!("{resp}");
            let _ = std::io::stdout().flush();
        }
    }
}

fn handle_line(line: &str) -> Option<String> {
    let method = extract_method(line)?;
    let id = extract_raw_id(line);
    // Notifications carry no id: acknowledge with nothing.
    let id = id?;
    let result = match method.as_str() {
        "initialize" => ok(
            &id,
            r#"{"protocolVersion":"2024-11-05","capabilities":{"tools":{}},"serverInfo":{"name":"axiom-mcp","version":"0.1.0"}}"#,
        ),
        "notifications/initialized" | "notifications/cancelled" => return None,
        "ping" => ok(&id, "{}"),
        "tools/list" => ok(&id, TOOLS_LIST),
        "tools/call" => {
            let name = extract_string(line, "name").unwrap_or_default();
            match name.as_str() {
                "axiom_prove" => {
                    let program = extract_string(line, "program").unwrap_or_default();
                    let q = extract_u64(line, "query_index").unwrap_or(0) as usize;
                    let steps = extract_u64(line, "max_steps").unwrap_or(1_000_000);
                    ok(&id, &tool_prove(&program, q, steps))
                }
                "axiom_sat" => {
                    let dimacs = extract_string(line, "dimacs").unwrap_or_default();
                    let steps = extract_u64(line, "max_steps").unwrap_or(1_000_000);
                    ok(&id, &tool_sat(&dimacs, steps))
                }
                "axiom_version" => ok(&id, &tool_version()),
                _ => err(&id, -32602, "unknown tool"),
            }
        }
        _ => err(&id, -32601, "method not found"),
    };
    Some(result)
}

// ---- tools ---------------------------------------------------------------

fn tool_prove(program_src: &str, query_index: usize, max_steps: u64) -> String {
    let parsed = match axiom::exterior::parse(program_src) {
        Ok(p) => p,
        Err(e) => {
            return obj(&[
                ("status", s("exhausted")),
                ("summary", s(&format!("parse error: {e}"))),
                ("steps", n(0)),
                ("proof_present", b(false)),
            ]);
        }
    };
    if parsed.queries.is_empty() {
        return obj(&[
            ("status", s("exhausted")),
            ("summary", s("no ?- query in program")),
            ("steps", n(0)),
            ("proof_present", b(false)),
        ]);
    }
    if query_index >= parsed.queries.len() {
        return obj(&[
            ("status", s("exhausted")),
            ("summary", s("query_index out of range")),
            ("steps", n(0)),
            ("proof_present", b(false)),
        ]);
    }
    let goal = parsed.queries[query_index];
    let mut solver = Solver::new(parsed.program);
    let mut budget = Budget::steps(max_steps.max(1));
    let out = solver.prove(goal, &mut budget);
    let status = out.status.to_string();
    let spent = budget.spent();
    let present = out.proof.is_some();
    let verified = out.proof.as_ref().is_some_and(|p| solver.verify(p).is_ok());
    let mut summary = format!("{status} after {spent} steps");
    if !out.notes.is_empty() {
        summary.push_str(&format!(" ({})", out.notes.join("; ")));
    }
    obj(&[
        ("status", s(&status)),
        ("summary", s(&summary)),
        ("steps", n(spent)),
        ("proof_present", b(present)),
        ("verified", b(verified)),
    ])
}

fn tool_sat(dimacs: &str, max_steps: u64) -> String {
    let (num_vars, clauses) = match parse_dimacs(dimacs) {
        Ok(v) => v,
        Err(msg) => {
            return obj(&[
                ("status", s("exhausted")),
                ("summary", s(&format!("dimacs error: {msg}"))),
                ("steps", n(0)),
            ]);
        }
    };
    let mut solver = SatSolver::new();
    for _ in 0..num_vars {
        solver.new_var();
    }
    for c in &clauses {
        solver.add_clause(c);
    }
    let mut budget = Budget::steps(max_steps.max(1));
    match solver.solve(&mut budget) {
        Ok(axiom::SatOutcome::Sat { .. }) => obj(&[
            ("status", s("found")),
            ("summary", s(&format!("sat after {} steps", budget.spent()))),
            ("steps", n(budget.spent())),
        ]),
        Ok(axiom::SatOutcome::Unsat { .. }) => obj(&[
            ("status", s("impossible")),
            (
                "summary",
                s(&format!("unsat after {} steps", budget.spent())),
            ),
            ("steps", n(budget.spent())),
        ]),
        Err(e) => obj(&[
            ("status", s("exhausted")),
            ("summary", s(&format!("budget stopped: {e}"))),
            ("steps", n(budget.spent())),
        ]),
    }
}

fn tool_version() -> String {
    obj(&[
        ("name", s("axiom-mcp")),
        ("version", s(VERSION)),
        (
            "representations",
            s("datalog,sat,csp,states,graph,game,chess,go,word"),
        ),
    ])
}

fn parse_dimacs(src: &str) -> Result<(u32, Vec<Vec<i32>>), String> {
    let mut num_vars: u32 = 0;
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut cur: Vec<i32> = Vec::new();
    let mut header_seen = false;
    for (ln, raw) in src.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        if line.starts_with('p') {
            let parts: Vec<&str> = line.split_whitespace().collect();
            if parts.len() != 4 || parts[1] != "cnf" {
                return Err(format!("line {}: want 'p cnf VARS CLAUSES'", ln + 1));
            }
            num_vars = parts[2]
                .parse::<u32>()
                .map_err(|_| format!("line {}: bad var count", ln + 1))?;
            header_seen = true;
            continue;
        }
        for tok in line.split_whitespace() {
            let lit: i32 = tok
                .parse()
                .map_err(|_| format!("line {}: bad literal '{tok}'", ln + 1))?;
            if lit == 0 {
                clauses.push(std::mem::take(&mut cur));
            } else {
                if lit.unsigned_abs() as u32 > num_vars && num_vars > 0 {
                    return Err(format!("line {}: var out of range", ln + 1));
                }
                cur.push(lit);
            }
        }
    }
    if !header_seen {
        return Err("missing 'p cnf VARS CLAUSES' header".to_string());
    }
    if !cur.is_empty() {
        return Err("unterminated clause (missing trailing 0)".to_string());
    }
    Ok((num_vars, clauses))
}

// ---- tiny JSON helpers (std only) -----------------------------------------

const TOOLS_LIST: &str = r#"{"tools":[{"name":"axiom_prove","description":"Prove a query over a stratified Datalog program. Returns the honest Status plus whether a checkable proof is present.","inputSchema":{"type":"object","properties":{"program":{"type":"string","description":"Datalog source with facts, rules and at least one ?- query."},"query_index":{"type":"number","description":"Which ?- query to prove (0-based)."},"max_steps":{"type":"number","description":"Step budget (default 1000000)."}},"required":["program"]}},{"name":"axiom_sat","description":"Solve ground CNF given as DIMACS text. Returns found (sat) / impossible (unsat) / exhausted.","inputSchema":{"type":"object","properties":{"dimacs":{"type":"string","description":"DIMACS CNF including the p cnf header."},"max_steps":{"type":"number"}},"required":["dimacs"]}},{"name":"axiom_version","description":"Server name, version and supported representations.","inputSchema":{"type":"object","properties":{}}}]}"#;

fn ok(id_raw: &str, result_json: &str) -> String {
    format!(r#"{{"jsonrpc":"2.0","id":{id_raw},"result":{result_json}}}"#)
}

fn err(id_raw: &str, code: i32, message: &str) -> String {
    format!(
        r#"{{"jsonrpc":"2.0","id":{id_raw},"error":{{"code":{code},"message":"{}"}}}}"#,
        esc(message)
    )
}

fn obj(fields: &[(&str, String)]) -> String {
    let mut out = String::from("{");
    for (i, (k, v)) in fields.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        out.push('"');
        out.push_str(k);
        out.push_str("\":");
        out.push_str(v);
    }
    out.push('}');
    // MCP tools/call wraps the object in {content:[{type:text,text}]}.
    format!(
        r#"{{"content":[{{"type":"text","text":"{}"}}]}}"#,
        esc(&out)
    )
}

fn s(v: &str) -> String {
    format!(r#""{}""#, esc(v))
}

fn n(v: u64) -> String {
    v.to_string()
}

fn b(v: bool) -> String {
    v.to_string()
}

fn esc(v: &str) -> String {
    let mut out = String::with_capacity(v.len() + 2);
    for c in v.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

/// Method is always a JSON string: `"method" : "tools/call"`.
fn extract_method(line: &str) -> Option<String> {
    extract_string(line, "method")
}

/// The raw JSON value after `"id"`, verbatim (number/string/null), trimmed.
fn extract_raw_id(line: &str) -> Option<String> {
    let key = "\"id\"";
    let k = line.find(key)?;
    let after = line[k + key.len()..].find(':')?;
    let mut rest = line[k + key.len() + after + 1..].trim_start();
    if rest.starts_with('"') {
        rest = &rest[1..];
        let mut esc_next = false;
        for (i, c) in rest.char_indices() {
            if esc_next {
                esc_next = false;
                continue;
            }
            if c == '\\' {
                esc_next = true;
                continue;
            }
            if c == '"' {
                return Some(format!(r#""{}""#, &rest[..i]));
            }
        }
        return None;
    }
    let end = rest
        .find(|c: char| c == ',' || c == '}')
        .unwrap_or(rest.len());
    let v = rest[..end].trim();
    if v.is_empty() {
        None
    } else {
        Some(v.to_string())
    }
}

/// First JSON string value for a given key, with escapes resolved.
/// Searches for `"key"` then the next quoted string after `:`.
fn extract_string(line: &str, key: &str) -> Option<String> {
    let pat = format!("\"{key}\"");
    let k = line.find(pat.as_str())?;
    let after = line[k + pat.len()..].find(':')?;
    let rest = line[k + pat.len() + after + 1..].trim_start();
    if !rest.starts_with('"') {
        return None;
    }
    let body = &rest[1..];
    let mut out = String::new();
    let mut chars = body.chars();
    loop {
        let c = chars.next()?;
        match c {
            '"' => return Some(out),
            '\\' => match chars.next()? {
                '"' => out.push('"'),
                '\\' => out.push('\\'),
                'n' => out.push('\n'),
                'r' => out.push('\r'),
                't' => out.push('\t'),
                'u' => {
                    let hex: String = chars.by_ref().take(4).collect();
                    let cp = u32::from_str_radix(&hex, 16).ok()?;
                    out.push(char::from_u32(cp)?);
                }
                e => {
                    out.push('\\');
                    out.push(e);
                }
            },
            c => out.push(c),
        }
    }
}

fn extract_u64(line: &str, key: &str) -> Option<u64> {
    let pat = format!("\"{key}\"");
    let k = line.find(pat.as_str())?;
    let after = line[k + pat.len()..].find(':')?;
    let rest = line[k + pat.len() + after + 1..].trim_start();
    let num: String = if rest.starts_with('"') {
        let s = extract_string(line[k..].trim_start(), key)?;
        s.trim().to_string()
    } else {
        rest.chars()
            .take_while(|c| c.is_ascii_digit())
            .collect::<String>()
    };
    if num.is_empty() {
        None
    } else {
        num.parse::<u64>().ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn escapes_round_trip() {
        let raw = "a\"b\\c\nd";
        let e = esc(raw);
        let line = format!(r#"{{"k":"{e}"}}"#);
        assert_eq!(extract_string(&line, "k").as_deref(), Some(raw));
    }

    #[test]
    fn id_shapes_pass_through() {
        assert_eq!(extract_raw_id(r#"{"id":1}"#).as_deref(), Some("1"));
        assert_eq!(
            extract_raw_id(r#"{"id":"a-1"}"#).as_deref(),
            Some(r#""a-1""#)
        );
        assert_eq!(extract_raw_id(r#"{"id":null}"#).as_deref(), Some("null"));
    }

    #[test]
    fn prove_tool_is_honest_on_parse_error() {
        let out = tool_prove("this is not datalog", 0, 1000);
        assert!(out.contains("exhausted"), "{out}");
    }

    #[test]
    fn prove_tool_proves_transitive_closure() {
        let src = "edge(a, b).\nedge(b, c).\npath(X, Y) :- edge(X, Y).\npath(X, Z) :- path(X, Y), edge(Y, Z).\n?- path(a, c).\n";
        let out = tool_prove(src, 0, 1_000_000);
        assert!(out.contains("proved"), "{out}");
        assert!(out.contains("proof_present"), "{out}");
    }

    #[test]
    fn sat_tool_solves_trivial() {
        let dimacs = "c trivial\np cnf 1 1\n1 0\n";
        let out = tool_sat(dimacs, 100_000);
        assert!(out.contains("found"), "{out}");
    }

    #[test]
    fn sat_tool_rejects_bad_header() {
        let out = tool_sat("1 0\n", 100_000);
        assert!(out.contains("exhausted"), "{out}");
    }
}
