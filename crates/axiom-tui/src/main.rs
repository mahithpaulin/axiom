//! axiom-tui: chat with any OpenAI-compatible / Anthropic agent, Axiom local.
//!
//! Loop: user text -> LLM (with an `axiom_prove` tool) -> optional local
//! Axiom execution -> tool result fed back -> final answer rendered.
//! Axiom verdicts keep their honest `Status`; inconclusive answers never
//! render as negatives.

use std::io::Write as _;
use std::time::Duration;

use crossterm::event::{self, Event, KeyCode, KeyModifiers};
use ratatui::layout::{Constraint, Direction, Layout};
use ratatui::style::{Color, Style};
use ratatui::widgets::{Block, Borders, List, ListItem, Paragraph};
use ratatui::Terminal;
use serde_json::{json, Value};

const SYSTEM_PROMPT: &str = "You are a reasoning assistant with one tool: axiom_prove {program: string (Datalog source with facts, rules and at least one ?- query), query_index?: number, max_steps?: number}. Use it for logic, puzzles, or planning questions instead of guessing. Report its status verbatim (proved/refuted/found/impossible/exhausted/unknown); exhausted and unknown are not answers.";

#[derive(Clone, Copy, PartialEq, Eq)]
enum ProviderKind {
    OpenAI,
    Anthropic,
}

impl ProviderKind {
    fn name(self) -> &'static str {
        match self {
            ProviderKind::OpenAI => "openai",
            ProviderKind::Anthropic => "anthropic",
        }
    }
}

struct Config {
    provider: ProviderKind,
    openai_base: String,
    openai_key: String,
    openai_model: String,
    anthropic_key: String,
    anthropic_model: String,
    max_steps: u64,
}

impl Config {
    fn from_env(provider: ProviderKind) -> Self {
        let env = |k: &str| std::env::var(k).unwrap_or_default();
        let max_steps = env("AXIOM_MAX_STEPS").parse::<u64>().unwrap_or(1_000_000);
        Config {
            provider,
            openai_base: {
                let b = env("OPENAI_BASE_URL");
                if b.is_empty() {
                    "https://api.openai.com/v1".to_string()
                } else {
                    b.trim_end_matches('/').to_string()
                }
            },
            openai_key: env("OPENAI_API_KEY"),
            openai_model: {
                let m = env("OPENAI_MODEL");
                if m.is_empty() {
                    "gpt-4o-mini".to_string()
                } else {
                    m
                }
            },
            anthropic_key: env("ANTHROPIC_API_KEY"),
            anthropic_model: {
                let m = env("ANTHROPIC_MODEL");
                if m.is_empty() {
                    "claude-haiku-4-5".to_string()
                } else {
                    m
                }
            },
            max_steps: max_steps.max(1),
        }
    }

    fn model(&self) -> &str {
        match self.provider {
            ProviderKind::OpenAI => &self.openai_model,
            ProviderKind::Anthropic => &self.anthropic_model,
        }
    }
}

struct ChatLine {
    role: String,
    text: String,
}

struct App {
    cfg: Config,
    lines: Vec<ChatLine>,
    input: String,
    status: String,
}

impl App {
    fn push(&mut self, role: &str, text: String) {
        self.lines.push(ChatLine {
            role: role.to_string(),
            text,
        });
        if self.lines.len() > 500 {
            let drop = self.lines.len() - 500;
            self.lines.drain(..drop);
        }
    }
}

fn main() -> Result<(), String> {
    let provider = parse_provider_arg();
    let mut app = App {
        cfg: Config::from_env(provider),
        lines: vec![ChatLine {
            role: "axiom".to_string(),
            text: "axiom-tui: Enter sends, Tab switches provider, Esc quits. Axiom runs locally; the LLM never guesses what Axiom can prove.".to_string(),
        }],
        input: String::new(),
        status: String::new(),
    };

    let mut stdout = std::io::stdout();
    crossterm::terminal::enable_raw_mode().map_err(err_str)?;
    let backend = ratatui::backend::CrosstermBackend::new(&mut stdout);
    let mut terminal = Terminal::new(backend).map_err(err_str)?;
    let out = run_loop(&mut terminal, &mut app);
    drop(terminal);
    let _ = crossterm::terminal::disable_raw_mode();
    let _ = writeln!(stdout);
    out
}

type Anyhow = Result<(), String>;

fn err_str<E: std::fmt::Display>(e: E) -> String {
    e.to_string()
}

fn parse_provider_arg() -> ProviderKind {
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        if a == "--provider" {
            if let Some(v) = args.next() {
                if v.eq_ignore_ascii_case("anthropic") {
                    return ProviderKind::Anthropic;
                }
            }
        }
    }
    ProviderKind::OpenAI
}

fn run_loop<B>(terminal: &mut Terminal<B>, app: &mut App) -> Anyhow
where
    B: ratatui::backend::Backend,
{
    loop {
        terminal
            .draw(|f| {
                let chunks = Layout::default()
                    .direction(Direction::Vertical)
                    .constraints([
                        Constraint::Min(3),
                        Constraint::Length(3),
                        Constraint::Length(1),
                    ])
                    .split(f.area());
                let items: Vec<ListItem> = app
                    .lines
                    .iter()
                    .map(|l| ListItem::new(format!("[{}] {}", l.role, l.text)))
                    .collect();
                let list =
                    List::new(items).block(Block::default().borders(Borders::ALL).title(format!(
                        "axiom-tui · {} · {}",
                        app.cfg.provider.name(),
                        app.cfg.model()
                    )));
                f.render_widget(list, chunks[0]);
                let prompt = Paragraph::new(app.input.as_str())
                    .block(Block::default().borders(Borders::ALL).title("message"));
                f.render_widget(prompt, chunks[1]);
                let bar =
                    Paragraph::new(app.status.as_str()).style(Style::default().fg(Color::DarkGray));
                f.render_widget(bar, chunks[2]);
            })
            .map_err(err_str)?;
        if !event::poll(Duration::from_millis(100)).map_err(err_str)? {
            continue;
        }
        let Event::Key(k) = event::read().map_err(err_str)? else {
            continue;
        };
        match k.code {
            KeyCode::Esc => return Ok(()),
            KeyCode::Char('c') if k.modifiers.contains(KeyModifiers::CONTROL) => {
                return Ok(());
            }
            KeyCode::Tab => {
                app.cfg.provider = match app.cfg.provider {
                    ProviderKind::OpenAI => ProviderKind::Anthropic,
                    ProviderKind::Anthropic => ProviderKind::OpenAI,
                };
                app.status = format!("provider: {}", app.cfg.provider.name());
            }
            KeyCode::Enter => {
                let text = std::mem::take(&mut app.input);
                if text.trim().is_empty() {
                    continue;
                }
                app.push("you", text.clone());
                app.status = "thinking…".to_string();
                match answer_once(app, &text) {
                    Ok(reply) => {
                        app.push("agent", reply);
                        app.status.clear();
                    }
                    Err(e) => {
                        app.push("error", e.clone());
                        app.status = e;
                    }
                }
            }
            KeyCode::Backspace => {
                app.input.pop();
            }
            KeyCode::Char(c) => {
                if !k.modifiers.contains(KeyModifiers::CONTROL) {
                    app.input.push(c);
                }
            }
            _ => {}
        }
    }
}

/// One agent turn, including at most one Axiom tool round-trip.
fn answer_once(app: &App, user: &str) -> Result<String, String> {
    match app.cfg.provider {
        ProviderKind::OpenAI => openai_turn(app, user),
        ProviderKind::Anthropic => anthropic_turn(app, user),
    }
}

// ---- local Axiom execution (direct crate call, not a subprocess) ----------

fn axiom_prove_tool(args: &Value, default_steps: u64) -> String {
    let program = args
        .get("program")
        .and_then(Value::as_str)
        .unwrap_or_default();
    let q = args.get("query_index").and_then(Value::as_u64).unwrap_or(0) as usize;
    let steps = args
        .get("max_steps")
        .and_then(Value::as_u64)
        .unwrap_or(default_steps);
    let parsed = match axiom::exterior::parse(program) {
        Ok(p) => p,
        Err(e) => return format!("{{\"status\":\"exhausted\",\"summary\":\"parse error: {e}\"}}"),
    };
    if parsed.queries.is_empty() {
        return "{\"status\":\"exhausted\",\"summary\":\"no ?- query in program\"}".to_string();
    }
    if q >= parsed.queries.len() {
        return "{\"status\":\"exhausted\",\"summary\":\"query_index out of range\"}".to_string();
    }
    let goal = parsed.queries[q];
    let mut solver = axiom::Solver::new(parsed.program);
    let mut budget = axiom::Budget::steps(steps.max(1));
    let out = solver.prove(goal, &mut budget);
    let verified = out.proof.as_ref().is_some_and(|p| solver.verify(p).is_ok());
    let summary = format!("{} after {} steps", out.status, budget.spent());
    json!({
        "status": out.status.to_string(),
        "summary": summary,
        "steps": budget.spent(),
        "proof_present": out.proof.is_some(),
        "verified": verified,
    })
    .to_string()
}

// ---- OpenAI-compatible ----------------------------------------------------

fn openai_tool_spec() -> Value {
    json!({
        "type": "function",
        "function": {
            "name": "axiom_prove",
            "description": "Prove a query over Datalog source with Axiom. Returns status/summary/steps/proof_present/verified.",
            "parameters": {
                "type": "object",
                "properties": {
                    "program": {"type": "string", "description": "Datalog source with facts, rules and at least one ?- query."},
                    "query_index": {"type": "number"},
                    "max_steps": {"type": "number"}
                },
                "required": ["program"]
            }
        }
    })
}

fn http_post(url: &str, headers: &[(&str, String)], body: &str) -> Result<String, String> {
    let mut req = ureq::post(url).timeout(Duration::from_secs(120));
    for (k, v) in headers.iter() {
        req = req.set(*k, v.as_str());
    }
    let resp = req.send_string(body).map_err(|e| format!("http: {e}"))?;
    resp.into_string().map_err(|e| format!("read body: {e}"))
}

fn openai_turn(app: &App, user: &str) -> Result<String, String> {
    let url = format!("{}/chat/completions", app.cfg.openai_base);
    let mut headers = vec![("Content-Type".to_string(), "application/json".to_string())];
    if !app.cfg.openai_key.is_empty() {
        headers.push((
            "Authorization".to_string(),
            format!("Bearer {}", app.cfg.openai_key),
        ));
    }
    let headers_ref: Vec<(&str, String)> = headers
        .iter()
        .map(|(k, v)| (k.as_str(), v.clone()))
        .collect();
    let first = json!({
        "model": app.cfg.openai_model,
        "messages": [
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": user},
        ],
        "tools": [openai_tool_spec()],
        "tool_choice": "auto",
    })
    .to_string();
    let text = http_post(&url, &headers_ref, &first)?;
    let v: Value = serde_json::from_str(&text).map_err(|e| format!("bad json: {e}"))?;
    if let Some(err) = v.get("error") {
        return Err(format!("provider: {err}"));
    }
    let msg = &v["choices"][0]["message"];
    let calls = msg
        .get("tool_calls")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    let axiom_calls: Vec<&Value> = calls
        .iter()
        .filter(|c| c["function"]["name"].as_str() == Some("axiom_prove"))
        .collect();
    if axiom_calls.is_empty() {
        let content = msg
            .get("content")
            .and_then(Value::as_str)
            .unwrap_or("(empty reply)")
            .to_string();
        return Ok(content);
    }
    // Slice 1: single tool round-trip.
    let call = axiom_calls[0];
    let id = call["id"].as_str().unwrap_or("call-1").to_string();
    let args: Value = call["function"]["arguments"]
        .as_str()
        .and_then(|s| serde_json::from_str(s).ok())
        .unwrap_or(json!({}));
    let result = axiom_prove_tool(&args, app.cfg.max_steps);
    let second = json!({
        "model": app.cfg.openai_model,
        "messages": [
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": user},
            {"role": "assistant", "tool_calls": calls},
            {"role": "tool", "tool_call_id": id, "content": result},
        ],
    })
    .to_string();
    let text2 = http_post(&url, &headers_ref, &second)?;
    let v2: Value = serde_json::from_str(&text2).map_err(|e| format!("bad json: {e}"))?;
    Ok(v2["choices"][0]["message"]["content"]
        .as_str()
        .unwrap_or("(empty reply)")
        .to_string())
}

// ---- Anthropic native -----------------------------------------------------

fn anthropic_tool_spec() -> Value {
    json!({
        "name": "axiom_prove",
        "description": "Prove a query over Datalog source with Axiom. Returns status/summary/steps/proof_present/verified.",
        "input_schema": {
            "type": "object",
            "properties": {
                "program": {"type": "string", "description": "Datalog source with facts, rules and at least one ?- query."},
                "query_index": {"type": "number"},
                "max_steps": {"type": "number"}
            },
            "required": ["program"]
        }
    })
}

fn anthropic_turn(app: &App, user: &str) -> Result<String, String> {
    if app.cfg.anthropic_key.is_empty() {
        return Err("ANTHROPIC_API_KEY is not set".to_string());
    }
    let url = "https://api.anthropic.com/v1/messages".to_string();
    let headers = vec![
        ("Content-Type", "application/json".to_string()),
        ("x-api-key", app.cfg.anthropic_key.clone()),
        ("anthropic-version", "2023-06-01".to_string()),
    ];
    let headers_ref: Vec<(&str, String)> = headers.iter().map(|(k, v)| (*k, v.clone())).collect();
    let first = json!({
        "model": app.cfg.anthropic_model,
        "max_tokens": 1024,
        "system": SYSTEM_PROMPT,
        "messages": [{"role": "user", "content": user}],
        "tools": [anthropic_tool_spec()],
    })
    .to_string();
    let text = http_post(&url, &headers_ref, &first)?;
    let v: Value = serde_json::from_str(&text).map_err(|e| format!("bad json: {e}"))?;
    if v.get("error").is_some() {
        return Err(format!("provider: {}", v["error"]));
    }
    let content = v
        .get("content")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    let tool = content.iter().find(|b| {
        b.get("type").and_then(Value::as_str) == Some("tool_use")
            && b.get("name").and_then(Value::as_str) == Some("axiom_prove")
    });
    let Some(tool) = tool else {
        let txt = content
            .iter()
            .filter_map(|b| b.get("text").and_then(Value::as_str))
            .collect::<Vec<_>>()
            .join("");
        if txt.is_empty() {
            return Ok("(empty reply)".to_string());
        }
        return Ok(txt);
    };
    let id = tool["id"].as_str().unwrap_or("tool-1").to_string();
    let args = tool.get("input").cloned().unwrap_or(json!({}));
    let result = axiom_prove_tool(&args, app.cfg.max_steps);
    let second = json!({
        "model": app.cfg.anthropic_model,
        "max_tokens": 1024,
        "system": SYSTEM_PROMPT,
        "messages": [
            {"role": "user", "content": user},
            {"role": "assistant", "content": content},
            {"role": "user", "content": [{"type": "tool_result", "tool_use_id": id, "content": result}]},
        ],
    })
    .to_string();
    let text2 = http_post(&url, &headers_ref, &second)?;
    let v2: Value = serde_json::from_str(&text2).map_err(|e| format!("bad json: {e}"))?;
    let c2 = v2
        .get("content")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    Ok(c2
        .iter()
        .filter_map(|b| b.get("text").and_then(Value::as_str))
        .collect::<Vec<_>>()
        .join(""))
}
