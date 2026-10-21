//! Small process boundary used by `benchmarks/external/run.py`.
//!
//! It is deliberately not a shell-out wrapper around tests: each invocation
//! parses one fixture, runs one engine, and prints a machine-readable one-line
//! result plus deterministic counters. The external harness compares that line
//! with an independent oracle's answer.

use axiom::sat::parse_dimacs;
use axiom::{Budget, SatOutcome, SatSolver};
use axiom_asp::AspEngine;
use axiom_core::{DatalogEngine, Engine, Problem, Verdict};
use axiom_planning::PlanningEngine;
use axiom_prover::FolEngine;
use axiom_smt::SmtEngine;
use std::process::ExitCode;

fn usage() -> ! {
    eprintln!(
        "usage: axiom-bench sat <dimacs> | datalog <source> [goal] | \
         asp <source> [max_models] | planning <domain> <problem> | fol <source> | \
         smt <source>"
    );
    std::process::exit(2);
}

fn read(path: &str) -> Result<String, String> {
    std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))
}

fn field(payload: &str, key: &str) -> Option<String> {
    payload.split(';').find_map(|f| {
        let (k, v) = f.split_once('=')?;
        (k == key).then(|| v.to_string())
    })
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some(command) = args.first().map(String::as_str) else {
        usage();
    };
    match command {
        "sat" => {
            let path = args.get(1).ok_or("sat needs a DIMACS path")?;
            let source = read(path)?;
            let (nvars, clauses) = parse_dimacs(&source).map_err(|e| e.to_string())?;
            let mut sat = SatSolver::new();
            for _ in 0..nvars {
                sat.new_var();
            }
            for clause in &clauses {
                sat.add_clause(clause);
            }
            let mut budget = Budget::steps(100_000_000);
            match sat.solve(&mut budget).map_err(|e| e.to_string())? {
                SatOutcome::Sat { .. } => println!("result=sat"),
                SatOutcome::Unsat { .. } => println!("result=unsat"),
            }
            println!("steps={}", budget.spent());
        }
        "datalog" => {
            let path = args.get(1).ok_or("datalog needs a source path")?;
            let goal = args.get(2).cloned();
            let source = read(path)?;
            let problem = Problem::datalog(source, goal);
            let mut engine = DatalogEngine::new();
            let mut budget = Budget::steps(100_000_000);
            let out = engine.solve(&problem, &mut budget);
            println!("verdict={}", out.verdict.as_str());
            println!("steps={}", out.stats.steps);
            println!("derivations={}", out.stats.get("derivations").unwrap_or(0));
            if out.verdict == Verdict::Error {
                println!("notes={}", out.notes.join(" ").replace(';', ","));
            }
        }
        "asp" => {
            let path = args.get(1).ok_or("asp needs a source path")?;
            let max_models = args
                .get(2)
                .map(|s| s.parse::<usize>())
                .transpose()
                .map_err(|_| "bad max_models")?
                .unwrap_or(64);
            let source = read(path)?;
            let problem = Problem::asp(source, max_models);
            let mut engine = AspEngine::new();
            let mut budget = Budget::steps(100_000_000);
            let out = engine.solve(&problem, &mut budget);
            println!("verdict={}", out.verdict.as_str());
            if let Some(e) = &out.evidence {
                println!("models={}", field(&e.payload, "count").unwrap_or_default());
                println!(
                    "complete={}",
                    field(&e.payload, "complete").unwrap_or_default()
                );
            }
            println!("steps={}", out.stats.steps);
        }
        "planning" => {
            let domain = read(args.get(1).ok_or("planning needs a domain path")?)?;
            let problem = read(args.get(2).ok_or("planning needs a problem path")?)?;
            let p = Problem::planning(domain, problem);
            let mut engine = PlanningEngine::new();
            let mut budget = Budget::steps(100_000_000);
            let out = engine.solve(&p, &mut budget);
            println!("verdict={}", out.verdict.as_str());
            if let Some(e) = &out.evidence {
                if let Some(len) = field(&e.payload, "length") {
                    println!("length={len}");
                }
            }
            println!("expanded={}", out.stats.get("expanded").unwrap_or(0));
            println!("states={}", out.stats.get("states").unwrap_or(0));
        }
        "fol" => {
            let path = args.get(1).ok_or("fol needs a source path")?;
            let source = read(path)?;
            let problem = Problem::fol(source);
            let mut engine = FolEngine::new();
            let mut budget = Budget::steps(100_000_000);
            let out = engine.solve(&problem, &mut budget);
            println!("verdict={}", out.verdict.as_str());
            println!("steps={}", out.stats.steps);
        }
        "smt" => {
            let path = args.get(1).ok_or("smt needs a source path")?;
            let source = read(path)?;
            let problem = Problem::smt(source);
            let mut engine = SmtEngine::new();
            let mut budget = Budget::steps(100_000_000);
            let out = engine.solve(&problem, &mut budget);
            println!("verdict={}", out.verdict.as_str());
            println!("steps={}", out.stats.steps);
        }
        _ => usage(),
    }
    Ok(())
}
