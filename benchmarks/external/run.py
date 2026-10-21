#!/usr/bin/env python3
"""Differential benchmark round for Axiom and independent solvers.

The harness is intentionally small and explicit. It builds every fixture,
checks the Axiom answer, asks at most one external oracle, and reports a
mismatch as a failure. An oracle that is not installed is reported as skipped;
it is never silently treated as agreement.

Run from the repository root after building `axiom-bench`:

    cargo build --release -p axiom-bench
    python3 benchmarks/external/run.py --axiom target/release/axiom-bench
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import asdict, dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


@dataclass
class Case:
    family: str
    name: str
    expected: object
    axiom: dict | None = None
    oracle: str = ""
    oracle_result: object | None = None
    match: bool | None = None
    skipped: bool = False
    note: str = ""
    display: str = ""


def run(cmd, timeout=120, cwd=None):
    started = time.perf_counter()
    try:
        p = subprocess.run(
            [str(c) for c in cmd],
            cwd=cwd,
            text=True,
            capture_output=True,
            timeout=timeout,
        )
        return {
            "code": p.returncode,
            "stdout": p.stdout,
            "stderr": p.stderr,
            "ms": round((time.perf_counter() - started) * 1000),
        }
    except subprocess.TimeoutExpired as e:
        return {
            "code": None,
            "stdout": e.stdout or "",
            "stderr": f"timeout after {timeout}s",
            "ms": round((time.perf_counter() - started) * 1000),
        }


def axiom_run(binary: Path, args, timeout=120):
    r = run([binary, *args], timeout=timeout)
    fields = {}
    for line in r["stdout"].splitlines():
        if "=" in line:
            k, v = line.split("=", 1)
            fields[k.strip()] = v.strip()
    answer = fields.get("verdict", fields.get("result"))
    r["answer"] = answer
    r["fields"] = fields
    return r


def php_cnf(pigeons: int, holes: int) -> str:
    def var(p, h):
        return p * holes + h + 1

    clauses = []
    for p in range(pigeons):
        clauses.append([var(p, h) for h in range(holes)])
        for h in range(holes):
            for h2 in range(h + 1, holes):
                clauses.append([-var(p, h), -var(p, h2)])
    for h in range(holes):
        for p in range(pigeons):
            for p2 in range(p + 1, pigeons):
                clauses.append([-var(p, h), -var(p2, h)])
    lines = [f"p cnf {pigeons * holes} {len(clauses)}"]
    lines += [" ".join(map(str, c)) + " 0" for c in clauses]
    return "\n".join(lines) + "\n"


def z3_sat(path: Path):
    try:
        import z3  # type: ignore
    except ImportError:
        return None
    clauses = []
    for line in path.read_text().splitlines():
        if not line or line[0] in "cp":
            continue
        lits = [int(x) for x in line.split() if x != "0"]
        clauses.append(lits)
    n = max((abs(x) for c in clauses for x in c), default=0)
    xs = [z3.Bool(f"x{i}") for i in range(1, n + 1)]
    s = z3.Solver()
    for clause in clauses:
        s.add(z3.Or([xs[abs(l) - 1] if l > 0 else z3.Not(xs[abs(l) - 1]) for l in clause]))
    return str(s.check())


def z3_smt(path: Path):
    try:
        import z3  # type: ignore
    except ImportError:
        return None
    text = path.read_text().replace("(check-sat)", "")
    try:
        assertions = z3.parse_smt2_string(text)
    except z3.Z3Exception:
        return "error"
    solver = z3.Solver()
    solver.add(assertions)
    result = solver.check()
    if result == z3.sat:
        return "sat"
    if result == z3.unsat:
        return "unsat"
    return "unknown"


def read_smt_script(path: Path):
    """Read an SMT-LIB script into nested lists, keeping the term structure.

    Only what the harness needs is supported: commands are read as lists, so
    `(assert (<= x 2))` keeps its inner list and can be rendered back
    unchanged.
    """
    text = path.read_text()
    text = "\n".join(line.split(";")[0] for line in text.splitlines())
    tokens = text.replace("(", " ( ").replace(")", " ) ").split()

    def read_expr(index):
        token = tokens[index]
        if token != "(":
            return token, index + 1
        index += 1
        items = []
        while tokens[index] != ")":
            item, index = read_expr(index)
            items.append(item)
        return items, index + 1

    commands = []
    index = 0
    while index < len(tokens):
        command, index = read_expr(index)
        commands.append(command)
    return commands


def render_smt(node) -> str:
    if isinstance(node, str):
        return node
    return "(" + " ".join(render_smt(item) for item in node) + ")"


def z3_smt_script(path: Path):
    """Interpret a small SMT-LIB script (assert/push/pop/check-sat) with Z3.

    The same file that Axiom reads is replayed here, so the two sides answer
    the same sequence of questions.
    """
    try:
        import z3  # type: ignore
    except ImportError:
        return None
    declarations = []
    solver = z3.Solver()
    answers = []
    for command in read_smt_script(path):
        if not isinstance(command, list) or not command:
            continue
        head = command[0]
        if head in ("declare-fun", "declare-const"):
            declarations.append(render_smt(command))
        elif head == "assert":
            source = " ".join(declarations + [render_smt(command)])
            try:
                solver.add(z3.parse_smt2_string(source))
            except z3.Z3Exception:
                # The declarations are already in the context; a repeated
                # declaration is not an error for the assertion itself.
                try:
                    solver.add(z3.parse_smt2_string(render_smt(command)))
                except z3.Z3Exception:
                    return "error"
        elif head == "push":
            solver.push()
        elif head == "pop":
            solver.pop()
        elif head == "check-sat":
            result = solver.check()
            if result == z3.sat:
                answers.append("sat")
            elif result == z3.unsat:
                answers.append("unsat")
            else:
                answers.append("unknown")
    return ",".join(answers) if answers else None


def clingo_count(path: Path, max_models: int = 64):
    try:
        import clingo  # type: ignore
    except ImportError:
        return None
    ctl = clingo.Control([f"--models={max_models}"])
    ctl.add("base", [], path.read_text())
    ctl.ground([("base", [])])
    models = []
    with ctl.solve(yield_=True) as handle:
        for model in handle:
            models.append(model)
    return len(models)


def souffle_contains(program: Path, relation: str, wanted: tuple[str, ...]):
    exe = shutil.which("souffle")
    if not exe:
        return None
    work = program.parent
    r = run([exe, program.name], cwd=work, timeout=120)
    if r["code"] != 0:
        raise RuntimeError(f"souffle failed: {r['stderr']}")
    out = work / f"{relation}.csv"
    if not out.exists():
        raise RuntimeError(f"souffle did not write {out.name}")
    rows = []
    for line in out.read_text().splitlines():
        if line.strip():
            rows.append(tuple(x.strip().strip('"') for x in line.split("\t")))
    return wanted in rows


def fast_downward_plan(domain: Path, problem: Path):
    fd = os.environ.get("FAST_DOWNWARD")
    if not fd:
        fd = shutil.which("fast-downward.py")
    if not fd:
        return None
    work = domain.parent
    r = run(
        [sys.executable, fd, "--alias", "lama-first", domain.name, problem.name],
        cwd=work,
        timeout=180,
    )
    text = r["stdout"] + r["stderr"]
    plan = work / "sas_plan"
    if "Solution found" in text or plan.exists():
        return {"status": "found", "length": plan_length(plan)}
    if "Completely explored" in text or "no solution" in text.lower():
        return {"status": "impossible", "length": None}
    return {"status": "unknown", "length": None, "detail": text[-800:]}


def plan_length(path: Path):
    if not path.exists():
        return None

    def n():
        for line in path.read_text().splitlines():
            line = line.strip()
            if line and not line.startswith(";"):
                yield line

    return sum(1 for _ in n())


def vampire_status(path: Path):
    exe = os.environ.get("VAMPIRE") or shutil.which("vampire")
    if not exe:
        return None
    r = run([exe, "--mode", "casc", "--time_limit", "20", path.name], cwd=path.parent, timeout=40)
    text = r["stdout"] + r["stderr"]
    for line in text.splitlines():
        if "SZS status Theorem" in line:
            return "proved"
        if "SZS status CounterSatisfiable" in line or "SZS status Satisfiable" in line:
            return "not-proved"
        if "SZS status GaveUp" in line or "SZS status Timeout" in line:
            return "unknown"
    return "unknown"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--axiom", default=str(ROOT / "target/release/axiom-bench"))
    ap.add_argument("--out", default=str(ROOT / "benchmarks/external/out"))
    ap.add_argument("--allow-missing-oracles", action="store_true")
    args = ap.parse_args()
    axiom_bin = Path(args.axiom).resolve()
    if not axiom_bin.exists():
        sys.exit(f"missing Axiom binary: {axiom_bin}")

    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    work = Path(tempfile.mkdtemp(prefix="axiom-external-"))
    cases: list[Case] = []

    # ---- SAT: pigeonhole, with Z3 as the oracle -------------------------
    sat_cases = [
        ("php-4-4-sat", 4, 4, "sat"),
        ("php-5-4-unsat", 5, 4, "unsat"),
    ]
    for name, p, h, expected in sat_cases:
        path = work / f"{name}.cnf"
        path.write_text(php_cnf(p, h))
        c = Case("sat", name, expected)
        c.axiom = axiom_run(axiom_bin, ["sat", str(path)])
        c.oracle = "z3"
        c.oracle_result = z3_sat(path)
        c.skipped = c.oracle_result is None
        c.match = None if c.skipped else c.axiom["answer"] == c.oracle_result == expected
        if c.match is False:
            print(f"MISMATCH sat/{name}: axiom={c.axiom['answer']} oracle={c.oracle_result}", file=sys.stderr)
        cases.append(c)

    # ---- ASP: model counts, with clingo as the oracle -------------------
    asp_cases = {
        "choice_one": ("{ p }.", 2),
        "choice_two": ("{ p }. { q }.", 4),
        "negation_split": ("p :- not q. q :- not p.", 2),
        "constraint_eliminates": ("p. :- p.", 0),
        "reachability": (
            "edge(a,b). edge(b,c). path(X,Y) :- edge(X,Y). "
            "path(X,Z) :- path(X,Y), edge(Y,Z).",
            1,
        ),
    }
    for name, (source, expected) in asp_cases.items():
        path = work / f"asp-{name}.lp"
        path.write_text(source + "\n")
        c = Case("asp", name, expected)
        c.axiom = axiom_run(axiom_bin, ["asp", str(path), "64"])
        c.oracle = "clingo"
        c.oracle_result = clingo_count(path)
        c.skipped = c.oracle_result is None
        if c.skipped:
            c.match = None
        else:
            if c.axiom["answer"] == "impossible":
                got = 0
                complete = True
            else:
                try:
                    got = int(c.axiom["fields"].get("models", "-1"))
                except ValueError:
                    got = -1
                complete = c.axiom["fields"].get("complete") == "true"
            c.match = got == c.oracle_result == expected and complete
        if c.match is False:
            print(f"MISMATCH asp/{name}: axiom={c.axiom['fields']} oracle={c.oracle_result}", file=sys.stderr)
        cases.append(c)

    # ---- Datalog: transitive closure and safe negation, Soufflé oracle --
    tc_work = work / "datalog-tc"
    tc_work.mkdir()
    n = 14
    axiom_src = [f"edge(n{i},n{i + 1})." for i in range(n - 1)]
    axiom_src += [
        "path(X,Y) :- edge(X,Y).",
        "path(X,Z) :- path(X,Y), edge(Y,Z).",
    ]
    (tc_work / "tc.dl").write_text("\n".join(axiom_src) + "\n")
    souffle_src = [".decl edge(x:symbol, y:symbol)", ".decl path(x:symbol, y:symbol)"]
    souffle_src += [f'edge("n{i}","n{i + 1}").' for i in range(n - 1)]
    souffle_src += [
        "path(x,y) :- edge(x,y).",
        "path(x,z) :- path(x,y), edge(y,z).",
        ".output path",
    ]
    (tc_work / "tc.dl.souffle").write_text("\n".join(souffle_src) + "\n")
    c = Case("datalog", "transitive_closure", "proved")
    c.axiom = axiom_run(axiom_bin, ["datalog", str(tc_work / "tc.dl"), f"path(n0,n{n-1})"])
    c.oracle = "souffle"
    # Soufflé program has a different file name/extension; run it from a copy.
    sf = tc_work / "tc_souffle.dl"
    shutil.copy(tc_work / "tc.dl.souffle", sf)
    c.oracle_result = souffle_contains(sf, "path", ("n0", f"n{n-1}"))
    c.skipped = c.oracle_result is None
    c.match = None if c.skipped else (c.axiom["answer"] == "proved" and c.oracle_result is True)
    if c.match is False:
        print(f"MISMATCH datalog/{c.name}: axiom={c.axiom['answer']} oracle={c.oracle_result}", file=sys.stderr)
    cases.append(c)

    neg_work = work / "datalog-neg"
    neg_work.mkdir()
    source = "node(a). node(b). blocked(b). safe(X) :- node(X), not blocked(X).\n"
    (neg_work / "neg.dl").write_text(source)
    souffle_neg = [
        ".decl node(x:symbol)",
        ".decl blocked(x:symbol)",
        ".decl safe(x:symbol)",
        'node("a"). node("b"). blocked("b").',
        "safe(x) :- node(x), !blocked(x).",
        ".output safe",
    ]
    (neg_work / "neg_souffle.dl").write_text("\n".join(souffle_neg) + "\n")
    for goal, expected, wanted in [("safe(a)", "proved", ("a",)), ("safe(b)", "refuted", ("b",))]:
        c = Case("datalog", f"safe_negation_{goal[-2]}", expected)
        c.axiom = axiom_run(axiom_bin, ["datalog", str(neg_work / "neg.dl"), goal])
        c.oracle = "souffle"
        present = souffle_contains(neg_work / "neg_souffle.dl", "safe", wanted)
        c.oracle_result = None if present is None else ("proved" if present else "refuted")
        c.skipped = c.oracle_result is None
        c.match = None if c.skipped else c.axiom["answer"] == c.oracle_result == expected
        if c.match is False:
            print(f"MISMATCH datalog/{c.name}: axiom={c.axiom['answer']} oracle={c.oracle_result}", file=sys.stderr)
        cases.append(c)

    # ---- Planning: STRIPS chain, Fast Downward oracle -------------------
    plan_work = work / "planning"
    plan_work.mkdir()
    domain = """(define (domain move)
  (:requirements :strips :negative-preconditions)
  (:predicates (at ?x ?y) (connected ?x ?y))
  (:action move
    :parameters (?x ?from ?to)
    :precondition (and (at ?x ?from) (connected ?from ?to))
    :effect (and (not (at ?x ?from)) (at ?x ?to))))
"""
    nodes = [f"n{i}" for i in range(7)]
    problem = "(define (problem chain) (:domain move)\n"
    problem += "  (:objects " + " ".join(["item", *nodes]) + ")\n"
    problem += "  (:init (at item n0) " + " ".join(f"(connected {a} {b})" for a, b in zip(nodes, nodes[1:])) + ")\n"
    problem += "  (:goal (at item n6)))\n"
    (plan_work / "domain.pddl").write_text(domain)
    (plan_work / "problem.pddl").write_text(problem)
    c = Case("planning", "chain", "found")
    c.axiom = axiom_run(axiom_bin, ["planning", str(plan_work / "domain.pddl"), str(plan_work / "problem.pddl")])
    c.oracle = "fast-downward"
    fd = fast_downward_plan(plan_work / "domain.pddl", plan_work / "problem.pddl")
    c.oracle_result = None if fd is None else fd["status"]
    c.skipped = c.oracle_result is None
    c.match = None if c.skipped else c.axiom["answer"] == c.oracle_result == "found"
    if fd and fd.get("length") is not None:
        c.note = f"fast-downward length={fd['length']}"
    if c.match is False:
        print(f"MISMATCH planning/{c.name}: axiom={c.axiom['answer']} oracle={c.oracle_result}", file=sys.stderr)
    cases.append(c)

    # ---- FOL: implication and equality, Vampire oracle -----------------
    fol_work = work / "fol"
    fol_work.mkdir()
    fol_cases = [
        (
            "implication",
            "axiom P(a) -> Q(a). axiom P(a). goal Q(a).\n",
            "fof(ax1,axiom,(p(a) => q(a))).\nfof(ax2,axiom,p(a)).\nfof(goal,conjecture,q(a)).\n",
        ),
        (
            "equality-substitution",
            "axiom a = b. axiom P(a). goal P(b).\n",
            "fof(ax1,axiom,a=b).\nfof(ax2,axiom,p(a)).\nfof(goal,conjecture,p(b)).\n",
        ),
        (
            "equality-congruence",
            "fun f/1. axiom a = b. goal f(a) = f(b).\n",
            "fof(ax1,axiom,a=b).\nfof(goal,conjecture,f(a)=f(b)).\n",
        ),
    ]
    for name, axiom_src, tptp_src in fol_cases:
        (fol_work / f"{name}.ax").write_text(axiom_src)
        (fol_work / f"{name}.p").write_text(tptp_src)
        c = Case("fol", name, "proved")
        c.axiom = axiom_run(axiom_bin, ["fol", str(fol_work / f"{name}.ax")])
        c.oracle = "vampire"
        c.oracle_result = vampire_status(fol_work / f"{name}.p")
        c.skipped = c.oracle_result is None
        c.match = None if c.skipped else c.axiom["answer"] == c.oracle_result == "proved"
        if c.match is False:
            print(f"MISMATCH fol/{c.name}: axiom={c.axiom['answer']} oracle={c.oracle_result}", file=sys.stderr)
        cases.append(c)

    # ---- SMT: difference logic and equality, Z3 as the oracle ------------
    smt_work = work / "smt"
    smt_work.mkdir()
    smt_cases = [
        (
            "difference-sat",
            "(set-logic QF_IDL)\n"
            "(declare-fun x () Int)\n"
            "(declare-fun y () Int)\n"
            "(assert (<= (- y x) 3))\n"
            "(assert (>= x 0))\n"
            "(assert (<= x 2))\n"
            "(check-sat)\n",
            "found",
        ),
        (
            "difference-unsat",
            "(set-logic QF_IDL)\n"
            "(declare-fun x () Int)\n"
            "(assert (<= x 2))\n"
            "(assert (>= x 5))\n"
            "(check-sat)\n",
            "impossible",
        ),
        (
            "equality-unsat",
            "(set-logic QF_IDL)\n"
            "(declare-fun x () Int)\n"
            "(assert (= x 3))\n"
            "(assert (= x 4))\n"
            "(check-sat)\n",
            "impossible",
        ),
        (
            "congruence-unsat",
            "(set-logic QF_UFIDL)\n"
            "(declare-fun f (Int) Int)\n"
            "(declare-fun a () Int)\n"
            "(declare-fun b () Int)\n"
            "(assert (= a b))\n"
            "(assert (not (= (f a) (f b))))\n"
            "(check-sat)\n",
            "impossible",
        ),
        (
            "boolean-sat",
            "(set-logic QF_IDL)\n"
            "(declare-fun p () Bool)\n"
            "(declare-fun x () Int)\n"
            "(assert (or p (and (<= x 0) (<= (- x 0) 1))))\n"
            "(check-sat)\n",
            "found",
        ),
    ]
    smt_oracle_vocabulary = {"sat": "found", "unsat": "impossible"}
    for name, source, expected in smt_cases:
        path = smt_work / f"{name}.smt2"
        path.write_text(source)
        c = Case("smt", name, expected)
        c.axiom = axiom_run(axiom_bin, ["smt", str(path)])
        c.oracle = "z3"
        raw = z3_smt(path)
        c.oracle_result = None if raw is None else smt_oracle_vocabulary.get(raw, raw)
        c.skipped = c.oracle_result is None
        c.match = None if c.skipped else c.axiom["answer"] == c.oracle_result == expected
        if c.match is False:
            print(f"MISMATCH smt/{name}: axiom={c.axiom['answer']} oracle={c.oracle_result}", file=sys.stderr)
        cases.append(c)

    # ---- SMT: a push/pop session, Z3 replaying the same file -------------
    session_work = work / "smt-session"
    session_work.mkdir()
    session_source = (
        "(set-logic QF_IDL)\n"
        "(declare-fun x () Int)\n"
        "(assert (<= x 2))\n"
        "(assert (>= x 0))\n"
        "(check-sat)\n"
        "(push 1)\n"
        "(assert (>= x 5))\n"
        "(check-sat)\n"
        "(pop 1)\n"
        "(check-sat)\n"
    )
    session_path = session_work / "push-pop.smt2"
    session_path.write_text(session_source)
    c = Case("smt", "push-pop-session", "sat,unsat,sat")
    c.axiom = axiom_run(axiom_bin, ["smt", str(session_path)])
    c.oracle = "z3"
    raw = z3_smt_script(session_path)
    c.oracle_result = None if raw is None else raw
    c.skipped = c.oracle_result is None
    c.match = None if c.skipped else c.axiom["fields"].get("checks") == c.oracle_result == "sat,unsat,sat"
    c.display = c.axiom["fields"].get("checks", "")
    if c.match is False:
        print(
            f"MISMATCH smt/{c.name}: axiom={c.axiom['fields'].get('checks')} oracle={c.oracle_result}",
            file=sys.stderr,
        )
    cases.append(c)

    summary = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "axiom_binary": str(axiom_bin),
        "total": len(cases),
        "matched": sum(1 for c in cases if c.match is True),
        "mismatched": sum(1 for c in cases if c.match is False),
        "skipped": sum(1 for c in cases if c.skipped),
    }
    payload = {"summary": summary, "cases": [asdict(c) for c in cases]}
    (out / "results.json").write_text(json.dumps(payload, indent=2) + "\n")

    lines = [
        "# External differential benchmark round",
        "",
        f"Generated: {summary['generated_at']}",
        "",
        f"- cases: {summary['total']}",
        f"- matched: {summary['matched']}",
        f"- mismatched: {summary['mismatched']}",
        f"- skipped (oracle unavailable): {summary['skipped']}",
        "",
        "| family | case | expected | axiom | oracle | oracle answer | match |",
        "|---|---|---|---|---|---|---|",
    ]
    for c in cases:
        answer = c.display or c.axiom["answer"]
        lines.append(
            f"| {c.family} | {c.name} | {c.expected} | {answer} | {c.oracle} | "
            f"{'' if c.oracle_result is None else c.oracle_result} | "
            f"{'skip' if c.skipped else ('yes' if c.match else 'NO')} |"
        )
    (out / "results.md").write_text("\n".join(lines) + "\n")
    print(json.dumps(summary, indent=2))
    if summary["mismatched"]:
        return 1
    if summary["skipped"] and not args.allow_missing_oracles:
        print("some oracles were unavailable; pass --allow-missing-oracles to accept", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
