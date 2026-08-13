#!/usr/bin/env python3
"""Evaluate the gates.json predicates against a beat-llvm results JSON — no dependencies.

The predicates are written in a jq-compatible conjunction subset:
    .path.to.field OP literal [and .path OP literal ...]
where OP is one of == != <= >= < > and literal is a number, `null`, `true`, `false`,
or a double-quoted string. `jq '<predicate>' results.json` gives identical verdicts
on hosts that have jq; this checker exists because the x86 Mac does not.

Usage: python3 check_gates.py <results.json> [gates.json]
Exit:  0 = all ELIGIBLE gates evaluated (verdicts printed; gates are goals, not ratchets —
           failing a parity gate is expected during the climb)
       2 = run is INELIGIBLE (LOADED/dirty/mismatch/gate-off) or input/predicate error
"""
import json
import re
import sys
from pathlib import Path

TOKEN = re.compile(r'\s*(\.[A-Za-z_][A-Za-z0-9_.]*|==|!=|<=|>=|<|>|and\b|null\b|true\b|false\b|"[^"]*"|-?\d+(?:\.\d+)?)')


def tokenize(pred):
    out, i = [], 0
    while i < len(pred):
        m = TOKEN.match(pred, i)
        if not m:
            if pred[i:].strip():
                raise ValueError(f"unparseable predicate at: {pred[i:]!r}")
            break
        out.append(m.group(1))
        i = m.end()
    return out


def literal(tok):
    if tok == "null":
        return None
    if tok == "true":
        return True
    if tok == "false":
        return False
    if tok.startswith('"'):
        return tok[1:-1]
    return float(tok) if "." in tok else int(tok)


def lookup(doc, path):
    cur = doc
    for part in path[1:].split("."):
        if not isinstance(cur, dict) or part not in cur:
            return None
        cur = cur[part]
    return cur


def evaluate(pred, doc):
    toks = tokenize(pred)
    result, i = True, 0
    while i < len(toks):
        lhs, op, rhs = toks[i], toks[i + 1], toks[i + 2]
        i += 3
        if i < len(toks):
            if toks[i] != "and":
                raise ValueError(f"only 'and' conjunctions supported, got {toks[i]!r}")
            i += 1
        l = lookup(doc, lhs) if lhs.startswith(".") else literal(lhs)
        r = lookup(doc, rhs) if rhs.startswith(".") else literal(rhs)
        if op == "==":
            ok = l == r
        elif op == "!=":
            ok = l != r
        else:
            if l is None or r is None:
                ok = False  # jq: null comparisons with <=/< are ordered, but a missing metric must never pass a gate
            else:
                ok = {"<=": l <= r, ">=": l >= r, "<": l < r, ">": l > r}[op]
        result = result and ok
    return result


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(2)
    results = json.load(open(sys.argv[1]))
    gates_path = sys.argv[2] if len(sys.argv) > 2 else str(Path(__file__).parent / "gates.json")
    gates = json.load(open(gates_path))
    if not evaluate(gates["eligibility"], results):
        p = results.get("provenance", {})
        print(f"INELIGIBLE run (load_status={p.get('load_status')}, dirty={p.get('git_dirty')}, "
              f"mismatches={results.get('aggregates', {}).get('mismatch_count')}, "
              f"headline_eligible={results.get('headline_eligible')}) — verdicts below are informational only:")
        eligible = False
    else:
        print("run is ELIGIBLE (quiet, clean tree, default gates, 0 MISMATCH)")
        eligible = True
    for name, g in gates["gates"].items():
        v = evaluate(g["predicate"], results)
        print(f"  {'PASS' if v else 'fail'}  {name}  — {g['description']}")
    sys.exit(0 if eligible else 2)


if __name__ == "__main__":
    main()
