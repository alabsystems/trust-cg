#!/usr/bin/env python3
"""Re-apply the harness's round-1 library rules to the retained 2026-10-14 run.

Usage: rescore_object_rule.py <trust-cg checkout> <results.json> <out-prefix>

The run in l14p7-real-corpus/real-corpus/ was measured by the harness at
efc47d3bc, which counted a library compile that exited 0 as COMPILED even when
it wrote no object. The round-1 harness (benchmarks/real-corpus/run.py) makes
that compile an ERROR row (and the LLVM lane's a BASELINE-FAILED row), flags a
library whose LLVM object holds 0 code bytes as vacuous, and reports the
completions with code. Every input those rules need is in the retained samples
(each successful library compile kept its `code_bytes`, None when no readable
object was written), so this script recomputes the outcomes, ratios and
aggregates with the harness's own functions (object_problem, row_ratios,
aggregates). It compiles and measures nothing, and the run's eligibility does
not change: it stays not evidence for the reasons the run itself names.
"""
import hashlib
import importlib.util
import json
import sys
from pathlib import Path

repo, source, prefix = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
spec = importlib.util.spec_from_file_location("rc", repo / "benchmarks/real-corpus/run.py")
rc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(rc)
data = json.loads(source.read_text())
lane_keys = {"bridge": "outcome", "diagnostic": "diagnostic_outcome"}
changes = []
for row in data["rows"]:
    lanes = row.get("lanes") or {}
    if row["crate_type"] != "lib" or "llvm" not in lanes or row.get("outcome") == "BASELINE-FAILED":
        continue
    llvm_problem = next((rc.object_problem(s) for s in lanes["llvm"]["samples"] if rc.object_problem(s)), None)
    if llvm_problem:
        for lane, key in lane_keys.items():
            if key in row:
                changes.append((row["id"], lane, row[key], "BASELINE-FAILED", f"LLVM lane: {llvm_problem}"))
                row[key] = "BASELINE-FAILED"
        continue
    row["vacuous"] = lanes["llvm"].get("code_bytes") == 0
    for lane, key in lane_keys.items():
        if row.get(key) != "COMPILED":
            continue
        record = lanes[lane]
        problem = next((rc.object_problem(s) for s in [record["attempts"][0], *record["samples"]]
                        if rc.object_problem(s)), None)
        if problem:
            changes.append((row["id"], lane, row[key], "ERROR", problem))
            row[key] = "ERROR"
            record["error"] = problem
    row["ratios"] = {lane: rc.Harness.row_ratios(row, lane) for lane, key in lane_keys.items()
                     if row.get(key) in rc.COMPLETED}
aggregates = {lane: rc.Harness.aggregates(data["rows"], key, lane) for lane, key in lane_keys.items()
              if lane in data["aggregates"]}
out = {"schema": "trust-cg-real-corpus-rescore-v1",
       "source": {"path": str(source.name), "sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                  "git_sha": data["provenance"]["git_sha"], "eligible": data["eligible"],
                  "ineligible_reasons": data["ineligible_reasons"]},
       "rules": "benchmarks/real-corpus/run.py object_problem (a library compile that exits 0 without a "
                "readable object is ERROR; the LLVM lane's is BASELINE-FAILED), vacuous rows "
                "(LLVM object holds 0 code bytes; no code-bytes ratio), completions with code",
       "reclassified": [{"id": i, "lane": l, "from": a, "to": b, "why": w} for i, l, a, b, w in changes],
       "vacuous_rows": [r["id"] for r in data["rows"] if r.get("vacuous")],
       "aggregates": aggregates}
Path(f"{prefix}.json").write_text(json.dumps(out, indent=1, sort_keys=True) + "\n")
fmt = rc.fmt
lines = [f"# Re-scored under the round-1 library rules: `{source.name}`", "",
         "Computed from the retained samples by `commands/rescore_object_rule.py`; nothing was "
         "re-measured. The run stays not evidence: " + "; ".join(data["ineligible_reasons"]) + ".", "",
         "| row | lane | as run | re-scored | why |", "| --- | --- | --- | --- | --- |"]
lines += [f"| {i} | {l} | {a} | {b} | {w} |" for i, l, a, b, w in changes]
lines += ["", "Vacuous rows (LLVM's `-O3` object holds no code): "
          + ", ".join(f"`{i}`" for i in out["vacuous_rows"]), ""]
for lane, a in aggregates.items():
    lines += [f"## {lane} lane: {a['completed']} of {a['rows']} rows completed ({a['completion_pct']}%), "
              f"{a['completed_with_code']} with code ({a['completion_with_code_pct']}%)", "",
              "| outcome | rows |", "| --- | ---: |"]
    lines += [f"| {o} | {c} |" for o, c in a["counts"].items() if c]
    lines += ["", "| kind | rows | completed | % |", "| --- | ---: | ---: | ---: |"]
    lines += [f"| {k} | {v['rows']} | {v['completed']} | {v['completion_pct']} |" for k, v in a["by_kind"].items()]
    if a["ratios"]:
        lines += ["", "| ratio vs LLVM (completed rows) | geomean | worst | rows |", "| --- | ---: | ---: | ---: |"]
        lines += [f"| {k} | {fmt(v['geomean'])} | {fmt(v['worst'])} | {v['rows']} |" for k, v in a["ratios"].items()]
    lines.append("")
Path(f"{prefix}.md").write_text("\n".join(lines))
print(f"{len(changes)} reclassified; " + "; ".join(
    f"{lane} {a['completed']}/{a['rows']} ({a['completed_with_code']} with code)" for lane, a in aggregates.items()))
