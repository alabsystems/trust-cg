#!/usr/bin/env bash
#
# scripts/summarize_llvm_test_suite.sh — WS2 weekly-report hook.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# Reads an evals JSON produced by run_llvm_test_suite.sh and emits a
# Markdown summary on stdout. Called automatically at the end of
# run_llvm_test_suite.sh to refresh reports/llvm-test-suite-latest.md.
#
# Usage:
#   scripts/summarize_llvm_test_suite.sh <path-to-eval.json>
#
# If no argument is given the script picks the newest JSON from
# evals/results/llvm-test-suite/.

set -u
set -o pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
JSON="${1:-}"

if [[ -z "$JSON" ]]; then
    JSON="$(ls -t "$REPO_ROOT"/evals/results/llvm-test-suite/*.json 2>/dev/null | head -1)"
fi
if [[ -z "$JSON" || ! -f "$JSON" ]]; then
    echo "no llvm-test-suite eval JSON found" >&2
    exit 1
fi

python3 - "$JSON" <<'PY'
import json, os, sys

path = sys.argv[1]
with open(path) as fh:
    data = json.load(fh)

metrics = data.get("metrics", {})
passed = metrics.get("passed", 0)
total = metrics.get("total", 0)
items = data.get("items", [])
ts = data.get("timestamp", "?")
commit = data.get("commit", "?")
clang = data.get("clang_version", "?")

# Bucket statuses so the report tells us *why* the unsupporteds aren't
# passing. That's the whole point of the corpus: a truthful per-reason
# count drives the next importer expansion.
buckets = {}
for it in items:
    buckets.setdefault(it.get("status", "?"), []).append(it)

print("# llvm-test-suite SingleSource — latest run")
print()
print(f"- source: `{os.path.basename(path)}`")
print(f"- timestamp: {ts}")
print(f"- commit: {commit}")
print(f"- clang: {clang}")
print()
print(f"**Pass rate: {passed} / {total}**")
print()
print("| status | count |")
print("| --- | --- |")
for status in ("pass", "fail", "unsupported", "crash"):
    n = len(buckets.get(status, []))
    print(f"| {status} | {n} |")
print()
print("## Per-program breakdown")
print()
print("| program | status | reason / output |")
print("| --- | --- | --- |")
for it in items:
    name = it.get("name", "?")
    status = it.get("status", "?")
    reason = it.get("reason") or it.get("stdout_head") or ""
    # Keep cells short so GitHub renders the table.
    reason = reason.replace("|", "\\|").replace("\n", " ")
    if len(reason) > 80:
        reason = reason[:77] + "..."
    print(f"| `{name}` | {status} | {reason} |")
print()
print("## Notes")
print()
print("- `unsupported` is the designed signal for a construct the importer")
print("  or codegen pipeline does not yet translate; inspect the per-program")
print("  reason above for the exact coverage gap.")
print("- `crash` marks a true failure (parser panic, clang error,")
print("  link/run failure). Crashes should never be counted as passes.")
PY
