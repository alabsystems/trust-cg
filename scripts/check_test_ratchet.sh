#!/usr/bin/env bash
# scripts/check_test_ratchet.sh
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Issue:  Part of #437 (WS1 — Measured workspace pass-count)
#
# Monotonic-pass-count ratchet for the workspace test matrix.
#
# Compares a test-matrix JSON against an explicitly supplied baseline. Fails if:
#   * any `(crate, shard)` pair in the baseline has a lower `passed` count
#     in the current run;
#   * any `(crate, shard)` pair in the baseline has a higher `failed` count
#     in the current run;
#   * any previously-present shard has disappeared (can't silently delete).
#
# New shards in the current run that are not in the baseline are OK — the
# baseline gains coverage monotonically.
#
# Exit codes:
#   0 — current run is at or above baseline on every pair.
#   1 — regression detected.
#   2 — tooling error (missing files, parse error, etc.).
#
# Usage:
#   scripts/check_test_ratchet.sh CURRENT.json BASELINE.json
#
# Refresh baseline after an approved improvement:
#   cp evals/results/tests/<date>.json path/to/reviewed-baseline.json
#
# Note (#446): the canonical implementation has been ported to
# `trust-cg-test ratchet tests` (see crates/trust-cg-test/src/cmd/ratchet.rs).
# This shell wrapper is kept for CI compatibility during the transition
# and produces the same exit-code contract. New workflows should prefer
#   cargo run -p trust-cg-test --quiet -- ratchet tests \
#     --baseline path/to/reviewed-baseline.json
# Pass `--current <PATH>` to override the newest matrix result.

set -euo pipefail

if ! command -v python3 >/dev/null 2>&1; then
    echo "check_test_ratchet: python3 not found on PATH" >&2
    exit 2
fi

if [ "$#" -ne 2 ]; then
    echo "usage: scripts/check_test_ratchet.sh CURRENT.json BASELINE.json" >&2
    echo "check_test_ratchet: an explicit reviewed baseline is required" >&2
    exit 2
fi
CURRENT="$1"
BASELINE="$2"

if [ ! -f "${CURRENT}" ]; then
    echo "check_test_ratchet: current test-matrix JSON missing: ${CURRENT}" >&2
    exit 2
fi

if [ ! -f "${BASELINE}" ]; then
    echo "check_test_ratchet: baseline file missing: ${BASELINE}" >&2
    echo "To seed the selected baseline from the current run for review:" >&2
    echo "  cp ${CURRENT} ${BASELINE}" >&2
    exit 2
fi

python3 - "${CURRENT}" "${BASELINE}" <<'PYEOF'
import json
import sys

cur_path, base_path = sys.argv[1], sys.argv[2]
with open(cur_path) as fh:
    cur = json.load(fh)
with open(base_path) as fh:
    base = json.load(fh)

def index_shards(doc):
    out = {}
    for s in doc.get("shards", []):
        key = (s.get("crate", "?"), s.get("shard", "?"))
        out[key] = s
    return out

cur_ix = index_shards(cur)
base_ix = index_shards(base)

# Issue #624: keep the old integration-jit floor strict while #437 current
# matrices report it as two split shards.
SPLIT_SHARD_MIGRATIONS = {
    ("trust-cg-codegen", "integration-jit"): [
        ("trust-cg-codegen", "integration-jit-runtime"),
        ("trust-cg-codegen", "integration-jit-observability"),
    ],
}

def current_shard_for_baseline(key):
    cur_s = cur_ix.get(key)
    if cur_s is not None:
        return cur_s

    split_keys = SPLIT_SHARD_MIGRATIONS.get(key)
    if split_keys is None:
        return None

    split_shards = []
    for split_key in split_keys:
        split_s = cur_ix.get(split_key)
        if split_s is None:
            return None
        split_shards.append(split_s)

    return {
        "crate": key[0],
        "shard": key[1],
        "passed": sum(int(s.get("passed", 0)) for s in split_shards),
        "failed": sum(int(s.get("failed", 0)) for s in split_shards),
    }

violations = []
missing = []
for key, base_s in base_ix.items():
    cur_s = current_shard_for_baseline(key)
    if cur_s is None:
        missing.append(key)
        continue
    base_pass = int(base_s.get("passed", 0))
    cur_pass = int(cur_s.get("passed", 0))
    base_fail = int(base_s.get("failed", 0))
    cur_fail = int(cur_s.get("failed", 0))
    if cur_pass < base_pass:
        violations.append((key, "passed decreased", base_pass, cur_pass))
    if cur_fail > base_fail:
        violations.append((key, "failed increased", base_fail, cur_fail))

if missing:
    print("test ratchet FAILED: baseline shards missing from current run:")
    for c, s in missing:
        print(f"  {c}/{s}")
    print()

if violations:
    print("test ratchet FAILED: regression detected.")
    print(f"  current:  {cur_path}")
    print(f"  baseline: {base_path}")
    print()
    print(f"{'crate/shard':<42s} {'metric':<20s} {'base':>8s} {'cur':>8s} {'delta':>8s}")
    for (c, s), metric, b, cv in violations:
        print(f"{(c + '/' + s):<42s} {metric:<20s} {b:>8d} {cv:>8d} {cv - b:>+8d}")
    print()
    print("Fix the regression, or refresh the baseline after approval:")
    print(f"  cp {cur_path} {base_path}")
    sys.exit(1)

if missing and not violations:
    sys.exit(1)

cur_pass = int(cur.get("totals", {}).get("passed", 0))
cur_fail = int(cur.get("totals", {}).get("failed", 0))
base_pass = int(base.get("totals", {}).get("passed", 0))
base_fail = int(base.get("totals", {}).get("failed", 0))
print(f"test ratchet OK: passed {cur_pass} >= baseline {base_pass}; failed {cur_fail} <= baseline {base_fail}.")
PYEOF
