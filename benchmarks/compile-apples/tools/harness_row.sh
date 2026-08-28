#!/usr/bin/env bash
# One authoritative evidence row: benchmarks/beat-llvm/run.py with --cold (so
# all seven contract gates are evaluated), then the ratchet stamp. Run ONCE per
# landed change on a quiet box with a clean tree and a dylib built from HEAD;
# never re-run to fish for a favourable row.
#   usage: harness_row.sh [REPO=.] [DYLIB=target-bridge/release/librustc_codegen_trust_cg.so]
set -euo pipefail
export PATH="$HOME/.cargo/bin:$HOME/.rustup/toolchains/stable-aarch64-unknown-linux-gnu/lib/rustlib/aarch64-unknown-linux-gnu/bin/gcc-ld:$PATH"
REPO=${1:-$(cd "$(dirname "$0")/../../.." && pwd)}
DYLIB=${2:-$REPO/crates/rustc-codegen-trust-cg/target-bridge/release/librustc_codegen_trust_cg.so}
TARGET=${TCG_TARGET:-aarch64-unknown-linux-gnu}
cd "$REPO"
if ! git diff --quiet || ! git diff --cached --quiet; then
  echo "refusing evidence run from a dirty tracked tree" >&2
  exit 1
fi
if [[ ! -f "$DYLIB" ]]; then
  echo "backend dylib not found: $DYLIB" >&2
  exit 1
fi
LOAD=$(cut -d' ' -f1-3 /proc/loadavg 2>/dev/null || uptime)
echo "tree: $(git log --oneline -1)  target: $TARGET  load: $LOAD"
MARKER=$(mktemp)
LOG=$(mktemp)
trap 'rm -f "$MARKER" "$LOG"' EXIT
python3 benchmarks/beat-llvm/run.py --cold --repo "$REPO" --dylib "$DYLIB" --target "$TARGET" 2>&1 | tee "$LOG"
grep -E 'headline|geomean|MISMATCH|INCOMPLETE|results/|FATAL|error' "$LOG" || true
J=$(find benchmarks/beat-llvm/results -type f -name '*.json' -newer "$MARKER" -print -quit)
if [[ -z "$J" ]]; then
  echo "benchmark completed without producing a fresh result JSON" >&2
  exit 1
fi
echo "results: $J"
python3 benchmarks/beat-llvm/contract/check_gates.py "$J" | grep -E 'PASS|FAIL|ELIGIBLE'
python3 scripts/check_perf_ratchet.py --append "$J" 2>&1 | tail -2
