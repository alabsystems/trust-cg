#!/usr/bin/env bash
# gen_aarch64_nzcv_silicon_truth.sh — REGENERATOR for aarch64_nzcv_silicon_truth.json.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# Builds gen_aarch64_nzcv_silicon_truth.c NATIVELY for the host AArch64 CPU,
# runs it, and writes the committed fixture aarch64_nzcv_silicon_truth.json.
# Each fact executes one instruction between MSR NZCV and MRS NZCV in a single
# inline-asm block (see the harness header). The CPU, hardware model, OS and
# compiler recorded in the fixture header come from this host.
#
# Usage:
#   crates/trust-cg-verify/tests/fixtures/gen_aarch64_nzcv_silicon_truth.sh [OUT]
# (run from anywhere; paths are resolved relative to this script).
#
# OUT defaults to the committed fixture, which records the Apple silicon the
# bridge test and the documentation name. On any other host (for example the
# Linux AArch64 host) pass an explicit OUT so that recording does not replace
# the committed one, then replay it with
#   TCG_NZCV_SILICON_TRUTH=OUT cargo test -p trust-cg-verify \
#     --test aarch64_nzcv_silicon_bridge
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SRC="$HERE/gen_aarch64_nzcv_silicon_truth.c"
BIN="$(mktemp -t gen_aarch64_nzcv_silicon_truth.XXXXXX)"
OUT="${1:-$HERE/aarch64_nzcv_silicon_truth.json}"
trap 'rm -f "$BIN"' EXIT

case "$(uname -m)" in
  arm64 | aarch64) ;;
  *)
    echo "ERROR: this generator must run natively on an AArch64 host (uname -m = $(uname -m))" >&2
    exit 1
    ;;
esac

if [ "$(uname -s)" = "Darwin" ]; then
  CPU="$(sysctl -n machdep.cpu.brand_string 2>/dev/null || echo unknown)"
  MODEL="$(sysctl -n hw.model 2>/dev/null || echo unknown)"
  OS="macOS $(sw_vers -productVersion 2>/dev/null || echo unknown) build $(sw_vers -buildVersion 2>/dev/null || echo unknown)"
else
  CPU="$(awk -F: '/^(model name|CPU part|CPU implementer)/ && !seen[$1]++ {gsub(/^ +/, "", $2); printf "%s%s", sep, $2; sep=" / "}' /proc/cpuinfo 2>/dev/null || echo unknown)"
  MODEL="$(cat /sys/firmware/devicetree/base/model 2>/dev/null | tr -d '\0' || echo unknown)"
  OS="$(uname -sr)"
fi
CC_BIN="${CC:-cc}"
CC_VER="$("$CC_BIN" --version 2>/dev/null | head -n 1 || echo unknown)"
DATE="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

echo "Building $SRC natively with $CC_BIN ..." >&2
"$CC_BIN" -O0 -Wall -Wextra -Werror -o "$BIN" "$SRC"

echo "Recording on: $CPU ($MODEL), $OS" >&2
"$BIN" "$CPU" "$MODEL" "$OS" "$CC_VER" "$DATE" > "$OUT"

python3 - "$OUT" <<'PY'
import json, sys
doc = json.load(open(sys.argv[1]))
facts = doc["facts"]
per_op = {}
for fact in facts:
    per_op[fact["op"]] = per_op.get(fact["op"], 0) + 1
acct = doc["_accounting"]
assert acct["facts"] == len(facts), (acct["facts"], len(facts))
assert acct["per_op"] == per_op, (acct["per_op"], per_op)
print("OK facts=%d per_op=%s" % (len(facts), per_op), file=sys.stderr)
PY

echo "Wrote $OUT" >&2
