#!/usr/bin/env bash
# gen_x86_fp_rosetta_truth.sh — REGENERATOR for x86_fp_rosetta_truth.json.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# Builds the Rosetta scalar-FP x86 oracle harness (gen_x86_fp_rosetta_truth.c) as
# an x86-64 Mach-O with `clang -arch x86_64`, runs it under `arch -x86_64`
# (Rosetta 2 — an INDEPENDENT x86 implementation, NOT a second in-house model),
# and writes the committed fixture x86_fp_rosetta_truth.json. Scalar SSE/SSE2 FP
# never traps, so no fork/SIGFPE machinery is needed — every fact is a VALUE fact.
#
# Provenance (oracle, macOS version, Rosetta version, date) is captured here and
# passed into the harness for the JSON _header. Exact accounting is emitted by the
# harness itself (_accounting block).
#
# Usage:
#   crates/trust-cg-verify/tests/fixtures/gen_x86_fp_rosetta_truth.sh
# (run from anywhere; paths are resolved relative to this script).
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SRC="$HERE/gen_x86_fp_rosetta_truth.c"
BIN="$HERE/gen_x86_fp_rosetta_truth.bin"
OUT="$HERE/x86_fp_rosetta_truth.json"

# Confirm Rosetta is available (the oracle).
if ! arch -x86_64 /usr/bin/true 2>/dev/null; then
  echo "ERROR: Rosetta 2 not available (arch -x86_64 /usr/bin/true failed). Cannot regenerate." >&2
  exit 1
fi

MACOS_VER="$(sw_vers -productVersion 2>/dev/null || echo unknown)-build$(sw_vers -buildVersion 2>/dev/null || echo unknown)"
ROSETTA_VER="$(/usr/bin/pkgutil --pkg-info com.apple.pkg.RosettaUpdateAuto 2>/dev/null | awk '/version:/{print $2}' || true)"
[ -z "${ROSETTA_VER:-}" ] && ROSETTA_VER="installed (version not reported by pkgutil)"
DATE="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

echo "Building $SRC for x86_64 ..." >&2
clang -arch x86_64 -O0 -msse4.2 -Wall -Wextra -o "$BIN" "$SRC"
file "$BIN" >&2

echo "Running under Rosetta (arch -x86_64) ..." >&2
arch -x86_64 "$BIN" "$MACOS_VER" "$ROSETTA_VER" "$DATE" > "$OUT"

# Validate the JSON parses.
python3 -c "import json,sys; d=json.load(open('$OUT')); print('OK facts=%d value=%d trap=%d' % (len(d['facts']), d['_accounting']['value_facts'], d['_accounting']['trap_facts']), file=sys.stderr)"

# The committed binary is a build artifact — remove it (regen rebuilds).
rm -f "$BIN"

echo "Wrote $OUT" >&2
