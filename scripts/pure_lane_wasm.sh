#!/usr/bin/env bash
# pure_lane_wasm.sh --- real Rust to WebAssembly with no LLVM in the chain.
#
# Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0 OR MIT.
#
# WHAT THIS DEMONSTRATES
# ----------------------
# Every wasm artifact this project ships to alab.systems today is either (a) the
# aterm engine, compiled by rustc/LLVM, or (b) an "island" whose trust-ir was
# written BY HAND in a generator example. Neither shows the thing the
# one-Module design is actually about: real Rust source reaching wasm through
# the Trust lane.
#
# This script does that, end to end:
#
#   add3.rs  --(rustc -Ztrust-cg-frontend=trust-ir)-->  trust-ir Module
#            --(trust-cg --target wasm32-unknown-unknown)-->  .wasm
#            --(node)-->  differential against the Rust source semantics
#
# `-Ztrust-cg-frontend=trust-ir` is the source-first path: THIR -> `trust_ir_of`
# -> trust_ir::Module. Its own flag documentation is the reason this is worth
# something --- it "fails the build on any item the producer or the converter
# declines; it never falls back to the MIR path, so one unsupported item refuses
# the whole crate". There is no silent LLVM fallback hiding inside a green run.
#
# Measured 2026-08-27: 3 functions, 139 bytes, 46,878/46,878 agreeing checks.
#
# WHAT IT DOES NOT DEMONSTRATE, stated here because the gap IS the finding
# ------------------------------------------------------------------------
# The pipeline is NOT push-button. Two edits are applied to the producer's
# module between the halves, and each names a real missing piece:
#
#   1. TARGET STAMP. The producer stamps the HOST config into the module ---
#      `target "arm64-apple-macosx" 8 little`. The wasm backend correctly
#      refuses it ("triple is not a wasm32 triple; pointer_size 8 != 4"). So the
#      trust-ir Module as emitted is NOT target-independent, and "one Module,
#      every target" is today "one Module per target config" with no way to ask
#      the producer for a config other than the host's. The honest fix is a
#      wasm32 sysroot in the stage2 so rustc can be asked for the wasm32
#      configuration directly; retargeting the stamp is a stand-in for that.
#
#      This is sound for THESE bodies and not in general: `add3` and `clamp_lo`
#      are i32-only, with no pointer, no usize, and no memory access, so the
#      pointer-size field cannot change what they compute. A body that touched
#      memory would need the real thing.
#
#   2. CALLING CONVENTION. The producer emits `rustcc` (CallingConv::Rust) even
#      for `extern "C"` items; the wasm backend lowers only CallingConv::C.
#      Rewriting the convention is safe for these signatures --- all-scalar
#      i32 arguments and returns, where the two conventions coincide --- and
#      would NOT be for an aggregate.
#
# Both edits are applied by `sed` below, in the open, rather than by a helper
# that would make them easy to stop noticing.
#
# The compile's own evidence block reports `"verdict":"missing_evidence"` and
# lists `translation_validation` under `not_run`. The CFG structural invariant
# DOES run and holds, but it is a necessary condition on the structuring, not a
# proof that the module computes what the trust-ir computes. The load-bearing
# evidence here is the execution differential at the end.
#
#   ./scripts/pure_lane_wasm.sh [stage2-rustc]
#
# Default rustc: $HOME/trust/build/host/stage2/bin/rustc. Any Trust-built rustc
# carrying `-Ztrust-cg-frontend` works; the script prints which one it used and
# its commit hash, because a stale stage2 measures the day it was built rather
# than the day you ran it.
set -euo pipefail

RUSTC="${1:-$HOME/trust/build/host/stage2/bin/rustc}"
HERE="$(cd "$(dirname "$0")" && pwd)"
CG="$HERE/../target/release/trust-cg"
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT

command -v node >/dev/null || { echo "node not found" >&2; exit 1; }
[ -x "$RUSTC" ] || { echo "no Trust rustc at $RUSTC" >&2; exit 1; }
[ -x "$CG" ] || { echo "build the CLI first: cargo build --release -p trust-cg-cli" >&2; exit 1; }

echo "==> compilers"
"$RUSTC" --version --verbose | sed -n '1p;/commit-hash/p' | sed 's/^/    rustc: /'
echo "    trust-cg: $(git -C "$HERE/.." rev-parse --short=12 HEAD)$([ -n "$(git -C "$HERE/.." status --porcelain)" ] && echo ' (DIRTY)')"

cat > "$OUT/src.rs" <<'RUST'
#![crate_type = "cdylib"]
#![no_std]
#[panic_handler]
fn ph(_: &core::panic::PanicInfo) -> ! { loop {} }

#[no_mangle]
pub extern "C" fn add3(a: i32, b: i32, c: i32) -> i32 { a + b + c }

#[no_mangle]
pub extern "C" fn clamp_lo(x: i32) -> i32 { if x < 0 { 0 } else { x } }
RUST

# `-C overflow-checks=off` so `a + b + c` lowers to plain adds. With checks on,
# the producer emits the overflow obligations instead, which is the correct
# behaviour and a different experiment.
echo "==> producer: THIR -> trust_ir_of -> trust-ir Module"
mkdir -p "$OUT/ir"
"$RUSTC" --edition 2021 --crate-name pl3 \
  -C panic=abort -C overflow-checks=off \
  -Ztrust-verify=off -Ztrust-ir-lower=on -Ztrust-cg-frontend=trust-ir \
  -Ztrust-dump=ir:"$OUT/ir" --emit=obj --crate-type cdylib \
  "$OUT/src.rs" -o "$OUT/src.o" 2>&1 | sed 's/^/    /'

python3 - "$OUT/ir/pl3.coverage.json" <<'PY'
import json, sys
t = json.load(open(sys.argv[1]))["totals"]
print(f"    coverage: {t['lowered']}/{t['bodies']} bodies lowered, "
      f"{t['unsupported']} unsupported, {t['instr_count']} instructions, "
      f"{t['calls']['unresolved']} unresolved calls")
if t["unsupported"] or t["calls"]["unresolved"]:
    raise SystemExit("refusing: the module is not self-contained")
PY

# The two documented edits. Kept visible; see the header for why each is sound
# for these specific bodies and unsound in general.
echo "==> retarget the module stamp (host config -> wasm32) and set C convention"
sed -e 's|target "[^"]*" 8 little|target "wasm32-unknown-unknown" 4 little|' \
    -e 's|^rustcc fn |fn |' \
    "$OUT/ir/pl3.trust-ir.txt" > "$OUT/pl3.trust_ir"
grep -n '^target' "$OUT/pl3.trust_ir" | sed 's/^/    /'

echo "==> backend: trust-ir Module -> wasm32"
"$CG" "$OUT/pl3.trust_ir" --format=text --target wasm32-unknown-unknown \
  -o "$OUT/pl3.wasm" 2>&1 | grep -v '^trust-cg: wasm-evidence:' | sed 's/^/    /'
python3 - "$OUT/pl3.wasm" <<'PY'
import sys, hashlib
b = open(sys.argv[1], "rb").read()
print(f"    module: {len(b)} bytes  sha256:{hashlib.sha256(b).hexdigest()[:16]}")
PY

echo "==> differential: the wasm against the Rust source semantics"
cat > "$OUT/check.mjs" <<'JS'
import { readFileSync } from "node:fs";
const { instance } = await WebAssembly.instantiate(readFileSync(process.argv[2]), {});
const { add3, clamp_lo } = instance.exports;
const refAdd3 = (a, b, c) => (((a + b) | 0) + c) | 0;
const refClamp = (x) => (x < 0 ? 0 : x);
const I32 = [0, 1, -1, 2, -2, 7, -7, 127, -128, 255, -256, 65535, -65536,
  0x7fffffff, -0x80000000, 0x7ffffffe, -0x7fffffff, 1 << 30, -(1 << 30)];
let checks = 0; const fails = [];
for (const a of I32) for (const b of I32) for (const c of I32) {
  const got = add3(a, b, c) | 0, want = refAdd3(a, b, c); checks++;
  if (got !== want) fails.push(`add3(${a},${b},${c}) = ${got}, want ${want}`);
}
for (const x of I32) {
  const got = clamp_lo(x) | 0, want = refClamp(x); checks++;
  if (got !== want) fails.push(`clamp_lo(${x}) = ${got}, want ${want}`);
}
let s = 0x9e3779b9; const next = () => { s = (Math.imul(s, 1664525) + 1013904223) >>> 0; return s | 0; };
for (let i = 0; i < 20000; i++) {
  const a = next(), b = next(), c = next();
  const got = add3(a, b, c) | 0, want = refAdd3(a, b, c); checks++;
  if (got !== want) fails.push(`add3(${a},${b},${c}) = ${got}, want ${want}`);
  const x = next(), gotc = clamp_lo(x) | 0, wantc = refClamp(x); checks++;
  if (gotc !== wantc) fails.push(`clamp_lo(${x}) = ${gotc}, want ${wantc}`);
}
if (fails.length) {
  console.error(`    DIVERGED: ${fails.length} of ${checks}`);
  for (const f of fails.slice(0, 10)) console.error("      " + f);
  process.exit(1);
}
console.log(`    agree ${checks}/${checks}`);
JS
node "$OUT/check.mjs" "$OUT/pl3.wasm"

echo
echo "PURE LANE GREEN --- real Rust to wasm with no LLVM in the chain."
echo "Read the header before quoting this: two documented edits stand in for a"
echo "wasm32 sysroot and for extern \"C\" convention propagation, and the"
echo "compile's own evidence block reports translation_validation as not_run."
