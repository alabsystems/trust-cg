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
#   add3.rs  --(trustc -Ztrust-cg-frontend=trust-ir)-->  trust-ir Module
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
# With WASM32_SYSROOT pointing at a wasm32 sysroot
# (scripts/build_wasm32_sysroot.sh builds one), the producer is asked for the
# wasm32 configuration directly: it stamps `wasm32-unknown-unknown 4 little`
# and keeps `extern "C"` items on the C convention, so its module reaches the
# backend UNEDITED (measured 2026-09-27: 3 functions, 139 bytes). Without a
# wasm32 sysroot the pipeline is NOT push-button, and one edit is applied
# between the halves:
#
#   1. TARGET STAMP. The producer stamps the HOST config into the module ---
#      `target "arm64-apple-macosx" 8 little`. The wasm backend correctly
#      refuses it ("triple is not a wasm32 triple; pointer_size 8 != 4"). So the
#      trust-ir Module as emitted is NOT target-independent, and "one Module,
#      every target" is today "one Module per target config" with no way to ask
#      the producer for a config other than the host's. The honest fix is a
#      wasm32 sysroot in the stage2 so trustc can be asked for the wasm32
#      configuration directly; retargeting the stamp is a stand-in for that.
#
#      This is sound for THESE bodies and not in general: `add3` and `clamp_lo`
#      are i32-only, with no pointer, no usize, and no memory access, so the
#      pointer-size field cannot change what they compute. A body that touched
#      memory would need the real thing.
#
# A second edit, rewriting `rustcc` to the C convention, is gone: the wasm
# backend now lowers CallingConv::Rust itself. The remaining edit is applied by
# `sed` below, in the open, rather than by a helper that would make it easy to
# stop noticing.
#
# The compile's own evidence block reports `"verdict":"missing_evidence"` and
# lists `translation_validation` under `not_run`. The CFG structural invariant
# DOES run and holds, but it is a necessary condition on the structuring, not a
# proof that the module computes what the trust-ir computes. The load-bearing
# evidence here is the execution differential at the end.
#
#   [WASM32_SYSROOT=<sysroot>] ./scripts/pure_lane_wasm.sh [trustc]
#
# Default: the installed Trust package's trustc (scripts/trust_toolchain.py;
# it carries `-Ztrust-cg-frontend`). Never a stage of the Trust bootstrap build
# tree: it is exclusive and x.py deletes its compilers mid-build. The script
# prints which compiler it used and its commit hash.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
RUSTC="${1:-$(python3 -B "$HERE/trust_toolchain.py" --print compiler)}"
CG="$HERE/../target/release/trust-cg"
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT

command -v node >/dev/null || { echo "node not found" >&2; exit 1; }
[ -x "$RUSTC" ] || { echo "no trustc at $RUSTC" >&2; exit 1; }
[ -x "$CG" ] || { echo "build the CLI first: targo --unverified build --release -p trust-cg-cli" >&2; exit 1; }

echo "==> compilers"
"$RUSTC" --version --verbose | sed -n '1p;/commit-hash/p' | sed 's/^/    trustc: /'
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
TARGET_ARGS=()
if [ -n "${WASM32_SYSROOT:-}" ]; then
  TARGET_ARGS=(--target wasm32-unknown-unknown --sysroot "$WASM32_SYSROOT")
  echo "    target: wasm32-unknown-unknown (sysroot $WASM32_SYSROOT)"
fi
"$RUSTC" --edition 2021 --crate-name pl3 ${TARGET_ARGS[@]+"${TARGET_ARGS[@]}"} \
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

# The documented edit, needed only without a wasm32 sysroot. Kept visible; see
# the header for why it is sound for these specific bodies and unsound in
# general.
if [ -n "${WASM32_SYSROOT:-}" ]; then
  echo "==> no edits: the producer targeted wasm32 itself"
  cp "$OUT/ir/pl3.trust-ir.txt" "$OUT/pl3.trust_ir"
else
  echo "==> retarget the module stamp (host config -> wasm32)"
  sed -e 's|target "[^"]*" 8 little|target "wasm32-unknown-unknown" 4 little|' \
    "$OUT/ir/pl3.trust-ir.txt" > "$OUT/pl3.trust_ir"
fi
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
if [ -z "${WASM32_SYSROOT:-}" ]; then
  echo "Read the header before quoting this: a documented edit stands in for a"
  echo "wasm32 sysroot (set WASM32_SYSROOT to remove it)."
fi
echo "The compile's own evidence block reports translation_validation as not_run."
