#!/usr/bin/env bash
# Differential shape-coverage gate for the RUSTC BRIDGE.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# WHY THIS EXISTS: the differential fuzz campaign (scripts/fuzz_campaign.sh)
# drives trust-ir-gen / trust-ir-jit-diff / csmith / yarpgen — all of which feed
# the trust_ir and LLVM-import frontends. The rustc BRIDGE, the primary
# user-facing frontend, had no differential net beyond the 18-program
# beat-llvm corpus. A 2026-08-18 audit found SEVEN wrong-code bugs reachable
# from ordinary Rust that the corpus simply did not contain the shapes for
# (FP fills, i32 matmul, seeded reductions, conditional stores, a second
# loop-carried value, mixed element types).
#
# Each program here is one SHAPE, is deterministic, and encodes its whole
# result in its exit status. rustc's LLVM backend is the oracle. Every binary
# is run TWICE: an out-of-bounds read shows up as run-to-run variation, which
# is exactly how two of those seven bugs announced themselves.
#
# Usage:  ./run.sh [path-to-backend.so]
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
DYLIB="${1:-$HERE/../../crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.so}"
RUSTC="$(rustup which --toolchain nightly-2026-04-20 rustc 2>/dev/null || echo rustc)"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
BASE="--edition=2021 --crate-type bin -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1"
pass=0; fail=0; unsup=0
for src in "$HERE"/progs/*.rs; do
  n="$(basename "$src" .rs)"
  for opt in 0 1 2 3; do
    if ! $RUSTC $BASE -Copt-level=$opt -o "$TMP/l" "$src" 2>/dev/null; then
      echo "SKIP  $n O$opt (llvm oracle failed to build)"; continue; fi
    "$TMP/l" >/dev/null 2>&1; want=$?
    if ! env TCG_NO_PROOF_CERTS=1 TCG_REFINE_SOLVER=0 $RUSTC $BASE -Copt-level=$opt \
         -Zcodegen-backend="$DYLIB" -o "$TMP/t" "$src" 2>"$TMP/err"; then
      # A clean FAIL-CLOSED refusal is correct behaviour, not a miscompile:
      # the backend declines MIR it cannot lower rather than guessing. Count
      # it separately so coverage stays visible without faking a failure.
      if grep -qE "\[TCG-[A-Z-]+[0-9]*\]" "$TMP/err"; then
        code="$(grep -oE "\[TCG-[A-Z-]+[0-9]*\]" "$TMP/err" | head -1)"
        echo "UNSUP $n O$opt: declined ($code)"; unsup=$((unsup+1))
      else
        echo "FAIL  $n O$opt: trust-cg failed to compile with no fail-closed diagnostic"
        fail=$((fail+1))
      fi
      continue; fi
    "$TMP/t" >/dev/null 2>&1; got1=$?
    "$TMP/t" >/dev/null 2>&1; got2=$?
    if [ "$got1" != "$want" ] || [ "$got2" != "$want" ]; then
      echo "FAIL  $n O$opt: llvm=$want trust-cg=$got1,$got2$([ "$got1" != "$got2" ] && echo '  (NON-DETERMINISTIC)')"
      fail=$((fail+1))
    else
      pass=$((pass+1))
    fi
  done
done
echo "shape-coverage: $pass passed, $fail WRONG-ANSWER, $unsup declined-fail-closed"
[ "$fail" -eq 0 ]
