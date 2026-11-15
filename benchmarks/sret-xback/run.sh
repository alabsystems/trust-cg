#!/usr/bin/env bash
# sret-xback — the INDIRECT-RETURN convention, measured ACROSS a codegen boundary.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# WHY THIS EXISTS, and why ../abi-xback does not cover it.
#
# Every whole-program differential in this repo (beat-llvm, bridge-fuzz,
# shape-coverage, fmt-selfhost) builds caller and callee with the SAME backend.
# A calling-convention disagreement is structurally invisible to all of them:
# trust-cg's caller reads the value from wherever trust-cg's callee left it, so
# the program agrees with itself and matches LLVM's exit code. ../abi-xback makes
# exactly this argument for ARGUMENTS and links across backends to test it. This
# gate makes the same measurement for the RETURN convention, also using `trustc`
# on both sides, which is the compiler this backend loads into.
#
# THE SHAPE UNDER TEST: a 16-byte `BackendRepr::Memory` aggregate (the
# `core::fmt::rt::ArgumentType` layout). rustc's Rust ABI returns it
# `PassMode::Indirect` — the CALLER allocates the buffer and passes its address
# in `x8` (AAPCS64) / `rdi` (System V), and the callee writes through it. The C
# rule for a 16-byte aggregate says `x0`/`x1` instead. Measured 2026-09-10, with
# trust-cg applying the C rule:
#
#   caller    callee    result
#   LLVM      LLVM      42          (the oracle)
#   trust-cg  trust-cg  42          (self-consistent — why every other gate passed)
#   LLVM      trust-cg  0           a SILENT WRONG VALUE
#   trust-cg  LLVM      138         a crash
#
# All four directions must now agree with the oracle. A single disagreement is a
# P0 ABI mismatch; a DECLINE is also a failure here, because the point of this
# gate is that the convention is emitted, not refused.
#
# Usage:  ./run.sh [backend.dylib] [trustc] [opt-levels...]
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
if [[ "${1:-}" == "--selftest" ]]; then
  echo "sret-xback: 4 link directions x 2 default opt levels; every one must match the oracle"
  exit 0
fi
case "$(uname -s)" in
  Linux) suffix=so ;;
  Darwin) suffix=dylib ;;
  *) echo "unsupported native benchmark host" >&2; exit 2 ;;
esac
DYLIB="${1:-$HERE/../../crates/rustc-codegen-trust-cg/target/debug/librustc_codegen_trust_cg.$suffix}"
RUSTC="${2:-trustc}"
shift 2 2>/dev/null || true
OPTS=("$@")
[ "${#OPTS[@]}" -eq 0 ] && OPTS=(0 2)

TMP="$(mktemp -d)" || exit 2
echo "sret-xback: retained artifacts: $TMP"
BASE=(--edition=2021 -Ztrust-verify=off -Cpanic=abort -Ccodegen-units=1)
BOUNDED=(python3 "$HERE/../../scripts/run_with_timeout.py" --grace-seconds 5)

fail=0
for opt in "${OPTS[@]}"; do
  W="$TMP/o$opt"; mkdir -p "$W/llvm" "$W/tcg"
  # Both callee halves. `--crate-type rlib` keeps the callee in its own
  # separately compiled object, which is what makes the call cross a boundary.
  for be in llvm tcg; do
    flags=("${BASE[@]}" "-Copt-level=$opt")
    [ "$be" = tcg ] && flags+=(-Zcodegen-backend="$DYLIB")
    if ! "${BOUNDED[@]}" 300 "$RUSTC" "${flags[@]}" --crate-type rlib --out-dir "$W/$be" \
         "$HERE/progs/argty_callee.rs" >"$W/callee.$be.err" 2>&1; then
      echo "FAIL  callee[$be] O$opt did not build:"; tail -3 "$W/callee.$be.err"
      fail=$((fail+1))
    fi
  done
  want=""
  for caller in llvm tcg; do for callee in llvm tcg; do
    [ -f "$W/$callee/libsretcallee.rlib" ] || { fail=$((fail+1)); continue; }
    flags=("${BASE[@]}" "-Copt-level=$opt")
    [ "$caller" = tcg ] && flags+=(-Zcodegen-backend="$DYLIB")
    bin="$W/bin_${caller}_${callee}"
    if ! "${BOUNDED[@]}" 300 "$RUSTC" "${flags[@]}" --crate-type bin -L "$W/$callee" -o "$bin" \
         "$HERE/progs/argty_caller.rs" >"$bin.err" 2>&1; then
      echo "FAIL  caller=$caller callee=$callee O$opt did not build:"; tail -3 "$bin.err"
      fail=$((fail+1)); continue
    fi
    "${BOUNDED[@]}" 30 "$bin" >"$bin.out" 2>"$bin.run.err"; got=$?
    if [ "$got" -ge 124 ]; then
      echo "FAIL  caller=$caller callee=$callee O$opt abnormal execution: $got"
      fail=$((fail+1)); continue
    fi
    # LLVM/LLVM is the oracle only after matching the fixture's independently
    # expected result. A later cell must never replace a failed oracle.
    if [ "$caller" = llvm ] && [ "$callee" = llvm ]; then
      if [ "$got" -ne 42 ]; then
        echo "FAIL  O$opt LLVM oracle disagrees with fixture result 42: $got"
        fail=$((fail+1)); continue
      fi
      want=$got
      echo "ORACLE caller=llvm callee=llvm O$opt: exit $want"
      continue
    fi
    if [ -z "$want" ]; then
      echo "FAIL  caller=$caller callee=$callee O$opt has no successful LLVM oracle"
      fail=$((fail+1)); continue
    fi
    if [ "$got" != "$want" ]; then
      echo "MISMATCH caller=$caller callee=$callee O$opt: want $want got $got"
      fail=$((fail+1))
    else
      echo "MATCH  caller=$caller callee=$callee O$opt: exit $got"
    fi
  done; done
done
echo "sret-xback: $fail failure(s)"
[ "$fail" -eq 0 ]
