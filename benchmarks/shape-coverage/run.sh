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
# result in its exit status. trustc's LLVM backend is the oracle. Every binary
# is run TWICE: an out-of-bounds read shows up as run-to-run variation, which
# is exactly how two of those seven bugs announced themselves.
#
# Both sides use the Trust compiler the bridge pin (channel = "trust") names,
# resolved by scripts/trust_toolchain.py from the PATH trustc/targo package or
# the package trustc named by --driver. The retired stock nightly, any
# unidentified compiler and a bare `rustc` fallback are refused (exit 2). Both
# sides compile in Trust's explicit unverified frontend lane (-Ztrust-verify=off),
# a diagnostic lane with no Trust-verified compilation claim.
#
# Usage:  ./run.sh [--driver TRUSTC] [path-to-backend.so]
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
DRIVER_ARGS=()
if [ "${1:-}" = "--driver" ]; then
  [ "$#" -ge 2 ] || { echo "shape-coverage: --driver needs a trustc path" >&2; exit 2; }
  DRIVER_ARGS=(--driver "$2"); shift 2
fi
DYLIB="${1:-$HERE/../../crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.so}"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
BASE="-Ztrust-verify=off --edition=2021 --crate-type bin -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1"
# trust-cg halves switch proof certificates and the refinement solver off
# through the backend's TRACKED knob option; trustc refuses the former
# TCG_NO_PROOF_CERTS / TCG_REFINE_SOLVER environment variables as untracked
# codegen controls, which made every trust-cg compile fail (2026-09-22).

# Exact fail-closed coverage floor at the final s72 corpus. A new decline is a
# lost differential regression and fails. If one of these known gaps starts
# compiling, the stale allowance also fails until it is consciously removed.
is_expected_decline() {
  case "$1 O$2" in
    "s13_zero_trip O2"|"s13_zero_trip O3"|\
    "s27_dyn_box_drop O0"|"s27_dyn_box_drop O1"|\
    "s27_dyn_box_drop O2"|"s27_dyn_box_drop O3"|\
    "s31_vec_sort_dedup O0"|"s31_vec_sort_dedup O1"|\
    "s31_vec_sort_dedup O2"|"s31_vec_sort_dedup O3") return 0 ;;
    *) return 1 ;;
  esac
}

if [[ "${1:-}" == "--selftest" ]]; then
  expected=0
  for row in \
    "s13_zero_trip 2" "s13_zero_trip 3" \
    "s27_dyn_box_drop 0" "s27_dyn_box_drop 1" \
    "s27_dyn_box_drop 2" "s27_dyn_box_drop 3" \
    "s31_vec_sort_dedup 0" "s31_vec_sort_dedup 1" \
    "s31_vec_sort_dedup 2" "s31_vec_sort_dedup 3"; do
    # shellcheck disable=SC2086 # each fixture is deliberately two words
    is_expected_decline $row || exit 1
    expected=$((expected+1))
  done
  ! is_expected_decline s13_zero_trip 1 || exit 1
  ! is_expected_decline s72_mut_ref_return 0 || exit 1
  echo "shape-coverage decline-ratchet selftest: $expected expected rows, 2 rejection arms"
  exit 0
fi

RUSTC="$(python3 "$HERE/../../scripts/trust_toolchain.py" ${DRIVER_ARGS[@]+"${DRIVER_ARGS[@]}"} --print compiler)" || {
  echo "shape-coverage: cannot resolve the pinned Trust compiler" >&2; exit 2; }
echo "shape-coverage: driver $(python3 "$HERE/../../scripts/trust_toolchain.py" --driver "$RUSTC" --print summary)"

pass=0; fail=0; unsup=0; expected_unsup=0
for src in "$HERE"/progs/*.rs; do
  n="$(basename "$src" .rs)"
  for opt in 0 1 2 3; do
    # shellcheck disable=SC2086 # BASE is a deliberate word list
    if ! "$RUSTC" $BASE -Copt-level=$opt -o "$TMP/l" "$src" 2>"$TMP/llvm.err"; then
      echo "FAIL  $n O$opt: LLVM oracle failed to build"
      tail -5 "$TMP/llvm.err"
      fail=$((fail+1))
      continue
    fi
    "$TMP/l" >/dev/null 2>&1; want=$?
    if ! "$RUSTC" $BASE -Ztrust-ir-cg-args=no-proof-certs -Ztrust-ir-cg-args=refine-solver=0 -Copt-level=$opt \
         -Zcodegen-backend="$DYLIB" -o "$TMP/t" "$src" 2>"$TMP/err"; then
      # A clean FAIL-CLOSED refusal is correct behaviour, not a miscompile:
      # the backend declines MIR it cannot lower rather than guessing. Count
      # it separately so coverage stays visible without faking a failure.
      if grep -qE "\[TCG-[A-Z-]+[0-9]*\]" "$TMP/err"; then
        code="$(grep -oE "\[TCG-[A-Z-]+[0-9]*\]" "$TMP/err" | head -1)"
        if is_expected_decline "$n" "$opt"; then
          echo "UNSUP $n O$opt: expected decline ($code)"
          expected_unsup=$((expected_unsup+1))
        else
          echo "FAIL  $n O$opt: NEW fail-closed decline ($code)"
          fail=$((fail+1))
        fi
        unsup=$((unsup+1))
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
if [[ "$expected_unsup" -ne 10 ]]; then
  echo "FAIL  decline ratchet: observed $expected_unsup/10 expected rows; update the exact allowlist consciously"
  fail=$((fail+1))
fi
echo "shape-coverage: $pass passed, $fail failure(s), $unsup declined-fail-closed"
[ "$fail" -eq 0 ]
