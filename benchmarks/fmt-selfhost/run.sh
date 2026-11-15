#!/usr/bin/env bash
# Differential gate for the `core::fmt` interception, both sides. See README.md.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# Unlike ../shape-coverage/run.sh this compares STDOUT as well as the exit
# status: formatted BYTES are the observable these programs exist to pin, and a
# gate that only reads the exit code cannot see a wrong digit. A panicking
# program's stderr is NOT compared — the panic message text is a documented,
# accepted deviation of this backend (`emit_unwinding_panic_raise`).
#
# Usage:  ./run.sh [backend.dylib] [trustc]
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
DYLIB="${1:-$HERE/../../crates/rustc-codegen-trust-cg/target/debug/librustc_codegen_trust_cg.dylib}"
RUSTC="${2:-trustc}"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
BASE="--edition=2021 --crate-type bin -Ztrust-verify=off -Cpanic=abort -Ccodegen-units=1"

# Exact fail-closed coverage floor. A decline is correct behaviour (the backend
# refuses MIR it cannot lower rather than guessing), but an UNEXPECTED one is a
# lost differential and fails; a stale allowance also fails, so the list cannot
# outlive the gap it records. Each row also names a substring of the DIAGNOSTIC
# it expects, so a row that starts declining for a DIFFERENT reason fails too —
# an allowance may cover one known gap, never whatever appears next.
expected_decline_code() {
  case "$1 O$2" in
    # `String` slot path: `memory-backed aggregate assignment Rvalue::Cast`.
    # Unrelated to the fmt interception; present before and after the self-host
    # layout change (measured 2026-09-10).
    "fmt_write O2") printf '%s' "memory-backed aggregate assignment" ;;
    # `abi_aggregate_return` was listed here while the hidden return-buffer
    # pointer had no lowering and `[TCG-RET-ABI]` refused the function. It is
    # NOT listed any more: the convention is implemented (the callee writes
    # through the `x8` buffer, the caller allocates it and passes its address),
    # so the program compiles and is compared like every other row. The gate
    # itself is untouched and still runs on every aggregate return — it simply
    # agrees now. The four-way mixed-link table that the refusal stood in for
    # lives in ../abi-xback/, which measures it directly.
    *) printf '%s' "" ;;
  esac
}
is_expected_decline() { [[ -n "$(expected_decline_code "$1" "$2")" ]]; }

# Per-program compiler flags, applied to BOTH sides so the oracle and the bridge
# compile the SAME crate. Only one program needs any: `selfhost_live_reader`
# must be compiled under `--crate-name core`, because the backend recognizes a
# crate-LOCAL `core::fmt::rt::ArgumentType` by its crate-qualified def path plus
# `DefId::is_local` (`is_local_fmt_internal_ty`). That, and nothing else, is what
# puts a user-runnable program on the SELF-HOST deadness path.
extra_flags() {
  case "$1" in
    selfhost_live_reader) printf '%s' "--crate-name core" ;;
    *) printf '%s' "" ;;
  esac
}

if [[ "${1:-}" == "--selftest" ]]; then
  [[ "$(extra_flags selfhost_live_reader)" == "--crate-name core" ]] || exit 1
  [[ -z "$(extra_flags fmt_println)" ]] || exit 1
  is_expected_decline fmt_write 2 || exit 1
  [[ "$(expected_decline_code fmt_write 2)" == "memory-backed aggregate assignment" ]] || exit 1
  ! is_expected_decline fmt_write 0 || exit 1
  ! is_expected_decline fmt_println 2 || exit 1
  # `abi_aggregate_return` is deliberately NOT an expected decline any more:
  # the indirect-return convention is implemented, so the program compiles and
  # is compared. A row that starts declining again fails the gate.
  ! is_expected_decline abi_aggregate_return 0 || exit 1
  ! is_expected_decline abi_aggregate_return 2 || exit 1
  echo "fmt-selfhost decline-ratchet selftest: 1 expected row, 4 rejection arms, 2 extra-flag arms, 1 code arm"
  exit 0
fi

pass=0; fail=0; expected_unsup=0
for src in "$HERE"/progs/*.rs; do
  n="$(basename "$src" .rs)"
  EXTRA="$(extra_flags "$n")"
  for opt in 0 2; do
    # shellcheck disable=SC2086 # $BASE/$EXTRA are deliberate word lists
    if ! "$RUSTC" $BASE $EXTRA -Copt-level=$opt -o "$TMP/l" "$src" 2>"$TMP/llvm.err"; then
      echo "FAIL  $n O$opt: LLVM oracle failed to build"; tail -5 "$TMP/llvm.err"
      fail=$((fail+1)); continue
    fi
    want_out="$("$TMP/l" 2>/dev/null)"; want=$?
    # shellcheck disable=SC2086 # $BASE/$EXTRA are deliberate word lists
    if ! "$RUSTC" $BASE $EXTRA -Copt-level=$opt -Zcodegen-backend="$DYLIB" -o "$TMP/t" "$src" 2>"$TMP/err"; then
      if grep -q "TCG-MIR-UNSUPPORTED\|failing closed" "$TMP/err"; then
        if is_expected_decline "$n" "$opt"; then
          want_code="$(expected_decline_code "$n" "$opt")"
          if grep -qF "$want_code" "$TMP/err"; then
            echo "UNSUP $n O$opt: expected decline ($want_code)"
            expected_unsup=$((expected_unsup+1))
          else
            echo "FAIL  $n O$opt: declined, but NOT for the allowed reason ($want_code)"
            sed -n '1,3p' "$TMP/err"
            fail=$((fail+1))
          fi
        else
          echo "FAIL  $n O$opt: NEW fail-closed decline"
          sed -n '1,3p' "$TMP/err"
          fail=$((fail+1))
        fi
      else
        echo "FAIL  $n O$opt: trust-cg failed to compile with no fail-closed diagnostic"
        fail=$((fail+1))
      fi
      continue
    fi
    got_out1="$("$TMP/t" 2>/dev/null)"; got1=$?
    got_out2="$("$TMP/t" 2>/dev/null)"; got2=$?
    if [ "$got1" != "$want" ] || [ "$got2" != "$want" ]; then
      echo "FAIL  $n O$opt: exit llvm=$want trust-cg=$got1,$got2$([ "$got1" != "$got2" ] && echo '  (NON-DETERMINISTIC)')"
      fail=$((fail+1))
    elif [ "$got_out1" != "$want_out" ] || [ "$got_out2" != "$want_out" ]; then
      echo "FAIL  $n O$opt: STDOUT differs"
      echo "  llvm    : $(printf %s "$want_out" | head -c 200)"
      echo "  trust-cg: $(printf %s "$got_out1" | head -c 200)"
      fail=$((fail+1))
    else
      pass=$((pass+1))
    fi
  done
done
if [[ "$expected_unsup" -ne 1 ]]; then
  echo "FAIL  decline ratchet: observed $expected_unsup/1 expected rows; update the exact allowlist consciously"
  fail=$((fail+1))
fi
echo "fmt-selfhost: $pass passed, $fail failure(s), $expected_unsup expected decline(s)"
[ "$fail" -eq 0 ]
