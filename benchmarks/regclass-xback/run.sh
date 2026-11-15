#!/usr/bin/env bash
# regclass-xback — the register CLASS and COUNT of a by-value scalar pair,
# measured ACROSS a codegen boundary, in BOTH directions.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# WHY THIS EXISTS, and why ../sret-xback does not cover it.
#
# `sret-xback` measures WHERE a returned aggregate goes — the return registers
# or the caller's `x8` buffer. That is the question `ReturnPlacement` could ask
# when it had two variants, and `822fdc69` closed it. Its own commit message
# named what was left: "a register-CLASS disagreement is still outside this
# gate's reach — a `PassMode::Pair` of floats bound for `d0`/`d1`, or a Pair of
# 32-bit scalars packed into one register, are both 'the return REGISTERS' to
# `ReturnPlacement`, so it cannot see them."
#
# Both were CONFIRMED, at `-Copt-level=0` AND `=2`, with the callee in a
# separately compiled rlib. Measured 2026-09-11 against the pre-fix backend:
#
#   shape                        direction   llvm x tcg   tcg x llvm   oracle
#   struct P { a: f64, b: f64 }  return          0            0          42
#   struct Q { a: i32, b: i32 }  return        188/28        20          42
#   struct P (by value)          argument       80          60/80        42
#   struct Q (by value)          argument       20          244/4        42
#
# LLVM's `P` callee is `fmul d0 ; fmul d1 ; ret`; trust-cg's was
# `ldr x0,[x2] ; ldr x1,[x2,#8] ; ret` — the same bytes out of the wrong
# register file. LLVM's `Q` callee is `ldr w0 ; ldur w1 ; ret`; trust-cg's was
# `ldr x0,[x1]` — one register too few. Both backends were self-consistent,
# which is exactly why every whole-program differential in this repo passed.
#
# WHAT MUST HOLD NOW. Every cell that BUILDS must match the oracle. A DECLINE is
# permitted here, unlike in `sret-xback`, and is reported: the register-class
# gates (`[TCG-RET-ABI]` / `[TCG-ARG-ABI]`) refuse the shapes trust-cg cannot
# place conformantly, and a refusal is always acceptable where a silently
# divergent ABI is not. What is NEVER acceptable is a built binary that
# disagrees with the oracle.
#
# Usage:  ./run.sh [backend.dylib] [trustc] [opt-levels...]
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"

if [[ "${1:-}" == "--selftest" ]]; then
  echo "regclass-xback: 9 program pairs (float/int x return/argument, plus the five sub-eightbyte / mixed-width / tagged-enum / register-pair ARGUMENT pair shapes the core census measured) x 4 link directions x 2 opt levels; every BUILT cell must match the oracle, a DECLINE is reported"
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
echo "regclass-xback: retained artifacts: $TMP"
BASE=(--edition=2021 --error-format=json -Ztrust-verify=off -Cpanic=abort -Ccodegen-units=1)
BOUNDED=(python3 "$HERE/../../scripts/run_with_timeout.py" --grace-seconds 5)

fail=0
declined=0
for shape in fret farg iret iarg barg harg earg marg qarg; do
  for opt in "${OPTS[@]}"; do
    W="$TMP/$shape.o$opt"; mkdir -p "$W/llvm" "$W/tcg"
    # Both callee halves. `--crate-type rlib` keeps the callee in its own
    # separately compiled object, which is what makes the call cross a boundary.
    for be in llvm tcg; do
      flags=("${BASE[@]}" "-Copt-level=$opt")
      [ "$be" = tcg ] && flags+=(-Zcodegen-backend="$DYLIB")
      "${BOUNDED[@]}" 300 "$RUSTC" "${flags[@]}" --crate-type rlib --out-dir "$W/$be" \
        "$HERE/progs/${shape}_callee.rs" >"$W/callee.$be.out" 2>"$W/callee.$be.err"
      compile_status=$?
      if [ "$compile_status" -ne 0 ]; then
        if [ "$be" = tcg ] && python3 "$HERE/refusal.py" "$compile_status" "$W/callee.$be.err"; then
          echo "DECLINE $shape O$opt callee[tcg]: explicit ABI diagnostic (status $compile_status)"
          declined=$((declined+1))
        else
          echo "FAIL   $shape O$opt callee[$be] did not build (status $compile_status):"
          tail -3 "$W/callee.$be.err"; fail=$((fail+1))
        fi
      fi
    done
    want=""
    for caller in llvm tcg; do for callee in llvm tcg; do
      if ! ls "$W/$callee"/*.rlib >/dev/null 2>&1; then continue; fi
      flags=("${BASE[@]}" "-Copt-level=$opt")
      [ "$caller" = tcg ] && flags+=(-Zcodegen-backend="$DYLIB")
      bin="$W/bin_${caller}_${callee}"
      "${BOUNDED[@]}" 300 "$RUSTC" "${flags[@]}" --crate-type bin -L "$W/$callee" -o "$bin" \
        "$HERE/progs/${shape}_caller.rs" >"$bin.build.out" 2>"$bin.err"
      compile_status=$?
      if [ "$compile_status" -ne 0 ]; then
        if [ "$caller" = tcg ] && python3 "$HERE/refusal.py" "$compile_status" "$bin.err"; then
          echo "DECLINE $shape O$opt caller=$caller callee=$callee: explicit ABI diagnostic (status $compile_status)"
          declined=$((declined+1))
        else
          echo "FAIL   $shape O$opt caller=$caller callee=$callee did not build (status $compile_status):"
          tail -3 "$bin.err"; fail=$((fail+1))
        fi
        continue
      fi
      "${BOUNDED[@]}" 30 "$bin" >"$bin.out" 2>"$bin.run.err"; got=$?
      if [ "$got" -ge 124 ]; then
        echo "FAIL   $shape O$opt caller=$caller callee=$callee abnormal execution: $got"
        fail=$((fail+1)); continue
      fi
      # LLVM/LLVM is the oracle only after matching the fixture's independently
      # expected result. A later cell must never replace a failed oracle.
      if [ "$caller" = llvm ] && [ "$callee" = llvm ]; then
        if [ "$got" -ne 42 ]; then
          echo "FAIL   $shape O$opt LLVM oracle disagrees with fixture result 42: $got"
          fail=$((fail+1)); continue
        fi
        want=$got
        echo "ORACLE $shape O$opt caller=llvm callee=llvm: exit $want"
        continue
      fi
      if [ -z "$want" ]; then
        echo "FAIL   $shape O$opt caller=$caller callee=$callee has no successful LLVM oracle"
        fail=$((fail+1)); continue
      fi
      if [ "$got" != "$want" ]; then
        echo "MISMATCH $shape O$opt caller=$caller callee=$callee: want $want got $got"
        fail=$((fail+1))
      else
        echo "MATCH  $shape O$opt caller=$caller callee=$callee: exit $got"
      fi
    done; done
  done
done
echo "regclass-xback: $fail failure(s), $declined decline(s)"
[ "$fail" -eq 0 ]
