#!/usr/bin/env bash
# run.sh <first-seed> <count> [opt-levels...]
#
# Generative differential gate for the RUSTC BRIDGE. For each seed: generate a
# deterministic, UB-free safe-Rust program, compile it with rustc's LLVM backend
# (the ORACLE) and with trust-cg, run both, compare exit status.
#
#   WRONG-ANSWER  exit codes differ            -> P0, program kept
#   NONDET        trust-cg differs run to run  -> P0, program kept
#   DECLINED      trust-cg failed closed       -> tracked, not a defect
#   MATCH         agree
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
FIRST="${1:-1}"; COUNT="${2:-25}"; shift 2 2>/dev/null || true
OPTS=("$@"); [ ${#OPTS[@]} -eq 0 ] && OPTS=(3)
OUT="${BRIDGE_FUZZ_OUT:-$(mktemp -d)}"; mkdir -p "$OUT/fail"
DYLIB="${BRIDGE_FUZZ_DYLIB:-$HERE/../../crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.so}"
export PATH="$HOME/.cargo/bin:$HOME/.rustup/toolchains/stable-aarch64-unknown-linux-gnu/lib/rustlib/aarch64-unknown-linux-gnu/bin/gcc-ld:$PATH"
RUSTC="$(rustup which --toolchain nightly-2026-04-20 rustc 2>/dev/null || echo rustc)"
BASE="--edition=2021 --crate-type bin -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1 -Cdefault-linker-libraries=y"
match=0; wrong=0; declined=0; nondet=0; genfail=0
for ((s=FIRST; s<FIRST+COUNT; s++)); do
  src="$OUT/g$s.rs"
  python3 "$HERE/gen.py" "$s" > "$src" 2>/dev/null || { genfail=$((genfail+1)); continue; }
  for o in "${OPTS[@]}"; do
    if ! "$RUSTC" $BASE -Copt-level=$o -o "$OUT/l$s" "$src" 2>"$OUT/l$s.err"; then
      genfail=$((genfail+1)); continue
    fi
    "$OUT/l$s" >/dev/null 2>&1; le=$?
    if ! env TCG_NO_PROOF_CERTS=1 TCG_REFINE_SOLVER=0 "$RUSTC" $BASE -Copt-level=$o \
         -Zcodegen-backend="$DYLIB" -o "$OUT/t$s" "$src" 2>"$OUT/t$s.err"; then
      declined=$((declined+1)); continue
    fi
    "$OUT/t$s" >/dev/null 2>&1; t1=$?
    "$OUT/t$s" >/dev/null 2>&1; t2=$?
    if [ "$t1" != "$t2" ]; then
      nondet=$((nondet+1)); cp "$src" "$OUT/fail/nondet_s${s}_O$o.rs"
      echo "NONDET  seed=$s O$o  tcg=$t1 then $t2 (llvm=$le)"
    elif [ "$le" != "$t1" ]; then
      wrong=$((wrong+1)); cp "$src" "$OUT/fail/wrong_s${s}_O$o.rs"
      echo "WRONG-ANSWER  seed=$s O$o  llvm=$le tcg=$t1"
    else
      match=$((match+1))
    fi
  done
done
echo "bridge-fuzz: $match MATCH, $wrong WRONG-ANSWER, $nondet NONDET, $declined declined, $genfail gen/oracle-fail"
echo "artifacts: $OUT"
[ $wrong -gt 0 ] || [ $nondet -gt 0 ] && exit 1
exit 0
