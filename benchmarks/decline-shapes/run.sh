#!/usr/bin/env bash
# Minimal named shapes for the [TCG-SSA-071] decline class.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
# WHY: ~38% of generated safe Rust fails closed, and essentially all of it is
# ONE diagnostic. This pins the boundary as minimal programs so the gap is
# measurable instead of a percentage:
#
#   d_*   currently DECLINE  — each should flip to a MATCH when the class is fixed
#   ok_*  currently COMPILE  — the near-miss neighbours; they must NEVER regress
#
# Every program is UB-free, deterministic, and encodes its answer in its exit
# status, with rustc's LLVM backend as the oracle. A d_* that starts compiling is
# progress; an ok_* that starts declining, or any WRONG-ANSWER, is a regression.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
DYLIB="${DECLINE_DYLIB:-$HERE/../../crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.so}"
OUT="${DECLINE_OUT:-$(mktemp -d)}"; mkdir -p "$OUT"
export PATH="$HOME/.cargo/bin:$HOME/.rustup/toolchains/stable-aarch64-unknown-linux-gnu/lib/rustlib/aarch64-unknown-linux-gnu/bin/gcc-ld:$PATH"
RUSTC="$(rustup which --toolchain nightly-2026-04-20 rustc 2>/dev/null || echo rustc)"
B="--edition=2021 --crate-type bin -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1 -Cdefault-linker-libraries=y"
declined=0; compiled=0; wrong=0; regressed=0; progressed=0
for f in "$HERE"/progs/*.rs; do
  n=$(basename "$f" .rs); exp=${n%%_*}
  "$RUSTC" $B -Copt-level=2 -o "$OUT/l_$n" "$f" 2>/dev/null || { echo "ORACLE-FAIL $n"; continue; }
  "$OUT/l_$n" >/dev/null 2>&1; want=$?
  if env TCG_NO_PROOF_CERTS=1 TCG_REFINE_SOLVER=0 "$RUSTC" $B -Copt-level=2 \
       -Zcodegen-backend="$DYLIB" -o "$OUT/t_$n" "$f" 2>"$OUT/$n.err"; then
    "$OUT/t_$n" >/dev/null 2>&1; got=$?
    compiled=$((compiled+1))
    if [ "$got" != "$want" ]; then
      wrong=$((wrong+1)); echo "WRONG-ANSWER $n: want $want got $got"
    elif [ "$exp" = "d" ]; then
      progressed=$((progressed+1)); echo "PROGRESS $n now compiles and MATCHES (was a tracked decline)"
    fi
  else
    declined=$((declined+1))
    if [ "$exp" = "ok" ]; then
      regressed=$((regressed+1)); echo "REGRESSION $n used to compile and now DECLINES"
    fi
  fi
done
echo "decline-shapes: $compiled compiled, $declined declined, $wrong WRONG-ANSWER, $progressed progressed, $regressed regressed"
[ "$wrong" -eq 0 ] && [ "$regressed" -eq 0 ]
