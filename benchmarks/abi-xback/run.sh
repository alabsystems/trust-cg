#!/usr/bin/env bash
# Cross-backend AArch64 calling-convention differential.
set -u

HERE="$(cd "$(dirname "$0")" && pwd)"
FIRST=1
COUNT=25
if [ "$#" -gt 0 ]; then
  FIRST="$1"
  shift
fi
if [ "$#" -gt 0 ]; then
  COUNT="$1"
  shift
fi
OPTS=("$@")
[ "${#OPTS[@]}" -eq 0 ] && OPTS=(2)

OUT="${ABI_XBACK_OUT:-$(mktemp -d)}"
mkdir -p "$OUT/fail"
DYLIB="${ABI_XBACK_DYLIB:-$HERE/../../crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.so}"
RUSTC="$(rustup which --toolchain nightly-2026-04-20 rustc 2>/dev/null || echo rustc)"
LIB=(--edition=2021 --crate-type staticlib -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1)
BIN=(--edition=2021 --crate-type bin -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1 -Cdefault-linker-libraries=y)
TCG=(env TCG_NO_PROOF_CERTS=1 TCG_REFINE_SOLVER=0)

match=0
mismatch=0
declined=0
skipped=0

for ((seed = FIRST; seed < FIRST + COUNT; seed++)); do
  python3 "$HERE/gen.py" "$seed" callee >"$OUT/callee$seed.rs" 2>/dev/null || {
    skipped=$((skipped + 1))
    continue
  }
  python3 "$HERE/gen.py" "$seed" caller >"$OUT/caller$seed.rs" 2>/dev/null || {
    skipped=$((skipped + 1))
    continue
  }

  for opt in "${OPTS[@]}"; do
    dir="$OUT/s${seed}o${opt}"
    mkdir -p "$dir"

    "$RUSTC" "${LIB[@]}" -Copt-level="$opt" -o "$dir/libxl.a" "$OUT/callee$seed.rs" 2>/dev/null || {
      skipped=$((skipped + 1))
      continue
    }
    "$RUSTC" "${BIN[@]}" -Copt-level="$opt" -o "$dir/oracle" "$OUT/caller$seed.rs" -L "$dir" -l static=xl 2>/dev/null || {
      skipped=$((skipped + 1))
      continue
    }
    "$dir/oracle" >/dev/null 2>&1
    want=$?

    if "${TCG[@]}" "$RUSTC" "${LIB[@]}" -Copt-level="$opt" -Zcodegen-backend="$DYLIB" -o "$dir/libxt.a" "$OUT/callee$seed.rs" 2>/dev/null \
      && "$RUSTC" "${BIN[@]}" -Copt-level="$opt" -o "$dir/llvm_x_tcg" "$OUT/caller$seed.rs" -L "$dir" -l static=xt 2>/dev/null; then
      "$dir/llvm_x_tcg" >/dev/null 2>&1
      got=$?
      if [ "$got" != "$want" ]; then
        mismatch=$((mismatch + 1))
        cp "$OUT/callee$seed.rs" "$OUT/fail/"
        cp "$OUT/caller$seed.rs" "$OUT/fail/"
        echo "MISMATCH llvm-caller x tcg-callee seed=$seed O$opt: want $want got $got"
      else
        match=$((match + 1))
      fi
    else
      declined=$((declined + 1))
    fi

    if "${TCG[@]}" "$RUSTC" "${BIN[@]}" -Copt-level="$opt" -Zcodegen-backend="$DYLIB" -o "$dir/tcg_x_llvm" "$OUT/caller$seed.rs" -L "$dir" -l static=xl 2>/dev/null; then
      "$dir/tcg_x_llvm" >/dev/null 2>&1
      got=$?
      if [ "$got" != "$want" ]; then
        mismatch=$((mismatch + 1))
        cp "$OUT/callee$seed.rs" "$OUT/fail/"
        cp "$OUT/caller$seed.rs" "$OUT/fail/"
        echo "MISMATCH tcg-caller x llvm-callee seed=$seed O$opt: want $want got $got"
      else
        match=$((match + 1))
      fi
    else
      declined=$((declined + 1))
    fi
    rm -rf "$dir"
  done
done

echo "abi-xback: $match MATCH, $mismatch MISMATCH, $declined declined, $skipped skipped"
echo "artifacts: $OUT"
[ "$mismatch" -eq 0 ]
