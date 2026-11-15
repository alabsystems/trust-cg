#!/bin/zsh
# Compile a three-function no_std crate through a bridge dylib hosted by a trustc, with the
# body trace and the uncertified-query dump.
# usage: smoke.sh <trustc> <bridge dylib> <out dir>
TRUSTC=${1:?trustc}
DYLIB=${2:?dylib}
OUT=${3:?out}
rm -rf "$OUT" && mkdir -p "$OUT/dump" "$OUT/obj" || exit 9
cat > "$OUT/smoke.rs" <<'EOF'
#![no_std]
#[inline(never)] pub fn add(a: u64, b: u64) -> u64 { a.wrapping_add(b) }
#[inline(never)] pub fn mul32(a: u32, b: u32) -> u32 { a.wrapping_mul(b) }
#[inline(never)] pub fn sub128(a: u128, b: u128) -> u128 { a.wrapping_sub(b) }
EOF
env -u RUSTUP_TOOLCHAIN RUSTC_BOOTSTRAP=1 "$TRUSTC" --edition 2024 --crate-type lib --crate-name smoke \
  --emit=obj -Zcodegen-backend="$DYLIB" -Ccodegen-units=1 -Cpanic=abort -Copt-level=0 \
  -Ztrust-verify=off -Ztrust-ir-cg-args=x86-body-trace -Ztrust-ir-cg-args=x86-body-dump="$OUT/dump" \
  --out-dir "$OUT/obj" "$OUT/smoke.rs" > "$OUT/stderr.log" 2>&1
echo "exit=$?" >> "$OUT/stderr.log"
