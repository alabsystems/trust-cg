#!/usr/bin/env bash
# Prove a dylib build-config change did NOT alter emitted code.
#
# Compiles the same sources to the SAME output path with two dylibs and
# compares sha256. Using one fixed path matters: rustc hashes the output
# filename into symbol/metadata, so differing -o names alone change the hash.
#   usage: dylib_codegen_identity.sh <dylib-A> <dylib-B>
set -euo pipefail
A="$1"; B="$2"
RUSTC="$(rustup which --toolchain nightly-2026-04-20 rustc)"
SCRATCH="${SCRATCH:-/tmp/claude-1000/-home-ayates-trust-cg/06b728f2-f196-4490-9fb3-3291b4078e33/scratchpad}"
W="$SCRATCH/ident"; rm -rf "$W"; mkdir -p "$W"
export TCG_NO_PROOF_CERTS=1 TCG_REFINE_SOLVER=0

cat > "$W/bench.rs" <<'RS'
use std::hint::black_box as bb;
fn main() {
    let mut x: u64 = bb(0x9E3779B97F4A7C15u64);
    let mut acc: u64 = 0;
    let mut i: u64 = 0;
    let n = bb(10_000u64);
    while i < n {
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        acc = acc.wrapping_add(x ^ i);
        acc ^= i.rotate_left((i % 63) as u32);
        acc = acc.wrapping_mul(0x2545F4914F6CDD1D);
        i += 1;
    }
    std::process::exit((acc % 126) as i32);
}
RS

run() { # $1=dylib $2=optlevel -> prints sha256 of the fixed-path artifact
  local so="$1" lvl="$2"
  rm -f "$W/out.bin"
  "$RUSTC" "-Zcodegen-backend=$so" --edition=2021 --crate-type bin \
      -Cpanic=abort "-Copt-level=$lvl" -o "$W/out.bin" "$W/bench.rs" >/dev/null 2>"$W/err.txt" || {
      echo "COMPILE-FAILED"; sed -n '1,20p' "$W/err.txt" >&2; return 0; }
  sha256sum "$W/out.bin" | awk '{print $1}'
}

rc=0
for lvl in 0 1 2 3; do
  ha="$(run "$A" "$lvl")"; hb="$(run "$B" "$lvl")"
  if [ "$ha" = "$hb" ] && [ "$ha" != "COMPILE-FAILED" ]; then
    echo "  opt-level=$lvl  IDENTICAL   $ha"
  else
    echo "  opt-level=$lvl  *** DIFFER ***  A=$ha  B=$hb"; rc=1
  fi
done
exit $rc
