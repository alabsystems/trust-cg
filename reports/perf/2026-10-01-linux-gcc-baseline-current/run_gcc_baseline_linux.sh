#!/bin/bash
# Linux gcc baseline against the CURRENT trust-cg backend. The repo's
# run_gcc_baseline.sh is zsh + macOS (Homebrew gcc, -march=native,
# x86_64-apple-darwin, .dylib), so it cannot run here.
#
# clang is NOT measurable on this host: there is no clang driver anywhere
# ($HOME/trust/build/host/llvm/bin has only clang-offload-packager).
#
# Two gcc ISA levels are reported deliberately:
#   -march=x86-64  matches what rustc targets for x86_64-unknown-linux-gnu
#                  (baseline SSE2), so it is the apples-to-apples row;
#   -march=native  is what the repo's macOS script gives gcc, and on this
#                  Ryzen that unlocks AVX-512 the Rust lanes never use.
set -uo pipefail
export PATH="/usr/bin:$HOME/.cargo/bin:$PATH" CC=/usr/bin/gcc
R=/home/ayates/trust-cg-wt-cleanprof
S=$SCRATCH
cd "$R"
DY="$R/target-bridge/release/librustc_codegen_trust_cg.so"
TC=$HOME/trust/build/host/stage2/bin/trustc
gcc --version | head -1

best() { # best-of-N wall time in ms for "$@"
  local n=$1; shift; local b=999999
  for _ in $(seq "$n"); do
    local t0 t1 ms
    t0=$(date +%s%N); taskset -c 2 "$@" >/dev/null 2>&1; t1=$(date +%s%N)
    ms=$(( (t1-t0)/1000000 )); [ "$ms" -lt "$b" ] && b=$ms
  done
  echo "$b"
}

printf "  %-16s %6s %6s %8s %8s %9s %9s\n" program rust_ec gcc_ec trustcg gcc_base gcc_nat ratio_base
for c in benchmarks/beat-llvm/progs_c/*.c; do
  p=$(basename "$c" .c)
  rs="benchmarks/beat-llvm/progs/$p.rs"
  [ -f "$rs" ] || continue
  # trust-cg Rust binary
  $TC -Zcodegen-backend="$DY" -Ztrust-verify=off -Ztrust-ir-cg-args=no-proof-certs \
     --edition=2021 --crate-type bin --target x86_64-unknown-linux-gnu \
     -Cpanic=abort -Copt-level=3 -o "$S/gb_${p}_tcg" "$rs" >/dev/null 2>&1 || { printf "  %-16s RUST COMPILE FAILED\n" "$p"; continue; }
  /usr/bin/gcc -O3 -march=x86-64 -o "$S/gb_${p}_gccb" "$c" >/dev/null 2>&1 || { printf "  %-16s GCC COMPILE FAILED\n" "$p"; continue; }
  /usr/bin/gcc -O3 -march=native -o "$S/gb_${p}_gccn" "$c" >/dev/null 2>&1 || true
  # exit-code agreement: a port that disagrees is a broken port, not a result
  taskset -c 2 "$S/gb_${p}_tcg" >/dev/null 2>&1; rec=$?
  taskset -c 2 "$S/gb_${p}_gccb" >/dev/null 2>&1; gec=$?
  if [ "$rec" != "$gec" ]; then
    printf "  %-16s %6s %6s  PORT DISAGREES — not a result\n" "$p" "$rec" "$gec"; continue
  fi
  t=$(best 5 "$S/gb_${p}_tcg"); gb=$(best 5 "$S/gb_${p}_gccb")
  gn="-"; [ -x "$S/gb_${p}_gccn" ] && gn=$(best 5 "$S/gb_${p}_gccn")
  r="-"; [ "$gb" -gt 0 ] && r=$(awk -v a="$t" -v b="$gb" 'BEGIN{printf "%.3f", a/b}')
  printf "  %-16s %6s %6s %8s %8s %9s %9s\n" "$p" "$rec" "$gec" "$t" "$gb" "$gn" "$r"
done
echo "GCCBASE done at $(date -Is)"
