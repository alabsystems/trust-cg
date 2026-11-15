#!/bin/bash
# clang on Linux against the CURRENT backend.
#
# There is no binary named `clang` on this host, which is why earlier runs
# recorded clang as unmeasurable. But `zig cc` IS a clang driver — zig 0.16.0
# bundles clang 21.1.0 targeting x86_64-unknown-linux-gnu — so clang's frontend
# and LLVM backend are both available after all.
#
# NOTE the scope: zig cc is used ONLY to compile the C benchmark corpus. It must
# NOT become the host CC for building trust-cg itself (it breaks the DRAT
# checker, the i128 differentials and the bridge link); that is a separate,
# recorded hazard and nothing here changes it.
set -uo pipefail
export PATH="/usr/bin:$HOME/.cargo/bin:$PATH" CC=/usr/bin/gcc
R=/home/ayates/trust-cg-wt-cleanprof
S=$SCRATCH
ZIG=/home/ayates/.local/bin/zig
cd "$R"
DY="$R/target-bridge/release/librustc_codegen_trust_cg.so"
TC=$HOME/trust/build/host/stage2/bin/trustc
$ZIG cc --version | head -1

best() { local n=$1; shift; local b=999999
  for _ in $(seq "$n"); do local t0 t1 ms
    t0=$(date +%s%N); taskset -c 2 "$@" >/dev/null 2>&1; t1=$(date +%s%N)
    ms=$(( (t1-t0)/1000000 )); [ "$ms" -lt "$b" ] && b=$ms; done; echo "$b"; }

printf "  %-16s %5s %5s %8s %9s %9s %10s\n" program r_ec c_ec trustcg clang_base clang_nat ratio_base
for c in benchmarks/beat-llvm/progs_c/*.c; do
  p=$(basename "$c" .c); rs="benchmarks/beat-llvm/progs/$p.rs"; [ -f "$rs" ] || continue
  tb="$S/gb_${p}_tcg"
  [ -x "$tb" ] || $TC -Zcodegen-backend="$DY" -Ztrust-verify=off -Ztrust-ir-cg-args=no-proof-certs \
     --edition=2021 --crate-type bin --target x86_64-unknown-linux-gnu \
     -Cpanic=abort -Copt-level=3 -o "$tb" "$rs" >/dev/null 2>&1
  [ -x "$tb" ] || { printf "  %-16s RUST COMPILE FAILED\n" "$p"; continue; }
  $ZIG cc -O3 -march=x86_64 -o "$S/cb_${p}_b" "$c" >/dev/null 2>&1 || { printf "  %-16s CLANG COMPILE FAILED\n" "$p"; continue; }
  $ZIG cc -O3 -march=native -o "$S/cb_${p}_n" "$c" >/dev/null 2>&1 || true
  taskset -c 2 "$tb" >/dev/null 2>&1; rec=$?
  taskset -c 2 "$S/cb_${p}_b" >/dev/null 2>&1; cec=$?
  if [ "$rec" != "$cec" ]; then printf "  %-16s %5s %5s  PORT DISAGREES — not a result\n" "$p" "$rec" "$cec"; continue; fi
  t=$(best 5 "$tb"); cb=$(best 5 "$S/cb_${p}_b")
  cn="-"; [ -x "$S/cb_${p}_n" ] && cn=$(best 5 "$S/cb_${p}_n")
  r="-"; [ "$cb" -gt 0 ] && r=$(awk -v a="$t" -v b="$cb" 'BEGIN{printf "%.3f", a/b}')
  printf "  %-16s %5s %5s %8s %9s %9s %10s\n" "$p" "$rec" "$cec" "$t" "$cb" "$cn" "$r"
done
echo "CLANGBASE done at $(date -Is)"
