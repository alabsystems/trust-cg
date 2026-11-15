#!/bin/zsh
# Three-way -O3 baseline: gcc vs clang vs LLVM-rustc vs trust-cg.
#
# The standing goal names gcc as a competitor, but until 2026-08-31 gcc had
# NEVER been measured here: /usr/bin/gcc on macOS is an Apple-clang shim, so
# every "gcc" number in this project's history was really clang. The real
# compiler is Homebrew's, at $(brew --prefix gcc)/bin/gcc-NN.
#
# gcc cannot compile Rust, so progs_c/ holds C ports of the scalar kernels:
# identical algorithm, identical constants, and `bb()` — an empty asm barrier —
# standing in for Rust's std::hint::black_box. Every port is exit-code checked
# against all four toolchains before it is timed; a port that disagrees is a
# broken port, not a result.
#
# Both Rust lanes use the Trust compiler the bridge pin (channel = "trust")
# names, resolved by scripts/trust_toolchain.py from the PATH trustc/targo
# package or the package trustc named by --driver; the retired stock nightly and
# any unidentified compiler stop the script. Both compile in Trust's explicit
# unverified frontend lane (-Ztrust-verify=off), a diagnostic lane with no
# Trust-verified compilation claim.
#
# Scope: an x86_64 macOS diagnostic (zsh, Homebrew gcc, clang, `-march=native`,
# `--target x86_64-apple-darwin`, a `.dylib` backend unless BRIDGE_DYLIB names
# one). It feeds no ledger row and does not use scripts/bridge_backend.py's
# host-suffixed resolution or freshness check.
#
# Usage: run_gcc_baseline.sh [--driver TRUSTC] [prog ...]
set -e
HERE=${0:a:h}
DRIVER_ARGS=()
if [[ ${1:-} == --driver ]]; then
  (( $# >= 2 )) || { print -u2 "gcc-baseline: --driver needs a trustc path"; exit 2; }
  DRIVER_ARGS=(--driver $2)
  shift 2
fi
GCC=${GCC_BIN:-$(brew --prefix gcc)/bin/gcc-16}
RUSTC=$(python3 $HERE/../../scripts/trust_toolchain.py $DRIVER_ARGS --print compiler)
print "gcc-baseline: driver $(python3 $HERE/../../scripts/trust_toolchain.py --driver $RUSTC --print summary)"
DY=${BRIDGE_DYLIB:-$HERE/../../crates/rustc-codegen-trust-cg/target-bridge/release/librustc_codegen_trust_cg.dylib}
OUT=${OUT_DIR:-${TMPDIR:-/tmp}/tcg-gcc-baseline}
REPS=${REPS:-8}
mkdir -p $OUT
# The VECTORIZABLE ports (v1/v2/v3) were added 2026-09-28. They are the rows that
# matter most for the "at least LLVM/clang" clause: trust-cg reads 0.401x against
# LLVM-through-rustc and 0.415x against clang AT EQUAL ISA, so measuring only the
# scalar kernels understates the backend.
#
# ISA WARNING, learned the hard way: if `clang` here is a `zig cc` wrapper (this
# host's `~/.local/bin/cc` is), it defaults to the NATIVE CPU and will emit
# AVX-512 while the Rust lanes run at `-C target-cpu` default (SSE2). That is a 4x
# width advantage and it produced a spurious "1.875x slower than clang" reading
# that had to be withdrawn. Use `-target x86_64-linux-gnu` (zig) or `-march=x86-64`
# (real clang/gcc) for an equal-ISA row, and report a native row separately.
PROGS=(${@:-p1_xorshift p2_collatz p3_gcd p5_struct_acc p7_sieve v1_saxpy v2_memfill v3_popcount p6_branch_match m1_call_chain m2_call_heavy b1_mispredict p8_closure_nest p4_matmul})

# TCG_NO_PROOF_CERTS: this script measures RUNTIME of emitted code. Proof
# certificates affect compile time only. (It is also required while the
# production promotion lane is broken upstream — see the TCG-PROOF-465 handoff.)
for P in $PROGS; do
  $GCC -O3 -march=native -o $OUT/${P}_gcc     $HERE/progs_c/$P.c
  clang -O3 -march=native -o $OUT/${P}_clang  $HERE/progs_c/$P.c
  "$RUSTC" -Ztrust-verify=off --edition=2021 --crate-type bin --target x86_64-apple-darwin \
      -Cpanic=abort -Copt-level=3 -o $OUT/${P}_llvmrs $HERE/progs/$P.rs 2>/dev/null
  "$RUSTC" -Ztrust-verify=off -Ztrust-ir-cg-args=no-proof-certs -Zcodegen-backend=$DY --edition=2021 \
      --crate-type bin --target x86_64-apple-darwin -Cpanic=abort -Copt-level=3 \
      -o $OUT/${P}_tcg $HERE/progs/$P.rs 2>/dev/null
  $OUT/${P}_gcc; g=$?; $OUT/${P}_clang; c=$?; $OUT/${P}_llvmrs; l=$?; $OUT/${P}_tcg; t=$?
  if [ "$g" != "$c" ] || [ "$g" != "$l" ] || [ "$g" != "$t" ]; then
    echo "FATAL $P: exit codes disagree (gcc=$g clang=$c llvm-rs=$l tcg=$t) — the C port is not equivalent"
    exit 2
  fi
done

printf "%-16s %9s %9s %9s %9s %9s %9s\n" prog gcc clang llvm-rs trust-cg tcg/gcc tcg/llvm
for P in $PROGS; do
  gs=0; cs=0; ls=0; ts=0
  for i in $(seq 1 $REPS); do
    gs=$(echo "$gs+$( { /usr/bin/time -p $OUT/${P}_gcc; } 2>&1 | awk '/real/{print $2}')"|bc)
    cs=$(echo "$cs+$( { /usr/bin/time -p $OUT/${P}_clang; } 2>&1 | awk '/real/{print $2}')"|bc)
    ls=$(echo "$ls+$( { /usr/bin/time -p $OUT/${P}_llvmrs; } 2>&1 | awk '/real/{print $2}')"|bc)
    ts=$(echo "$ts+$( { /usr/bin/time -p $OUT/${P}_tcg; } 2>&1 | awk '/real/{print $2}')"|bc)
  done
  gm=$(echo "scale=4;$gs/$REPS"|bc); cm=$(echo "scale=4;$cs/$REPS"|bc)
  lm=$(echo "scale=4;$ls/$REPS"|bc); tm=$(echo "scale=4;$ts/$REPS"|bc)
  printf "%-16s %9s %9s %9s %9s %9s %9s\n" $P $gm $cm $lm $tm \
      $(echo "scale=3;$tm/$gm"|bc) $(echo "scale=3;$tm/$lm"|bc)
done
