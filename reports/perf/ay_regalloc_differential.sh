#!/usr/bin/env bash
# STAGE3-2 — AY-PBO register-allocation END-TO-END backend differential.
#
# Proves, through the REAL rustc bridge (`-Zcodegen-backend=<dylib>`), that the
# AY-PBO optimal register allocator (STAGE 3, crates/trust-cg-regalloc/src/
# ay_regalloc.rs) produces CORRECT machine code end-to-end: for every program in
# the beat-llvm corpus + the perf kernels (b01 int-loop, b05 matmul), at
# -Copt-level 0/2/3, the bridge binary compiled with `TCG_AY_REGALLOC=1` must
# yield the SAME process exit code (the folded checksum) as the LLVM binary.
# A single mismatch is a P0 stop-the-line (a wrong allocation the run-both-
# keep-better fallback + always-on translation validator + TV-4 missed).
#
# The bridge dylib must be built WITH the `ay-regalloc` feature:
#   (cd crates/rustc-codegen-trust-cg && cargo build --release --features ay-regalloc)
# With the feature compiled in but `TCG_AY_REGALLOC` unset, codegen is
# byte-identical to origin (the AY path is entered only when the env is set).
#
# Env knobs (all optional):
#   DYLIB=<path>            bridge dylib (default: the release build path)
#   PROOFS=on|off           certs+TV-4 on (default off = fast; regalloc runs
#                           upstream of cert emission, so the AY differential is
#                           valid either way; PROOFS=on additionally exercises
#                           the per-instruction cert + TV-4 post_regalloc_recheck
#                           surface with AY engaged and must not fail closed)
#   OPTS="0 2 3"            opt levels to sweep
#   PROGS_ONLY="a b"        restrict to these stems
#   MAXV/MAXP/AYMS          AY size/pair bounds + anytime cap (override to force
#                           engagement on larger functions)
#
# Author: Andrew Yates · Copyright 2026 Andrew Yates · License: Apache-2.0
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WT="$(cd "$HERE/../.." && pwd)"
DYLIB="${DYLIB:-$WT/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib}"
TC="${TCG_TOOLCHAIN:-nightly-2026-04-20}"
TARGET="${TARGET:-x86_64-apple-darwin}"
[[ -f "$DYLIB" ]] || { echo "FATAL: bridge dylib not found: $DYLIB (build with --features ay-regalloc)"; exit 2; }
SCRATCH="$(mktemp -d)"; trap 'rm -rf "$SCRATCH"' EXIT

AYENV=(TCG_AY_REGALLOC=1 TCG_AY_REGALLOC_MAX_VREGS="${MAXV:-400}" TCG_AY_REGALLOC_MAX_PAIRS="${MAXP:-40000}" TCG_AY_REGALLOC_MS="${AYMS:-800}")
if [[ "${PROOFS:-off}" == "off" ]]; then AYENV+=(TCG_NO_PROOF_CERTS=1); fi
ONLY="${PROGS_ONLY:-}"
PROGS_DIR="$WT/benchmarks/beat-llvm/progs"
BENCH_DIR="$WT/reports/perf/benches"

declare -a ITEMS=(
  "p1_xorshift:$PROGS_DIR/p1_xorshift.rs" "p2_collatz:$PROGS_DIR/p2_collatz.rs"
  "p3_gcd:$PROGS_DIR/p3_gcd.rs" "p4_matmul:$PROGS_DIR/p4_matmul.rs"
  "p5_struct_acc:$PROGS_DIR/p5_struct_acc.rs" "p6_branch_match:$PROGS_DIR/p6_branch_match.rs"
  "p7_sieve:$PROGS_DIR/p7_sieve.rs" "p8_closure_nest:$PROGS_DIR/p8_closure_nest.rs"
  "v1_saxpy:$PROGS_DIR/v1_saxpy.rs" "v2_memfill:$PROGS_DIR/v2_memfill.rs"
  "v3_popcount:$PROGS_DIR/v3_popcount.rs" "h1_vec_push_sum:$PROGS_DIR/h1_vec_push_sum.rs"
  "h2_vec_grow:$PROGS_DIR/h2_vec_grow.rs" "h4_vec_dropper:$PROGS_DIR/h4_vec_dropper.rs"
  "m1_call_chain:$PROGS_DIR/m1_call_chain.rs" "m2_call_heavy:$PROGS_DIR/m2_call_heavy.rs"
  "b1_mispredict:$PROGS_DIR/b1_mispredict.rs"
  "b01_intloop:$BENCH_DIR/b01_intloop_sum.rs" "b05_matmul:$BENCH_DIR/b05_matmul.rs"
)

# no_std/no_main kernels emit an object that we link with `cc` + abort stubs for
# any undefined panic_* symbols (mirrors reports/perf/run_bench.sh); std corpus
# programs are linked directly by rustc.
link_objdir() {
  local objdir="$1" bin="$2"; local objs=("$objdir"/*.o)
  [[ -e "${objs[0]}" ]] || return 1
  local stubs="$objdir/stubs.c"
  { echo '#include <stdlib.h>'
    nm -u "${objs[@]}" 2>/dev/null | while read -r line; do
      sym="${line#U}"; sym="${sym// /}"
      case "$sym" in *panic*) c="${sym#_}";
        echo "void ${c}(void) __asm__(\"${sym}\"); void ${c}(void){ abort(); }";; esac
    done; } > "$stubs"
  cc -o "$bin" "${objs[@]}" "$stubs" 2>/dev/null
}

compile_run() { # <src> <opt> <mode:llvm|bridge> <outbin>
  local src="$1" opt="$2" mode="$3" bin="$4"; local nostd=0
  grep -q "no_main" "$src" && nostd=1
  local pre=(); [[ "$mode" == bridge ]] && pre=(env "${AYENV[@]}")
  local be=(); [[ "$mode" == bridge ]] && be=(-Zcodegen-backend="$DYLIB")
  if [[ "$nostd" == 1 ]]; then
    local od="$SCRATCH/od"; rm -rf "$od"; mkdir -p "$od"
    "${pre[@]+"${pre[@]}"}" rustup run "$TC" rustc "${be[@]+"${be[@]}"}" --edition=2021 --crate-type bin \
      --target "$TARGET" -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1 \
      -Copt-level="$opt" --emit=obj -o "$od/o.o" "$src" >/dev/null 2>"$SCRATCH/err" || return 1
    link_objdir "$od" "$bin" || return 2
  else
    "${pre[@]+"${pre[@]}"}" rustup run "$TC" rustc "${be[@]+"${be[@]}"}" --edition=2021 --crate-type bin \
      --target "$TARGET" -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1 \
      -Copt-level="$opt" -o "$bin" "$src" >/dev/null 2>"$SCRATCH/err" || return 1
  fi
  return 0
}

mismatch=0; tested=0; failclosed=0
printf "%-16s %-4s %-9s %-11s %s\n" PROG OPT LLVM BRIDGEay VERDICT
for opt in ${OPTS:-0 2 3}; do
  for item in "${ITEMS[@]}"; do
    stem="${item%%:*}"; src="${item#*:}"
    if [[ -n "$ONLY" && " $ONLY " != *" $stem "* ]]; then continue; fi
    lbin="$SCRATCH/${stem}.l"; bbin="$SCRATCH/${stem}.b"
    if ! compile_run "$src" "$opt" llvm "$lbin"; then
      printf "%-16s O%-3s %-9s %-11s %s\n" "$stem" "$opt" "LLVMFAIL" "-" "SKIP"; continue; fi
    "$lbin"; lrc=$?
    if ! compile_run "$src" "$opt" bridge "$bbin"; then
      failclosed=$((failclosed+1))
      printf "%-16s O%-3s %-9s %-11s %s\n" "$stem" "$opt" "$lrc" "FAILCLOSED" "fc(ok)"; continue; fi
    "$bbin"; brc=$?; tested=$((tested+1))
    if [[ "$lrc" == "$brc" ]]; then v=MATCH; else v="*** MISMATCH ***"; mismatch=$((mismatch+1)); fi
    printf "%-16s O%-3s %-9s %-11s %s\n" "$stem" "$opt" "$lrc" "$brc" "$v"
  done
done
echo "-----"
echo "tested=$tested match=$((tested-mismatch)) mismatch=$mismatch failclosed(compile)=$failclosed proofs=${PROOFS:-off}"
if [[ "$mismatch" == 0 ]]; then
  echo "RESULT: 0-MISMATCH (AY-PBO regalloc correct end-to-end)"; exit 0
else
  echo "RESULT: *** MISMATCH -> P0 STOP-THE-LINE ***"; exit 1
fi
