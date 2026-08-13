#!/usr/bin/env bash
# Warm-start form (b) A/B — greedy-incumbent PHASE SEEDING on/off, at the
# SHIPPING caps (200ms anytime, 64 vregs, 4000 pairs), -Copt-level=3.
#
# For each pressured corpus function the f602c94 measurement mapped, compile
# through the real bridge twice with TCG_AY_REGALLOC=1 TCG_AY_REGALLOC_STATS=1:
#   A (seeded, default):  the solver's decision phases start at greedy's
#                         collapsed solution (PbCdclSolver::seed_phases);
#   B (TCG_AY_REGALLOC_NO_SEED=1): the pre-seed behavior (objective-direction
#                         phases only).
# and print the per-function [ay-regalloc] solver-result + keep lines side by
# side. The interesting deltas: Unknown -> Feasible/Optimal flips (the seed
# makes the 200ms budget conclude), lower kept-traffic costs, new keeps.
#
# MEASUREMENT ONLY — no keep-path change; the always-on validator + the
# strictly-better-or-decline bound gate every kept allocation in both arms.
#
# Env knobs: DYLIB=<path> OPTS="3" AYMS=200 PROGS_ONLY="stems"
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

PROGS_DIR="$WT/benchmarks/beat-llvm/progs"
BENCH_DIR="$WT/reports/perf/benches"
declare -a ITEMS=(
  "b01_intloop:$BENCH_DIR/b01_intloop_sum.rs"
  "p1_xorshift:$PROGS_DIR/p1_xorshift.rs" "p2_collatz:$PROGS_DIR/p2_collatz.rs"
  "p3_gcd:$PROGS_DIR/p3_gcd.rs" "p5_struct_acc:$PROGS_DIR/p5_struct_acc.rs"
  "p6_branch_match:$PROGS_DIR/p6_branch_match.rs" "p8_closure_nest:$PROGS_DIR/p8_closure_nest.rs"
  "m1_call_chain:$PROGS_DIR/m1_call_chain.rs" "m2_call_heavy:$PROGS_DIR/m2_call_heavy.rs"
  "b1_mispredict:$PROGS_DIR/b1_mispredict.rs"
  "h1_vec_push_sum:$PROGS_DIR/h1_vec_push_sum.rs"
)
ONLY="${PROGS_ONLY:-}"

compile_stats() { # <src> <opt> <mode:seed|noseed> <logfile>
  local src="$1" opt="$2" mode="$3" log="$4"
  local extra=(); [[ "$mode" == noseed ]] && extra=(TCG_AY_REGALLOC_NO_SEED=1)
  local od="$SCRATCH/od"; rm -rf "$od"; mkdir -p "$od"
  env TCG_AY_REGALLOC=1 TCG_AY_REGALLOC_STATS=1 TCG_NO_PROOF_CERTS=1 \
      TCG_AY_REGALLOC_MS="${AYMS:-200}" "${extra[@]+"${extra[@]}"}" \
    rustup run "$TC" rustc -Zcodegen-backend="$DYLIB" --edition=2021 --crate-type bin \
      --target "$TARGET" -Cpanic=abort -Coverflow-checks=off -Ccodegen-units=1 \
      -Copt-level="$opt" --emit=obj -o "$od/o.o" "$src" >/dev/null 2>"$log"
}

for opt in ${OPTS:-3}; do
  for item in "${ITEMS[@]}"; do
    stem="${item%%:*}"; src="${item#*:}"
    if [[ -n "$ONLY" && " $ONLY " != *" $stem "* ]]; then continue; fi
    echo "=== $stem O$opt ==="
    for mode in noseed seed; do
      log="$SCRATCH/$stem.$mode.log"
      if compile_stats "$src" "$opt" "$mode" "$log"; then st=ok; else st=FAILCLOSED; fi
      echo "--- $mode ($st)"
      grep -E "^\[ay-regalloc\]" "$log" | sed "s/^/    /" || true
    done
  done
done
