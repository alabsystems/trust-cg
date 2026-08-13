#!/usr/bin/env bash
# INTERLEAVED runtime A/B: greedy (TCG_AY_REGALLOC unset) vs AY-kept
# (TCG_AY_REGALLOC=1, warm-start seeded by default; TCG_AY_REGALLOC_NO_SEED=1
# for the unseeded arm via SEED=off) on the self-iterating no_std perf kernels.
#
# Builds each kernel twice through the SAME bridge dylib (only the env
# differs), links with cc + abort stubs, verifies BOTH binaries yield the same
# exit code (correctness oracle), then runs A/B interleaved N rounds
# (A B A B ...) and reports per-arm min/median — interleaving spreads
# thermal/background drift across both arms instead of biasing one.
#
# Env: DYLIB=<path> ROUNDS=7 OPT=3 AYMS=200 SEED=on|off PROGS_ONLY="stems"
#
# Author: Andrew Yates · Copyright 2026 Andrew Yates · License: Apache-2.0
set -u
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WT="$(cd "$HERE/../.." && pwd)"
DYLIB="${DYLIB:-$WT/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib}"
TC="${TCG_TOOLCHAIN:-nightly-2026-04-20}"
TARGET="${TARGET:-x86_64-apple-darwin}"
[[ -f "$DYLIB" ]] || { echo "FATAL: bridge dylib not found: $DYLIB"; exit 2; }
SCRATCH="$(mktemp -d)"; trap 'rm -rf "$SCRATCH"' EXIT
ROUNDS="${ROUNDS:-7}"; OPT="${OPT:-3}"

PROGS_DIR="$WT/benchmarks/beat-llvm/progs"
BENCH_DIR="$WT/reports/perf/benches"
declare -a ITEMS=(
  "b01_intloop:$BENCH_DIR/b01_intloop_sum.rs"
  "p2_collatz:$PROGS_DIR/p2_collatz.rs" "p5_struct_acc:$PROGS_DIR/p5_struct_acc.rs"
  "m1_call_chain:$PROGS_DIR/m1_call_chain.rs" "m2_call_heavy:$PROGS_DIR/m2_call_heavy.rs"
)
ONLY="${PROGS_ONLY:-}"

link_objdir() { # <objdir> <bin>
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

compile_bin() { # <src> <arm:greedy|ay> <bin>
  local src="$1" arm="$2" bin="$3"
  local pre=(TCG_NO_PROOF_CERTS=1)
  if [[ "$arm" == ay ]]; then
    pre+=(TCG_AY_REGALLOC=1 TCG_AY_REGALLOC_MS="${AYMS:-200}")
    [[ "${SEED:-on}" == off ]] && pre+=(TCG_AY_REGALLOC_NO_SEED=1)
  fi
  local od="$SCRATCH/od"; rm -rf "$od"; mkdir -p "$od"
  env "${pre[@]}" rustup run "$TC" rustc -Zcodegen-backend="$DYLIB" --edition=2021 \
    --crate-type bin --target "$TARGET" -Cpanic=abort -Coverflow-checks=off \
    -Ccodegen-units=1 -Copt-level="$OPT" --emit=obj -o "$od/o.o" "$src" \
    >/dev/null 2>"$SCRATCH/err" || return 1
  link_objdir "$od" "$bin"
}

ms_run() { # <bin> -> echoes elapsed ms
  local t0 t1
  t0=$(python3 -c 'import time; print(int(time.time()*1000))')
  "$1" >/dev/null 2>&1
  t1=$(python3 -c 'import time; print(int(time.time()*1000))')
  echo $((t1 - t0))
}

stats() { # numbers on stdin -> "min median"
  sort -n | awk '{a[NR]=$1} END {m=(NR%2)?a[(NR+1)/2]:int((a[NR/2]+a[NR/2+1])/2); print a[1], m}'
}

printf "%-16s %-8s %-8s %-8s %-8s %s\n" PROG Gmin Gmed AYmin AYmed VERDICT
for item in "${ITEMS[@]}"; do
  stem="${item%%:*}"; src="${item#*:}"
  if [[ -n "$ONLY" && " $ONLY " != *" $stem "* ]]; then continue; fi
  gbin="$SCRATCH/$stem.g"; abin="$SCRATCH/$stem.a"
  compile_bin "$src" greedy "$gbin" || { echo "$stem greedy FAILCLOSED"; continue; }
  compile_bin "$src" ay     "$abin" || { echo "$stem ay FAILCLOSED"; continue; }
  "$gbin"; grc=$?; "$abin"; arc=$?
  if [[ "$grc" != "$arc" ]]; then echo "$stem *** EXIT MISMATCH g=$grc ay=$arc ***"; exit 1; fi
  gt=(); at=()
  for ((r=0; r<ROUNDS; r++)); do
    gt+=("$(ms_run "$gbin")"); at+=("$(ms_run "$abin")")
  done
  read -r gmin gmed < <(printf "%s\n" "${gt[@]}" | stats)
  read -r amin amed < <(printf "%s\n" "${at[@]}" | stats)
  v="~"; if ((amed < gmed)); then v="AY faster"; elif ((amed > gmed)); then v="greedy faster"; fi
  printf "%-16s %-8s %-8s %-8s %-8s %s (exit %s, raw g:[%s] ay:[%s])\n" \
    "$stem" "$gmin" "$gmed" "$amin" "$amed" "$v" "$grc" "${gt[*]}" "${at[*]}"
done
