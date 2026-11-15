#!/bin/zsh
# O2 knob censuses on main b30110fcd (slice 25 landed): one release bridge from
# the detached tree wt-m301, then four O2 core proof censuses from that dylib:
#   o2-m301        plain (control: must equal census-o2-s25, 254)
#   o2k-m301-lr    no-x86-licm no-x86-loop-rotate (slice 26's ceiling on S25)
#   o2k-m301-all   + no-x86-ifconvert no-x86-cmov-swap (S24c+S26 combined)
#   o2k-m301-allbm + no-x86-block-merge (what the merge alone still blocks)
# Each knob run is compared with the plain run of the same dylib.
# Run as: BUILD_SLOT_MEM_GB=6 build-slot -- zsh census.sh
W=$HOME/tcg-scratch/wt-m301
WANT=b30110fcd18b232de9fa9b3377f19f6a823801d3
OUT=$HOME/tcg-scratch/knobs-m301/out
P=$W/reports/perf
C=$P/2026-10-06-darwin-x86-64-census-slice15/census/census_compare.py
RC=$P/2026-09-27-darwin-x86-64-census/root_classes.py
F=$P/2026-11-04-darwin-x86-64-slice25-sib-rows/scripts/census_s25.py
R=$HOME/tcg-scratch/runs
unset CARGO_TARGET_DIR
[ "$(git -C $W rev-parse HEAD)" = "$WANT" ] || { echo "wt-m301 is not at $WANT"; exit 3; }
[ -z "$(git -C $W status --porcelain --untracked-files=no)" ] || { echo "wt-m301 is dirty"; exit 3; }
STAMP=$(mktemp); sleep 1
echo "bridge build $(date +%H:%M) at $WANT"
BOUT=$(~/tcg-scratch/build_bridge.t011.sh "$W"); echo "$BOUT" | tail -5
echo "$BOUT" | grep -qx "EXIT=0" || { echo "bridge build failed"; exit 3; }
D="$W/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
[ -f "$D" ] && [ "$D" -nt "$STAMP" ] || { echo "no fresh dylib: $D"; exit 3; }
shasum -a 256 "$D"
run() { # tag knobs...
  local T=$1; shift
  echo "== $T $(date +%H:%M) knobs=[$*]"
  ~/tcg-scratch/census_t011_dylib.sh "$D" $T 2 "$@" || { echo "$T census rc=$?"; return 1; }
  mkdir -p $OUT/$T
  python3 -I $RC $R/census-$T > $OUT/$T/root_classes.txt; echo "-- root classes $T"; head -25 $OUT/$T/root_classes.txt
}
cmpto() { # base new
  python3 -I $C $R/census-$1 $R/census-$2 $OUT/$2/vs-$1 > $OUT/$2/vs-$1.log 2>&1 || echo "compare rc=$?"
  echo "-- $2 vs $1"; head -12 $OUT/$2/vs-$1/compare.txt 2>/dev/null || head -12 $OUT/$2/vs-$1.log
}
run o2-m301 && {
  cmpto o2-s25 o2-m301
  cmp $R/census-o2-s25/failed_roots.jsonl $R/census-o2-m301/failed_roots.jsonl && echo "plain failed_roots byte-identical to o2-s25" || echo "plain failed_roots DIFFER from o2-s25"
}
run o2k-m301-lr no-x86-licm no-x86-loop-rotate && cmpto o2-m301 o2k-m301-lr
run o2k-m301-all no-x86-licm no-x86-loop-rotate no-x86-ifconvert no-x86-cmov-swap && {
  cmpto o2-m301 o2k-m301-all
  python3 -I $F $R/census-o2-m301 $R/census-o2k-m301-all $OUT/o2k-m301-all/followup > /dev/null && head -60 $OUT/o2k-m301-all/followup/followup.txt
}
run o2k-m301-allbm no-x86-licm no-x86-loop-rotate no-x86-ifconvert no-x86-cmov-swap no-x86-block-merge && cmpto o2-m301 o2k-m301-allbm
echo "KNOBS-M301-DONE $(date +%H:%M)"
