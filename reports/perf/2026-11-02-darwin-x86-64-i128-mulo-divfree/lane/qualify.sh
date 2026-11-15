#!/bin/zsh
# OD-224 lane (the OD-215 lane's qualify.sh): tool-gated x86 body tests, ONE TEST
# PER PROCESS, each through build-slot, on the qualification pair AY 0.27.0 build 13556 + Clean
# 5f09e36c from the x86-stage1-ay13556-t011 overlay (byte-identical to the x86-stage1-ay13556
# overlay's). It waits while ~/tcg-scratch/quiet.request exists or a census runs, before taking the
# slot. Each test's replayed queries go to <out dir>/<test>/queries (TCG_X86_BODY_QUALIFY_DUMP).
# usage: qualify.sh <test binary> <out dir> <test name>...
export BUILD_SLOT_MEM_GB=6
BIN="${1:?test binary}"; OUT="${2:?out dir}"; shift 2
OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
export TCG_X86_BODY_QUALIFY_AY=$OVERLAY/bin/ay
export TCG_EXTERNAL_CLEAN_CHECKER=$OVERLAY/bin/clean
mkdir -p "$OUT"
cd $HOME/tcg-scratch/wt-mulo/crates/trust-cg-verify || exit 9
for TEST in "$@"; do
  while [ -e $HOME/tcg-scratch/quiet.request ] || pgrep -f "[t]rust_ir_cg_census" >/dev/null; do
    echo "# waiting (quiet.request or census) $(date +%H:%M:%S) before $TEST" >> "$OUT/waits.log"; sleep 60
  done
  NAME=${TEST##*::}
  mkdir -p "$OUT/$NAME/queries"
  START=$(date +%s)
  build-slot -- env TCG_X86_BODY_QUALIFY_DUMP="$OUT/$NAME/queries" RUST_MIN_STACK=67108864 \
    nice -n 19 "$BIN" "$TEST" --exact --test-threads=1 --nocapture > "$OUT/$NAME.log" 2>&1
  RC=$?
  echo "$NAME exit=$RC seconds=$(( $(date +%s) - START )) load=$(uptime | sed 's/.*averages: //')" >> "$OUT/summary.txt"
done
echo "QUALIFY-DONE $(date)" >> "$OUT/summary.txt"
