#!/bin/zsh
# Tool-gated x86 body tests on the qualification pair the tree pins (QUALIFIED_AY): AY 0.27.0
# build 13556 (ebde49de3) and Clean 5f09e36c through the x86-stage1-ay13556 overlay (OD-190),
# ONE TEST PER PROCESS (an in-process session memo would otherwise answer a sibling test's
# queries). Before each test it waits while ~/tcg-scratch/quiet.request exists, a trust-cg
# census runs, or any other AY solver process runs (slice 19: one solver at a time on the
# host). Each test's replayed queries go to <out dir>/<test>/queries (TCG_X86_BODY_QUALIFY_DUMP).
# usage: qualify19.sh <worktree> <test binary> <out dir> <test name>...
W="${1:?worktree}"; BIN="${2:?test binary}"; OUT="${3:?out dir}"; shift 3
OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay13556
export TCG_X86_BODY_QUALIFY_AY=$OVERLAY/bin/ay
export TCG_EXTERNAL_CLEAN_CHECKER=$OVERLAY/bin/clean
export TRUST_TARGO=$OVERLAY/bin/targo
mkdir -p "$OUT"
cd "$W/crates/trust-cg-verify" || exit 9
busy() {
  [ -e $HOME/tcg-scratch/quiet.request ] || pgrep -f "[t]rust_ir_cg_census" >/dev/null \
    || pgrep -f "[/]ay(-[A-Za-z0-9]+)* +(-smt2|--incremental|solve)" >/dev/null
}
for TEST in "$@"; do
  while busy; do
    echo "# waiting (quiet.request, census or another AY) $(date +%H:%M:%S) before $TEST" >> "$OUT/waits.log"; sleep 30
  done
  NAME=${TEST##*::}
  mkdir -p "$OUT/$NAME/queries"
  START=$(date +%s)
  TCG_X86_BODY_QUALIFY_DUMP="$OUT/$NAME/queries" RUST_MIN_STACK=67108864 nice -n "${NICENESS:-19}" \
    "$BIN" "$TEST" --exact --test-threads=1 --nocapture --include-ignored > "$OUT/$NAME.log" 2>&1
  RC=$?
  echo "$NAME exit=$RC seconds=$(( $(date +%s) - START )) load=$(uptime | sed 's/.*averages: //')" >> "$OUT/summary.txt"
done
echo "QUALIFY-DONE $(date)" >> "$OUT/summary.txt"
