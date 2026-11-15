#!/bin/zsh
# The explicit (ignored) deadline-bound lane: each deadline-bound label replayed with the record's
# 300 s budget, on the qualification pair, in a process of its own.
BIN="${1:?test binary}"; OUT="${2:?out dir}"
OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay13556
export TCG_X86_BODY_QUALIFY_AY=$OVERLAY/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OVERLAY/bin/clean
mkdir -p "$OUT"; cd $HOME/tcg-scratch/wt-s23/crates/trust-cg-verify || exit 9
while [ -e $HOME/tcg-scratch/quiet.request ] || pgrep -f "[t]rust_ir_cg_census" >/dev/null; do sleep 60; done
T=x86_source_bound_body::tests::host_qualification_replays_each_deadline_bound_label_with_the_recorded_budget
START=$(date +%s)
RUST_MIN_STACK=67108864 nice -n 19 "$BIN" "$T" --exact --ignored --test-threads=1 --nocapture > "$OUT/deadline_bound.log" 2>&1
echo "deadline_bound exit=$? seconds=$(( $(date +%s) - START )) load=$(uptime | sed 's/.*averages: //')" >> "$OUT/summary.txt"
