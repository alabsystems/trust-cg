#!/bin/zsh
# Every recorded gap left after the move, and SubU128 (which leaves), replayed offline on AY
# build 13556 with a 300 s budget (`replay/replay_one.py`, one-shot strict Alethe, then Clean),
# from the qualification run's own dumped queries. Sequential; waits on quiet.request or a
# census before each query.
# usage: gaps300.sh <ledger dir> <out tsv>
L="${1:?ledger dir}"; OUT="${2:?out tsv}"
AY=$HOME/.local/share/trust-overlays/x86-stage1-ay13556/bin/ay
R=${0:A:h}
: > "$OUT"
for q in \
  host_qualification_replays_the_canonical_body_theorems/queries/MulI16.smt2 \
  host_qualification_replays_the_canonical_body_theorems/queries/Mul__commuted.smt2 \
  host_qualification_replays_the_slice_nine_body_theorems/queries/LongChain.smt2 \
  host_qualification_replays_the_slice_ten_body_theorems/queries/MulU64.smt2 \
  host_qualification_replays_the_slice_eleven_body_theorems/queries/SubU128.smt2 \
  host_qualification_replays_the_slice_eleven_body_theorems/queries/MulU128.smt2 \
  host_qualification_replays_the_slice_fourteen_body_theorems/queries/UdivConst.smt2 \
  host_qualification_replays_the_slice_fourteen_body_theorems/queries/UremConst32.smt2 \
  host_qualification_replays_the_slice_sixteen_parts/queries/LongChain.part1.smt2 \
  host_qualification_replays_the_slice_sixteen_parts/queries/LongChain.part2.smt2 \
  host_qualification_replays_the_slice_sixteen_parts/queries/LongChain.part3.smt2; do
  while [ -e $HOME/tcg-scratch/quiet.request ] || pgrep -f "[t]rust_ir_cg_census" >/dev/null; do sleep 60; done
  printf '%s\t' "${q%%/*}" >> "$OUT"
  nice -n 19 python3 "$R/replay_one.py" "$AY" "$L/$q" 300000 >> "$OUT" 2>&1
done
echo "GAPS300-DONE $(date)" >> "$OUT"
