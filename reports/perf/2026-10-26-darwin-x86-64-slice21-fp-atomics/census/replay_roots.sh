#!/bin/zsh
# Replay the 12 roots' queries the probe wrote (<dir>/roots12.smt2) on AY 13556 + Clean 5f09e36c
# at the lane's 30 s deadline, one at a time (replay_one.py: strict Alethe one-shot, then Clean).
# Waits while ~/tcg-scratch/quiet.request exists or a trust-cg census runs.
# usage: replay_roots.sh <probe out dir> <out.txt>
D=${0:A:h}
AY=$HOME/.local/share/trust-overlays/x86-stage1-ay13556/bin/ay
Q=${1:?dir}/roots12.smt2; OUT=${2:?out}
for f in $Q/*.smt2; do
  until [ ! -e $HOME/tcg-scratch/quiet.request ] && ! pgrep -f '[t]rust_ir_cg_census' >/dev/null; do sleep 15; done
  echo "== $(grep "^$(basename $f .smt2)" $Q/index.tsv | cut -f2)" >> $OUT
  python3 $D/replay_one.py $AY $f 30000 1 >> $OUT
done
echo REPLAY-DONE >> $OUT
