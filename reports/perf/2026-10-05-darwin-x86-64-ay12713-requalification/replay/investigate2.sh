#!/bin/zsh
# The rest of investigate.sh, with a 310 s wall cap that kills AY's process group
# (AY build 12713 ran Diamonds5 past 900 s on a 300 s `:timeout`).
cd $HOME/tcg-scratch/runs/requal-12713 || exit 9
NEW=$HOME/.local/share/trust-overlays/x86-stage1-ay12713/bin/ay
OLD=$HOME/trust/build/x86_64-apple-darwin/stage1/bin/ay
OUT=inv/changed_replay.tsv
for q in SwitchChain LongArm CallJoin LoadDag NestedTree SlotJoin BoolDag MulU128; do
  [ $q = SwitchChain ] || nice python3 replay_one.py $OLD qdump/$q.smt2 - 1 >> $OUT
  nice python3 replay_one.py $NEW qdump/$q.smt2 300000 1 >> $OUT
done
echo INVESTIGATE-DONE >> $OUT
