#!/bin/zsh
# Replay every fixture query whose outcome changed under AY build 12713, on the new AY with a
# 300 s budget (does it certify given time?) and on AY build 10530 with the lane's 30 s budget.
cd $HOME/tcg-scratch/runs/requal-12713 || exit 9
NEW=$HOME/.local/share/trust-overlays/x86-stage1-ay12713/bin/ay
OLD=$HOME/trust/build/x86_64-apple-darwin/stage1/bin/ay
OUT=inv/changed_replay.tsv
: > $OUT
for q in SubU128 MulI16 MulU64 MulPanics MulI64 MulU32 Diamonds5 Diamonds6 GuardChain9 SwitchChain LongArm CallJoin LoadDag NestedTree SlotJoin BoolDag MulU128; do
  nice python3 replay_one.py $OLD qdump/$q.smt2 - 1 >> $OUT
  nice python3 replay_one.py $NEW qdump/$q.smt2 300000 1 >> $OUT
done
echo INVESTIGATE-DONE >> $OUT
