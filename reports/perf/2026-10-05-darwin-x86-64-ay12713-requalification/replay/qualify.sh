#!/bin/zsh
# Run trust-cg-verify's x86 host-qualification tests under the x86-stage1-ay12713 overlay.
# usage: qualify.sh <log name> [test filter ...]
cd $HOME/trust-cg/.claude/worktrees/agent-a7f097cbafaac5b63 || exit 9
LOG=$HOME/tcg-scratch/runs/requal-12713/${1:?log}.log
shift
OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay12713
export TRUST_TARGO=$OVERLAY/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/agent-a7f097cbafaac5b63
export TCG_X86_BODY_QUALIFY_AY=$OVERLAY/bin/ay
export TCG_EXTERNAL_CLEAN_CHECKER=$OVERLAY/bin/clean
export TCG_X86_BODY_QUALIFY_DUMP=$HOME/tcg-scratch/runs/requal-12713/qdump
date > $LOG
nice bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- "$@" --nocapture --test-threads=1 >> $LOG 2>&1
echo "EXIT=$?" >> $LOG
date >> $LOG
