#!/bin/zsh
# The verify step of ~/tcg-scratch/gates_stage1.ay12713.sh with its complete output kept.
# usage: gate_verify.sh <log name>
cd $HOME/trust-cg/.claude/worktrees/agent-a7f097cbafaac5b63 || exit 9
LOG=$HOME/tcg-scratch/runs/requal-12713/${1:?log}.log
OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay12713
export TRUST_TARGO=$OVERLAY/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/agent-a7f097cbafaac5b63
export TCG_X86_BODY_QUALIFY_AY=$OVERLAY/bin/ay
export TCG_EXTERNAL_CLEAN_CHECKER=$OVERLAY/bin/clean
date > $LOG
nice bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- x86_source_bound_body x86_source_bound_envelope diag:: >> $LOG 2>&1
echo "EXIT=$?" >> $LOG
date >> $LOG
