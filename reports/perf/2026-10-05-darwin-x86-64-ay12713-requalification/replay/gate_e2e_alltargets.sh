#!/bin/zsh
# The codegen end-to-end body test with its output, then `--lib --tests --no-run --keep-going`
# of every root-workspace test target, both on the x86-stage1-ay12713 overlay.
cd $HOME/trust-cg/.claude/worktrees/agent-a7f097cbafaac5b63 || exit 9
R=$HOME/tcg-scratch/runs/requal-12713
OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay12713
export TRUST_TARGO=$OVERLAY/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/agent-a7f097cbafaac5b63
export TCG_EXTERNAL_CLEAN_CHECKER=$OVERLAY/bin/clean
if [ "${1:-}" != "--alltargets-only" ]; then
  date > $R/e2e.log
  nice bash scripts/trust_cargo.sh test -p trust-cg-codegen --test x86_source_bound_body -j2 -- --nocapture >> $R/e2e.log 2>&1
  echo "EXIT=$?" >> $R/e2e.log
fi
# `test` takes no --keep-going; `build --lib --tests` compiles the same test targets.
date > $R/gates_alltargets.log
nice bash scripts/trust_cargo.sh build --workspace --lib --tests --keep-going -j2 >> $R/gates_alltargets.log 2>&1
echo "EXIT=$?" >> $R/gates_alltargets.log
date >> $R/gates_alltargets.log
