#!/bin/zsh
# The codegen end-to-end body test and must-refuse corpus on the x86-stage1-ay13556 overlay
# (production replay routes: the resident `ay --incremental` first, then the fresh
# proof-producing solve), with the body trace on and every output line time-stamped
# (replay/stamp.py). usage: gate_e2e.sh <worktree> <log>
cd "${1:?worktree}" || exit 9
LOG="${2:?log}"
OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay13556
export TRUST_TARGO=$OVERLAY/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/$(basename "$PWD")
export TCG_X86_BODY_QUALIFY_AY=$OVERLAY/bin/ay
export TCG_EXTERNAL_CLEAN_CHECKER=$OVERLAY/bin/clean
export TCG_X86_BODY_TRACE=1
R=${0:A:h}
date > "$LOG"
nice -n 19 bash scripts/trust_cargo.sh test -p trust-cg-codegen --test x86_source_bound_body \
  --test must_refuse_corpus -j2 --no-fail-fast -- --nocapture --test-threads=1 2>&1 \
  | python3 "$R/stamp.py" >> "$LOG"
echo "EXIT=${pipestatus[1]}" >> "$LOG"
date >> "$LOG"
