#!/bin/zsh
# Tool-gated slice-15 tests with the lane's qualification toolchain, as
# ~/tcg-scratch/gates_stage1.ay12713.sh: the x86-stage1-ay12713 overlay's targo, AY 0.27.0
# build 12713 (TCG_X86_BODY_QUALIFY_AY) and Clean 5f09e36c (TCG_EXTERNAL_CLEAN_CHECKER).
# Waits while ~/tcg-scratch/quiet.request exists or reclaimable memory (free + inactive +
# speculative pages) is below 1.6M pages. QDUMP=<dir> writes every replayed query there.
# usage: qualify.sh <log> <libtest filter> [libtest args...]
LOG="${1:?log}"; shift
FILTER="${1:?filter}"; shift
cd "$(dirname "$0")/../../../.." || exit 9
reclaimable() {
  vm_stat | awk '/Pages (free|inactive|speculative)/ {gsub(/\./,"",$NF); n += $NF} END {print n}'
}
until [ ! -e ~/tcg-scratch/quiet.request ] && [ "$(reclaimable)" -gt 1600000 ]; do sleep 30; done
OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay12713
export TRUST_TARGO=${TRUST_TARGO:-$OVERLAY/bin/targo}
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$HOME/tcg-scratch/stage1-targets/$(basename "$PWD")}
export CARGO_BUILD_JOBS=${CARGO_BUILD_JOBS:-2}
export TCG_X86_BODY_QUALIFY_AY=${TCG_X86_BODY_QUALIFY_AY:-$OVERLAY/bin/ay}
export TCG_EXTERNAL_CLEAN_CHECKER=${TCG_EXTERNAL_CLEAN_CHECKER:-$OVERLAY/bin/clean}
[ -n "$QDUMP" ] && export TCG_X86_BODY_QUALIFY_DUMP="$QDUMP"
nice bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -- "$FILTER" --nocapture "$@" > "$LOG" 2>&1
RC=$?
echo "EXIT=$RC"
grep -E 'test result|FAILED|panicked|QUALIFICATION|REPLAY_IDENTITY|SKIP' "$LOG" | cut -c1-400 | head -60
