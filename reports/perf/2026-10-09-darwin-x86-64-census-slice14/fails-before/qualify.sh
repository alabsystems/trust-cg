#!/bin/zsh
# Slice-14 tests on the qualification pair the tree pins (QUALIFIED_AY): AY 0.27.0 build 12713
# and Clean 5f09e36c through the x86-stage1-ay12713 overlay (OD-85), one job, niced (a shared
# host). QDUMP=<dir> writes every replayed query there.
# usage: qualify.sh <log> <libtest filter> [libtest args...]
LOG="${1:?log}"; shift
FILTER="${1:?filter}"; shift
cd "$(dirname "$0")/../../../.." || exit 9
OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay12713
export TRUST_TARGO=${TRUST_TARGO:-$OVERLAY/bin/targo}
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$HOME/tcg-scratch/stage1-targets/$(basename "$PWD")}
export TCG_X86_BODY_QUALIFY_AY=${TCG_X86_BODY_QUALIFY_AY:-$OVERLAY/bin/ay}
export TCG_EXTERNAL_CLEAN_CHECKER=${TCG_EXTERNAL_CLEAN_CHECKER:-$OVERLAY/bin/clean}
[ -n "$QDUMP" ] && export TCG_X86_BODY_QUALIFY_DUMP="$QDUMP"
nice -n 19 bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j1 -- "$FILTER" --nocapture "$@" > "$LOG" 2>&1
RC=$?
echo "EXIT=$RC"
grep -E 'test result|FAILED|panicked|QUALIFICATION|REPLAY_IDENTITY|SKIP' "$LOG" | cut -c1-400 | head -80
