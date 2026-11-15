#!/bin/zsh
# Tool-gated slice-17 tests on the qualification pair the tree pins (QUALIFIED_AY): AY 0.27.0
# build 12713 and Clean 5f09e36c through the x86-stage1-ay12713 overlay (OD-85), ONE TEST PER
# PROCESS (an in-process session memo would otherwise answer a sibling test's queries).
# QDUMP=<dir> writes every replayed query there.
# usage: qualify.sh <test binary> <log> <exact test name>
BIN="${1:?test binary}"; LOG="${2:?log}"; TEST="${3:?test}"
OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay12713
export TCG_X86_BODY_QUALIFY_AY=${TCG_X86_BODY_QUALIFY_AY:-$OVERLAY/bin/ay}
export TCG_EXTERNAL_CLEAN_CHECKER=${TCG_EXTERNAL_CLEAN_CHECKER:-$OVERLAY/bin/clean}
[ -n "$QDUMP" ] && export TCG_X86_BODY_QUALIFY_DUMP="$QDUMP"
RUST_MIN_STACK=67108864 nice -n "${NICENESS:-19}" "$BIN" "$TEST" --exact --test-threads=1 --nocapture > "$LOG" 2>&1
RC=$?
echo "EXIT=$RC"
grep -E 'test result|FAILED|panicked|QUALIFICATION|REPLAY_IDENTITY|SKIP' "$LOG" | cut -c1-400 | head -80
