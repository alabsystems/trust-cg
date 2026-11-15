#!/bin/zsh
# Tool-gated slice-9 tests with the stage-1 toolchain, as ~/tcg-scratch/gates_stage1.sh:
# AY 0.27.0 build 10530 (TCG_X86_BODY_QUALIFY_AY) and Clean 5f09e36c
# (TCG_EXTERNAL_CLEAN_CHECKER). QDUMP=<dir> writes every replayed query there.
# usage: qualify.sh <log> <libtest filter> [libtest args...]
LOG="${1:?log}"; shift
FILTER="${1:?filter}"; shift
cd "$(dirname "$0")/../../../.." || exit 9
export TRUST_TARGO=${TRUST_TARGO:-$HOME/trust/build/x86_64-apple-darwin/stage1/bin/targo}
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$HOME/tcg-scratch/stage1-targets/$(basename "$PWD")}
export TCG_X86_BODY_QUALIFY_AY=${TCG_X86_BODY_QUALIFY_AY:-$HOME/trust/build/x86_64-apple-darwin/stage1/bin/ay}
export TCG_EXTERNAL_CLEAN_CHECKER=${TCG_EXTERNAL_CLEAN_CHECKER:-$HOME/clean-checker/bin/clean}
[ -n "$QDUMP" ] && export TCG_X86_BODY_QUALIFY_DUMP="$QDUMP"
nice bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- "$FILTER" --nocapture "$@" > "$LOG" 2>&1
RC=$?
echo "EXIT=$RC"
grep -E 'test result|FAILED|panicked|QUALIFICATION|REPLAY_IDENTITY|SKIP' "$LOG" | cut -c1-400 | head -60
