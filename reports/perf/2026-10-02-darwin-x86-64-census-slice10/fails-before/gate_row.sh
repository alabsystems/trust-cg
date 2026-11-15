#!/bin/zsh
# The slice-10 library gate row exactly as scripts/soundness_check.sh runs it
# (`test --locked -p trust-cg-verify --lib <filter> -- --show-output
# --test-threads=1`), parsed by `matrix_results.py check-cargo-gate
# --allow-filtered`. Stage-1 toolchain and the worktree's own target dir, as
# ~/tcg-scratch/gates_stage1.sh; the qualification variables are set only so
# the build matches the qualification runs (the filter's tests make no AY call).
# usage: gate_row.sh <log> [filter]
cd "$(dirname "$0")/../../../.." || exit 9
export TRUST_TARGO=${TRUST_TARGO:-$HOME/trust/build/x86_64-apple-darwin/stage1/bin/targo}
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$HOME/tcg-scratch/stage1-targets/$(basename "$PWD")}
export TCG_X86_BODY_QUALIFY_AY=${TCG_X86_BODY_QUALIFY_AY:-$HOME/trust/build/x86_64-apple-darwin/stage1/bin/ay}
export TCG_EXTERNAL_CLEAN_CHECKER=${TCG_EXTERNAL_CLEAN_CHECKER:-$HOME/clean-checker/bin/clean}
LOG=${1:?log}
FILTER=${2:-x86_source_bound_body::tests::slice10::}
nice bash scripts/trust_cargo.sh test --locked -p trust-cg-verify --lib "$FILTER" -- --show-output --test-threads=1 > "$LOG" 2>&1
RC=$?
echo "cargo rc=$RC"
python3 -I scripts/matrix_results.py check-cargo-gate "$LOG" "$RC" --allow-filtered
echo "parser rc=$?"
