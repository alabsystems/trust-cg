#!/bin/zsh
# Slice 19: build trust-cg-verify's library tests in a worktree (no proof claim: targo
# --unverified via scripts/trust_cargo.sh, nice -n 19, -j2), and print the test binary.
# usage: build_tests.sh <worktree> <log>
W=${1:?worktree}; LOG=${2:?log}
cd $W || exit 9
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s19
while [ -e ~/tcg-scratch/quiet.request ]; do sleep 60; done
rm -rf "${CARGO_TARGET_DIR:?}/debug/incremental"
date
nice -n 19 bash scripts/trust_cargo.sh test -p trust-cg-verify --lib --no-run -j2 > $LOG 2>&1
RC=$?
date
grep -E "^error|could not compile|Finished|Executable" $LOG | tail -5
echo "TEST-BUILD-DONE rc=$RC"
