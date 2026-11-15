#!/bin/zsh
# Slice 19: build the local x86 body probe (never committed) in a worktree.
# No proof claim: targo --unverified via scripts/trust_cargo.sh, nice -n 19, -j2.
# usage: build_probe.sh <worktree> <log> <copy-to>
W=${1:?worktree}; LOG=${2:?log}; OUTBIN=${3:?copy-to}
cd $W || exit 9
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s19
while [ -e ~/tcg-scratch/quiet.request ]; do sleep 60; done
rm -rf "${CARGO_TARGET_DIR:?}/debug/incremental"
date
nice -n 19 bash scripts/trust_cargo.sh build -p trust-cg-verify --example x86_body_probe -j2 > $LOG 2>&1
RC=$?
date
grep -E "^error|could not compile|Finished" $LOG | tail -20
[ $RC = 0 ] && cp $CARGO_TARGET_DIR/debug/examples/x86_body_probe $OUTBIN
echo "PROBE-BUILD-DONE rc=$RC"
