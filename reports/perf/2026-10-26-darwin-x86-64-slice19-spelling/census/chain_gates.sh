#!/bin/zsh
# The remaining gates' builds on the branch tree (one heavy lane, nice 19, -j2): trust-cg-lower's
# library tests (built and run: no AY), then trust-cg-codegen's x86_source_bound_body and
# must_refuse_corpus targets (built only: they replay with AY, run after the qualification).
S=$HOME/tcg-scratch/s19; W=$HOME/tcg-scratch/wt-s19
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s19
cd $W || exit 9
while [ -e ~/tcg-scratch/quiet.request ]; do sleep 60; done
rm -rf "${CARGO_TARGET_DIR:?}/debug/incremental"
echo "== lower $(date +%H:%M)"
nice -n 19 bash scripts/trust_cargo.sh test -p trust-cg-lower --lib -j2 > $S/logs/gate_lower.log 2>&1
echo "lower rc=$?"; grep -E "^test result|FAILED" $S/logs/gate_lower.log | head
echo "== codegen build $(date +%H:%M)"
nice -n 19 bash scripts/trust_cargo.sh test --no-run -p trust-cg-codegen --test x86_source_bound_body --test must_refuse_corpus -j2 > $S/logs/gate_codegen_build.log 2>&1
echo "codegen build rc=$?"; grep -E "Executable|^error" $S/logs/gate_codegen_build.log | head
echo "CHAIN-GATES-DONE $(date)"
