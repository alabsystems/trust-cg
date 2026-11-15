#!/bin/bash
# The S25.1 gate: build the lane's trust-cg-verify library tests (no run),
# mark the build done (so the sources may change again), run the solver-free
# x86 body suite, then the LeaSib control printer (its S25_LEA_SIB lines are
# compared with the fails-before record's). Run under build-slot.
MARK=${MARK:-s251}
cd ~/tcg-scratch/wt-s25 || exit 9
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s25
git -C ~/tcg-scratch/wt-s25 diff --stat
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 --no-run || { touch ~/tcg-scratch/s25-run/lane/markers/$MARK.built-failed; exit 7; }
touch ~/tcg-scratch/s25-run/lane/markers/$MARK.built
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- x86_source_bound_body::tests::
echo "suite-exit=$?"
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- x86_source_bound_body::tests::slice25::print_lea_sib_control_refusals --exact --ignored --nocapture
echo "printer-exit=$?"
