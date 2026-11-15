#!/bin/bash
# Build the lane's trust-cg-verify library tests, mark the build (MARK), and
# run the slice-25 solver-free module (extra test args passed through).
# Run under build-slot.
MARK=${MARK:?}
cd ~/tcg-scratch/wt-s25 || exit 9
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s25
git -C ~/tcg-scratch/wt-s25 diff --stat
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 --no-run || { touch ~/tcg-scratch/s25-run/lane/markers/$MARK.built-failed; exit 7; }
touch ~/tcg-scratch/s25-run/lane/markers/$MARK.built
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- x86_source_bound_body::tests::slice25:: "$@"
echo "module-exit=$?"
