#!/bin/bash
# The fails-before record: the slice-25 fixture section with one recording
# test, built and run in the detached worktree at 6c036f1de (slice 25.0).
# The generator is the lane's fails-before/make_fails_before.py; LANE (default
# the lane worktree) is the tree whose fixture section is copied, COPY the
# name the generated file is kept under. The base tree builds in its OWN target
# dir: one the lane tree also built in can hand cargo the lane's fresh-looking
# artifacts.
LANE=${LANE:-$HOME/tcg-scratch/wt-s25}
COPY=${COPY:-copy}
cd ~/tcg-scratch/wt-s25-base || exit 9
[ "$(git rev-parse HEAD)" = 6c036f1de27e70e9cca4dcc973ada6434c6f249d ] || { echo "wt-s25-base moved"; exit 9; }
python3 -I ~/tcg-scratch/wt-s25/reports/perf/2026-11-04-darwin-x86-64-slice25-sib-rows/fails-before/make_fails_before.py "$LANE" ~/tcg-scratch/wt-s25-base || exit 8
mkdir -p ~/tcg-scratch/s25-run/fails-before
cp crates/trust-cg-verify/src/x86_source_bound_body_slice25_tests.rs ~/tcg-scratch/s25-run/fails-before/${COPY}_x86_source_bound_body_slice25_tests.rs
git status --short
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s25-base-own
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- x86_source_bound_body::tests::slice25:: --include-ignored --nocapture --test-threads=1
