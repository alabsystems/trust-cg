#!/bin/bash
# The fails-before record: the slice-24a fixture section with one recording
# test, built and run in the detached worktree at 7ee0def54. The generator
# is the lane's committed fails-before/make_fails_before.py.
cd ~/tcg-scratch/wt-s24a-base || exit 9
python3 -I ~/tcg-scratch/wt-s24a/reports/perf/2026-11-04-darwin-x86-64-slice24a-chain-quotient/fails-before/make_fails_before.py ~/tcg-scratch/wt-s24a ~/tcg-scratch/wt-s24a-base || exit 8
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s24a
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- x86_source_bound_body::tests::slice24::s24_fails_before --exact --nocapture
