#!/bin/bash
# The lane's test wrapper: one cargo test invocation of trust-cg-verify's
# library tests in ~/tcg-scratch/wt-s24a (the t011 overlay targo), args passed
# through. Run under build-slot.
cd ~/tcg-scratch/wt-s24a || exit 9
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s24a
exec bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- "$@"
