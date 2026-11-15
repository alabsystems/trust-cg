#!/bin/zsh
# Slice-23 lane: one trust_cargo.sh verb in the wt-s23 worktree with the AY 13556 overlay,
# through the machine-wide build gate. usage: run.sh <trust_cargo args...>
# build-slot admits one job at a time; 6 GiB is the documented memory override (coordinator, 2026-10-27).
export BUILD_SLOT_MEM_GB=6
cd $HOME/tcg-scratch/wt-s23 || exit 9
OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay13556
export TRUST_TARGO=$OVERLAY/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s23
export TCG_X86_BODY_QUALIFY_AY=$OVERLAY/bin/ay
export TCG_EXTERNAL_CLEAN_CHECKER=$OVERLAY/bin/clean
while [ -e $HOME/tcg-scratch/quiet.request ]; do echo "# quiet.request $(date +%T)"; sleep 60; done
exec build-slot -- nice -n 19 bash scripts/trust_cargo.sh "$@"
