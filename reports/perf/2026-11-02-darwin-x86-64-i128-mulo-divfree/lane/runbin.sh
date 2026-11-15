#!/bin/zsh
# OD-224 lane: run a saved test binary under build-slot from the verify crate dir, solver lanes on the
# t011 qualification pair. usage: runbin.sh <binary> <test args...>
export BUILD_SLOT_MEM_GB=6
BIN=${1:?binary}; shift
OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
export TCG_X86_BODY_QUALIFY_AY=$OVERLAY/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OVERLAY/bin/clean
cd $HOME/tcg-scratch/wt-mulo/crates/trust-cg-verify || exit 9
while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
exec build-slot -- env RUST_MIN_STACK=67108864 nice -n 19 "$BIN" "$@"
