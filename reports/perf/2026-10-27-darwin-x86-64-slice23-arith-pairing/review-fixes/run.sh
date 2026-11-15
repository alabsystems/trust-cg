#!/bin/zsh
# Slice-23 review fixes, on the code merged with origin/main 9d9e1a372: one trust_cargo.sh verb in
# wt-s23 through the machine-wide build gate (6 GiB). main's trust-ir pin brings AY 7ed2ea1da,
# whose manifest carries `[trust] backstop`, which the x86-stage1-ay13556 overlay's targo
# (d7f143f3b) refuses; the x86-stage1-ay13556-t011 overlay is the same stage-1 trustc d7f143f3b,
# the same AY 13556 and Clean 5f09e36c (identical SHA-256), with only targo replaced by one that
# reads `backstop` (its T011-PACK.txt). `targo --unverified` only (no proof claim about any build).
# usage: run.sh <trust_cargo args...>
export BUILD_SLOT_MEM_GB=6
cd $HOME/tcg-scratch/wt-s23 || exit 9
OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay13556
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s23
export TCG_X86_BODY_QUALIFY_AY=$OVERLAY/bin/ay
export TCG_EXTERNAL_CLEAN_CHECKER=$OVERLAY/bin/clean
while [ -e $HOME/tcg-scratch/quiet.request ]; do echo "# quiet.request $(date +%T)"; sleep 60; done
exec build-slot -- nice -n 19 bash scripts/trust_cargo.sh "$@"
