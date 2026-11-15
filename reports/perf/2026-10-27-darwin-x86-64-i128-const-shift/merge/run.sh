#!/bin/zsh
# OD-215 lane merged with origin/main e74f215c6: one trust_cargo.sh verb in wt-i128sh through the
# machine-wide build gate (6 GiB). main's AY pin (7ed2ea1da) carries `[trust] backstop`, so builds use
# the x86-stage1-ay13556-t011 overlay's targo (same stage-1 trustc d7f143f3b, AY 13556, Clean 5f09e36c;
# ~/tcg-scratch/trust-t011/README.md). `targo --unverified` only (no proof claim about any build).
# usage: run.sh <trust_cargo args...>
export BUILD_SLOT_MEM_GB=6
cd $HOME/tcg-scratch/wt-i128sh || exit 9
OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
export TRUST_TARGO=$OVERLAY/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-i128sh
export TCG_X86_BODY_QUALIFY_AY=$OVERLAY/bin/ay
export TCG_EXTERNAL_CLEAN_CHECKER=$OVERLAY/bin/clean
while [ -e $HOME/tcg-scratch/quiet.request ]; do echo "# quiet.request $(date +%T)"; sleep 60; done
exec build-slot -- nice -n 19 bash scripts/trust_cargo.sh "$@"
