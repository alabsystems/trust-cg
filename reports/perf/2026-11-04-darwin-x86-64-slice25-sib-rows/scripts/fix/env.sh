# The fix lane's environment (sourced): the lane worktree, the t011 overlay
# targo and the lane's own target dir; AY/Clean for qualification runs.
cd ~/tcg-scratch/wt-s25 || exit 9
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo
export CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-s25
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
verify() { bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- "$@"; }
