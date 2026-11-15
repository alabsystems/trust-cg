cd ~/tcg-scratch/wt-od233 || exit 9
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-od233-own
T=x86_source_bound_body::tests
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- $T::od233:: --nocapture --test-threads=2 --skip defined_cut_inputs_never_stop_a_part_holding --include-ignored --skip print_od233
echo "== OD233-QUICK-RC=$?"
