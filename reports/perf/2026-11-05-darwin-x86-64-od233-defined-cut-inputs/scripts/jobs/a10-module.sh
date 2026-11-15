cd ~/tcg-scratch/wt-od233 || exit 9
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-od233-own
T=x86_source_bound_body::tests
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- $T::slice25::scaled_index_and_rmw_rows_are_stated_in_parts --exact --nocapture
echo "== S25-PARTS-RC=$?"
TCG_OD233_PRINT_TEXT=1 bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- $T::od233:: --include-ignored --nocapture --test-threads=2 --skip od233_diagnose
echo "== OD233-RC=$?"
