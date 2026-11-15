cd ~/tcg-scratch/wt-od233 || exit 9
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-od233-own
git rev-parse HEAD
TCG_OD233_PRINT_TEXT=1 bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- x86_source_bound_body::tests::od233::print_od233 --ignored --nocapture --test-threads=1
echo "== PRINTERS-RC=$?"
