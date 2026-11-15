cd ~/tcg-scratch/wt-od233 || exit 9
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-od233-own
T=x86_source_bound_body::tests
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- $T::od233::od233_diagnose_v9 --exact --ignored --nocapture
echo "== DIAG-RC=$?"
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- $T::od233::every_positive_fixture_holds_in_parts --exact --nocapture
echo "== POS-RC=$?"
