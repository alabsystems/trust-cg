cd ~/tcg-scratch/wt-od233 || exit 9
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-od233-own
T=x86_source_bound_body::tests
git rev-parse HEAD; git status --short | head -20
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- $T::od233:: --nocapture --test-threads=2 --skip defined_cut_inputs_never_stop_a_part_holding
echo "== OD233-QUICK-RC=$?"
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- $T::od233::defined_cut_inputs_never_stop_a_part_holding --exact --nocapture
echo "== OD233-SWEEP-RC=$?"
