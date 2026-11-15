cd ~/tcg-scratch/wt-od233 || exit 9
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-od233-own
T=x86_source_bound_body::tests::od233
echo "== od233 module"
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- $T:: --include-ignored --nocapture --test-threads=2 --skip od233_diagnose
echo "== OD233-RC=$?"
echo "== diag on"
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- $T::od233_diagnose_the_every_point_overflow --exact --include-ignored --nocapture
echo "== DIAG-ON-RC=$?"
echo "== diag off"
TCG_OD233_DIAG_OFF=1 bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- $T::od233_diagnose_the_every_point_overflow --exact --include-ignored --nocapture
echo "== DIAG-OFF-RC=$?"
