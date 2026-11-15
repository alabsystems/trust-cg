cd ~/tcg-scratch/wt-od233 || exit 9
export TRUST_TARGO=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/targo CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-od233-own
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- x86_source_bound_body::tests::od233::od233_diagnose_the_every_point_overflow --exact --include-ignored --nocapture
echo "== DEPTH-RC=$?"
bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- x86_source_bound_body::tests::slice16::every_earlier_fixture_cut_at_every_clean_point_holds_part_by_part --exact --nocapture
echo "== S16-POINT-RC=$?"
