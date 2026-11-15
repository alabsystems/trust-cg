cd ~/tcg-scratch/wt-od233 || exit 9
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
export TRUST_TARGO=$OV/bin/targo CARGO_TARGET_DIR=$HOME/tcg-scratch/stage1-targets/wt-od233-own
git rev-parse HEAD
TCG_X86_BODY_QUALIFY_AY=$OV/bin/ay TCG_EXTERNAL_CLEAN_CHECKER=$OV/bin/clean \
  bash scripts/trust_cargo.sh test -p trust-cg-verify --lib -j2 -- \
  x86_source_bound_body::tests::od233_qualification::host_qualification_times_the_largest_recut_statement \
  --exact --ignored --test-threads=1 --nocapture
echo "== RECUT-TIME-RC=$?"
