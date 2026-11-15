#!/bin/zsh
# Dump core's trust-ir modules at O0 (lowering only, no proof certificates) for the
# offline slice-7 probe: the same harness and flags as the census, plus
# dump-trust-ir. The dumped modules are the bridge's input, independent of the
# verifier.
until [ "$(vm_stat | awk '/Pages free/ {gsub(/\./,"",$3); print $3}')" -gt 300000 ] && ! pgrep -f 'trust_ir_cg_[c]ensus' > /dev/null; do
  sleep 30
done
date
RUSTC_BOOTSTRAP=1 python3 trust/scripts/trust_ir_cg_census.py \
  --trustc trust/build/x86_64-apple-darwin/stage1/bin/trustc --crate core \
  --out-dir ~/tcg-scratch/runs/census-s7-dump --backend ~/tcg-scratch/runs/s7.dylib \
  --opt-level 0 --panic abort --diag-json \
  --extra-flag=-Ztrust-verify=off \
  "--extra-flag=-Ztrust-ir-cg-args=no-proof-certs dump-trust-ir=$HOME/tcg-scratch/runs/core-ir-s7" \
  --timeout 7200 > ~/tcg-scratch/runs/census-s7-dump.out 2>&1
echo "dump exit=$?"
date
ls ~/tcg-scratch/runs/core-ir-s7 | wc -l
