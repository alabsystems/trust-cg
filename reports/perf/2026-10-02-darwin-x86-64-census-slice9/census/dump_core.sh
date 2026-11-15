#!/bin/zsh
# Dump core's trust-ir modules at O0 (lowering only, no proof certificates) for the
# offline slice-9 measurement: the census harness and flags plus dump-trust-ir, on
# the baseline `main` bridge (runs/main-ac04.dylib). The dumped modules are the
# bridge's input, independent of the verifier. Waits for no other census and
# > 300000 free pages.
until [ "$(vm_stat | awk '/Pages free/ {gsub(/\./,"",$3); print $3}')" -gt 300000 ] && ! pgrep -f 'trust_ir_cg_[c]ensus' > /dev/null; do
  sleep 30
done
date
RUSTC_BOOTSTRAP=1 python3 trust/scripts/trust_ir_cg_census.py \
  --trustc trust/build/x86_64-apple-darwin/stage1/bin/trustc --crate core \
  --out-dir ~/tcg-scratch/runs/census-s9-dump --backend ~/tcg-scratch/runs/main-ac04.dylib \
  --opt-level 0 --panic abort --diag-json \
  --extra-flag=-Ztrust-verify=off \
  "--extra-flag=-Ztrust-ir-cg-args=no-proof-certs dump-trust-ir=$HOME/tcg-scratch/runs/core-ir-s9" \
  --timeout 7200 > ~/tcg-scratch/runs/census-s9-dump.out 2>&1
echo "dump exit=$?"
date
ls ~/tcg-scratch/runs/core-ir-s9 | wc -l
