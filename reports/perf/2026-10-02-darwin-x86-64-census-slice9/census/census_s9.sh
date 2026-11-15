#!/bin/zsh
# The Darwin x86-64 core proof census (O0, panic=abort, proofs required = the bridge
# default), exactly postpush_census.sh's command plus the uncertified-body query dump,
# on the already-built slice-9 bridge (runs/$TAG.dylib). Waits for > 600000 free
# pages and no other census before starting.
TAG=${1:-s9}
until [ "$(vm_stat | awk '/Pages free/ {gsub(/\./,"",$3); print $3}')" -gt 600000 ] && ! pgrep -f 'trust_ir_cg_[c]ensus' > /dev/null; do
  sleep 30
done
date
echo "free pages at start: $(vm_stat | awk '/Pages free/ {gsub(/\./,"",$3); print $3}')"
shasum -a 256 ~/tcg-scratch/runs/$TAG.dylib
mkdir -p ~/tcg-scratch/runs/dump-$TAG
RUSTC_BOOTSTRAP=1 python3 trust/scripts/trust_ir_cg_census.py \
  --trustc trust/build/x86_64-apple-darwin/stage1/bin/trustc --crate core \
  --out-dir ~/tcg-scratch/runs/census-$TAG --backend ~/tcg-scratch/runs/$TAG.dylib \
  --opt-level 0 --panic abort --diag-json \
  --extra-flag=-Ztrust-verify=off --extra-flag=-Ztrust-ir-cg-args=x86-body-trace \
  --extra-flag=-Ztrust-ir-cg-args=x86-body-dump=$HOME/tcg-scratch/runs/dump-$TAG \
  --timeout "${CENSUS_TIMEOUT:-21600}" \
  > ~/tcg-scratch/runs/census-$TAG.out 2>&1
RC=$?
echo "census exit=$RC"
date
if [ "$RC" -ne 0 ] || grep -q 'TIMED OUT' ~/tcg-scratch/runs/census-$TAG.out; then
  echo "CENSUS INCOMPLETE (exit=$RC): NO RESULT"
  grep -E 'exit code|emitted objects' ~/tcg-scratch/runs/census-$TAG.out | head -3
  exit 4
fi
grep -E 'failed roots|emitted objects|harness|wall' ~/tcg-scratch/runs/census-$TAG.out | head -6
echo "budget refusals: $(grep -c 'large-stack slot' ~/tcg-scratch/runs/census-$TAG/stderr.log)"
echo CENSUS-DONE
