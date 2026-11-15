#!/bin/zsh
# The Darwin x86-64 core proof census (O0, panic=abort, proofs required = the bridge
# default), exactly census_main_dump.sh's command (the baseline `main-ac04` row), on the
# slice-10 bridge built from this branch (runs/<tag>.dylib), with the uncertified-body
# query dump. Waits for > 600000 free pages and no other census before starting.
# usage: census_s10.sh <tag> <worktree>
TAG=${1:?tag}
W=${2:?worktree}
D=$(ls -t "$W"/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib | head -1)
cp "$D" ~/tcg-scratch/runs/$TAG.dylib && shasum -a 256 ~/tcg-scratch/runs/$TAG.dylib
mkdir -p ~/tcg-scratch/runs/dump-$TAG
until [ "$(vm_stat | awk '/Pages free/ {gsub(/\./,"",$3); print $3}')" -gt 600000 ] && ! pgrep -f 'trust_ir_cg_[c]ensus' > /dev/null; do
  sleep 30
done
date
echo "free pages at start: $(vm_stat | awk '/Pages free/ {gsub(/\./,"",$3); print $3}')"
RUSTC_BOOTSTRAP=1 python3 trust/scripts/trust_ir_cg_census.py \
  --trustc trust/build/x86_64-apple-darwin/stage1/bin/trustc --crate core \
  --out-dir ~/tcg-scratch/runs/census-$TAG --backend ~/tcg-scratch/runs/$TAG.dylib \
  --opt-level 0 --panic abort --diag-json \
  --extra-flag=-Ztrust-verify=off --extra-flag=-Ztrust-ir-cg-args=x86-body-trace \
  --extra-flag=-Ztrust-ir-cg-args=x86-body-dump=$HOME/tcg-scratch/runs/dump-$TAG \
  --timeout 21600 > ~/tcg-scratch/runs/census-$TAG.out 2>&1
RC=$?
echo "census exit=$RC"
date
grep -q 'TIMED OUT' ~/tcg-scratch/runs/census-$TAG.out && RC=99
grep -E 'failed roots|emitted objects|harness|wall' ~/tcg-scratch/runs/census-$TAG.out | head -6
echo "budget refusals: $(grep -c 'invalid execution resource budget' ~/tcg-scratch/runs/census-$TAG/stderr.log)"
ls ~/tcg-scratch/runs/dump-$TAG | wc -l | sed 's/^/dumped queries: /'
echo CENSUS-DONE
