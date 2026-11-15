#!/bin/zsh
# The Darwin x86-64 core proof census (O0, panic=abort, proofs required = the bridge
# default), the command of every earlier census row, on a bridge built from a worktree
# (runs/<tag>.dylib), with the uncertified-body query dump. Waits until no other census
# runs, no quiet request exists and free + inactive + speculative pages exceed 1.6M
# (macOS keeps "Pages free" alone low; the file cache is reclaimable).
# A worktree of `-` runs the bridge already copied to runs/<tag>.dylib. TRUSTC names the
# compiler (default: the native stage-1 trustc; for a bridge built against the AY 12713
# overlay, the root overlay's trustc, whose sysroot bin/ay is the AY the bridge recorded).
# usage: [TRUSTC=...] census_s12.sh <tag> <worktree|->
TAG=${1:?tag}
W=${2:?worktree}
if [ "$W" != "-" ]; then
  D=$(ls -t "$W"/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib | head -1)
  cp "$D" ~/tcg-scratch/runs/$TAG.dylib || exit 9
fi
shasum -a 256 ~/tcg-scratch/runs/$TAG.dylib || exit 9
mkdir -p ~/tcg-scratch/runs/dump-$TAG
avail() {
  vm_stat | awk '/Pages free|Pages inactive|Pages speculative/ {gsub(/\./,"",$NF); s+=$NF} END {print s}'
}
until [ "$(avail)" -gt 1600000 ] \
  && ! pgrep -f 'trust_ir_cg_[c]ensus' > /dev/null && [ ! -e ~/tcg-scratch/quiet.request ]; do
  sleep 30
done
date
echo "trustc: ${TRUSTC:-$HOME/trust/build/x86_64-apple-darwin/stage1/bin/trustc}"
echo "free+inactive+speculative pages at start: $(avail)"
RUSTC_BOOTSTRAP=1 python3 trust/scripts/trust_ir_cg_census.py \
  --trustc ${TRUSTC:-$HOME/trust/build/x86_64-apple-darwin/stage1/bin/trustc} --crate core \
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
