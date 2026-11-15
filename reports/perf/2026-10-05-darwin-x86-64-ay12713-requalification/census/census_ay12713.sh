#!/bin/zsh
# The Darwin x86-64 `core` proof census (O0, panic=abort, proofs required = the bridge
# default), the command of every earlier census row, on the bridge built against the
# bridge overlay (AY build 12713 + Clean 5f09e36c; ~/tcg-scratch/build_bridge.sh) and
# HOSTED by the root overlay's trustc: a backend loaded into a compiler admits that
# compiler's sysroot `bin/ay`, which must be the build-12713 bytes the bridge recorded
# (the stage-1 trustc's own `bin/ay` is build 10530 and would be refused).
# Waits until free + inactive + speculative pages exceed 1.6M, no other census runs and
# no quiet request exists.
# usage: census_ay12713.sh <tag> <worktree|->
TAG=${1:?tag}
W=${2:?worktree}
ROOT_OVERLAY=$HOME/.local/share/trust-overlays/x86-stage1-ay12713
if [ "$W" != "-" ]; then
  D=$(ls -t "$W"/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib | head -1)
  cp "$D" ~/tcg-scratch/runs/$TAG.dylib || exit 9
fi
shasum -a 256 ~/tcg-scratch/runs/$TAG.dylib || exit 9
mkdir -p ~/tcg-scratch/runs/dump-$TAG
reclaimable() {
  vm_stat | awk '/Pages (free|inactive|speculative)/ {gsub(/\./,"",$NF); n += $NF} END {print n}'
}
# CENSUS_QUIET_HOLDS_OTHERS=1: the quiet request exists to hold OTHER censuses for this one
# (the coordinator's hold for the rerun of 2026-10-05); start without waiting for it.
quiet_clear() {
  [ "${CENSUS_QUIET_HOLDS_OTHERS:-0}" = 1 ] || [ ! -e ~/tcg-scratch/quiet.request ]
}
until [ "$(reclaimable)" -gt 1600000 ] \
  && ! pgrep -f 'trust_ir_cg_[c]ensus' > /dev/null && quiet_clear; do
  sleep 30
done
echo "free disk at start: $(df -h ~/tcg-scratch | awk 'NR==2 {print $4}')"
date
echo "free+inactive+speculative pages at start: $(reclaimable)"
RUSTC_BOOTSTRAP=1 python3 trust/scripts/trust_ir_cg_census.py \
  --trustc $ROOT_OVERLAY/bin/trustc --crate core \
  --out-dir ~/tcg-scratch/runs/census-$TAG --backend ~/tcg-scratch/runs/$TAG.dylib \
  --opt-level 0 --panic abort --diag-json \
  --extra-flag=-Ztrust-verify=off --extra-flag=-Ztrust-ir-cg-args=x86-body-trace \
  --extra-flag=-Ztrust-ir-cg-args=x86-body-dump=$HOME/tcg-scratch/runs/dump-$TAG \
  --timeout 28800 > ~/tcg-scratch/runs/census-$TAG.out 2>&1
RC=$?
echo "census exit=$RC"
date
grep -q 'TIMED OUT' ~/tcg-scratch/runs/census-$TAG.out && RC=99
grep -E 'failed roots|emitted objects|harness|wall' ~/tcg-scratch/runs/census-$TAG.out | head -6
echo "budget refusals: $(grep -c 'invalid execution resource budget' ~/tcg-scratch/runs/census-$TAG/stderr.log)"
ls ~/tcg-scratch/runs/dump-$TAG | wc -l | sed 's/^/dumped queries: /'
echo CENSUS-DONE
