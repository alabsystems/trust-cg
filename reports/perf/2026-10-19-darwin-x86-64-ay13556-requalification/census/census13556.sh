#!/bin/zsh
# The census of this move is the coordinator's: a copy of ~/tcg-scratch/census13556.sh as run for it
# (the Darwin x86-64 core proof census, O0, panic=abort, proofs required, on the AY 13556 lane).
# Darwin x86-64 core proof census (O0, panic=abort, proofs required) on the AY 13556 lane:
# release bridge from <worktree> against the x86-stage0-bridge-ay13556 overlay, census on
# the ROOT overlay's trustc (a bridge admits its host compiler's sysroot bin/ay), with the
# body trace and the uncertified-query dump. Usage: census13556.sh <worktree> <tag>
W="${1:?worktree}"; TAG="${2:?tag}"
# The bridge must build into ITS OWN tree's target dir: an inherited CARGO_TARGET_DIR
# (shared across worktrees) once served a stale dylib to a census (2026-10-14).
unset CARGO_TARGET_DIR
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556
avail() { vm_stat | awk '/Pages (free|inactive|speculative)/ {gsub(/\./,"",$NF); s+=$NF} END {print s}'; }
while [ -e ~/tcg-scratch/quiet.request ]; do sleep 60; done
echo "bridge build $(date +%H:%M) at $(git -C $W rev-parse --short HEAD)"
STAMP=$(mktemp); sleep 1
~/tcg-scratch/build_bridge.sh "$W" || exit 3
D="$W/crates/rustc-codegen-trust-cg/target/release/librustc_codegen_trust_cg.dylib"
[ -f "$D" ] || { echo "no dylib"; exit 3; }
# Fail closed on a dylib this build did not write.
[ "$D" -nt "$STAMP" ] || { echo "STALE dylib (not written by this build): $D"; exit 3; }
cp "$D" ~/tcg-scratch/runs/$TAG.dylib && shasum -a 256 ~/tcg-scratch/runs/$TAG.dylib
mkdir -p ~/tcg-scratch/runs/dump-$TAG
while [ -e ~/tcg-scratch/quiet.request ] || [ "$(avail)" -lt 1600000 ]; do sleep 30; done
echo "census start $(date +%H:%M), avail pages $(avail), disk $(df -g ~ | awk 'NR==2{print $4}') GiB"
RUSTC_BOOTSTRAP=1 python3 trust/scripts/trust_ir_cg_census.py \
  --trustc $OV/bin/trustc --crate core \
  --out-dir ~/tcg-scratch/runs/census-$TAG --backend ~/tcg-scratch/runs/$TAG.dylib \
  --opt-level 0 --panic abort --diag-json \
  --extra-flag=-Ztrust-verify=off --extra-flag=-Ztrust-ir-cg-args=x86-body-trace \
  --extra-flag=-Ztrust-ir-cg-args=x86-body-dump=$HOME/tcg-scratch/runs/dump-$TAG \
  --timeout 21600 > ~/tcg-scratch/runs/census-$TAG.out 2>&1
RC=$?; echo "census exit=$RC $(date +%H:%M)"
grep -q 'TIMED OUT' ~/tcg-scratch/runs/census-$TAG.out && { echo "CENSUS INCOMPLETE (timeout)"; exit 4; }
grep -E 'failed roots|emitted objects|wall' ~/tcg-scratch/runs/census-$TAG.out | head -4
grep -c 'invalid execution resource budget' ~/tcg-scratch/runs/census-$TAG/stderr.log | sed 's/^/budget refusals: /'
ls ~/tcg-scratch/runs/dump-$TAG | wc -l | sed 's/^/dumped queries: /'
grep -h "DISK-LOW" ~/tcg-scratch/diskwatch.log 2>/dev/null | tail -1 | sed 's/^/diskwatch: /'
echo CENSUS-DONE
