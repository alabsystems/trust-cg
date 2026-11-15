#!/bin/zsh
# Darwin x86-64 core proof census from an EXISTING bridge dylib, at a chosen opt level.
# Usage: census_t011_dylib.sh <dylib> <tag> <opt-level> [knob ...]
# Each extra argument is passed as one -Ztrust-ir-cg-args=<knob> (for example no-x86-block-merge).
# The dylib must be a bridge built by build_bridge.t011.sh from a known commit (record which);
# the census runs the ROOT t011 overlay's trustc (same compiler, sysroot and bin/ay as the 13556 lane).
SRC="${1:?dylib}"; TAG="${2:?tag}"; OPT="${3:?opt-level}"; shift 3
KNOBS=(); for k in "$@"; do KNOBS+=("--extra-flag=-Ztrust-ir-cg-args=$k"); done
OV=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011
avail() { vm_stat | awk '/Pages (free|inactive|speculative)/ {gsub(/\./,"",$NF); s+=$NF} END {print s}'; }
[ -f "$SRC" ] || { echo "no dylib $SRC"; exit 3; }
cp "$SRC" ~/tcg-scratch/runs/$TAG.dylib && shasum -a 256 ~/tcg-scratch/runs/$TAG.dylib
~/tcg-scratch/check_dylib_tools.sh ~/tcg-scratch/runs/$TAG.dylib || exit 5
mkdir -p ~/tcg-scratch/runs/dump-$TAG
while [ -e ~/tcg-scratch/quiet.request ] || [ "$(avail)" -lt 1600000 ]; do sleep 30; done
echo "census start $(date +%H:%M) opt=$OPT knobs=[$*], avail pages $(avail), disk $(df -g ~ | awk 'NR==2{print $4}') GiB"
RUSTC_BOOTSTRAP=1 python3 trust/scripts/trust_ir_cg_census.py \
  --trustc $OV/bin/trustc --crate core \
  --out-dir ~/tcg-scratch/runs/census-$TAG --backend ~/tcg-scratch/runs/$TAG.dylib \
  --opt-level "$OPT" --panic abort --diag-json \
  --extra-flag=-Ztrust-verify=off --extra-flag=-Ztrust-ir-cg-args=x86-body-trace \
  --extra-flag=-Ztrust-ir-cg-args=x86-body-dump=$HOME/tcg-scratch/runs/dump-$TAG "${KNOBS[@]}" \
  --timeout 21600 > ~/tcg-scratch/runs/census-$TAG.out 2>&1
RC=$?; echo "census exit=$RC $(date +%H:%M)"
grep -q 'TIMED OUT' ~/tcg-scratch/runs/census-$TAG.out && { echo "CENSUS INCOMPLETE (timeout)"; exit 4; }
grep -E 'failed roots|emitted objects|wall' ~/tcg-scratch/runs/census-$TAG.out | head -4
grep -c 'invalid execution resource budget' ~/tcg-scratch/runs/census-$TAG/stderr.log | sed 's/^/budget refusals: /'
ls ~/tcg-scratch/runs/dump-$TAG | wc -l | sed 's/^/dumped queries: /'
echo CENSUS-DONE
