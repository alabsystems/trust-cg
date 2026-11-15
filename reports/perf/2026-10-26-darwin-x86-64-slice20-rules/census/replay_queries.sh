#!/bin/zsh
# Replay the queries the branch's probe run wrote for the design's 33 in-scope roots
# (s20-design/data/inscope_names.txt, through <dir>/index.tsv; single theorems and parts) on
# AY 13556 + Clean 5f09e36c at the lane's 30 s deadline, one at a time, via replay_one.py (the
# design's: strict Alethe one-shot, then Clean). Waits while ~/tcg-scratch/quiet.request exists
# or a trust-cg census runs.
# usage: replay_queries.sh <smt2 dir> <out.tsv>
D=$HOME/tcg-scratch/s20-impl/census
AY=$HOME/.local/share/trust-overlays/x86-stage1-ay13556/bin/ay
Q=${1:?dir}; OUT=${2:?out}
export REPLAY_WALL_CAP=40
FILES=($(python3 - $Q $HOME/tcg-scratch/s20-design/data/inscope_names.txt <<'PY'
import sys
q, names = sys.argv[1], set(l.strip() for l in open(sys.argv[2]))
for l in open(f"{q}/index.tsv"):
    f = l.rstrip("\n").split("\t")
    if f[1] not in names: continue
    if len(f) == 3:
        for k in range(1, int(f[2]) + 1): print(f"{q}/{f[0]}.part{k}.smt2")
    else:
        print(f"{q}/{f[0]}.smt2")
PY
))
echo "queries: ${#FILES}"
for q in $FILES; do
  grep -qF "$(basename $q)" $OUT 2>/dev/null && continue
  until [ ! -e $HOME/tcg-scratch/quiet.request ] && ! pgrep -f '[t]rust_ir_cg_census' >/dev/null && ! pgrep -f 'trustc .*-Zcodegen-backend=.*[c]ensus' >/dev/null; do sleep 15; done
  python3 $D/replay_one.py $AY $q 30000 1 >> $OUT
done
echo REPLAY-DONE
