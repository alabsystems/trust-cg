#!/bin/zsh
# replay_dir.sh <dump-dir> <out-dir>: replay every *.smt2 in dump-dir on AY 13556 with (get-model).
AY=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/ay
S=${1:?dump dir}; D=${2:?out dir}; mkdir -p $D
for f in $S/*.smt2; do
  n=${f:t:r}; n=${n##*.}
  python3 -I -c 'import sys; s=open(sys.argv[1]).read(); assert s.count("(check-sat)\n(exit)")==1, sys.argv[1]; open(sys.argv[2],"w").write(s.replace("(check-sat)\n(exit)","(check-sat)\n(get-model)\n(exit)"))' $f $D/$n.get-model.smt2
  (cd $D && $AY solve --stats $n.get-model.smt2 > $n.ay.txt 2>&1)
  echo "$n $(grep -m1 -E '^(sat|unsat|unknown)$' $D/$n.ay.txt) $(grep -m1 -oE 'wall_time_ms=[0-9]+' $D/$n.ay.txt)"
done
