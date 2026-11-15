#!/bin/zsh
# Replay every dumped part of core::str::slice_error_fail_rt from the three knob censuses
# on the overlay's AY 13556, with (get-model) inserted before (exit). Writes
# ~/tcg-scratch/sefrt-diag/ay/<run>/partN.get-model.smt2 and partN.ay.txt (stdout+stderr, --stats).
AY=$HOME/.local/share/trust-overlays/x86-stage1-ay13556-t011/bin/ay
P=_RNvNtCs7e1ihmkzmZ8_4core3str19slice_error_fail_rt
for run in o2k-m301-lr o2k-m301-all o2k-m301-allbm; do
  D=$HOME/tcg-scratch/sefrt-diag/ay/$run; mkdir -p $D
  for f in $HOME/tcg-scratch/runs/dump-$run/$P.part*.smt2; do
    n=${${f:t}#$P.}; n=${n%.smt2}
    sed 's/^(exit)$/(get-model)\n(exit)/' $f > $D/$n.get-model.smt2
    # BSD sed: do it portably
    python3 -I -c 'import sys; s=open(sys.argv[1]).read(); assert s.count("(check-sat)\n(exit)")==1, sys.argv[1]; open(sys.argv[2],"w").write(s.replace("(check-sat)\n(exit)","(check-sat)\n(get-model)\n(exit)"))' $f $D/$n.get-model.smt2
    (cd $D && $AY solve --stats $n.get-model.smt2 > $n.ay.txt 2>&1)
    v=$(head -5 $D/$n.ay.txt | grep -m1 -E '^(sat|unsat|unknown)$')
    c=$(grep -m1 'ay.proof.certificate' $D/$n.ay.txt | grep -oE 'unproved_steps=[0-9]+|trust_free=[a-z]+|unsat_admission=[a-z-]+' | tr '\n' ' ')
    t=$(grep -m1 -oE 'wall_time_ms=[0-9]+' $D/$n.ay.txt)
    echo "$run $n $v $t $c"
  done
done
