#!/bin/zsh
# Dump the probe's view (LIR, pre-RA machine rows, verdict) of every function of a
# slice-11 class file (split_classes.py) from a cleaned core dump.
# usage: dump_class.sh <cls file> <out>
P=${PROBE:-$HOME/tcg-scratch/stage1-targets/agent-a4adc703a60c6af6b/debug/examples/x86_body_probe}
M=${MODULE:-$HOME/tcg-scratch/s8/core-ir-clean/core.trust_irbin}
: > "$2"
for fn in $(cut -f1 "$1" | sort -u); do
  "$P" "$M" "$fn" 2>/dev/null | awk -v want="==== $fn" 'BEGIN{p=0} /^==== /{p=(index($0, want) > 0)} p' >> "$2"
done
grep -c '^====' "$2"
