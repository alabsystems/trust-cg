#!/bin/zsh
# Dump the probe's view (LIR, pre-RA machine rows, verdict) of every function of a
# class file (fn<TAB>roots<TAB>trace; the census name, whose private-symbol prefix
# is stripped) from a cleaned core module.
# usage: dump_class.sh <cls file> <out>
P=${PROBE:-$HOME/tcg-scratch/s13/probe_main}
M=${MODULE:-$HOME/tcg-scratch/s8/core-ir-clean/core.trust_irbin}
: > "$2"
for fn in $(cut -f1 "$1" | sed -E 's/^__trust_cg_private\.[^.]+\.[^.]+\.[0-9]+\.[0-9]+\.//' | sort -u); do
  "$P" "$M" "$fn" 2>/dev/null | awk -v want="==== $fn" 'BEGIN{p=0} /^==== /{p=($0 == want)} p' >> "$2"
done
grep -c '^====' "$2"
