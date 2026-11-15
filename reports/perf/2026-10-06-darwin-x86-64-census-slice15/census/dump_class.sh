#!/bin/zsh
# Dump the probe's view (LIR, pre-RA machine rows, verdict) of every function named in a
# class file (one census name per line, private-symbol prefix stripped) from a cleaned core
# module. usage: dump_class.sh <names file> <out> [probe] [module]
P=${3:-$HOME/tcg-scratch/s15/probe_base}
M=${4:-$HOME/tcg-scratch/s8/core-ir-clean/core.trust_irbin}
: > "$2"
for fn in $(sed -E 's/^__trust_cg_private\.[^.]+\.[^.]+\.[0-9]+\.[0-9]+\.//' "$1" | sort -u); do
  "$P" "$M" "$fn" 2>/dev/null | awk -v want="==== $fn" 'BEGIN{p=0} /^==== /{p=($0 == want)} p' >> "$2"
done
grep -c '^====' "$2"
