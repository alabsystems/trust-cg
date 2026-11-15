#!/bin/bash
# Runtime evidence for inline-only bodies on non-TY programs (this record).
#
#   fastpath.sh <target/release/examples dir> <out dir> [reps] [n]
#
# JIT: examples/jit_inline_only_fast_path compiles sum(table, n) over a host
# helper whose fast path the module carries as an inline-only body, at O2,
# and runs it in-process. Arms: `on` (the body spliced) and `off`
# (TCG_NO_JIT_LIR_PREPARE=1: every read calls the host definition). Same
# binary; /usr/bin/time -l per process.
#
# AOT: examples/aot_inline_only_fast_path writes the object for the host
# triple at O2, twice from one compiler binary — `on` and `off`
# (TCG_NO_INLINE_ONLY_BODIES=1) — each linked (cc -O2) with the same C
# runtime; the linked programs run under /usr/bin/time -l and check their own
# answer against the closed form (exit 1 on a mismatch).
#
# Output: fastpath-jit.tsv and fastpath-aot.tsv (arm, n, rep, the printed
# answer and call counters, instructions retired, cycles elapsed, max RSS).
set -euo pipefail
EX="$1"
OUT="$2"
REPS="${3:-3}"
N="${4:-50000000}"
WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

metric() { awk -v k="$2" '$0 ~ k {print $1}' "$1" | tail -1; }

JIT="$OUT/fastpath-jit.tsv"
echo -e "arm\tn\trep\tanswer\tdefinition_calls\tslow_calls\tspliced\tinstructions_retired\tcycles_elapsed\tmax_rss" > "$JIT"
for n in 0 "$N"; do
  for rep in $(seq 1 "$REPS"); do
    for arm in on off; do
      if [ "$arm" = off ]; then export TCG_NO_JIT_LIR_PREPARE=1; else unset TCG_NO_JIT_LIR_PREPARE; fi
      /usr/bin/time -l "$EX/jit_inline_only_fast_path" 2 "$n" > "$WORK/out" 2> "$WORK/time"
      unset TCG_NO_JIT_LIR_PREPARE
      answer=$(sed -n 's/^answer=\([-0-9]*\).*/\1/p' "$WORK/out")
      calls=$(sed -n 's/^definition_calls=\([0-9]*\) slow_calls=\([0-9]*\)/\1\t\2/p' "$WORK/out")
      spliced=$(sed -n 's/^spliced=\(.*\) withheld=.*/\1/p' "$WORK/out")
      echo -e "$arm\t$n\t$rep\t$answer\t$calls\t$spliced\t$(metric "$WORK/time" 'instructions retired')\t$(metric "$WORK/time" 'cycles elapsed')\t$(metric "$WORK/time" 'maximum resident set size')" >> "$JIT"
    done
  done
done

AOT="$OUT/fastpath-aot.tsv"
unset TCG_NO_INLINE_ONLY_BODIES
"$EX/aot_inline_only_fast_path" "$WORK/on.o" 2 --runtime "$WORK/runtime.c" > "$WORK/on.compile"
TCG_NO_INLINE_ONLY_BODIES=1 "$EX/aot_inline_only_fast_path" "$WORK/off.o" 2 > "$WORK/off.compile"
cc -O2 "$WORK/runtime.c" "$WORK/on.o" -o "$WORK/on"
cc -O2 "$WORK/runtime.c" "$WORK/off.o" -o "$WORK/off"
{
  echo "# on:  $(tr '\n' ' ' < "$WORK/on.compile")"
  echo "# off: $(tr '\n' ' ' < "$WORK/off.compile")"
  echo "# object sha256: on $(shasum -a 256 "$WORK/on.o" | cut -c1-16) off $(shasum -a 256 "$WORK/off.o" | cut -c1-16)"
  echo -e "arm\tn\trep\tanswer\treference\tdefinition_calls\tslow_calls\tinstructions_retired\tcycles_elapsed\tmax_rss"
} > "$AOT"
for n in 0 "$N"; do
  for rep in $(seq 1 "$REPS"); do
    for arm in on off; do
      /usr/bin/time -l "$WORK/$arm" "$n" > "$WORK/out" 2> "$WORK/time"
      line=$(cat "$WORK/out")
      answer=$(echo "$line" | sed -n 's/.* answer=\([-0-9]*\).*/\1/p')
      reference=$(echo "$line" | sed -n 's/.* reference=\([-0-9]*\).*/\1/p')
      dcalls=$(echo "$line" | sed -n 's/.* definition_calls=\([0-9]*\).*/\1/p')
      scalls=$(echo "$line" | sed -n 's/.* slow_calls=\([0-9]*\).*/\1/p')
      echo -e "$arm\t$n\t$rep\t$answer\t$reference\t$dcalls\t$scalls\t$(metric "$WORK/time" 'instructions retired')\t$(metric "$WORK/time" 'cycles elapsed')\t$(metric "$WORK/time" 'maximum resident set size')" >> "$AOT"
    done
  done
done
cat "$JIT" "$AOT"
