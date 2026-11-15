#!/bin/sh
# Twelve concurrent offline replays (three of each near-deadline query) at the
# lane's 30 s budget, as run on 2026-10-16 under `build-slot --`:
#   burst.sh <overlay> <dump dir> <out dir>
# The dump dir holds the lane's own queries (TCG_X86_BODY_QUALIFY_DUMP).
OV=${1:?overlay}
DUMP=${2:?dump dir}
OUT=${3:?out dir}
HERE=$(cd "$(dirname "$0")" && pwd)
for k in 1 2 3; do
  for q in EarlyExit SubU128 SlotU128 MulI16; do
    python3 -I "$HERE/offline_replay.py" --ay "$OV/bin/ay" --clean "$OV/bin/clean" \
      --budget-ms 30000 --out "$OUT/burst-$q-$k.tsv" "$DUMP/$q.smt2" > /dev/null 2>&1 &
  done
done
wait
