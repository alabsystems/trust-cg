#!/bin/bash
# Byte-compare every .o and .bin of two ladder directories.
# Usage: compare_dirs.sh <before-dir> <after-dir>
set -u
n=0
d=0
for f in "$1"/*.o "$1"/*.bin; do
  b=$(basename "$f")
  n=$((n + 1))
  if ! cmp -s "$f" "$2/$b"; then
    echo "DIFF $b"
    d=$((d + 1))
  fi
done
echo "compared=$n differing=$d"
