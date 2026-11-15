#!/bin/bash
# Run the ordinary-link matrix through case2.sh with TCG, 4 at a time.
# Usage: TCG=<cli> run_sweep.sh <matrix> <out>
cd "$(dirname "$0")" || exit 2
rm -rf out res
xargs -P 4 -L 1 ./case2.sh < "$1" > "$2" 2> "$2.err"
