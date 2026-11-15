#!/bin/zsh
# OD-215 lane merged with origin/main: re-render every x86 body golden from the merged code through
# its test binary (TCG_X86_BODY_SNAPSHOT_WRITE=1, inside build-slot), pin each printed digest in the
# test sources, and copy the goldens to <copy dir> for the review.
# usage: golden_write.sh <test binary> <log> <copy dir>
W=$HOME/tcg-scratch/wt-i128sh; BIN=${1:?bin}; LOG=${2:?log}; COPY=${3:?copy dir}
export BUILD_SLOT_MEM_GB=6
cd $W/crates/trust-cg-verify || exit 9
while [ -e $HOME/tcg-scratch/quiet.request ]; do sleep 60; done
TCG_X86_BODY_SNAPSHOT_WRITE=1 RUST_MIN_STACK=67108864 build-slot -- nice -n 19 "$BIN" smt2_is_canonical_per_shape --test-threads=2 > "$LOG" 2>&1
echo "golden render exit=$?"
grep -o "set [A-Z_0-9]*SHA256 to [0-9a-f]*" "$LOG" | while read -r _ name _ digest; do
  files=($(grep -l "const $name: &str" src/*.rs))
  [ ${#files} = 1 ] || { echo "no unique const $name (${#files})"; continue; }
  python3 - "$files[1]" "$name" "$digest" <<'PY'
import re, sys
p, name, digest = sys.argv[1:4]
s = open(p).read()
s2, n = re.subn(r'(const ' + name + r': &str =\s*"?)([0-9a-f]{64})', lambda m: m.group(1) + digest, s)
assert n == 1, (name, n)
open(p, 'w').write(s2)
print(f'pinned {name} {digest[:12]} in {p}')
PY
done
rm -rf "$COPY"; mkdir -p "$COPY"; cp tests/fixtures/x86_source_bound_body/*.smt2 "$COPY"/
echo "GOLDEN-WRITE-DONE"
