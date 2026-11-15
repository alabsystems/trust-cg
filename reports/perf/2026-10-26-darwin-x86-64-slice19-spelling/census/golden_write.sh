#!/bin/zsh
# Slice 19: re-render every x86 body golden in a worktree through its test binary
# (TCG_X86_BODY_SNAPSHOT_WRITE=1), pin each printed digest in the test sources, and copy the
# goldens to <copy dir> for review19.py. usage: golden_write.sh <worktree> <test binary> <log> <copy dir>
W=${1:?worktree}; BIN=${2:?test binary}; LOG=${3:?log}; COPY=${4:?copy dir}
cd $W/crates/trust-cg-verify || exit 9
TCG_X86_BODY_SNAPSHOT_WRITE=1 RUST_MIN_STACK=67108864 nice -n 19 "$BIN" smt2_is_canonical_per_shape --test-threads=2 > "$LOG" 2>&1
grep -o "set [A-Z_]*SHA256 to [0-9a-f]*" "$LOG" | while read -r _ name _ digest; do
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
