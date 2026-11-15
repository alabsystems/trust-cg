#!/usr/bin/env bash
# Re-qualify x86_64-unknown-linux-gnu's recorded body-theorem outcomes against
# the installed AY/Clean pair, printing the 1-minute load before each lane so a
# near-deadline answer can be read against the host's state.
#
# Fails closed: a non-zero lane is reported and the script exits non-zero.
set -uo pipefail
cd "$(dirname "$0")/../../../.." || exit 2

run() {
  local label="$1"; shift
  printf '=== %s  load=%s ===\n' "$label" "$(cut -d' ' -f1 /proc/loadavg)"
  PATH=/usr/bin:/bin:$PATH CC=/usr/bin/gcc RUST_MIN_STACK=134217728 \
    scripts/trust_cargo.sh "$@"
  local rc=$?
  printf '=== %s rc=%d ===\n' "$label" "$rc"
  return $rc
}

rc=0
run "every x86-64 body lane" test -p trust-cg-verify --lib x86_source_bound_body || rc=1
run "slice 10 gap lane" test -p trust-cg-verify --lib slice10_qualification -- --nocapture || rc=1
run "slice 14 gap lane" test -p trust-cg-verify --lib slice14_qualification -- --nocapture || rc=1
exit $rc
