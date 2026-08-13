#!/usr/bin/env bash
#
# Focused regression test for soundness_check.sh's Clean-summary non-vacuity
# guard. This does not run the cross-repository soundness constellation.
#
set -u
set -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")/.." && pwd)"
SOUNDNESS_CHECK="${ROOT}/scripts/soundness_check.sh"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/test_soundness_check.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT HUP INT TERM

PASS=0
FAIL=0

accepts() {
  local name="$1" contents="$2" expected="$3"
  local log="${TMP}/${name}.log"
  local output
  printf '%s' "$contents" >"$log"
  if output="$("$SOUNDNESS_CHECK" --validate-clean-summary "$log" 2>&1)" && \
     [ "$output" = "$expected" ]; then
    printf 'ok - accepts %s\n' "$name"
    PASS=$((PASS + 1))
  else
    printf 'not ok - accepts %s (output: %s)\n' "$name" "${output:-<empty>}" >&2
    FAIL=$((FAIL + 1))
  fi
}

rejects() {
  local name="$1" contents="$2"
  local log="${TMP}/${name}.log"
  local output
  printf '%s' "$contents" >"$log"
  if output="$("$SOUNDNESS_CHECK" --validate-clean-summary "$log" 2>&1)"; then
    printf 'not ok - rejects %s (unexpected success: %s)\n' "$name" "$output" >&2
    FAIL=$((FAIL + 1))
  else
    printf 'ok - rejects %s\n' "$name"
    PASS=$((PASS + 1))
  fi
}

accepts \
  valid_241 \
  $'Loading proof...\nChecked 241 declarations in 1.038183542s\n  241 passed, 0 failed\n' \
  'Checked 241 declarations; 241 passed, 0 failed'

rejects empty_rc0 ''
rejects zero_zero $'Checked 0 declarations in 1ms\n  0 passed, 0 failed\n'
rejects mismatch $'Checked 241 declarations in 1ms\n  240 passed, 0 failed\n'
rejects failed $'Checked 241 declarations in 1ms\n  240 passed, 1 failed\n'
rejects malformed $'Checked: 241 declarations\n  241 passed / 0 failed\n'
rejects duplicate_summaries \
  $'Checked 241 declarations in 1ms\n  241 passed, 0 failed\nChecked 241 declarations in 1ms\n  241 passed, 0 failed\n'
rejects duplicate_checked \
  $'Checked 241 declarations in 1ms\nChecked 241 declarations in 2ms\n  241 passed, 0 failed\n'
rejects duplicate_result \
  $'Checked 241 declarations in 1ms\n  241 passed, 0 failed\n  241 passed, 0 failed\n'

printf '%d passed, %d failed\n' "$PASS" "$FAIL"
[ "$FAIL" -eq 0 ]
