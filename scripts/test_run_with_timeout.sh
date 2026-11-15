#!/usr/bin/env bash
#
# Focused regression tests for scripts/run_with_timeout.py.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
#
set -u
set -o pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")/.." && pwd)"
RUNNER="${ROOT}/scripts/run_with_timeout.py"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/test_run_with_timeout.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT HUP INT TERM

PASS=0
FAIL=0

check_status() {
  local name="$1" expected="$2"
  shift 2
  local status
  "$@" >"${TMP}/${name}.out" 2>"${TMP}/${name}.err"
  status=$?
  if [ "$status" -eq "$expected" ]; then
    printf 'ok - %s returns %d\n' "$name" "$expected"
    PASS=$((PASS + 1))
  else
    printf 'not ok - %s returned %d, expected %d\n' \
      "$name" "$status" "$expected" >&2
    FAIL=$((FAIL + 1))
  fi
}

check_status success 0 "$RUNNER" 5 sh -c 'printf success'
if [ "$(cat "${TMP}/success.out")" != success ]; then
  echo 'not ok - success output was not preserved' >&2
  FAIL=$((FAIL + 1))
else
  echo 'ok - success output is preserved'
  PASS=$((PASS + 1))
fi

check_status nonzero 7 "$RUNNER" 5 sh -c 'exit 7'
# SIGKILL, not a core-dump signal: the runner maps any signal death to 128+N,
# and a SEGV'd /bin/sh made macOS write a crash report every run.
check_status signaled 137 "$RUNNER" 5 sh -c 'kill -KILL $$'

mkdir "${TMP}/working-directory"
working_directory="$(cd "${TMP}/working-directory" && pwd -P)"
check_status chdir 0 "$RUNNER" --chdir "${TMP}/working-directory" 5 \
  sh -c 'test "$(pwd -P)" = "$1"' sh "$working_directory"

timeout_pid_file="${TMP}/timeout-descendant.pid"
check_status timeout 124 "$RUNNER" --grace-seconds 0.2 0.2 \
  sh -c \
    'trap "" TERM; (trap "" HUP TERM; while :; do sleep 60; done) & echo $! >"$1"; wait' \
    sh "$timeout_pid_file"
if ! grep -Fq 'command exceeded 0.2s' "${TMP}/timeout.err"; then
  echo 'not ok - timeout diagnostic is missing' >&2
  FAIL=$((FAIL + 1))
else
  echo 'ok - timeout diagnostic names the bound'
    PASS=$((PASS + 1))
fi
if grep -Fq 'process group did not terminate' "${TMP}/timeout.err"; then
  echo 'not ok - timeout reported a spurious cleanup failure' >&2
  FAIL=$((FAIL + 1))
else
  echo 'ok - timeout cleanup completes without a spurious failure'
  PASS=$((PASS + 1))
fi

timeout_descendant="$(sed -n '1p' "$timeout_pid_file")"
attempts=0
while kill -0 "$timeout_descendant" 2>/dev/null && [ "$attempts" -lt 20 ]; do
  attempts=$((attempts + 1))
  sleep 0.1
done
if kill -0 "$timeout_descendant" 2>/dev/null; then
  echo "not ok - timed-out descendant $timeout_descendant survived" >&2
  FAIL=$((FAIL + 1))
else
  echo 'ok - timeout kills descendants'
  PASS=$((PASS + 1))
fi

normal_pid_file="${TMP}/normal-descendant.pid"
check_status lingering_descendant 0 "$RUNNER" --grace-seconds 0.2 5 \
  sh -c \
    '(trap "" HUP TERM; while :; do sleep 60; done) & echo $! >"$1"; exit 0' \
    sh "$normal_pid_file"
normal_descendant="$(sed -n '1p' "$normal_pid_file")"
attempts=0
while kill -0 "$normal_descendant" 2>/dev/null && [ "$attempts" -lt 20 ]; do
  attempts=$((attempts + 1))
  sleep 0.1
done
if kill -0 "$normal_descendant" 2>/dev/null; then
  echo "not ok - descendant $normal_descendant escaped a completed command" >&2
  FAIL=$((FAIL + 1))
else
  echo 'ok - completed commands cannot leave descendants'
  PASS=$((PASS + 1))
fi

interrupt_ready="${TMP}/interrupt.ready"
interrupt_seen="${TMP}/interrupt.seen"
"$RUNNER" --grace-seconds 0.2 5 sh -c \
  'trap '\''printf term >"$2"; exit 0'\'' TERM; printf ready >"$1"; while :; do sleep 1; done' \
  sh "$interrupt_ready" "$interrupt_seen" \
  >"${TMP}/interrupt.out" 2>"${TMP}/interrupt.err" &
runner_pid=$!
attempts=0
while [ ! -f "$interrupt_ready" ] && [ "$attempts" -lt 20 ]; do
  attempts=$((attempts + 1))
  sleep 0.1
done
if [ ! -f "$interrupt_ready" ]; then
  echo 'not ok - interrupt child did not become ready' >&2
  kill -KILL "$runner_pid" 2>/dev/null || true
  wait "$runner_pid" 2>/dev/null || true
  FAIL=$((FAIL + 1))
else
  kill -TERM "$runner_pid"
  wait "$runner_pid"
  interrupt_status=$?
  if [ "$interrupt_status" -eq 143 ] && [ -f "$interrupt_seen" ]; then
    echo 'ok - SIGTERM is forwarded and normalized'
    PASS=$((PASS + 1))
  else
    printf 'not ok - SIGTERM status=%d forwarded=%s\n' \
      "$interrupt_status" "$(test -f "$interrupt_seen" && echo yes || echo no)" >&2
    FAIL=$((FAIL + 1))
  fi
fi

check_status missing_command 127 "$RUNNER" 5 \
  "${TMP}/definitely-not-a-command"
check_status missing_chdir 125 "$RUNNER" \
  --chdir "${TMP}/definitely-not-a-directory" 5 sh -c 'exit 0'

# Resident-set ceiling: malformed ceilings are usage errors, never "no limit".
for bad_ceiling in 0 -1 nan inf not-a-number; do
  check_status "rss_ceiling_rejects_${bad_ceiling}" 2 "$RUNNER" \
    --max-rss-gib "$bad_ceiling" 5 sh -c 'exit 0'
done

check_rss_receipt() {
  local name="$1" outcome="$2"
  if grep -Eq "^run_with_timeout: RSS_RECEIPT ceiling_gib=[0-9.e+-]+ peak_mib=[0-9]+ samples=[0-9]+ outcome=${outcome}\$" \
      "${TMP}/${name}.err"; then
    printf 'ok - %s retains an RSS receipt with outcome=%s\n' "$name" "$outcome"
    PASS=$((PASS + 1))
  else
    printf 'not ok - %s has no RSS receipt with outcome=%s\n' "$name" "$outcome" >&2
    FAIL=$((FAIL + 1))
  fi
}

rss_ran="${TMP}/rss-command-ran"
if [ "$(uname -s)" = Linux ] && [ -r /proc/self/statm ]; then
  check_status rss_within 0 "$RUNNER" --max-rss-gib 4 5 \
    sh -c 'sleep 0.5; : >"$1"' sh "$rss_ran"
  check_rss_receipt rss_within within
  # Touch every page so the allocation is resident, then outlive the timeout
  # by far: only the resident-set ceiling can end this command early.
  rss_started="$(date +%s)"
  check_status rss_exceeded 122 "$RUNNER" --grace-seconds 5 --max-rss-gib 0.0625 60 \
    python3 -c 'import time; data = b"\x01" * (256 << 20); time.sleep(60)'
  check_rss_receipt rss_exceeded exceeded
  if [ $(( $(date +%s) - rss_started )) -lt 30 ]; then
    echo 'ok - resident-set breach kills the group without waiting for the timeout'
    PASS=$((PASS + 1))
  else
    echo 'not ok - resident-set breach waited for the wall-clock bound' >&2
    FAIL=$((FAIL + 1))
  fi
else
  # Without Linux /proc supervision a requested ceiling must refuse to launch
  # rather than run the command unsupervised.
  check_status rss_unsupported 125 "$RUNNER" --max-rss-gib 4 5 \
    sh -c ': >"$1"' sh "$rss_ran"
  if grep -Fq 'is unsupported on' "${TMP}/rss_unsupported.err" && [ ! -e "$rss_ran" ]; then
    echo 'ok - unsupported resident-set ceiling refuses without running the command'
    PASS=$((PASS + 1))
  else
    echo 'not ok - unsupported resident-set ceiling ran the command or lost its diagnostic' >&2
    FAIL=$((FAIL + 1))
  fi
fi

printf '%d passed, %d failed\n' "$PASS" "$FAIL"
[ "$FAIL" -eq 0 ]
