#!/bin/bash
# scripts/check_lock_drift.sh — BENCH-7: soundness_revs.lock drift alarm.
#
# soundness_revs.lock pins the exact cross-repo revision set (trust-cg, Clean,
# AY) recorded by scripts/soundness_check.sh. A stale pin means the
# soundness meta-gate vouches for a months-old constellation (the lock has been
# 269+ commits behind before — the failure mode this alarm exists to kill).
#
# This check is ADDITIVE (a new failure mode, never a bypass): it re-pins
# nothing. Re-pinning happens EXCLUSIVELY via `scripts/soundness_check.sh
# --update`, which self-enforces green-gates-first — never hand-edit the lock.
#
# THRESHOLD: 50 commits (roadmap BENCH-7 / M6 gate: "lock drift <= 50").
# Override for experiments with TCG_LOCK_DRIFT_MAX=<n>; tightening the default
# is a one-line commit here.
#
# EXIT CODES
#   0  every pinned rev is within the threshold of its repo's HEAD
#   1  drift beyond threshold, lock missing/unparsable, or pinned rev unknown
#   2  tooling error (git missing, repo dir absent)
set -u

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO="$(dirname "$SCRIPT_DIR")"
LOCK_FILE="$REPO/soundness_revs.lock"
MAX_DRIFT="${TCG_LOCK_DRIFT_MAX:-50}"

case "$MAX_DRIFT" in
  ''|*[!0-9]*)
    echo "check_lock_drift: TOOLING — TCG_LOCK_DRIFT_MAX must be a nonnegative integer" >&2
    exit 2
    ;;
esac

CLEAN_DIR="${CLEAN_DIR:-${HOME}/clean}"
AY_DIR="${AY_DIR:-${HOME}/ay}"

if ! command -v git >/dev/null 2>&1; then
  echo "check_lock_drift: TOOLING — git not on PATH" >&2
  exit 2
fi
if [ ! -f "$LOCK_FILE" ]; then
  echo "check_lock_drift: RED — soundness_revs.lock missing at $LOCK_FILE" >&2
  exit 1
fi

lock_get() {
  awk -F= -v k="$1" '
    /^[[:space:]]*#/ { next }
    { gsub(/^[[:space:]]+|[[:space:]]+$/, "", $1) }
    $1 == k { v=$2; gsub(/^[[:space:]]+|[[:space:]]+$/, "", v); print v; exit }
  ' "$LOCK_FILE"
}

RC=0
TOOLING=0

is_lock_only_attestation_child() {
  local dir="$1" pinned="$2" live="$3"
  local row parent changed
  row="$(git -C "$dir" rev-list --parents -n 1 "$live" 2>/dev/null)"
  [ "$(printf '%s\n' "$row" | awk '{print NF}')" -eq 2 ] || return 1
  parent="$(git -C "$dir" rev-parse "${live}^" 2>/dev/null)" || return 1
  [ "$parent" = "$pinned" ] || return 1
  changed="$(git -C "$dir" diff --name-only "$pinned" "$live" -- 2>/dev/null)"
  [ "$changed" = "soundness_revs.lock" ]
}

check_drift() {
  # check_drift <label> <repo_dir> <lock_key>
  local label="$1" dir="$2" key="$3"
  local pinned drift head behind
  pinned="$(lock_get "$key")"
  if [ -z "$pinned" ]; then
    echo "check_lock_drift: RED — $key missing from soundness_revs.lock" >&2
    RC=1
    return
  fi
  if ! git -C "$dir" rev-parse --git-dir >/dev/null 2>&1; then
    echo "check_lock_drift: TOOLING — $label repo not found at $dir (cannot measure drift)" >&2
    TOOLING=1
    return
  fi
  if ! git -C "$dir" cat-file -e "${pinned}^{commit}" 2>/dev/null; then
    echo "check_lock_drift: RED — $label pinned rev $pinned is unknown in $dir" >&2
    RC=1
    return
  fi
  head="$(git -C "$dir" rev-parse HEAD)"
  if [ "$label" = "trust-cg" ] && is_lock_only_attestation_child "$dir" "$pinned" "$head"; then
    echo "check_lock_drift: trust-cg OK — HEAD is the lock-only attestation child of ${pinned:0:9}"
    return
  fi
  if git -C "$dir" merge-base --is-ancestor "$pinned" "$head" 2>/dev/null; then
    drift="$(git -C "$dir" rev-list --count "${pinned}..${head}" 2>/dev/null || echo ERR)"
  elif git -C "$dir" merge-base --is-ancestor "$head" "$pinned" 2>/dev/null; then
    behind="$(git -C "$dir" rev-list --count "${head}..${pinned}" 2>/dev/null || echo ERR)"
    echo "check_lock_drift: RED — $label checkout is behind the pinned revision by ${behind} commit(s)" >&2
    RC=1
    return
  else
    echo "check_lock_drift: RED — $label HEAD and pinned revision have diverged" >&2
    RC=1
    return
  fi
  if [ "$drift" = "ERR" ]; then
    echo "check_lock_drift: RED — $label rev-list failed for ${pinned}..HEAD in $dir" >&2
    RC=1
    return
  fi
  if [ "$drift" -gt "$MAX_DRIFT" ]; then
    echo "check_lock_drift: RED — $label lock drift $drift commits (> $MAX_DRIFT): pinned=${pinned:0:9} head=${head:0:9}" >&2
    echo "  re-pin ONLY via: scripts/soundness_check.sh --update  (green gates first)" >&2
    RC=1
  else
    echo "check_lock_drift: $label OK — $drift commits behind HEAD (<= $MAX_DRIFT)"
  fi
}

check_drift "trust-cg" "$REPO" trust_cg_rev
check_drift "clean" "$CLEAN_DIR" clean_rev
check_drift "ay" "$AY_DIR" ay_rev

if [ "$RC" = 1 ]; then
  exit 1
fi
if [ "$TOOLING" = 1 ]; then
  exit 2
fi
exit 0
