#!/bin/bash
# scripts/check_fmt.sh — rustfmt conformance gate.
#
# The repo commits a rustfmt.toml (edition/style_edition 2024) and the root
# rust-toolchain.toml pins 1.97.1 *with the rustfmt component*, so `cargo fmt`
# output is deterministic for every checkout. Nothing enforced it: `cargo fmt
# --check` appeared nowhere in the tree, and formatting had drifted across
# several files before this gate existed.
#
# Formatting is checked, never rewritten. A gate that silently reformats would
# smuggle unreviewed edits into a landing diff; this one reports and exits.
# Apply fixes deliberately with `cargo fmt --all`.
#
# EXIT CODES
#   0  every workspace file matches rustfmt
#   1  at least one file differs (the diff is printed)
#   2  tooling error (cargo or the rustfmt component unavailable)
set -u

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO="$(dirname "$SCRIPT_DIR")"

if ! command -v cargo >/dev/null 2>&1; then
  echo "check_fmt: TOOLING — cargo not on PATH" >&2
  exit 2
fi
if ! cargo fmt --version >/dev/null 2>&1; then
  echo "check_fmt: TOOLING — rustfmt component missing; install with" >&2
  echo "  rustup component add rustfmt" >&2
  exit 2
fi

cd "$REPO" || {
  echo "check_fmt: TOOLING — cannot enter $REPO" >&2
  exit 2
}

# Capture the diff rather than piping into anything: a pipeline would report the
# exit status of the tail of the pipe, not of rustfmt, which is precisely how a
# gate ends up passing while it is failing.
FMT_OUT="$(cargo fmt --all -- --check 2>&1)"
FMT_RC=$?

if [ "$FMT_RC" -eq 0 ]; then
  echo "check_fmt: OK — every workspace file matches rustfmt"
  exit 0
fi

# rustfmt exits 1 for "would reformat"; anything else is a real tool failure and
# must not be reported as a formatting violation.
if [ "$FMT_RC" -ne 1 ]; then
  echo "check_fmt: TOOLING — cargo fmt exited $FMT_RC" >&2
  printf '%s\n' "$FMT_OUT" >&2
  exit 2
fi

# rustfmt writes `Diff in <path>:<line>:` and colours its output, so strip ANSI
# escapes before matching or every line arrives wrapped in control characters.
FILES="$(printf '%s\n' "$FMT_OUT" \
  | sed $'s/\033\\[[0-9;]*[A-Za-z]//g' \
  | sed -n 's/^Diff in \(.*\):[0-9][0-9]*:$/\1/p' \
  | sort -u)"
COUNT="$(printf '%s\n' "$FILES" | grep -c .)"

printf '%s\n' "$FMT_OUT"
echo "" >&2
echo "check_fmt: RED — $COUNT file(s) differ from rustfmt:" >&2
printf '%s\n' "$FILES" | sed 's|^|  |' >&2
echo "  fix with: cargo fmt --all" >&2
exit 1
