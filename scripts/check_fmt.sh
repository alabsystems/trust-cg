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

# FRONTEND RESOLUTION. rust-toolchain.toml pins 1.97.1 with the rustfmt
# component, but a checkout can instead resolve to a Trust-branded sysroot
# (`channel = "trust"`), which ships Trust frontends ONLY — `targo-fmt`,
# `trustfmt` — and deliberately does not install `cargo-fmt`. `cargo fmt` then
# cannot resolve:
#
#   error: 'cargo-fmt' is not installed for the custom toolchain 'trust'.
#
# and this gate exited 2 (TOOLING) without checking anything. Measured 2026-08-27
# on aarch64-unknown-linux-gnu: exit 2, while the pinned formatter found 19 files
# drifted. A gate that cannot run reports no violations, which reads exactly like
# a clean tree.
#
# Resolve through `rustc --print sysroot`, which honours rust-toolchain.toml and
# therefore follows the PIN rather than ambient PATH. Keep the stock `cargo fmt`
# path for a checkout on an upstream toolchain, and FAIL CLOSED if neither is
# available rather than falling back to something that would format to a
# different style under the same gate name.
if ! command -v rustc >/dev/null 2>&1; then
  echo "check_fmt: TOOLING — rustc not on PATH" >&2
  exit 2
fi
FMT_SYSROOT="$(rustc --print sysroot 2>/dev/null || true)"
if [ -n "$FMT_SYSROOT" ] && [ -x "$FMT_SYSROOT/bin/targo" ]; then
  FMT_FRONTEND=("$FMT_SYSROOT/bin/targo" fmt --all -- --check)
  FMT_FRONTEND_NAME="targo fmt (pinned Trust sysroot)"
elif command -v cargo >/dev/null 2>&1 && cargo fmt --version >/dev/null 2>&1; then
  FMT_FRONTEND=(cargo fmt --all -- --check)
  FMT_FRONTEND_NAME="cargo fmt (stock toolchain)"
else
  echo "check_fmt: TOOLING — no formatter frontend available." >&2
  echo "  a Trust-pinned sysroot should supply bin/targo; this one does not." >&2
  echo "  resolved sysroot: ${FMT_SYSROOT:-<none>}" >&2
  echo "  stock \`cargo fmt\` is also unavailable. Refusing — a gate that cannot" >&2
  echo "  run must not report a clean tree." >&2
  exit 2
fi

cd "$REPO" || {
  echo "check_fmt: TOOLING — cannot enter $REPO" >&2
  exit 2
}

# Capture the diff rather than piping into anything: a pipeline would report the
# exit status of the tail of the pipe, not of rustfmt, which is precisely how a
# gate ends up passing while it is failing.
FMT_OUT="$("${FMT_FRONTEND[@]}" 2>&1)"
FMT_RC=$?

if [ "$FMT_RC" -eq 0 ]; then
  echo "check_fmt: OK — every workspace file matches rustfmt (via ${FMT_FRONTEND_NAME})"
  exit 0
fi

# rustfmt exits 1 for "would reformat"; anything else is a real tool failure and
# must not be reported as a formatting violation.
if [ "$FMT_RC" -ne 1 ]; then
  echo "check_fmt: TOOLING — ${FMT_FRONTEND_NAME} exited $FMT_RC" >&2
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
