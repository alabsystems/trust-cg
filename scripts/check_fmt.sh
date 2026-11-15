#!/bin/bash
# scripts/check_fmt.sh — trustfmt conformance gate.
#
# The repo commits a rustfmt.toml (edition/style_edition 2024) and builds with
# the Trust toolchain (rust-toolchain.toml `channel = "trust"`; owner directive
# 2026-09-28), whose formatter frontend is `targo fmt` (trustfmt). This gate
# checks the root workspace; separate workspaces need their own formatter
# invocation.
#
# Formatting is checked, never rewritten. A gate that silently reformats would
# smuggle unreviewed edits into a landing diff; this one reports and exits.
# Apply fixes deliberately with `targo fmt --all`.
#
# EXIT CODES
#   0  every workspace file matches trustfmt
#   1  at least one file differs (the diff is printed)
#   2  tooling error (no installed Trust package, or its formatter failed)
set -u

# CDPATH=: a relative directory is never looked up in a CDPATH
# (OD-XHOST-GATE-CWD-20261025, repair round 2).
SCRIPT_DIR="$(CDPATH= cd -- "$(dirname "$0")" && pwd)"
REPO="$(dirname "$SCRIPT_DIR")"
CDPATH= cd -- "$REPO" || {
  echo "check_fmt: TOOLING — cannot enter $REPO" >&2
  exit 2
}

# FRONTEND RESOLUTION. The formatter is the installed Trust package's targo:
# TRUST_TARGO when set (an absolute path), else the package
# scripts/trust_toolchain.py resolves from PATH for the `workspace` purpose (the
# formatter needs no rustc_private crates). There is no rustup or stock
# `cargo fmt` fallback: a tool-resolution failure is TOOLING, never a
# clean-tree verdict.
if [ -n "${TRUST_TARGO:-}" ]; then
  FMT_TARGO="$TRUST_TARGO"
else
  # -I: no user site-packages or .pth file (OD-XHOST-GATE-CWD-20261025). The
  # python3 is resolved once, by an absolute path (repair round 3):
  # SOUNDNESS_PYTHON3 when the caller exported one, else the one PATH finds.
  SOUNDNESS_PYTHON3="${SOUNDNESS_PYTHON3:-$(type -P python3 || true)}"
  case "$SOUNDNESS_PYTHON3" in
    /*) ;;
    *)
      echo "check_fmt: TOOLING — no python3: no executable file by an absolute path (SOUNDNESS_PYTHON3, else PATH): '${SOUNDNESS_PYTHON3}'" >&2
      exit 2
      ;;
  esac
  FMT_TARGO="$("$SOUNDNESS_PYTHON3" -I -B "$SCRIPT_DIR/trust_toolchain.py" --purpose workspace --print targo 2>&1)" || {
    echo "check_fmt: TOOLING — no installed Trust package resolves (scripts/trust_toolchain.py):" >&2
    printf '  %s\n' "$FMT_TARGO" >&2
    exit 2
  }
fi
case "$FMT_TARGO" in
  /*) ;;
  *)
    echo "check_fmt: TOOLING — the Trust targo must be an absolute path, got '$FMT_TARGO'" >&2
    exit 2
    ;;
esac
if [ ! -x "$FMT_TARGO" ]; then
  echo "check_fmt: TOOLING — the Trust targo is not executable: $FMT_TARGO" >&2
  exit 2
fi
FMT_FRONTEND=("$FMT_TARGO" fmt --all -- --check)
FMT_FRONTEND_NAME="targo fmt ($FMT_TARGO)"

# Capture the diff rather than piping into anything: a pipeline would report the
# exit status of the tail of the pipe, not of trustfmt, which is precisely how a
# gate ends up passing while it is failing.
FMT_OUT="$("${FMT_FRONTEND[@]}" 2>&1)"
FMT_RC=$?

if [ "$FMT_RC" -eq 0 ]; then
  echo "check_fmt: OK — every workspace file matches trustfmt (via ${FMT_FRONTEND_NAME})"
  exit 0
fi

# trustfmt exits 1 for "would reformat"; anything else is a real tool failure and
# must not be reported as a formatting violation.
if [ "$FMT_RC" -ne 1 ]; then
  echo "check_fmt: TOOLING — ${FMT_FRONTEND_NAME} exited $FMT_RC" >&2
  printf '%s\n' "$FMT_OUT" >&2
  exit 2
fi

# trustfmt writes `Diff in <path>:<line>:` and colours its output, so strip ANSI
# escapes before matching or every line arrives wrapped in control characters.
FILES="$(printf '%s\n' "$FMT_OUT" \
  | sed $'s/\033\\[[0-9;]*[A-Za-z]//g' \
  | sed -n 's/^Diff in \(.*\):[0-9][0-9]*:$/\1/p' \
  | sort -u)"
COUNT="$(printf '%s\n' "$FILES" | grep -c .)"

printf '%s\n' "$FMT_OUT"
echo "" >&2
echo "check_fmt: RED — $COUNT file(s) differ from trustfmt:" >&2
printf '%s\n' "$FILES" | sed 's|^|  |' >&2
echo "  fix with: targo fmt --all" >&2
exit 1
