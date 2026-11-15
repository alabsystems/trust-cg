#!/bin/bash
# scripts/check_tippy.sh — tippy (Trust lint) conformance gate.
#
# WHY THIS EXISTS. The workspace already denies warnings
# (`[workspace.lints]`), so every lint finding is an `error:`. Nothing ran a
# linter. By the time anyone looked there were 142 findings across four crates
# — and, worse, they were UNREPORTABLE, twice over:
#
#   * The linter aborts on the first CRATE that fails. `trust-cg-lower` failed,
#     so a developer saw twelve errors there and never learned that
#     `trust-cg-verify` had fifty-one more behind them, which hid twenty-five in
#     `trust-cg-codegen`, which hid twenty-eight more.
#   * Within a crate, cargo stops at the first failing TARGET, so one red
#     integration test hid every later one.
#
# Hence both: lint each package SEPARATELY, and pass `--keep-going`. A gate that
# cannot see past the first red crate or the first red target is not a gate — it
# is a way to believe the tree is clean.
#
# The frontend is the installed Trust package's `targo tippy`; see the
# FRONTEND RESOLUTION block.
#
# This is the same lesson `check_fmt.sh` records in `hooks/pre-push`
# ("existed with NOTHING calling it, and went red three separate times"),
# applied to the lint surface the formatting gate does not cover.
#
# Findings are REPORTED, never auto-applied. `targo tippy --fix` rewrites
# source, and a gate that silently rewrites smuggles unreviewed edits into a
# landing diff.
#
# COST. Unlike the 7 s formatting gate this needs a type-check of the whole
# workspace: roughly 1-4 minutes cold, seconds warm. It is wired into
# `hooks/pre-push` AFTER the formatting pre-flight and BEFORE the soundness
# meta-gate (which itself takes several minutes), so the cheapest gate always
# fails first.
#
# SCOPE. `--no-deps` lints only the listed workspace packages: third-party
# crates are not this repo's lint debt. Libraries use `--lib --tests`, and the
# CLI uses `--bins --tests`, covering their shipping code and regression tests.
# Benches and standalone examples are out of scope.
#
# KNOWN GAP, stated rather than left to be discovered: `crates/rustc-codegen-
# trust-cg` is a SEPARATE workspace (Trust-pinned, rustc-private) and this gate
# never builds it. Some of its sources are pulled into `trust-cg-verify`'s
# tests with `#[path]`, so they ARE linted — but under the INCLUDING crate's
# edition (2024), not their own (2021). That difference is not academic: a
# `collapsible_if` suggestion taken here once produced a `&& let` chain that
# parses under 2024 and is a PARSE ERROR in the crate's own edition, leaving
# that crate unbuildable (4d50932d0, reverted by 39d3cc125). Those three sites
# now carry an edition-justified `#[allow]`. Linting that crate for real is a
# separate job (its own workspace and manifest).
#
# EXIT CODES
#   0  every LINTED package is clean. Targets that deliberately refuse this
#      frontend's compiler are reported as NOT LINTED on the verdict line —
#      they are neither findings nor coverage.
#   1  at least one finding (the diagnostics are printed)
#   2  tooling error (no lint frontend resolvable, or a non-lint build failure)
set -u

# CDPATH=: a relative directory is never looked up in a CDPATH
# (OD-XHOST-GATE-CWD-20261025, repair round 2).
SCRIPT_DIR="$(CDPATH= cd -- "$(dirname "$0")" && pwd)"
REPO="$(dirname "$SCRIPT_DIR")"
CDPATH= cd -- "$REPO" || {
  echo "check_tippy: TOOLING — cannot enter $REPO" >&2
  exit 2
}

# Packages to lint, in dependency order so the first failure is the most
# upstream one: every package of the root workspace (OD-LINT-WORKSPACE-20261011).
# Keep this list explicit rather than using `--workspace`: a package added
# without a deliberate decision about its lint debt should not silently join
# (or silently skip) the gate; scripts/tests/test_check_tippy.py checks that
# the list names every workspace member.
PACKAGES=(
  trust-cg-process-env
  trust-cg-ir
  trust-cg-dialect
  trust-cg-lower
  trust-cg-regalloc
  trust-cg-opt
  trust-cg-drat-trim
  trust-cg-eqsat-check
  trust-cg-eqsat
  trust-cg-verify
  trust-cg-irmid
  trust-cg-codegen
  trust-cg-lift
  trust-cg-llvm-import
  trust-cg-onnx-import
  trust-cg-jit-matrix
  trust-cg-sat-host
  trust-cg-fuzz
  trust-cg-test
  trust-types
  trust-cg-cli
)

# FRONTEND RESOLUTION — the same discipline as check_fmt.sh. ALab systems build
# with the Trust toolchain (rust-toolchain.toml `channel = "trust"`; owner
# directive 2026-09-28): `targo` is cargo, `trustc` is rustc, and `tippy` is
# clippy. The linter is the installed Trust package's `targo tippy`: TRUST_TARGO
# when set (an absolute path), else the package scripts/trust_toolchain.py
# resolves from PATH for the `workspace` purpose (the root workspace links no
# rustc_private crate). There is no rustup probing and no stock `cargo clippy`
# fallback; a tool-resolution failure returns TOOLING, never a clean-tree
# verdict. The verdict line NAMES the frontend that ran.
#
# Linting is not a proof claim: `tippy` runs Targo's UNVERIFIED lane and says
# so on stderr. Trust VERIFICATION is a separate, explicit gate
# (scripts/check_trust_default_authority.py, scripts/check_proof_gate.sh).
#
# atpkg's `tippy-driver` is `clippy 0.1.98`; its `chunks_exact` -> `as_chunks`
# family found 26 real sites in this tree when this gate first ran it (history:
# the stock-vs-Trust frontend choice this block used to carry, before the
# migration).
if [ -n "${TRUST_TARGO:-}" ]; then
  LINT_TARGO="$TRUST_TARGO"
else
  # -I: no user site-packages or .pth file (OD-XHOST-GATE-CWD-20261025). The
  # python3 is resolved once, by an absolute path (repair round 3):
  # SOUNDNESS_PYTHON3 when the caller exported one, else the one PATH finds.
  SOUNDNESS_PYTHON3="${SOUNDNESS_PYTHON3:-$(type -P python3 || true)}"
  case "$SOUNDNESS_PYTHON3" in
    /*) ;;
    *)
      echo "check_tippy: TOOLING — no python3: no executable file by an absolute path (SOUNDNESS_PYTHON3, else PATH): '${SOUNDNESS_PYTHON3}'" >&2
      exit 2
      ;;
  esac
  LINT_TARGO="$("$SOUNDNESS_PYTHON3" -I -B "$SCRIPT_DIR/trust_toolchain.py" --purpose workspace --print targo 2>&1)" || {
    echo "check_tippy: TOOLING — no installed Trust package resolves (scripts/trust_toolchain.py):" >&2
    printf '  %s\n' "$LINT_TARGO" >&2
    echo "  Refusing — a gate that cannot run must not report a clean tree." >&2
    exit 2
  }
fi
case "$LINT_TARGO" in
  /*) ;;
  *)
    echo "check_tippy: TOOLING — the Trust targo must be an absolute path, got '$LINT_TARGO'" >&2
    exit 2
    ;;
esac
if [ ! -x "$LINT_TARGO" ]; then
  echo "check_tippy: TOOLING — the Trust targo is not executable: $LINT_TARGO" >&2
  exit 2
fi
FRONTEND=("$LINT_TARGO" tippy)
FRONTEND_NAME="targo tippy ($LINT_TARGO)"

RED_PACKAGES=()
SKIPPED_PACKAGES=()
TOTAL=0

for pkg in "${PACKAGES[@]}"; do
  # Each package's shipping targets and regression tests: binaries where it
  # has them (the CLI and trust-cg-test have no library), and the importer's
  # `driver` feature, whose tests the AArch64 floors run.
  case "$pkg" in
    trust-cg-cli | trust-cg-test) TARGETS=(--bins --tests) ;;
    trust-cg-llvm-import) TARGETS=(--lib --bins --tests --features driver) ;;
    trust-cg-sat-host | trust-cg-onnx-import | trust-cg-jit-matrix | trust-cg-fuzz)
      TARGETS=(--lib --bins --tests) ;;
    *) TARGETS=(--lib --tests) ;;
  esac
  # Capture rather than pipe: a pipeline reports the exit status of the tail,
  # which is precisely how a gate ends up passing while it is failing.
  # `--keep-going` matters as much as the per-package loop: without it cargo
  # stops at the first failing TARGET, so a red integration test hides every
  # later one and the gate has to be re-run once per target to converge. With
  # it, one run reports the whole union.
  OUT="$("${FRONTEND[@]}" --locked -p "$pkg" "${TARGETS[@]}" --no-deps \
    --keep-going --message-format short 2>&1)"
  RC=$?
  if [ "$RC" -eq 0 ]; then
    echo "check_tippy: ok — $pkg"
    continue
  fi
  # Count real diagnostics. `--message-format short` emits most findings as
  # `path:line:col: error: ...`, but SOME carry no source location and print as
  # a bare `error: ...` — `duplicate_mod` is one, and counting only the located
  # form made this gate report TOOLING for a genuine lint failure. Match both,
  # and exclude cargo's own trailing summaries so they are not counted as
  # findings.
  DIAGS="$(printf '%s\n' "$OUT" \
    | grep -E ': error: |^error: ' \
    | grep -vE '^error: could not compile|^error: aborting|^error: build failed')"

  # DELIBERATE FRONTEND REFUSALS are not lint debt and not a clean result.
  #
  # Some `trust-cg-codegen` test targets carry
  #   #[cfg(kernel_fixture_layout_unknown)]
  #   compile_error!("kernel JIT fixtures require exact Rust 1.95.0, Rust
  #                   1.97.1, or the certified Trust compiler");
  # because they hard-code kernel type MEMORY OFFSETS (Name 40 bytes, tag @0,
  # Str{parent@8,ptr@16,len@24}, …). Under any other compiler those offsets may
  # be wrong and the JIT fixtures would decode garbage, so refusing is the
  # correct, fail-closed behaviour — and it fires for `tippy`, whose trustc is
  # not a compiler fixture_toolchain.rs certifies.
  #
  # Counting such a refusal as a finding would be a false alarm; ignoring it
  # would let the gate report "clean" for a target it never linted. Separate it
  # and SAY SO: silent truncation reads as "covered everything" when it did not.
  REFUSALS="$(printf '%s\n' "$DIAGS" | grep -c 'kernel JIT fixtures require exact')"
  DIAGS="$(printf '%s\n' "$DIAGS" | grep -v 'kernel JIT fixtures require exact')"
  N="$(printf '%s\n' "$DIAGS" | grep -c .)"
  if [ "$REFUSALS" -gt 0 ]; then
    SKIPPED_PACKAGES+=("$pkg($REFUSALS)")
    echo "check_tippy: NOT LINTED — $pkg: $REFUSALS target(s) refuse this frontend's" \
         "compiler (kernel fixture layout guard); they need a compiler" \
         "crates/trust-cg-codegen/fixture_toolchain.rs certifies" >&2
  fi
  if [ "$N" -eq 0 ]; then
    if [ "$REFUSALS" -gt 0 ]; then
      # Every diagnostic was a deliberate refusal: nothing to fix here.
      echo "check_tippy: ok — $pkg (minus the refused target(s) above)"
      continue
    fi
    # Non-zero with no diagnostics is a build/tooling failure, not lint debt.
    echo "check_tippy: TOOLING — ${FRONTEND_NAME} exited $RC for $pkg with no diagnostics" >&2
    printf '%s\n' "$OUT" >&2
    exit 2
  fi
  echo "check_tippy: RED — $pkg ($N finding(s))" >&2
  printf '%s\n' "$DIAGS" >&2
  RED_PACKAGES+=("$pkg($N)")
  TOTAL=$((TOTAL + N))
done

if [ "${#RED_PACKAGES[@]}" -eq 0 ]; then
  if [ "${#SKIPPED_PACKAGES[@]}" -gt 0 ]; then
    echo "check_tippy: OK — ${#PACKAGES[@]} package(s) clean (via ${FRONTEND_NAME})," \
         "EXCEPT the refused target(s) in: ${SKIPPED_PACKAGES[*]} — those were NOT linted"
  else
    echo "check_tippy: OK — ${#PACKAGES[@]} package(s) clean (via ${FRONTEND_NAME})"
  fi
  exit 0
fi

echo "" >&2
echo "check_tippy: RED — $TOTAL finding(s) in: ${RED_PACKAGES[*]}" >&2
echo "  The workspace denies warnings, so each of these fails the build." >&2
echo "  Inspect one package with:" >&2
echo "    targo tippy --locked -p <pkg> --tests --no-deps --keep-going" >&2
exit 1
