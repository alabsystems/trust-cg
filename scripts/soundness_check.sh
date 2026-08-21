#!/usr/bin/env bash
#
# soundness_check.sh — the #4 LOCAL soundness meta-gate ("meta-CI", local half).
#
# WHAT THIS IS
# ------------
# One runnable in-repo entrypoint that, at pinned cross-repository revisions,
# runs the configured soundness-evidence checks and fails closed (nonzero exit)
# if a listed gate is missing, vacuous, or erroring. A developer runs this
# locally before landing a change.
#
# This is not hosted CI. It is a shell script a developer runs locally; see
# SOUNDNESS_CHECK.md for the trust boundary and optional hook behavior.
#
# WHAT IT AGGREGATES
# ------------------
#   trust-cg (cargo test -p trust-cg-verify --test <target>):
#     - soundness_manifest      (THE meta-gate: every invariant has a live
#                                fail-closed test; every B-* id present)
#     - coverage_gate_tests     (accepted/deferred inventory: AArch64 155/248
#                                with 93 named RED rows; x86-64 163/192 with 29,
#                                RISC-V 14/17 with 3, WebAssembly 109/111 with 2.
#                                Exact classifications are pinned; unknown drift
#                                fails. Ratios are evidence coverage, not
#                                correctness-proof percentages; Statistical
#                                Valid is regression evidence, not formal proof)
#     - meta_theorems           (properties-not-values headline invariants)
#     - mutation_catalog        (mutation testing harness)
#     - proof_gate_strict       (universal non-degeneracy gate + fail-closed)
#     - fsym_real_function_corpus (real-function symbolic preflight corpus)
#     - the 9 differential bridges:
#         bdefs_differential_bridge            (B-aarch64-int)
#         bdefs_differential_bridge_x86        (B-x86-rosetta)
#         bdefs_differential_bridge_riscv      (B-riscv-qemu)
#         bdefs_differential_bridge_x86_packed (B-x86-sse-packed)
#         bdefs_differential_bridge_x86_fp     (B-x86-sse-fp)
#         bdefs_differential_bridge_neon       (B-aarch64-neon)
#         bdefs_differential_bridge_riscv_fp   (B-riscv-fp)
#         bdefs_differential_bridge_neon_fp    (B-aarch64-neon-fp)
#         fp_bitmodel_bridge                   (B-aarch64-fp / FP bit-model)
#
#   Clean checkout:
#     - clean check <file>      for each B-def / LRAT-checker .lean proof
#         aarch64_isa, aarch64_isa_chip, aarch64_fp, aarch64_fp_arith,
#         aarch64_fp_cvt, aarch64_fp_divsqrt, aarch64_fp16, reducible_word,
#         lrat_checker, lrat_checker_word, lrat_checker_tree
#     - cargo test -p clean-kernel --test micro_diversity_gate
#                               (the kernel diversity gate)
#
# EXIT CODE: 0 iff EVERY gate above passes. Nonzero if ANY gate fails, errors,
# or cannot be run (a missing/erroring gate is a FAIL, never a silent skip).
#
# v0.1.0 has no tolerated failing/missing gate target. The opcode inventory has
# pinned, explicitly named RED model gaps; an unknown/unclassified RED fails the
# inventory test. The separately run external-SMT full-database floor reports
# solver-capacity pending results without calling them proofs; see
# scripts/check_proof_gate.sh.
#
# USAGE
#   scripts/soundness_check.sh                 # run all gates, warn on rev drift
#   scripts/soundness_check.sh --pinned        # FAIL if any repo HEAD != lock
#   scripts/soundness_check.sh --update        # re-pin the lock after a green run
#   scripts/soundness_check.sh --list          # list the gates and exit
#   scripts/soundness_check.sh --validate-clean-summary <log>
#                                              # validate one Clean log and exit
#   scripts/soundness_check.sh --self-test-clean-cargo-command
#                                              # exercise the stock-Cargo wrapper only
#   scripts/soundness_check.sh -h | --help
#
# Each Cargo, Clean, and Lake workload is limited to 7200 seconds by default.
# Override that positive duration with SOUNDNESS_COMMAND_TIMEOUT_SECONDS.
#
set -u
set -o pipefail

# ----------------------------------------------------------------------------
# Paths (env-overridable; default to this checkout and its $HOME-sibling repos).
# ----------------------------------------------------------------------------
TRUST_CG_DIR="${TRUST_CG_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")/.." && pwd)}"
CLEAN_DIR="${CLEAN_DIR:-$HOME/clean}"
AY_DIR="${AY_DIR:-$HOME/ay}"
CLEAN_BIN="${CLEAN_DIR}/target/release/clean"
LOCK_FILE="${TRUST_CG_DIR}/soundness_revs.lock"
TIMEOUT_RUNNER="${TRUST_CG_DIR}/scripts/run_with_timeout.py"
SOUNDNESS_COMMAND_TIMEOUT_SECONDS="${SOUNDNESS_COMMAND_TIMEOUT_SECONDS:-7200}"

# The Lean forward-simulation development (ENC-1) is a conditional model-level
# theorem with classified gaps. The gate below asserts `lake build` is green and
# pins the classified-sorry and explicit-axiom counts at their baselines.
LEAN_FORMAL_DIR="${TRUST_CG_DIR}/formal/lean"
BASELINE_LEAN_SORRY=17   # classified sorries (grep '^\s*sorry'); lower ONLY when one is discharged
BASELINE_LEAN_AXIOM=4    # explicit trusted axioms: srcStep_spec, x86Step_decode, decode_encode, step_emitted
EXPECTED_RUSTC_VERSION="rustc 1.97.1"
EXPECTED_CARGO_VERSION="cargo 1.97.1"

# Older Clean development configs carried both the host tune and a Trust-only
# verifier opt-out in their aarch64 target rustflags. This soundness lane
# deliberately compiles Clean with a diverse stock toolchain. When that legacy
# stanza is present on the one host where it applies, validate its complete
# value before a global RUSTFLAGS replacement removes the Trust-only member and
# retains the compatible tune. A config with no Trust-only flag is already
# stock-compatible and must be preserved rather than rejected or overwritten.
CLEAN_STOCK_AARCH64_RUSTFLAGS="-C target-cpu=native"
CLEAN_TRUST_AARCH64_CONFIG_RUSTFLAGS='rustflags=["-C","target-cpu=native","-Ztrust-verify=off"]'

export PATH="${HOME}/.cargo/bin:${HOME}/.elan/bin:${PATH}"
export RUSTUP_TOOLCHAIN="1.97.1"
unset RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER RUSTFLAGS CARGO_ENCODED_RUSTFLAGS \
  CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS

# ----------------------------------------------------------------------------
# Flags.
# ----------------------------------------------------------------------------
MODE_PINNED=0     # --pinned : rev drift is a hard FAIL
MODE_UPDATE=0     # --update : re-pin lock after a green run
MODE_LIST=0       # --list   : list gates and exit
MODE_VALIDATE_CLEAN_SUMMARY=""
MODE_SELF_TEST_CLEAN_CARGO_COMMAND=0

usage() {
  sed -n '2,80p' "$0" | sed 's/^# \{0,1\}//'
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --pinned)  MODE_PINNED=1 ;;
    --update)  MODE_UPDATE=1 ;;
    --list)    MODE_LIST=1 ;;
    --validate-clean-summary)
      if [ "$#" -lt 2 ]; then
        echo "soundness_check.sh: --validate-clean-summary requires a log path" >&2
        exit 2
      fi
      MODE_VALIDATE_CLEAN_SUMMARY="$2"
      shift
      ;;
    --self-test-clean-cargo-command)
      MODE_SELF_TEST_CLEAN_CARGO_COMMAND=1
      ;;
    -h|--help) usage; exit 0 ;;
    *) echo "soundness_check.sh: unknown argument: $1" >&2
       echo "  try --help" >&2
       exit 2 ;;
  esac
  shift
done
if [ "$MODE_PINNED" -eq 1 ] && [ "$MODE_UPDATE" -eq 1 ]; then
  echo "soundness_check.sh: --pinned and --update are mutually exclusive" >&2
  exit 2
fi
if [ -n "$MODE_VALIDATE_CLEAN_SUMMARY" ] && \
   { [ "$MODE_PINNED" -eq 1 ] || [ "$MODE_UPDATE" -eq 1 ] || [ "$MODE_LIST" -eq 1 ] || \
     [ "$MODE_SELF_TEST_CLEAN_CARGO_COMMAND" -eq 1 ]; }; then
  echo "soundness_check.sh: --validate-clean-summary cannot be combined with another mode" >&2
  exit 2
fi
if [ "$MODE_SELF_TEST_CLEAN_CARGO_COMMAND" -eq 1 ] && \
   { [ "$MODE_PINNED" -eq 1 ] || [ "$MODE_UPDATE" -eq 1 ] || [ "$MODE_LIST" -eq 1 ]; }; then
  echo "soundness_check.sh: --self-test-clean-cargo-command cannot be combined with another mode" >&2
  exit 2
fi

# ----------------------------------------------------------------------------
# Output helpers.
# ----------------------------------------------------------------------------
if [ -t 1 ]; then
  C_RED=$'\033[31m'; C_GRN=$'\033[32m'; C_YEL=$'\033[33m'
  C_BLU=$'\033[34m'; C_BLD=$'\033[1m';  C_RST=$'\033[0m'
else
  C_RED=''; C_GRN=''; C_YEL=''; C_BLU=''; C_BLD=''; C_RST=''
fi

hr() { printf '%s\n' "------------------------------------------------------------------------"; }
section() { printf '\n%s%s%s\n' "$C_BLD" "$1" "$C_RST"; hr; }

# Per-gate result accounting. Parallel arrays keep order + status + detail.
GATE_NAMES=()
GATE_STATUS=()   # PASS / FAIL
GATE_DETAIL=()
FAIL_COUNT=0
PASS_COUNT=0

record() {
  # record <name> <PASS|FAIL> <detail>
  GATE_NAMES+=("$1")
  GATE_STATUS+=("$2")
  GATE_DETAIL+=("$3")
  if [ "$2" = "PASS" ]; then
    PASS_COUNT=$((PASS_COUNT + 1))
    printf '  %s[PASS]%s %-46s %s\n' "$C_GRN" "$C_RST" "$1" "$3"
  else
    FAIL_COUNT=$((FAIL_COUNT + 1))
    printf '  %s[FAIL]%s %-46s %s\n' "$C_RED" "$C_RST" "$1" "$3"
  fi
}

# ----------------------------------------------------------------------------
# Gate inventories (single source of truth — also used by --list).
# ----------------------------------------------------------------------------

# trust-cg cargo test targets. The meta-gate (soundness_manifest) leads.
TRUST_CG_GATES=(
  soundness_manifest
  coverage_gate_tests
  meta_theorems
  mutation_catalog
  proof_gate_strict
  fsym_real_function_corpus
  bdefs_differential_bridge
  bdefs_differential_bridge_x86
  bdefs_differential_bridge_riscv
  bdefs_differential_bridge_x86_packed
  bdefs_differential_bridge_x86_fp
  bdefs_differential_bridge_neon
  bdefs_differential_bridge_riscv_fp
  bdefs_differential_bridge_neon_fp
  fp_bitmodel_bridge
)

# Clean .lean proofs to clean-check (B-defs + LRAT checkers).
CLEAN_LEAN=(
  aarch64_isa
  aarch64_isa_chip
  aarch64_fp
  aarch64_fp_arith
  aarch64_fp_cvt
  aarch64_fp_divsqrt
  aarch64_fp16
  reducible_word
  lrat_checker
  lrat_checker_word
  lrat_checker_tree
)

if [ "$MODE_LIST" -eq 1 ]; then
  echo "trust-cg gate test targets (cargo test -p trust-cg-verify --test <name>):"
  for g in "${TRUST_CG_GATES[@]}"; do echo "  - $g"; done
  echo
  echo "Clean checkout: clean-check .lean proofs (clean check proofs/<name>.lean):"
  for f in "${CLEAN_LEAN[@]}"; do echo "  - $f"; done
  echo
  echo "Clean checkout: kernel diversity gate:"
  echo "  - cargo test -p clean-kernel --test micro_diversity_gate"
  echo
  echo "formal/lean forward-sim (ENC-1):"
  echo "  - lake build (formal/lean) + sorry-count==${BASELINE_LEAN_SORRY} + axiom-count==${BASELINE_LEAN_AXIOM}"
  echo
  echo "ENC-4 Lean<->backend encoder golden binding:"
  echo "  - cargo test -p trust-cg-codegen --test lean_encode_golden_binding (Rust leg;"
  echo "    Lean leg is the EncoderGolden.lean 'by decide' theorems compiled by lake above)"
  echo
  echo "Named exclusions: none in the v0.1.0 soundness gate."
  exit 0
fi

# ----------------------------------------------------------------------------
# Lock-file handling.
# ----------------------------------------------------------------------------
lock_get() {
  # lock_get <key> -> value (empty if absent)
  [ -f "$LOCK_FILE" ] || { echo ""; return; }
  awk -F= -v k="$1" '
    /^[[:space:]]*#/ { next }
    { gsub(/^[[:space:]]+|[[:space:]]+$/, "", $1) }
    $1 == k { v=$2; gsub(/^[[:space:]]+|[[:space:]]+$/, "", v); print v; exit }
  ' "$LOCK_FILE"
}

lock_key_count() {
  [ -f "$LOCK_FILE" ] || { echo 0; return; }
  awk -F= -v k="$1" '
    /^[[:space:]]*#/ { next }
    { gsub(/^[[:space:]]+|[[:space:]]+$/, "", $1) }
    $1 == k { n += 1 }
    END { print n + 0 }
  ' "$LOCK_FILE"
}

candidate_repository_org() {
  # Read the candidate's declared upstream identity from committed policy.
  # Publication rewrites this field together with dependency source owners,
  # so contributor forks do not depend on their mutable `origin` remote.
  local manifest="${TRUST_CG_DIR}/Cargo.toml"
  local parsed_org
  [ -f "$manifest" ] || { echo INVALID; return 1; }

  if ! parsed_org="$(
    sed -n \
      '/^[[:space:]]*\[workspace\.package\][[:space:]]*$/,/^[[:space:]]*\[/p' \
      "$manifest" |
      grep -E '^[[:space:]]*repository[[:space:]]*=' |
      sed -E 's|^[[:space:]]*repository[[:space:]]*=[[:space:]]*"https://github\.com/([A-Za-z0-9][A-Za-z0-9_.-]*)/trust-cg(\.git)?"[[:space:]]*$|ORG:\1|' |
      awk '
        NF != 1 || $1 !~ /^ORG:[A-Za-z0-9][A-Za-z0-9_.-]*$/ { bad=1; next }
        { count += 1; org = substr($1, 5) }
        END {
          if (!bad && count == 1) print org
          else exit 1
        }
      '
  )"; then
    echo INVALID
    return 1
  fi
  printf '%s\n' "$parsed_org"
}

candidate_dependency_rev() {
  # Resolve one exact first-party Git revision from the candidate root lock.
  # Require the dependency owner to match the candidate's declared upstream,
  # query and fragment SHAs to agree, and exactly one distinct revision.
  local repo="$1"
  local repository_org
  local parsed_rev

  [ -f "${TRUST_CG_DIR}/Cargo.lock" ] || { echo INVALID; return 1; }

  if ! repository_org="$(candidate_repository_org)"; then
    echo INVALID
    return 1
  fi
  if ! printf '%s\n' "$repository_org" | grep -Eq '^[A-Za-z0-9][A-Za-z0-9_.-]*$'; then
    echo INVALID
    return 1
  fi

  if ! parsed_rev="$(
    grep -E "^[[:space:]]*source = \"git\+[^\"]*/${repo}\\.git([?#\"]|$)" \
      "${TRUST_CG_DIR}/Cargo.lock" 2>/dev/null |
      sed -E "s|^[[:space:]]*source = \"git\\+https://github.com/([^/]+)/${repo}\\.git\\?rev=([0-9a-f]{40})#([0-9a-f]{40})\"[[:space:]]*\$|\\1 \\2 \\3|" |
      awk -v repository_org="$repository_org" '
        NF != 3 || $1 != repository_org || $2 != $3 { bad=1; next }
        { seen[$2]=1 }
        END {
          for (rev in seen) { count += 1; only = rev }
          if (!bad && count == 1) print only
          else exit 1
        }
      '
  )"; then
    echo INVALID
    return 1
  fi
  printf '%s\n' "$parsed_rev"
}

repo_head() {
  # repo_head <dir> -> HEAD sha (or "MISSING")
  if [ -d "$1/.git" ] || git -C "$1" rev-parse --git-dir >/dev/null 2>&1; then
    git -C "$1" rev-parse HEAD 2>/dev/null || echo "MISSING"
  else
    echo "MISSING"
  fi
}

REV_DRIFT=0
trust_cg_lock_attestation_child() {
  # A lock update necessarily creates a new trust-cg commit after the audited
  # source commit. Accept exactly one single-parent child whose sole tree change
  # is soundness_revs.lock; any source or second follow-up commit is drift.
  local dir="$1" pinned="$2" live="$3"
  local parent parent_fields changed
  git -C "$dir" cat-file -e "${pinned}^{commit}" >/dev/null 2>&1 || return 1
  parent_fields="$(git -C "$dir" rev-list --parents -n 1 "$live" 2>/dev/null)"
  [ "$(printf '%s\n' "$parent_fields" | awk '{print NF}')" -eq 2 ] || return 1
  parent="$(git -C "$dir" rev-parse "${live}^" 2>/dev/null)" || return 1
  [ "$parent" = "$pinned" ] || return 1
  changed="$(git -C "$dir" diff --name-only "$pinned" "$live" -- 2>/dev/null)"
  [ "$changed" = "soundness_revs.lock" ]
}

check_rev() {
  # check_rev <label> <dir> <lockkey>
  local label="$1" dir="$2" key="$3"
  local pinned live
  pinned="$(lock_get "$key")"
  live="$(repo_head "$dir")"
  if [ -z "$pinned" ]; then
    printf '  %s%-10s%s pinned=%s(none) live=%s\n' "$C_YEL" "$label" "$C_RST" "" "$live"
    REV_DRIFT=1
    return
  fi
  if [ "$pinned" = "$live" ]; then
    printf '  %s%-10s%s %s (matches lock)\n' "$C_GRN" "$label" "$C_RST" "$live"
  elif [ "$key" = "trust_cg_rev" ] && trust_cg_lock_attestation_child "$dir" "$pinned" "$live"; then
    printf '  %s%-10s%s %s (lock-only attestation child of audited %s)\n' \
      "$C_GRN" "$label" "$C_RST" "$live" "$pinned"
  else
    printf '  %s%-10s%s live=%s\n             pinned=%s %s(DRIFT)%s\n' \
      "$C_YEL" "$label" "$C_RST" "$live" "$pinned" "$C_YEL" "$C_RST"
    REV_DRIFT=1
  fi
}

# ----------------------------------------------------------------------------
# Gate runners. Each writes a temp log, inspects the REAL exit status (no pipe
# swallowing), and records PASS/FAIL. A nonzero rc, a compile error, or a
# missing target/file is always a FAIL — never a silent skip.
# ----------------------------------------------------------------------------

run_bounded() {
  # run_bounded <working-directory> <command> [args...]
  local dir="$1"
  shift
  "$TIMEOUT_RUNNER" --chdir "$dir" \
    "$SOUNDNESS_COMMAND_TIMEOUT_SECONDS" "$@"
}

clean_stock_aarch64_override_required() {
  [ "$(uname -s 2>/dev/null)" = "Darwin" ] && \
    [ "$(uname -m 2>/dev/null)" = "arm64" ]
}

clean_cargo_config_path() {
  local toml="$CLEAN_DIR/.cargo/config.toml"
  local legacy="$CLEAN_DIR/.cargo/config"
  if [ -f "$toml" ] && [ -f "$legacy" ]; then
    echo "soundness_check.sh: refusing ambiguous Clean Cargo config: both $toml and $legacy exist" >&2
    return 1
  fi
  if [ -f "$toml" ]; then
    printf '%s\n' "$toml"
  elif [ -f "$legacy" ]; then
    printf '%s\n' "$legacy"
  fi
}

clean_aarch64_config_rustflags() {
  local config
  config="$(clean_cargo_config_path)" || return 1
  [ -n "$config" ] || return 0
  awk '
    /^\[target\.aarch64-apple-darwin\]$/ { in_target=1; next }
    in_target && /^[[:space:]]*\[/ { in_target=0 }
    in_target && /^[[:space:]]*rustflags[[:space:]]*=/ {
      line=$0
      gsub(/[[:space:]]/, "", line)
      print line
    }
  ' "$config"
}

clean_build_config_rustflags() {
  local config
  config="$(clean_cargo_config_path)" || return 1
  [ -n "$config" ] || return 0
  awk '
    /^\[build\]$/ { in_build=1; next }
    in_build && /^[[:space:]]*\[/ { in_build=0 }
    in_build && /^[[:space:]]*rustflags[[:space:]]*=/ {
      line=$0
      gsub(/[[:space:]]/, "", line)
      print line
    }
  ' "$config"
}

validate_clean_stock_rustflags() {
  # Cargo concatenates target-specific config/env rustflag arrays; a matching
  # CARGO_TARGET_* override therefore cannot remove Clean's Trust-only `-Z`.
  # A global RUSTFLAGS value does replace the target stanza, but is sound here
  # only while the complete legacy stanza is the audited tune + opt-out pair.
  # Refuse Trust-only config drift instead of silently dropping a new flag.
  #
# A Clean config may already contain no Trust-only flag at all. That state
# needs no override: preserve Cargo's stock-compatible config exactly.
  local config
  local observed build_observed target_rows target_trust_rows build_trust_rows
  config="$(clean_cargo_config_path)" || return 1
  # A checkout with no repo-local Cargo config has no repo-local Trust-only
  # flag to neutralize and is already suitable for the stock lane.
  [ -n "$config" ] || return 0
  observed="$(clean_aarch64_config_rustflags)" || return 1
  build_observed="$(clean_build_config_rustflags)" || return 1
  target_rows="$(printf '%s\n' "$observed" | awk 'NF { count += 1 } END { print count + 0 }')"
  target_trust_rows="$(printf '%s\n' "$observed" | awk '/-Ztrust-verify/ { count += 1 } END { print count + 0 }')"
  build_trust_rows="$(printf '%s\n' "$build_observed" | awk '/-Ztrust-verify/ { count += 1 } END { print count + 0 }')"

  # A build-wide Trust opt-out would remain effective on hosts without an
  # overriding target stanza. It is never part of the audited exception.
  if [ "$build_trust_rows" -ne 0 ]; then
    echo "soundness_check.sh: refusing stock Clean cargo lane: unaudited build rustflags: $build_observed" >&2
    return 1
  fi

  # On Darwin/aarch64, Trust-only flags in other explicit target or rustdoc
  # sections are inert for these cargo build and named-integration-test
  # commands. Audit only the active target rustflags that global RUSTFLAGS
  # replaces; current Clean also carries an inactive Linux/aarch64 stanza. On
  # other hosts no replacement occurs, so Cargo retains their target policy
  # and fails closed if it is incompatible with the stock toolchain.
  if [ "$target_trust_rows" -eq 0 ]; then
    return 0
  fi

  if [ "$target_trust_rows" -ne 1 ] || [ "$target_rows" -ne 1 ] || \
     [ "$observed" != "$CLEAN_TRUST_AARCH64_CONFIG_RUSTFLAGS" ]; then
    echo "soundness_check.sh: refusing stock Clean cargo lane: unaudited aarch64 rustflags: $observed" >&2
    echo "  expected: $CLEAN_TRUST_AARCH64_CONFIG_RUSTFLAGS" >&2
    return 1
  fi
}

run_clean_cargo_bounded() {
  # run_clean_cargo_bounded <cargo-subcommand> [args...]
  #
  # On arm64 Darwin a global RUSTFLAGS value is required: real Cargo appends a
  # CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS value to the configured array,
  # leaving the stock-incompatible `-Z` in place. The validation above makes
  # this replacement exact and fail-closed. Other hosts do not select Clean's
  # Trust-only stanza and retain their existing target/build flags unchanged.
  validate_clean_stock_rustflags || return 2
  if clean_stock_aarch64_override_required && \
     [ "$(clean_aarch64_config_rustflags)" = "$CLEAN_TRUST_AARCH64_CONFIG_RUSTFLAGS" ]; then
    run_bounded "$CLEAN_DIR" \
      env CARGO_TARGET_DIR="$CLEAN_DIR/target" \
      RUSTFLAGS="$CLEAN_STOCK_AARCH64_RUSTFLAGS" \
      cargo "$@"
  else
    run_bounded "$CLEAN_DIR" \
      env CARGO_TARGET_DIR="$CLEAN_DIR/target" \
      cargo "$@"
  fi
}

validate_clean_check_summary() {
  # validate_clean_check_summary <captured-clean-check-log>
  #
  # A successful process status is insufficient evidence: Clean must report
  # exactly one non-empty, internally coherent declaration summary. Keep this
  # parser pure so the focused self-test exercises the production guard.
  local log="$1"
  if [ ! -f "$log" ]; then
    echo "invalid Clean summary: missing log: $log"
    return 1
  fi

  awk '
    /^Checked [0-9][0-9]* declarations( in [^[:space:]][^[:space:]]*)?$/ {
      checked_rows += 1
      declarations = $2 + 0
    }
    /^[[:space:]]*[0-9][0-9]* passed, [0-9][0-9]* failed$/ {
      result_rows += 1
      passed = $1 + 0
      failed = $3 + 0
    }
    END {
      if (checked_rows != 1) {
        printf "invalid Clean summary: expected exactly one Checked row, found %d\n",
          checked_rows
        exit 1
      }
      if (result_rows != 1) {
        printf "invalid Clean summary: expected exactly one result row, found %d\n",
          result_rows
        exit 1
      }
      if (declarations <= 0) {
        print "invalid Clean summary: declaration count must be greater than zero"
        exit 1
      }
      if (passed <= 0) {
        print "invalid Clean summary: passed count must be greater than zero"
        exit 1
      }
      if (failed != 0) {
        printf "invalid Clean summary: failed count must be zero, found %d\n", failed
        exit 1
      }
      if (declarations != passed + failed) {
        printf \
          "invalid Clean summary: declarations (%d) != passed + failed (%d)\n",
          declarations, passed + failed
        exit 1
      }
      printf "Checked %d declarations; %d passed, %d failed\n",
        declarations, passed, failed
    }
  ' "$log"
}

if [ -n "$MODE_VALIDATE_CLEAN_SUMMARY" ]; then
  validate_clean_check_summary "$MODE_VALIDATE_CLEAN_SUMMARY"
  exit $?
fi

LOGDIR="$(mktemp -d "${TMPDIR:-/tmp}/soundness_check.XXXXXX")"

run_cargo_gate() {
  # run_cargo_gate <repo_dir> <pkg> <test_target> [repo|clean-stock]
  local dir="$1" pkg="$2" target="$3"
  local cargo_lane="${4:-repo}"
  local log="${LOGDIR}/cargo_${pkg}_${target}.log"
  local rc summary
  case "$cargo_lane" in
    repo)
      run_bounded "$dir" \
        cargo test --locked -p "$pkg" --test "$target" >"$log" 2>&1
      ;;
    clean-stock)
      run_clean_cargo_bounded \
        test --locked -p "$pkg" --test "$target" >"$log" 2>&1
      ;;
    *)
      record "$target" FAIL "unknown cargo lane: $cargo_lane"
      return 1
      ;;
  esac
  rc=$?
  summary="$(grep -E '^test result:' "$log" | tail -1)"
  if [ "$rc" -ne 0 ]; then
    if [ "$rc" -eq 124 ]; then
      record "$target" FAIL \
        "TIMEOUT after ${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}s — see $log"
      return 1
    fi
    # Distinguish a build/compile error from a real test failure for clarity.
    if grep -qE '^error(\[|:)' "$log"; then
      record "$target" FAIL "BUILD/COMPILE ERROR (rc=$rc) — see $log"
    else
      record "$target" FAIL "${summary:-no 'test result' line (rc=$rc)} — see $log"
    fi
    return 1
  fi
  if [ -z "$summary" ]; then
    record "$target" FAIL "rc=0 but NO 'test result' line (vacuous?) — see $log"
    return 1
  fi
  # Defense in depth: rc==0 must coincide with an 'ok.' result and a non-zero
  # passed count (guards against a target that filtered everything out).
  if ! printf '%s' "$summary" | grep -q 'ok\.'; then
    record "$target" FAIL "$summary — see $log"
    return 1
  fi
  # Vacuity guard: a literal "0 passed" (not preceded by another digit, so
  # "10 passed" / "20 passed" are NOT matched). [^0-9] or start-of-string.
  if printf '%s' "$summary" | grep -qE '(^|[^0-9])0 passed'; then
    record "$target" FAIL "0 passed (vacuous) — $summary — see $log"
    return 1
  fi
  record "$target" PASS "$summary"
  return 0
}

build_clean_binary() {
  local log="${LOGDIR}/clean_release_build.log"
  local rc
  run_clean_cargo_bounded \
    build --locked --release -p clean --bin clean >"$log" 2>&1
  rc=$?
  if [ "$rc" -ne 0 ] || [ ! -x "$CLEAN_BIN" ]; then
    if [ "$rc" -eq 124 ]; then
      record "Clean release binary matches checkout" FAIL \
        "TIMEOUT after ${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}s — see $log"
    else
      record "Clean release binary matches checkout" FAIL \
        "build failed or binary missing (rc=$rc) — see $log"
    fi
    return 1
  fi
  record "Clean release binary matches checkout" PASS "$CLEAN_BIN"
  return 0
}

if [ "$MODE_SELF_TEST_CLEAN_CARGO_COMMAND" -eq 1 ]; then
  validate_clean_stock_rustflags || exit 1
  build_clean_binary
  run_cargo_gate "$CLEAN_DIR" clean-kernel micro_diversity_gate clean-stock
  [ "$FAIL_COUNT" -eq 0 ]
  exit $?
fi

run_clean_check() {
  # run_clean_check <lean_stem>
  local stem="$1"
  local file="${CLEAN_DIR}/proofs/${stem}.lean"
  local log="${LOGDIR}/clean_check_${stem}.log"
  local rc tail_line summary
  if [ ! -x "$CLEAN_BIN" ]; then
    record "clean-check ${stem}" FAIL "clean binary missing/not executable: $CLEAN_BIN"
    return 1
  fi
  if [ ! -f "$file" ]; then
    record "clean-check ${stem}" FAIL "missing .lean file: $file"
    return 1
  fi
  run_bounded "$CLEAN_DIR" "$CLEAN_BIN" check "$file" >"$log" 2>&1
  rc=$?
  tail_line="$(grep -E 'passed|failed|Checked' "$log" | tail -1)"
  if [ "$rc" -ne 0 ]; then
    if [ "$rc" -eq 124 ]; then
      record "clean-check ${stem}" FAIL \
        "TIMEOUT after ${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}s — see $log"
    else
      record "clean-check ${stem}" FAIL "${tail_line:-rc=$rc} — see $log"
    fi
    return 1
  fi
  if ! summary="$(validate_clean_check_summary "$log")"; then
    record "clean-check ${stem}" FAIL "$summary — see $log"
    return 1
  fi
  record "clean-check ${stem}" PASS "$summary"
  return 0
}

run_lean_formal_gate() {
  # run_lean_formal_gate : build the Lean forward-sim (ENC-1) and pin sorry/axiom counts.
  #   1. `lake build` must be green (a build/compile error is a FAIL, never a skip).
  #   2. classified-sorry count == BASELINE_LEAN_SORRY (growth => fail closed).
  #   3. explicit top-level axiom count == BASELINE_LEAN_AXIOM (a NEW axiom => fail closed).
  local dir="$LEAN_FORMAL_DIR"
  local log="${LOGDIR}/lean_formal_build.log"
  local rc sc ac
  if ! command -v lake >/dev/null 2>&1; then
    record "formal/lean lake build" FAIL "lake not on PATH (need elan: export PATH=\$HOME/.elan/bin:\$PATH)"
    return 1
  fi
  if [ ! -f "${dir}/lakefile.lean" ]; then
    record "formal/lean lake build" FAIL "missing lakefile: ${dir}/lakefile.lean"
    return 1
  fi
  run_bounded "$dir" lake build >"$log" 2>&1
  rc=$?
  if [ "$rc" -ne 0 ]; then
    if [ "$rc" -eq 124 ]; then
      record "formal/lean lake build" FAIL \
        "TIMEOUT after ${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}s — see $log"
    else
      record "formal/lean lake build" FAIL \
        "lake build rc=$rc (Lean forward-sim did not build) — see $log"
    fi
    return 1
  fi
  record "formal/lean lake build" PASS "green (compile_refines capstone builds)"

  # Sorry ratchet (pinned EXACTLY at baseline).
  sc="$(grep -rEc '^[[:space:]]*sorry\b' "${dir}/Trust" 2>/dev/null | awk -F: '{s+=$2} END{print s+0}')"
  if [ "$sc" -ne "$BASELINE_LEAN_SORRY" ]; then
    record "formal/lean sorry-count == ${BASELINE_LEAN_SORRY}" FAIL \
      "found ${sc} (baseline ${BASELINE_LEAN_SORRY}); growth fails closed — if a sorry was discharged, lower BASELINE_LEAN_SORRY"
  else
    record "formal/lean sorry-count == ${BASELINE_LEAN_SORRY}" PASS "${sc} classified sorries (pinned)"
  fi

  # Axiom ratchet (exactly the 4 explicit trusted axioms).
  ac="$(grep -rc '^axiom ' "${dir}/Trust" 2>/dev/null | awk -F: '{s+=$2} END{print s+0}')"
  if [ "$ac" -ne "$BASELINE_LEAN_AXIOM" ]; then
    record "formal/lean axiom-count == ${BASELINE_LEAN_AXIOM}" FAIL \
      "found ${ac} top-level axioms (baseline ${BASELINE_LEAN_AXIOM}); a new axiom fails closed"
  else
    record "formal/lean axiom-count == ${BASELINE_LEAN_AXIOM}" PASS "${ac} explicit trusted axioms (pinned)"
  fi
}

# ----------------------------------------------------------------------------
# Banner + preflight.
# ----------------------------------------------------------------------------
printf '%s%s%s\n' "$C_BLD" "==================== LOCAL SOUNDNESS META-GATE (#4) =====================" "$C_RST"
echo "trust-cg : $TRUST_CG_DIR"
echo "clean    : $CLEAN_DIR"
echo "ay       : $AY_DIR"
echo "lock     : $LOCK_FILE"
echo "logs     : $LOGDIR"
echo "timeout  : ${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}s per Cargo/Clean/Lake command"
echo "mode     : $( [ "$MODE_PINNED" -eq 1 ] && echo 'PINNED (rev drift = FAIL)' || echo 'warn-on-drift' )$( [ "$MODE_UPDATE" -eq 1 ] && echo ' + UPDATE' )"
echo "NOTE     : this is a LOCAL meta-gate, NOT GitHub CI."

# Preflight: tooling must exist, or this whole gate is vacuous.
section "Preflight"
PREFLIGHT_OK=1
if command -v cargo >/dev/null 2>&1; then
  record "preflight: cargo present" PASS "$(command -v cargo)"
else
  record "preflight: cargo present" FAIL "cargo not on PATH"
  PREFLIGHT_OK=0
fi
if [ -x "$TIMEOUT_RUNNER" ]; then
  record "preflight: timeout runner present" PASS "$TIMEOUT_RUNNER"
else
  record "preflight: timeout runner present" FAIL \
    "missing/not executable: $TIMEOUT_RUNNER"
  PREFLIGHT_OK=0
fi
if printf '%s\n' "$SOUNDNESS_COMMAND_TIMEOUT_SECONDS" |
   grep -Eq '^[0-9]+([.][0-9]+)?$' &&
   awk -v timeout="$SOUNDNESS_COMMAND_TIMEOUT_SECONDS" \
     'BEGIN { exit !(timeout > 0) }'; then
  record "preflight: positive command timeout" PASS \
    "${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}s"
else
  record "preflight: positive command timeout" FAIL \
    "invalid SOUNDNESS_COMMAND_TIMEOUT_SECONDS=${SOUNDNESS_COMMAND_TIMEOUT_SECONDS}"
  PREFLIGHT_OK=0
fi
rustc_version="$(cd "$TRUST_CG_DIR" 2>/dev/null && rustc -V 2>/dev/null || true)"
cargo_version="$(cd "$TRUST_CG_DIR" 2>/dev/null && cargo -V 2>/dev/null || true)"
if printf '%s\n' "$rustc_version" | grep -q "^${EXPECTED_RUSTC_VERSION} "; then
  record "preflight: pinned rustc" PASS "$rustc_version"
else
  record "preflight: pinned rustc" FAIL "expected ${EXPECTED_RUSTC_VERSION}, got ${rustc_version:-missing}"
  PREFLIGHT_OK=0
fi
if printf '%s\n' "$cargo_version" | grep -q "^${EXPECTED_CARGO_VERSION} "; then
  record "preflight: pinned cargo" PASS "$cargo_version"
else
  record "preflight: pinned cargo" FAIL "expected ${EXPECTED_CARGO_VERSION}, got ${cargo_version:-missing}"
  PREFLIGHT_OK=0
fi
if [ -d "$TRUST_CG_DIR" ]; then
  record "preflight: trust-cg dir present" PASS "$TRUST_CG_DIR"
else
  record "preflight: trust-cg dir present" FAIL "missing: $TRUST_CG_DIR"
  PREFLIGHT_OK=0
fi
if [ -d "$CLEAN_DIR" ]; then
  record "preflight: clean dir present" PASS "$CLEAN_DIR"
  clean_rustc_version="$(cd "$CLEAN_DIR" && rustc -V 2>/dev/null || true)"
  clean_cargo_version="$(cd "$CLEAN_DIR" && cargo -V 2>/dev/null || true)"
  if printf '%s\n' "$clean_rustc_version" | grep -q "^${EXPECTED_RUSTC_VERSION} "; then
    record "preflight: Clean rustc" PASS "$clean_rustc_version"
  else
    record "preflight: Clean rustc" FAIL \
      "expected ${EXPECTED_RUSTC_VERSION}, got ${clean_rustc_version:-missing}"
    PREFLIGHT_OK=0
  fi
  if printf '%s\n' "$clean_cargo_version" | grep -q "^${EXPECTED_CARGO_VERSION} "; then
    record "preflight: Clean cargo" PASS "$clean_cargo_version"
  else
    record "preflight: Clean cargo" FAIL \
      "expected ${EXPECTED_CARGO_VERSION}, got ${clean_cargo_version:-missing}"
    PREFLIGHT_OK=0
  fi
else
  record "preflight: clean dir present" FAIL "missing: $CLEAN_DIR"
  PREFLIGHT_OK=0
fi
if [ -d "$AY_DIR" ]; then
  record "preflight: ay dir present" PASS "$AY_DIR"
else
  record "preflight: ay dir present" FAIL "missing: $AY_DIR"
  PREFLIGHT_OK=0
fi
for key in trust_cg_rev clean_rev ay_rev; do
  count="$(lock_key_count "$key")"
  value="$(lock_get "$key")"
  if [ "$count" -eq 1 ] && printf '%s\n' "$value" | grep -Eq '^[0-9a-f]{40}$'; then
    record "preflight: lock key ${key}" PASS "$value"
  else
    record "preflight: lock key ${key}" FAIL \
      "expected exactly one full Git SHA, found count=$count value=${value:-missing}"
    PREFLIGHT_OK=0
  fi
done
CANDIDATE_CLEAN_REV="$(candidate_dependency_rev clean)"
CANDIDATE_AY_REV="$(candidate_dependency_rev ay)"
for row in "Clean:$CANDIDATE_CLEAN_REV" "AY:$CANDIDATE_AY_REV"; do
  label="${row%%:*}"
  value="${row#*:}"
  if printf '%s\n' "$value" | grep -Eq '^[0-9a-f]{40}$'; then
    record "preflight: candidate ${label} revision" PASS "$value"
  else
    record "preflight: candidate ${label} revision" FAIL \
      "Cargo.lock must contain one coherent exact ${label} Git revision"
    PREFLIGHT_OK=0
  fi
done

# A lock update records commit identities, not uncommitted bytes. Refuse to
# associate a green run with unrelated HEADs when any candidate worktree is
# dirty. Ordinary non-update runs may still be used while iterating.
START_TRUST_HEAD=""
START_CLEAN_HEAD=""
START_AY_HEAD=""
if [ "$MODE_UPDATE" -eq 1 ] || [ "$MODE_PINNED" -eq 1 ]; then
  clean_mode="$( [ "$MODE_UPDATE" -eq 1 ] && echo update || echo pinned )"
  for row in "trust-cg:$TRUST_CG_DIR" "clean:$CLEAN_DIR" "ay:$AY_DIR"; do
    label="${row%%:*}"
    dir="${row#*:}"
    if ! git -C "$dir" rev-parse --git-dir >/dev/null 2>&1; then
      record "${clean_mode}: ${label} worktree clean" FAIL "not a Git worktree: $dir"
      PREFLIGHT_OK=0
    elif [ -n "$(git -C "$dir" status --porcelain)" ]; then
      record "${clean_mode}: ${label} worktree clean" FAIL "uncommitted files present; refusing to attest HEAD"
      PREFLIGHT_OK=0
    else
      record "${clean_mode}: ${label} worktree clean" PASS "clean HEAD $(repo_head "$dir")"
    fi
  done
  START_TRUST_HEAD="$(repo_head "$TRUST_CG_DIR")"
  START_CLEAN_HEAD="$(repo_head "$CLEAN_DIR")"
  START_AY_HEAD="$(repo_head "$AY_DIR")"
  if [ "$START_CLEAN_HEAD" = "$CANDIDATE_CLEAN_REV" ]; then
    record "${clean_mode}: Clean matches candidate dependency" PASS "$START_CLEAN_HEAD"
  else
    record "${clean_mode}: Clean matches candidate dependency" FAIL \
      "checkout=$START_CLEAN_HEAD candidate=$CANDIDATE_CLEAN_REV"
    PREFLIGHT_OK=0
  fi
  if [ "$START_AY_HEAD" = "$CANDIDATE_AY_REV" ]; then
    record "${clean_mode}: AY matches candidate dependency" PASS "$START_AY_HEAD"
  else
    record "${clean_mode}: AY matches candidate dependency" FAIL \
      "checkout=$START_AY_HEAD candidate=$CANDIDATE_AY_REV"
    PREFLIGHT_OK=0
  fi
fi

# ----------------------------------------------------------------------------
# Pinned revisions.
# ----------------------------------------------------------------------------
section "Pinned revisions (soundness_revs.lock)"
check_rev "trust-cg" "$TRUST_CG_DIR" trust_cg_rev
check_rev "clean"    "$CLEAN_DIR"    clean_rev
check_rev "ay"       "$AY_DIR"       ay_rev
if [ "$REV_DRIFT" -eq 1 ]; then
  if [ "$MODE_PINNED" -eq 1 ]; then
    echo "  ${C_RED}rev drift under --pinned: this is a FAIL.${C_RST}"
    record "pinned-revs match lock" FAIL "HEAD != lock under --pinned"
  else
    echo "  ${C_YEL}rev drift (warn-only; pass --pinned to make this a FAIL).${C_RST}"
  fi
else
  echo "  ${C_GRN}all repo HEADs match soundness_revs.lock.${C_RST}"
fi

# ----------------------------------------------------------------------------
# Run the constellation. If preflight already failed, we STILL attempt every
# gate (so the summary is complete), but the overall result will be FAIL.
# ----------------------------------------------------------------------------
section "trust-cg gate test targets"
for g in "${TRUST_CG_GATES[@]}"; do
  run_cargo_gate "$TRUST_CG_DIR" trust-cg-verify "$g"
done

section "Clean checkout: clean-check (B-def / LRAT-checker proofs)"
build_clean_binary
for f in "${CLEAN_LEAN[@]}"; do
  run_clean_check "$f"
done

section "Clean checkout: kernel diversity gate"
run_cargo_gate "$CLEAN_DIR" clean-kernel micro_diversity_gate clean-stock

section "formal/lean forward-sim (ENC-1: lake build + sorry/axiom ratchet)"
run_lean_formal_gate

# ENC-4: the golden-vector binding of the Lean byte encoder to the REAL backend encoder.
# TWO legs anchored to ONE shared set of bytes (formal/lean/Trust/Model/EncoderGolden.lean):
#   * Lean leg  — `by decide` in EncoderGolden.lean pins the MODEL's `encode` to those bytes;
#                 already checked by `run_lean_formal_gate` above (lake build compiles it).
#   * Rust leg  — this cargo test parses that same file and asserts the real `encode.rs` emits
#                 byte-for-byte the identical lists (and that the golden key-set covers the bound
#                 matrix). A drift on EITHER encoder — or a hand-edited golden — fails a gate.
section "ENC-4: Lean<->backend encoder golden-vector binding (Rust leg)"
run_cargo_gate "$TRUST_CG_DIR" trust-cg-codegen lean_encode_golden_binding

# Pinned and update modes attest committed source, so detect any checkout
# mutation or commit movement that occurred while the long gate was running.
if [ "$MODE_UPDATE" -eq 1 ] || [ "$MODE_PINNED" -eq 1 ]; then
  section "Post-run revision and cleanliness check"
  for row in \
    "trust-cg:$TRUST_CG_DIR:$START_TRUST_HEAD" \
    "clean:$CLEAN_DIR:$START_CLEAN_HEAD" \
    "ay:$AY_DIR:$START_AY_HEAD"; do
    label="${row%%:*}"
    remainder="${row#*:}"
    expected="${remainder##*:}"
    dir="${remainder%:*}"
    live="$(repo_head "$dir")"
    if [ "$live" != "$expected" ]; then
      record "post-run: ${label} HEAD unchanged" FAIL \
        "started $expected, ended $live"
    else
      record "post-run: ${label} HEAD unchanged" PASS "$live"
    fi
    if [ -n "$(git -C "$dir" status --porcelain 2>/dev/null)" ]; then
      record "post-run: ${label} worktree clean" FAIL "files changed during gate"
    else
      record "post-run: ${label} worktree clean" PASS "clean"
    fi
  done
fi

# ----------------------------------------------------------------------------
# Summary.
# ----------------------------------------------------------------------------
section "SUMMARY"
TOTAL=$((PASS_COUNT + FAIL_COUNT))
for i in "${!GATE_NAMES[@]}"; do
  st="${GATE_STATUS[$i]}"
  if [ "$st" = "PASS" ]; then
    printf '  %s[PASS]%s %s\n' "$C_GRN" "$C_RST" "${GATE_NAMES[$i]}"
  else
    printf '  %s[FAIL]%s %-46s %s\n' "$C_RED" "$C_RST" "${GATE_NAMES[$i]}" "${GATE_DETAIL[$i]}"
  fi
done
hr
printf 'gates: %d total  %s%d passed%s  %s%d failed%s\n' \
  "$TOTAL" "$C_GRN" "$PASS_COUNT" "$C_RST" \
  "$( [ "$FAIL_COUNT" -gt 0 ] && printf '%s' "$C_RED" || printf '%s' "$C_GRN" )" \
  "$FAIL_COUNT" "$C_RST"

OVERALL_RC=0
if [ "$FAIL_COUNT" -gt 0 ] || [ "$PREFLIGHT_OK" -ne 1 ]; then
  OVERALL_RC=1
fi
if [ "$MODE_PINNED" -eq 1 ] && [ "$REV_DRIFT" -eq 1 ]; then
  OVERALL_RC=1
fi

if [ "$OVERALL_RC" -eq 0 ]; then
  printf '%s%s ALL SOUNDNESS GATES GREEN.%s\n' "$C_GRN" "$C_BLD" "$C_RST"
else
  printf '%s%s SOUNDNESS GATE FAILED — see [FAIL] rows above. Logs in %s%s\n' "$C_RED" "$C_BLD" "$LOGDIR" "$C_RST"
fi

# ----------------------------------------------------------------------------
# --update : re-pin the lock to current HEADs, ONLY after a fully green run.
# ----------------------------------------------------------------------------
if [ "$MODE_UPDATE" -eq 1 ]; then
  section "--update : re-pin soundness_revs.lock"
  if [ "$OVERALL_RC" -ne 0 ]; then
    echo "  ${C_RED}refusing to re-pin: the run was not green. Fix the reds first.${C_RST}"
    OVERALL_RC=1
  else
    new_trust="$(repo_head "$TRUST_CG_DIR")"
    new_clean="$(repo_head "$CLEAN_DIR")"
    new_ay="$(repo_head "$AY_DIR")"
    if [ "$new_trust" = "MISSING" ] || [ "$new_clean" = "MISSING" ] || [ "$new_ay" = "MISSING" ]; then
      echo "  ${C_RED}refusing to re-pin: could not read a repo HEAD.${C_RST}"
      OVERALL_RC=1
    else
      # Rewrite the three rev lines and migrate the exact legacy success
      # comment; preserve every other comment and the lock structure.
      tmp="${LOCK_FILE}.tmp.$$"
      legacy_green_comment="#  passed with no tolerated red in the v0.1.0 gate)."
      pinned_debt_comment="#  passed with only the explicitly pinned RED inventory debt)."
      if awk -v t="$new_trust" -v c="$new_clean" -v a="$new_ay" \
        -v old="$legacy_green_comment" -v new="$pinned_debt_comment" '
        /^[[:space:]]*trust_cg_rev[[:space:]]*=/ { print "trust_cg_rev = " t; next }
        /^[[:space:]]*clean_rev[[:space:]]*=/    { print "clean_rev = " c; next }
        /^[[:space:]]*ay_rev[[:space:]]*=/       { print "ay_rev = " a; next }
        $0 == old                                      { print new; next }
        { print }
      ' "$LOCK_FILE" > "$tmp" && mv "$tmp" "$LOCK_FILE" && \
        [ "$(lock_get trust_cg_rev)" = "$new_trust" ] && \
        [ "$(lock_get clean_rev)" = "$new_clean" ] && \
        [ "$(lock_get ay_rev)" = "$new_ay" ] && \
        ! grep -Fqx "$legacy_green_comment" "$LOCK_FILE" && \
        [ "$(grep -Fxc "$pinned_debt_comment" "$LOCK_FILE")" -eq 1 ]; then
        echo "  ${C_GRN}re-pinned:${C_RST}"
        echo "    trust_cg_rev = $new_trust"
        echo "    clean_rev    = $new_clean"
        echo "    ay_rev       = $new_ay"
        echo "  (review, then commit soundness_revs.lock as the sole changed file)"
      else
        rm -f "$tmp"
        echo "  ${C_RED}refusing to report success: lock rewrite or validation failed.${C_RST}"
        OVERALL_RC=1
      fi
    fi
  fi
fi

exit "$OVERALL_RC"
