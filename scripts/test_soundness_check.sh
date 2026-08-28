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

# The main workspace, rustc backend, and fuzz crate resolve dependencies as
# three independent Cargo roots.  A root-only check lets either standalone
# lock silently retain an older TrustIR/Clean/AY universe.  Exercise the
# toolchain-free preflight against a coherent copy, then split one standalone
# lock at a time and require a named refusal.
LOCK_FIXTURE="${TMP}/dependency-locks"
mkdir -p \
  "$LOCK_FIXTURE/crates/rustc-codegen-trust-cg" \
  "$LOCK_FIXTURE/fuzz"
cp "$ROOT/Cargo.toml" "$LOCK_FIXTURE/Cargo.toml"
cp "$ROOT/Cargo.lock" "$LOCK_FIXTURE/Cargo.lock"
cp "$ROOT/crates/rustc-codegen-trust-cg/Cargo.lock" \
  "$LOCK_FIXTURE/crates/rustc-codegen-trust-cg/Cargo.lock"
cp "$ROOT/fuzz/Cargo.lock" "$LOCK_FIXTURE/fuzz/Cargo.lock"

dependency_output=""
if dependency_output="$(
  TRUST_CG_DIR="$LOCK_FIXTURE" \
    "$SOUNDNESS_CHECK" --validate-dependency-locks 2>&1
)" && \
   [ "$(printf '%s\n' "$dependency_output" | grep -Ec '^trust_ir_rev=[0-9a-f]{40}$')" -eq 1 ] && \
   [ "$(printf '%s\n' "$dependency_output" | grep -Ec '^clean_rev=[0-9a-f]{40}$')" -eq 1 ] && \
   [ "$(printf '%s\n' "$dependency_output" | grep -Ec '^ay_rev=[0-9a-f]{40}$')" -eq 1 ]; then
  printf 'ok - independent dependency locks agree on one first-party graph\n'
  PASS=$((PASS + 1))
else
  printf 'not ok - coherent independent dependency locks (output: %s)\n' \
    "${dependency_output:-<empty>}" >&2
  FAIL=$((FAIL + 1))
fi

replace_sha() {
  local file="$1" old="$2" new="$3" tmp="${1}.tmp.$$"
  sed "s/${old}/${new}/g" "$file" >"$tmp" && mv "$tmp" "$file"
}

trust_ir_rev="$(printf '%s\n' "$dependency_output" | sed -n 's/^trust_ir_rev=//p')"
if [ "${#trust_ir_rev}" -eq 40 ]; then
  split_trust_ir_rev="1111111111111111111111111111111111111111"
  replace_sha \
    "$LOCK_FIXTURE/fuzz/Cargo.lock" \
    "$trust_ir_rev" \
    "$split_trust_ir_rev"
  if split_output="$(
    TRUST_CG_DIR="$LOCK_FIXTURE" \
      "$SOUNDNESS_CHECK" --validate-dependency-locks 2>&1
  )"; then
    printf 'not ok - split fuzz TrustIR lock unexpectedly passed: %s\n' "$split_output" >&2
    FAIL=$((FAIL + 1))
  elif printf '%s\n' "$split_output" | grep -Fq 'split first-party trust-ir revisions' && \
       printf '%s\n' "$split_output" | grep -Fq 'fuzz/Cargo.lock'; then
    printf 'ok - split fuzz TrustIR lock fails closed and names the divergent root\n'
    PASS=$((PASS + 1))
  else
    printf 'not ok - split fuzz TrustIR lock diagnostic: %s\n' "$split_output" >&2
    FAIL=$((FAIL + 1))
  fi
  replace_sha \
    "$LOCK_FIXTURE/fuzz/Cargo.lock" \
    "$split_trust_ir_rev" \
    "$trust_ir_rev"
else
  printf 'not ok - coherent dependency output did not yield a TrustIR revision\n' >&2
  FAIL=$((FAIL + 1))
fi

ay_rev="$(printf '%s\n' "$dependency_output" | sed -n 's/^ay_rev=//p')"
if [ "${#ay_rev}" -eq 40 ]; then
  split_ay_rev="2222222222222222222222222222222222222222"
  replace_sha \
    "$LOCK_FIXTURE/crates/rustc-codegen-trust-cg/Cargo.lock" \
    "$ay_rev" \
    "$split_ay_rev"
  if split_output="$(
    TRUST_CG_DIR="$LOCK_FIXTURE" \
      "$SOUNDNESS_CHECK" --validate-dependency-locks 2>&1
  )"; then
    printf 'not ok - split rustc AY lock unexpectedly passed: %s\n' "$split_output" >&2
    FAIL=$((FAIL + 1))
  elif printf '%s\n' "$split_output" | grep -Fq 'split first-party ay revisions' && \
       printf '%s\n' "$split_output" | grep -Fq 'crates/rustc-codegen-trust-cg/Cargo.lock'; then
    printf 'ok - split rustc AY lock fails closed and names the divergent root\n'
    PASS=$((PASS + 1))
  else
    printf 'not ok - split rustc AY lock diagnostic: %s\n' "$split_output" >&2
    FAIL=$((FAIL + 1))
  fi
else
  printf 'not ok - coherent dependency output did not yield an AY revision\n' >&2
  FAIL=$((FAIL + 1))
fi

# Exercise the same high-level Clean build and micro-diversity gate runners the
# constellation uses. The fake Cargo process makes the wrapper's effective
# environment and argv observable and creates the release binary expected by
# the build guard. Any missing/narrowed override, leaked Trust-only flag, or
# command drift fails this regression.
#
# KEYED ON THE HOST TRIPLE, never on uname. The production lane selects the
# `[target.<triple>]` stanza by asking `rustc -vV` for the host triple
# (soundness_check.sh's clean_host_triple), so a fixture hardcoded to
# aarch64-apple-darwin exercises the flag-replacement path on exactly one
# machine and is inert everywhere else — the same Darwin-only assumption
# 7a8ea174 removed from the production script. Key the fixture on this host so
# the replacement is actually tested wherever the gate runs.
HOST_TRIPLE="$(rustc -vV 2>/dev/null | awk '/^host:/ { print $2; exit }')"
if [ -z "${HOST_TRIPLE}" ]; then
  printf 'not ok - no rustc on PATH: the Clean stock-cargo lane cannot be tested\n' >&2
  printf '%d passed, %d failed\n' "$PASS" "$((FAIL + 1))"
  exit 1
fi
# Cargo's environment spelling of the same triple, e.g.
# aarch64-unknown-linux-gnu -> CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUSTFLAGS.
HOST_TRIPLE_ENV="CARGO_TARGET_$(printf '%s' "$HOST_TRIPLE" | tr 'a-z-' 'A-Z_')_RUSTFLAGS"

FAKE_CARGO_DIR="${TMP}/fake-bin"
FAKE_CARGO="${FAKE_CARGO_DIR}/cargo"
FAKE_CLEAN="${TMP}/fake-clean"
FAKE_HOME="${TMP}/fake-home"
CARGO_AUDIT="${TMP}/clean-cargo.audit"
mkdir -p "$FAKE_CARGO_DIR" "$FAKE_CLEAN/.cargo" "${FAKE_HOME}/.cargo/bin"
# soundness_check.sh prepends "$HOME/.cargo/bin" to PATH and then asks rustc for
# the host triple. This sandbox supplies a fake HOME and a PATH carrying no
# toolchain, so without a resolvable rustc the production script refuses BEFORE
# running cargo at all and the audit log is never written — a red that reads as
# a flag-isolation failure but is really a missing compiler. Expose the real
# compiler BINARY (not the rustup shim, which needs the real HOME) and nothing
# else, so `cargo` still resolves to the fake below.
ln -sf "$(rustc --print sysroot)/bin/rustc" "${FAKE_HOME}/.cargo/bin/rustc"
printf '%s\n' \
  "[target.${HOST_TRIPLE}]" \
  'rustflags = ["-C", "target-cpu=native", "-Ztrust-verify=off"]' \
  >"$FAKE_CLEAN/.cargo/config.toml"
sed "s/@HOST_TRIPLE_ENV@/${HOST_TRIPLE_ENV}/g" >"$FAKE_CARGO" <<'FAKE_CARGO_SCRIPT'
#!/usr/bin/env bash
set -u
{
  printf 'target_flags=%s\n' "${@HOST_TRIPLE_ENV@-<unset>}"
  printf 'rustflags=%s\n' "${RUSTFLAGS-<unset>}"
  printf 'encoded_rustflags=%s\n' "${CARGO_ENCODED_RUSTFLAGS-<unset>}"
  printf 'target_dir=%s\n' "${CARGO_TARGET_DIR-<unset>}"
  printf 'args='
  printf '<%s>' "$@"
  printf '\n'
} >>"$SOUNDNESS_CARGO_AUDIT_LOG"
case "${1-}" in
  build)
    mkdir -p "${CARGO_TARGET_DIR}/release"
    : >"${CARGO_TARGET_DIR}/release/clean"
    chmod +x "${CARGO_TARGET_DIR}/release/clean"
    ;;
  test)
    printf 'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out\n'
    ;;
  *) exit 91 ;;
esac
FAKE_CARGO_SCRIPT
chmod +x "$FAKE_CARGO"

# The audited stanza is this host's now, so the wrapper must REPLACE it with the
# stock tune-only value on every host: the expectation is no longer conditional.
EXPECTED_CLEAN_WRAPPER_RUSTFLAGS='-C target-cpu=native'

if output="$(
  env \
    CLEAN_DIR="$FAKE_CLEAN" \
    SOUNDNESS_CARGO_AUDIT_LOG="$CARGO_AUDIT" \
    HOME="$FAKE_HOME" \
    PATH="${FAKE_CARGO_DIR}:/usr/bin:/bin" \
    "${HOST_TRIPLE_ENV}=-Ztrust-verify=poison" \
    CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS='-Ztrust-verify=poison' \
    RUSTFLAGS='-Ztrust-verify=poison' \
    CARGO_ENCODED_RUSTFLAGS='poison' \
    "$SOUNDNESS_CHECK" --self-test-clean-cargo-command 2>&1
)" && \
   [ "$(grep -c '^target_flags=<unset>$' "$CARGO_AUDIT")" -eq 2 ] && \
   [ "$(grep -c "^rustflags=${EXPECTED_CLEAN_WRAPPER_RUSTFLAGS}$" "$CARGO_AUDIT")" -eq 2 ] && \
   [ "$(grep -c '^encoded_rustflags=<unset>$' "$CARGO_AUDIT")" -eq 2 ] && \
   [ "$(grep -c "^target_dir=${FAKE_CLEAN}/target$" "$CARGO_AUDIT")" -eq 2 ] && \
   [ "$(grep -c '^args=<build><--locked><--release><-p><clean><--bin><clean>$' "$CARGO_AUDIT")" -eq 1 ] && \
   [ "$(grep -c '^args=<test><--locked><-p><clean-kernel><--test><micro_diversity_gate>$' "$CARGO_AUDIT")" -eq 1 ] && \
   ! grep -q -- '-Ztrust-verify' "$CARGO_AUDIT"; then
  printf 'ok - Clean stock Cargo command isolates Trust-only flags\n'
  PASS=$((PASS + 1))
else
  printf 'not ok - Clean stock Cargo command isolation (output: %s; audit: %s)\n' \
    "${output:-<empty>}" "$(tr '\n' ' ' <"$CARGO_AUDIT" 2>/dev/null || true)" >&2
  FAIL=$((FAIL + 1))
fi

# A real Cargo fixture proves the distinction the command-capture test cannot:
# Cargo APPENDS a target-specific environment value, while global RUSTFLAGS
# replaces the matching config stanza. The fixture carries Clean's exact
# stock-incompatible target flags. Both production call paths must compile on
# stock 1.97.1, which is possible only if the wrapper truly removed the `-Z`.
REAL_CLEAN="${TMP}/real-clean"
mkdir -p \
  "$REAL_CLEAN/.cargo" \
  "$REAL_CLEAN/clean/src" \
  "$REAL_CLEAN/clean-kernel/src" \
  "$REAL_CLEAN/clean-kernel/tests"
printf '%s\n' \
  '[target.aarch64-apple-darwin]' \
  'rustflags = ["-C", "target-cpu=native", "-Ztrust-verify=off"]' \
  'rustdocflags = ["-Ztrust-verify=off"]' \
  '' \
  '[target.aarch64-unknown-linux-gnu]' \
  'rustflags = ["-C", "target-cpu=native", "-Ztrust-verify=off"]' \
  'rustdocflags = ["-Ztrust-verify=off"]' \
  >"$REAL_CLEAN/.cargo/config.toml"
printf '%s\n' \
  '[workspace]' \
  'resolver = "2"' \
  'members = ["clean", "clean-kernel"]' \
  >"$REAL_CLEAN/Cargo.toml"
printf '%s\n' \
  'version = 4' \
  '' \
  '[[package]]' \
  'name = "clean"' \
  'version = "0.0.0"' \
  '' \
  '[[package]]' \
  'name = "clean-kernel"' \
  'version = "0.0.0"' \
  >"$REAL_CLEAN/Cargo.lock"
printf '%s\n' \
  '[package]' \
  'name = "clean"' \
  'version = "0.0.0"' \
  'edition = "2021"' \
  >"$REAL_CLEAN/clean/Cargo.toml"
printf '%s\n' 'fn main() {}' >"$REAL_CLEAN/clean/src/main.rs"
printf '%s\n' \
  '[package]' \
  'name = "clean-kernel"' \
  'version = "0.0.0"' \
  'edition = "2021"' \
  >"$REAL_CLEAN/clean-kernel/Cargo.toml"
printf '%s\n' 'pub fn diversity_witness() -> bool { true }' \
  >"$REAL_CLEAN/clean-kernel/src/lib.rs"
printf '%s\n' \
  '#[test]' \
  'fn micro_diversity_is_nonvacuous() {' \
  '    assert!(clean_kernel::diversity_witness());' \
  '}' \
  >"$REAL_CLEAN/clean-kernel/tests/micro_diversity_gate.rs"

if output="$(
  CLEAN_DIR="$REAL_CLEAN" \
  CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS='-Ztrust-verify=poison' \
  RUSTFLAGS='-Ztrust-verify=poison' \
  CARGO_ENCODED_RUSTFLAGS='poison' \
    "$SOUNDNESS_CHECK" --self-test-clean-cargo-command 2>&1
)" && [ -x "$REAL_CLEAN/target/release/clean" ]; then
  printf 'ok - real Cargo replaces the audited Clean Trust-only flag\n'
  PASS=$((PASS + 1))
else
  printf 'not ok - real Cargo Clean flag replacement (output: %s)\n' \
    "${output:-<empty>}" >&2
  FAIL=$((FAIL + 1))
fi

# An already-stock Clean config carries no Trust-only target flag. This state
# must run unchanged: the wrapper should not require the legacy
# stanza and should not inject a replacement RUSTFLAGS value.
printf '%s\n' \
  '[build]' \
  'rustflags = ["-C", "target-cpu=native"]' \
  >"$REAL_CLEAN/.cargo/config.toml"
if output="$(
  CLEAN_DIR="$REAL_CLEAN" \
  CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS='-Ztrust-verify=poison' \
  RUSTFLAGS='-Ztrust-verify=poison' \
  CARGO_ENCODED_RUSTFLAGS='poison' \
    "$SOUNDNESS_CHECK" --self-test-clean-cargo-command 2>&1
)" && [ -x "$REAL_CLEAN/target/release/clean" ]; then
  printf 'ok - already-stock Clean config needs no legacy target stanza\n'
  PASS=$((PASS + 1))
else
  printf 'not ok - already-stock Clean config (output: %s)\n' \
    "${output:-<empty>}" >&2
  FAIL=$((FAIL + 1))
fi

# A fresh checkout may have no repo-local Cargo config at all. That is also a
# stock-compatible state and must not require a machine-local setup file.
rm -f "$REAL_CLEAN/.cargo/config.toml"
if output="$(
  CLEAN_DIR="$REAL_CLEAN" \
  CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS='-Ztrust-verify=poison' \
  RUSTFLAGS='-Ztrust-verify=poison' \
  CARGO_ENCODED_RUSTFLAGS='poison' \
    "$SOUNDNESS_CHECK" --self-test-clean-cargo-command 2>&1
)" && [ -x "$REAL_CLEAN/target/release/clean" ]; then
  printf 'ok - missing Clean config is already stock-compatible\n'
  PASS=$((PASS + 1))
else
  printf 'not ok - missing Clean config (output: %s)\n' \
    "${output:-<empty>}" >&2
  FAIL=$((FAIL + 1))
fi

# Adding even a compatible flag changes what a global RUSTFLAGS replacement
# would discard. The lane must stop for a new audit instead of silently
# weakening Clean's configuration.
# The drift must sit in THIS HOST's stanza: a Trust-only flag in another
# triple's stanza is inert (Cargo selects at most the host stanza) and the
# production lane documents it as such, so a Darwin-keyed fixture asserts
# nothing on any other host. The refusal names the triple it audited, which is
# why the expected message is built from the host triple rather than spelled
# out — it read `unaudited aarch64 rustflags` until 7a8ea174 generalized it.
printf '%s\n' \
  "[target.${HOST_TRIPLE}]" \
  'rustflags = ["-C", "target-cpu=native", "-D", "warnings", "-Ztrust-verify=off"]' \
  >"$REAL_CLEAN/.cargo/config.toml"
if output="$(CLEAN_DIR="$REAL_CLEAN" "$SOUNDNESS_CHECK" --self-test-clean-cargo-command 2>&1)"; then
  printf 'not ok - rejects unaudited Clean rustflag drift (unexpected success: %s)\n' \
    "$output" >&2
  FAIL=$((FAIL + 1))
elif printf '%s\n' "$output" | \
     grep -q "refusing stock Clean cargo lane: unaudited ${HOST_TRIPLE} rustflags"; then
  printf 'ok - rejects unaudited Clean rustflag drift\n'
  PASS=$((PASS + 1))
else
  printf 'not ok - rejects unaudited Clean rustflag drift (wrong failure: %s)\n' \
    "${output:-<empty>}" >&2
  FAIL=$((FAIL + 1))
fi

# A Trust-only flag anywhere except the one exact legacy target stanza cannot
# be neutralized without changing unrelated Cargo policy, so fail closed.
printf '%s\n' \
  '[build]' \
  'rustflags = ["-Ztrust-verify=off"]' \
  >"$REAL_CLEAN/.cargo/config.toml"
if output="$(CLEAN_DIR="$REAL_CLEAN" "$SOUNDNESS_CHECK" --self-test-clean-cargo-command 2>&1)"; then
  printf 'not ok - rejects misplaced Clean Trust flag (unexpected success: %s)\n' \
    "$output" >&2
  FAIL=$((FAIL + 1))
elif printf '%s\n' "$output" | grep -q 'refusing stock Clean cargo lane: unaudited build rustflags'; then
  printf 'ok - rejects misplaced Clean Trust flag\n'
  PASS=$((PASS + 1))
else
  printf 'not ok - rejects misplaced Clean Trust flag (wrong failure: %s)\n' \
    "${output:-<empty>}" >&2
  FAIL=$((FAIL + 1))
fi

# Cargo permits both config names but their precedence is easy to misread and
# has changed across tooling eras. Refuse the ambiguous state instead of
# validating one file while Cargo could consume policy from the other.
printf '%s\n' \
  '[build]' \
  'rustflags = ["-C", "target-cpu=native"]' \
  >"$REAL_CLEAN/.cargo/config.toml"
printf '%s\n' \
  '[build]' \
  'rustflags = ["-C", "target-cpu=native"]' \
  >"$REAL_CLEAN/.cargo/config"
if output="$(CLEAN_DIR="$REAL_CLEAN" "$SOUNDNESS_CHECK" --self-test-clean-cargo-command 2>&1)"; then
  printf 'not ok - rejects ambiguous Clean config files (unexpected success: %s)\n' \
    "$output" >&2
  FAIL=$((FAIL + 1))
elif printf '%s\n' "$output" | grep -q 'refusing ambiguous Clean Cargo config'; then
  printf 'ok - rejects ambiguous Clean config files\n'
  PASS=$((PASS + 1))
else
  printf 'not ok - rejects ambiguous Clean config files (wrong failure: %s)\n' \
    "${output:-<empty>}" >&2
  FAIL=$((FAIL + 1))
fi

printf '%d passed, %d failed\n' "$PASS" "$FAIL"
[ "$FAIL" -eq 0 ]
