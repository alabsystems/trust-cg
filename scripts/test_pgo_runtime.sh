#!/bin/sh
#
# Publication checks for the AOT PGO counter runtime and its real importer ABI.
#
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0

set -eu

SCRIPT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
REPO_ROOT=$(CDPATH= cd -- "${SCRIPT_DIR}/.." && pwd)
cd "${REPO_ROOT}"
unset TCG_PGO_GEN TCG_PGO_USE TCG_PGO_OUT

fail() {
    echo "test_pgo_runtime: $*" >&2
    exit 1
}

require_command() {
    if ! command -v "$1" >/dev/null 2>&1; then
        fail "required command not found: $1"
    fi
}

cc=${CC:-cc}
require_command "${cc}"
require_command cargo
require_command python3
require_command rustc

actual_host=$(rustc -vV | sed -n 's/^host: //p')
if [ "${actual_host}" != "aarch64-apple-darwin" ]; then
    fail "real PGO execution requires an aarch64-apple-darwin host, got ${actual_host:-unknown}"
fi

tmp_dir=$(mktemp -d "${TMPDIR:-/tmp}/trust-cg-pgo-runtime.XXXXXX")
wrapper_pid=
writer_pid=
cleanup() {
    status=$?
    trap - EXIT
    if [ -n "${wrapper_pid}" ]; then
        kill "${wrapper_pid}" >/dev/null 2>&1 || true
        wait "${wrapper_pid}" >/dev/null 2>&1 || true
    fi
    if [ -n "${writer_pid}" ]; then
        kill "${writer_pid}" >/dev/null 2>&1 || true
        wait "${writer_pid}" >/dev/null 2>&1 || true
    fi
    rm -rf "${tmp_dir}"
    exit "${status}"
}
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

file_size() {
    wc -c < "$1" | tr -d '[:space:]'
}

assert_exact_fixture_counters() {
    python3 - "$1" <<'PY'
import pathlib
import struct
import sys

path = pathlib.Path(sys.argv[1])
actual = path.read_bytes()
expected = struct.pack("<QQQ", 11, 22, 33)
if actual != expected:
    raise SystemExit(
        f"test_pgo_runtime: {path} contains {actual.hex()}, expected {expected.hex()}"
    )
PY
}

assert_sentinel() {
    python3 - "$1" "$2" <<'PY'
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
expected = sys.argv[2].encode() + b"\n"
actual = path.read_bytes()
if actual != expected:
    raise SystemExit(
        f"test_pgo_runtime: sentinel {path} changed: {actual!r} != {expected!r}"
    )
PY
}

assert_no_temporary() {
    if find "${tmp_dir}" -name "$1.tmp.*" -print -quit | grep -q .; then
        fail "$1 left its temporary file behind"
    fi
}

fixture_binary="${tmp_dir}/pgo-runtime-fixture"
"${cc}" -std=c11 -Wall -Wextra -Werror -pthread \
    crates/trust-cg-llvm-import/tests/fixtures/pgo_runtime_fixture.c \
    crates/trust-cg-llvm-import/rt/tcg_pgo_rt.c \
    -o "${fixture_binary}"

# A normal destructor replaces stale data with exactly the three documented
# little-endian u64 values and leaves no private temporary file behind.
normal_raw="${tmp_dir}/normal.raw"
dd if=/dev/zero of="${normal_raw}" bs=24 count=2 2>/dev/null
TCG_PGO_OUT="${normal_raw}" "${fixture_binary}"
assert_exact_fixture_counters "${normal_raw}"
assert_no_temporary normal.raw

# abort and _Exit both skip the destructor. The constructor must already have
# made the public raw file unusable, so an old same-length profile cannot live
# through an abnormal canary exit.
for mode in abort _Exit; do
    abnormal_raw="${tmp_dir}/${mode}.raw"
    dd if=/dev/zero of="${abnormal_raw}" bs=24 count=1 2>/dev/null
    # The nested shell converts a signal status into an ordinary nonzero exit
    # and suppresses the parent shell's platform-specific abort diagnostic.
    if TCG_PGO_OUT="${abnormal_raw}" sh -c \
        '"$1" "$2"; status=$?; exit "$status"' sh \
        "${fixture_binary}" "${mode}" >/dev/null 2>&1; then
        fail "${mode} fixture unexpectedly exited successfully"
    fi
    if [ "$(file_size "${abnormal_raw}")" -ne 0 ]; then
        fail "${mode} left a stale nonempty raw profile"
    fi
done

# Opening the public target must refuse a symlink without changing its
# referent. The persistent .lock file is expected and remains available for
# subsequent writers.
target_sentinel="${tmp_dir}/target-sentinel"
target_sentinel_text='target-sentinel-must-not-change'
printf '%s\n' "${target_sentinel_text}" > "${target_sentinel}"
symlink_raw="${tmp_dir}/target-symlink.raw"
ln -s "${target_sentinel}" "${symlink_raw}"
if env TCG_PGO_OUT="${symlink_raw}" "${fixture_binary}" >/dev/null 2>&1; then
    fail "symlink output target unexpectedly succeeded"
fi
if [ ! -L "${symlink_raw}" ]; then
    fail "symlink output target was replaced"
fi
assert_sentinel "${target_sentinel}" "${target_sentinel_text}"

# A hard link must likewise be rejected before truncation: O_NOFOLLOW alone
# does not distinguish one from an ordinary output file.
hardlink_sentinel="${tmp_dir}/hardlink-sentinel"
hardlink_sentinel_text='hardlink-sentinel-must-not-change'
printf '%s\n' "${hardlink_sentinel_text}" > "${hardlink_sentinel}"
hardlink_raw="${tmp_dir}/target-hardlink.raw"
ln "${hardlink_sentinel}" "${hardlink_raw}"
if env TCG_PGO_OUT="${hardlink_raw}" "${fixture_binary}" >/dev/null 2>&1; then
    fail "hard-linked output target unexpectedly succeeded"
fi
assert_sentinel "${hardlink_sentinel}" "${hardlink_sentinel_text}"
assert_sentinel "${hardlink_raw}" "${hardlink_sentinel_text}"

# Reproduce the old predictable `<raw>.tmp.<pid>` attack deterministically:
# hold an exec wrapper behind a gate, capture its eventual process id, install
# that name as a hostile symlink, and only then let the constructor run. The
# mkstemp-based runtime must neither follow nor modify the hostile name.
temp_sentinel="${tmp_dir}/temp-sentinel"
temp_sentinel_text='temporary-sentinel-must-not-change'
printf '%s\n' "${temp_sentinel_text}" > "${temp_sentinel}"
hostile_raw="${tmp_dir}/hostile.raw"
hostile_gate="${tmp_dir}/hostile.gate"
sh -c '
    while [ ! -e "$1" ]; do
        sleep 0.01
    done
    exec env TCG_PGO_OUT="$2" "$3"
' sh "${hostile_gate}" "${hostile_raw}" "${fixture_binary}" &
wrapper_pid=$!
hostile_temp="${hostile_raw}.tmp.${wrapper_pid}"
ln -s "${temp_sentinel}" "${hostile_temp}"
: > "${hostile_gate}"
if ! wait "${wrapper_pid}"; then
    wrapper_pid=
    fail "runtime rejected a harmless preexisting predictable-temp symlink"
fi
wrapper_pid=
assert_exact_fixture_counters "${hostile_raw}"
assert_sentinel "${temp_sentinel}" "${temp_sentinel_text}"
if [ ! -L "${hostile_temp}" ]; then
    fail "runtime replaced the hostile predictable-temp symlink"
fi

# pthread_atfork marks both processes invalid. Neither the parent nor child may
# install the shared temporary stream, and the public raw remains zero length.
fork_raw="${tmp_dir}/fork.raw"
dd if=/dev/zero of="${fork_raw}" bs=24 count=1 2>/dev/null
if env TCG_PGO_OUT="${fork_raw}" "${fixture_binary}" fork \
    >/dev/null 2>&1; then
    fail "forking fixture unexpectedly published a profile"
fi
if [ "$(file_size "${fork_raw}")" -ne 0 ]; then
    fail "forking fixture left a usable public raw profile"
fi
assert_no_temporary fork.raw

# The lock is acquired before public-target truncation. Hold the first writer
# in main, prove a second same-path writer fails, and verify that its failed
# constructor did not disturb the first writer's empty public target.
concurrent_raw="${tmp_dir}/concurrent.raw"
dd if=/dev/zero of="${concurrent_raw}" bs=24 count=2 2>/dev/null
env TCG_PGO_OUT="${concurrent_raw}" "${fixture_binary}" sleep \
    >/dev/null 2>&1 &
writer_pid=$!
attempt=0
while [ "$(file_size "${concurrent_raw}")" -ne 0 ]; do
    attempt=$((attempt + 1))
    if [ "${attempt}" -ge 500 ]; then
        fail "first writer did not truncate its public target"
    fi
    if ! kill -0 "${writer_pid}" >/dev/null 2>&1; then
        fail "first writer exited before the concurrency check"
    fi
    sleep 0.01
done
if env TCG_PGO_OUT="${concurrent_raw}" "${fixture_binary}" \
    >/dev/null 2>&1; then
    fail "same-path concurrent writer unexpectedly succeeded"
fi
if [ "$(file_size "${concurrent_raw}")" -ne 0 ]; then
    fail "rejected concurrent writer modified the public target"
fi
if ! wait "${writer_pid}"; then
    writer_pid=
    fail "first writer failed after rejecting its competitor"
fi
writer_pid=
assert_exact_fixture_counters "${concurrent_raw}"
assert_no_temporary concurrent.raw

# Exercise the real ABI and relocation path: instrument the existing
# multi-function LLVM fixture, link this runtime, execute the canary, and feed
# its emitted profile into a second importer compile.
build_messages="${tmp_dir}/cargo-build.json"
cargo build --locked -p trust-cg-llvm-import \
    --bin trust-cg-ws2-import --features driver \
    --message-format=json-render-diagnostics > "${build_messages}"
importer=$(
    python3 - "${build_messages}" <<'PY'
import json
import pathlib
import sys

result = None
for line in pathlib.Path(sys.argv[1]).read_text().splitlines():
    message = json.loads(line)
    target = message.get("target", {})
    if (
        message.get("reason") == "compiler-artifact"
        and target.get("name") == "trust-cg-ws2-import"
        and "bin" in target.get("kind", [])
        and message.get("executable")
    ):
        result = message["executable"]
if result is None:
    raise SystemExit("test_pgo_runtime: cargo did not report the importer executable")
print(result)
PY
)

assert_driver_rejection() {
    label=$1
    mode_variable=$2
    opt_level=$3
    target=$4
    rejected_base="${tmp_dir}/reject-${label}"
    rejected_object="${tmp_dir}/reject-${label}.o"
    rejected_error="${tmp_dir}/reject-${label}.stderr"

    if [ "${target}" = default ]; then
        if env "${mode_variable}=${rejected_base}" "${importer}" \
            --opt-level "${opt_level}" "${llvm_fixture}" "${rejected_object}" \
            >/dev/null 2>"${rejected_error}"; then
            fail "${label} PGO driver invocation unexpectedly succeeded"
        fi
    else
        if env "${mode_variable}=${rejected_base}" "${importer}" \
            --opt-level "${opt_level}" --target "${target}" \
            "${llvm_fixture}" "${rejected_object}" \
            >/dev/null 2>"${rejected_error}"; then
            fail "${label} PGO driver invocation unexpectedly succeeded"
        fi
    fi
    if ! grep -F 'require an AArch64 target at O2 or O3' \
        "${rejected_error}" >/dev/null; then
        fail "${label} did not exercise the PGO target/optimization gate"
    fi
    if [ -e "${rejected_object}" ] || [ -e "${rejected_base}.sites" ] ||
        [ -e "${rejected_base}.raw" ]; then
        fail "${label} emitted output before rejecting unsupported PGO controls"
    fi
}

real_base="${tmp_dir}/real-profile"
real_object="${tmp_dir}/revertBits.o"
real_binary="${tmp_dir}/revertBits"
real_stdout="${tmp_dir}/revertBits.stdout"
real_use_object="${tmp_dir}/revertBits-use.o"
llvm_fixture='crates/trust-cg-llvm-import/tests/fixtures/revertBits_clang_o0.ll'

# Keep pure validator tests wired through the actual CLI and environment
# boundary for both active modes. Rejection must happen before input import or
# output creation.
assert_driver_rejection gen-o1 TCG_PGO_GEN O1 default
assert_driver_rejection use-o1 TCG_PGO_USE O1 default
assert_driver_rejection gen-x86-o2 TCG_PGO_GEN O2 x86_64-apple-darwin
assert_driver_rejection use-x86-o2 TCG_PGO_USE O2 x86_64-apple-darwin

env TCG_PGO_GEN="${real_base}" "${importer}" --opt-level O2 \
    "${llvm_fixture}" "${real_object}"
if [ ! -s "${real_object}" ] || [ ! -s "${real_base}.sites" ]; then
    fail "real profile-generate compile did not emit its object and sidecar"
fi
"${cc}" -std=c11 -Wall -Wextra -Werror -pthread \
    "${real_object}" crates/trust-cg-llvm-import/rt/tcg_pgo_rt.c \
    -o "${real_binary}"
env TCG_PGO_OUT="${real_base}.raw" "${real_binary}" > "${real_stdout}"
python3 - "${real_base}.sites" "${real_base}.raw" "${real_stdout}" <<'PY'
import pathlib
import struct
import sys

sites_path, raw_path, stdout_path = map(pathlib.Path, sys.argv[1:])
site_lines = sites_path.read_text().splitlines()
site_rows = [line for line in site_lines if "\t" in line]
if len(site_rows) != 12:
    raise SystemExit(
        f"test_pgo_runtime: real sidecar has {len(site_rows)} site rows, expected 12"
    )
raw = raw_path.read_bytes()
if len(raw) != 12 * 8:
    raise SystemExit(
        f"test_pgo_runtime: real raw profile has {len(raw)} bytes, expected 96"
    )
counters = struct.unpack("<12Q", raw)
if not any(counters):
    raise SystemExit("test_pgo_runtime: real canary did not increment any counter")
expected_stdout = (
    b"0x12345678 -> 0x1e6a2c48\n"
    b"0x123456789012345 -> 0xa2c48091e6a2c480\n"
)
actual_stdout = stdout_path.read_bytes()
if actual_stdout != expected_stdout:
    raise SystemExit(
        f"test_pgo_runtime: real canary stdout {actual_stdout!r} "
        f"!= {expected_stdout!r}"
    )
PY
env TCG_PGO_USE="${real_base}" "${importer}" --opt-level O2 \
    "${llvm_fixture}" "${real_use_object}"
if [ ! -s "${real_use_object}" ]; then
    fail "real profile-use compile did not emit a nonempty object"
fi

echo "AOT PGO runtime safety and real GEN-to-USE checks: PASS"
