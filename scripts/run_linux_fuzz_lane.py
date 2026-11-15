#!/usr/bin/env python3
"""Run the Linux AArch64 fuzz lane with fixed seeds, retained JSON and negative controls.

Testing evidence only: a passing lane means that the configured budgets found
no panic, sanitizer report, miscompile or timeout, and that each planted
failure was detected. It is not a proof, a completeness claim or release
qualification.

The lane runs, in order, from the checkout it lives in:

1. Negative controls. Each detector must report a planted failure as FAIL
   through the same classifier that judges the campaign, for the planted
   reason:
   - panic-fuzz: `panic_fuzz_lower`'s deliberate-panic test with
     TRUST_CG_PANIC_FUZZ_NEGATIVE_CONTROL=1 must fail with its signature;
   - libFuzzer: `fuzz_encode_instruction` built with the fuzz crate's
     `negative-control` feature, seeded with one planted marker input per
     control, must crash with the planted panic, report the planted heap
     leak (LeakSanitizer) and report the planted heap-buffer-overflow read
     (AddressSanitizer), each leaving its marker input as the artifact;
   - JIT differential: `trust-ir-jit-diff --plant-miscompile-seed` perturbs
     the O2 JIT result of one seed after it executes, and the run must report
     that seed as a miscompile.
2. The seven panic-fuzz proptest families (`PANIC_FUZZ_FAMILIES`) as complete
   Cargo test targets at `--proptest-cases` cases with the fixed
   PROPTEST_RNG_SEED `--proptest-seed` and failure persistence disabled, so a
   failure cannot write into the source tree. Each must pass at least the
   Linux floor's minimum for that target, and each family's case-count probe
   must print that it was configured with, and ran, exactly
   `--proptest-cases` cases.
3. The six cargo-fuzz libFuzzer targets (`LIBFUZZER_TARGETS`), built with the
   pinned dated nightly `FUZZ_TOOLCHAIN` (cargo-fuzz defaults: release, debug
   assertions, overflow checks, AddressSanitizer), each run for
   `--fuzz-seconds` at `-seed=--libfuzzer-seed` from an empty corpus outside
   the source tree, at most `--parallel` (<= 4) at a time. A nonzero exit, a
   sanitizer or panic report, any crash/timeout/oom/leak artifact, an input
   slower than `--libfuzzer-slow-unit-seconds` (a slow-unit artifact), a
   missing completion line or final statistics, or a run that stopped before
   its budget fails the target.
4. The JIT differential driver `trust-ir-jit-diff` over the fixed seed range
   `--jit-seed-start` .. +`--jit-runs`: the trust-ir interpreter against JIT
   execution at O0/O2/O3 in forked sandboxes. The lane derives the rows the
   range must check itself (6 scalar rows per seed, 6 control-shape rows per
   seed, 4 consumer-shape rows per eighth seed) and requires exactly those,
   each executed at all three levels
   (a refused compile compared nothing and fails the lane), with no
   miscompile, crash, timeout or repro. Scalar rows the interpreter gave no
   value (a division by zero) are compared across the three levels only; at
   least JIT_MINIMUM_INTERPRETER_PERCENT of the scalar rows must have an
   interpreter value, and the report counts both kinds apart.

Every child runs in a controlled environment. Ambient variables that change
what is built or executed (sanitizer options, compiler, instrumentation and
Cargo profile/alias/config overrides, the variables Cargo sets for its
children, C/C++ compiler, driver and flags for build scripts and libFuzzer,
the library search path, proptest and libtest controls, the Rust stack size,
preloaded libraries, coverage output, trust-cg's TCG_*/TRUST_CG_* controls)
are removed and recorded, and the lane sets its own `PINNED_ENVIRONMENT`
(plus `LIBFUZZER_ENVIRONMENT` for the instrumented binaries).
RUSTUP_AUTO_INSTALL=0: a missing toolchain is reported, never downloaded.
Cargo config files cannot be scrubbed: before it runs any Cargo or rustc
command, version probes included (a config [alias] could run anything), the
lane records every config path Cargo would read and the config variables of
its environment (scripts/cargo_config_audit.py, shared with the Linux floor).
It refuses to run when a path is not a regular file, or when a file other
than a byte-identical copy of the repository's committed .cargo/config.toml
sets a key outside that module's allowlist; it audits again at the end and
fails when the record changed.

report.json records the source revision and content fingerprint before and
after (a change fails the run), the stable and pinned nightly toolchains,
cargo-fuzz, the root and fuzz lockfile hashes, every executable's SHA-256,
the scrubbed and pinned environment, every command, log and elapsed time, and
the parsed campaign figures. A passing run is `qualifying` only when every
budget meets its bound (QUALIFYING_MINIMUMS, QUALIFYING_MAXIMUMS), the
libFuzzer build used the pinned nightly, the non-fuzz builds used the stock
stable rustc and cargo this lane pins (STABLE_TOOLCHAIN, a STOCK EXCEPTION;
rust-toolchain.toml pins Trust since 2026-09-28), with the rustc commit
STABLE_RUSTC_COMMIT, the Cargo configuration audited clean and the source
tree was clean; otherwise it is reported as
non-qualifying and exits 3. --require-clean
refuses a dirty tree outright. --check-prerequisites only checks that the
pinned nightly, its rust-lld and cargo-fuzz are installed. Exit status: 0
qualifying pass (or prerequisites present), 3 non-qualifying pass, 1 failure
(or prerequisites missing), 2 usage error.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
FLOOR_SCRIPT = ROOT / "scripts" / "check_linux_aarch64.py"
TIMEOUT_RUNNER = ROOT / "scripts" / "run_with_timeout.py"
FUZZ_DIR = ROOT / "fuzz"
HOST = "aarch64-unknown-linux-gnu"
SCHEMA = "trust-cg-linux-fuzz-lane-v2"
OUTPUT_PREFIX = "trust-cg-linux-fuzz-lane-"

# STOCK EXCEPTION (Trust lacks an ASan runtime, rust-lld and cargo-fuzz;
# measured on the Darwin Trust package: `trustc -Zsanitizer=address` -> "ld:
# library 'rustc-trust_rt.asan' not found", no lib/rustlib/<host>/bin/rust-lld,
# no cargo-fuzz; the Linux Trust package is unmeasured). This whole lane stays
# on explicit stock rustup toolchains until Trust ships them. ALab builds are
# otherwise Trust (owner directive 2026-09-28): the repository's
# rust-toolchain.toml pins `channel = "trust"`, so the lane names its stock
# channels itself below and exports RUSTUP_TOOLCHAIN for its stock children.
#
# The nightly that builds the instrumented cargo-fuzz targets: a dated rustup
# channel and the compiler commit it must report. The lane qualified with
# this compiler; moving the pin is a reviewed edit here.
FUZZ_TOOLCHAIN = "nightly-2026-08-06"
FUZZ_TOOLCHAIN_COMMIT = "7608eb7b07eaf93f16d7cf5bcb2098eca87503df"
# The stock stable toolchain that builds everything else in this lane, and the
# rustc commit it must report. Until 2026-09-28 it was rust-toolchain.toml's
# channel; the repository pin is now Trust, so this lane pins it here.
# NOT itself capability-blocked: the panic-fuzz proptest and JIT-driver legs
# need no ASan, rust-lld or cargo-fuzz, and a Linux Trust package exists. They
# stay stock only because the lane is qualified as one unit on one audited stock
# Cargo (config audit, shared target dir, the TCG_* proof-tool routes its test
# processes read, which trustc refuses) and moving them needs a run on the Linux
# host, which the 2026-09-28 migration did not have. Open follow-up: run these
# legs through scripts/trust_cargo.sh and keep only the cargo-fuzz legs stock.
STABLE_TOOLCHAIN = "1.97.1"
STABLE_RUSTC_COMMIT = "8bab26f4f68e0e26f0bb7960be334d5b520ea452"

# Complete panic-fuzz proptest targets; the minimum each must pass is the
# Linux floor's TARGET_MINIMUM_PASSES entry for the same target.
PANIC_FUZZ_FAMILIES = (
    ("trust-cg-lower", "panic_fuzz_lower"),
    ("trust-cg-codegen", "panic_fuzz_compile"),
    ("trust-cg-codegen", "panic_fuzz_compile_x86_64"),
    ("trust-cg-codegen", "panic_fuzz_encode"),
    ("trust-cg-codegen", "panic_fuzz_encode_x86_64"),
    ("trust-cg-codegen", "panic_fuzz_macho_fixup"),
    ("trust-cg-verify", "panic_fuzz_verify"),
)
LIBFUZZER_TARGETS = (
    "fuzz_translate_function",
    "fuzz_compile_function",
    "fuzz_compile_x86_64",
    "fuzz_encode_instruction",
    "fuzz_macho_fixup",
    "fuzz_verify_module",
)
JIT_DRIVER = "trust-ir-jit-diff"
# The driver's row policy (crates/trust-cg-fuzz/src/bin/trust-ir-jit-diff.rs):
# 6 scalar rows per seed, the same 6 rows on each seed's control-shape module
# (crates/trust-cg-fuzz/src/control_gen.rs), and 4 consumer-shape rows for
# every eighth seed.
JIT_SCALAR_ROWS_PER_SEED = 6
JIT_CONTROL_ROWS_PER_SEED = JIT_SCALAR_ROWS_PER_SEED
JIT_CONSUMER_ROWS = 4
JIT_CONSUMER_EVERY = 8
# At least half of the scalar rows must have an interpreter value (the rest
# are compared across O0/O2/O3 only). Seeds 1-10,000 measured 44,996 of
# 60,000 (75%); 50% is a floor, not a prediction.
JIT_MINIMUM_INTERPRETER_PERCENT = 50

# The planted failures and the evidence each detector must produce.
PROPTEST_CONTROL = ("trust-cg-lower", "panic_fuzz_lower", "panic_fuzz_negative_control_fails_when_enabled")
PROPTEST_CONTROL_ENV = "TRUST_CG_PANIC_FUZZ_NEGATIVE_CONTROL"
PROPTEST_CONTROL_SIGNATURE = "panic-fuzz negative control observed deliberate panic"
LIBFUZZER_CONTROL_TARGET = "fuzz_encode_instruction"
LIBFUZZER_CONTROL_FEATURE = "negative-control"
# Must equal the NEGATIVE_*_MARKER constants in fuzz/fuzz_targets/fuzz_encode_instruction.rs.
LIBFUZZER_CONTROL_MARKER = b"TRUST-CG-FUZZ-LANE-NEGATIVE-CONTROL"
LIBFUZZER_LEAK_MARKER = b"TRUST-CG-FUZZ-LANE-NEGATIVE-LEAK"
LIBFUZZER_ASAN_MARKER = b"TRUST-CG-FUZZ-LANE-NEGATIVE-ASAN"
LIBFUZZER_CONTROL_PANIC = "planted fuzz-lane negative control"
# Each libFuzzer control: its planted input, the failure kind and artifact
# prefix the classifier must report, and the report text that names it.
LIBFUZZER_CONTROLS = {
    "libfuzzer": (LIBFUZZER_CONTROL_MARKER, "crash", LIBFUZZER_CONTROL_PANIC),
    "libfuzzer-leak": (LIBFUZZER_LEAK_MARKER, "leak", "ERROR: LeakSanitizer: detected memory leaks"),
    "libfuzzer-asan": (LIBFUZZER_ASAN_MARKER, "crash", "ERROR: AddressSanitizer: heap-buffer-overflow"),
}
# Must equal PLANTED_MISCOMPILE_TAG in crates/trust-cg-fuzz/src/bin/trust-ir-jit-diff.rs.
JIT_CONTROL_TAG = "planted-negative-control"
NEGATIVE_CONTROLS = ("panic-fuzz", *LIBFUZZER_CONTROLS, "jit-diff")
LIBFUZZER_CONTROL_SECONDS = 60

# A passing run is qualifying only when every budget is at least, and every
# per-input limit at most, the default.
QUALIFYING_MINIMUMS = {
    "fuzz_seconds": 600,
    "proptest_cases": 10000,
    "jit_runs": 10000,
}
QUALIFYING_MAXIMUMS = {
    "libfuzzer_timeout_seconds": 25,
    "libfuzzer_slow_unit_seconds": 10,
    "libfuzzer_rss_limit_mb": 4096,
}
DEFAULTS = {
    **QUALIFYING_MINIMUMS,
    **QUALIFYING_MAXIMUMS,
    "libfuzzer_seed": 20260924,
    "proptest_seed": 20260924,
    "jit_seed_start": 1,
    "jit_control_seed": 1,
    "jit_control_runs": 8,
    "parallel": 4,
    "jobs": 4,
    "toolchain": FUZZ_TOOLCHAIN,
}
MAX_PARALLEL = 4
# libFuzzer reports whole seconds; a run may report one second less than a
# budget it spent.
LIBFUZZER_BUDGET_TOLERANCE_SECONDS = 1

# Ambient variables removed from every child and recorded. They change what is
# built (compiler, wrappers, flags, profiles, targets, unstable Cargo options)
# or what executes (sanitizer runtime options, preloaded libraries, coverage
# output, proptest and libtest controls, the stack size, trust-cg's own
# controls). The proof-tool routes stay: the report records what they resolve.
SCRUBBED_NAMES = frozenset({
    "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTDOCFLAGS",
    "RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "RUSTC_BOOTSTRAP", "RUSTUP_TOOLCHAIN",
    "CARGO_BUILD_RUSTFLAGS", "CARGO_BUILD_RUSTDOCFLAGS", "CARGO_BUILD_RUSTC", "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "CARGO_BUILD_TARGET", "CARGO_BUILD_JOBS",
    "LLVM_PROFILE_FILE", "LD_PRELOAD", "LD_AUDIT", "GLIBC_TUNABLES", "LD_LIBRARY_PATH", "LIBRARY_PATH",
    "RUST_MIN_STACK", "RUST_BACKTRACE", "RUST_LIB_BACKTRACE", "RUSTUP_AUTO_INSTALL",
    # C/C++ compilation by build scripts and libfuzzer-sys (the cc crate).
    "CC", "CXX", "AR", "LD", "RANLIB", "CFLAGS", "CXXFLAGS", "CPPFLAGS", "LDFLAGS", "ARFLAGS",
    "CPATH", "C_INCLUDE_PATH", "CPLUS_INCLUDE_PATH", "CXXSTDLIB", "CRATE_CC_NO_DEFAULTS",
    "CUSTOM_LIBFUZZER_PATH", "CUSTOM_LIBFUZZER_STD_CXX",
    # The GCC/Clang driver and linker: program and library search, extra
    # options, dependency output and the LTO driver.
    "COMPILER_PATH", "GCC_EXEC_PREFIX", "OBJC_INCLUDE_PATH", "CCC_OVERRIDE_OPTIONS", "GCC_COMPARE_DEBUG",
    "DEPENDENCIES_OUTPUT", "SUNPRO_DEPENDENCIES", "COLLECT_GCC", "COLLECT_GCC_OPTIONS",
    "COLLECT_LTO_WRAPPER", "LD_RUN_PATH", "LDEMULATION", "RUST_TARGET_PATH",
})
SCRUBBED_PREFIXES = (
    "PROPTEST_", "RUST_TEST_", "CARGO_PROFILE_", "CARGO_UNSTABLE_", "CARGO_ALIAS_", "CARGO_ENV_",
    "CARGO_SOURCE_", "CARGO_PATCH_", "TCG_", "TRUST_CG_",
)
SCRUBBED_PATTERNS = (
    re.compile(r"[A-Z]*SAN_OPTIONS"),
    re.compile(r"[A-Z]*SAN_SYMBOLIZER_PATH"),
    re.compile(r"CARGO_TARGET_[A-Z0-9_]+_(?:RUSTFLAGS|RUSTDOCFLAGS|LINKER|RUNNER)"),
    # Per-target and host/target spellings the cc crate reads.
    re.compile(r"(?:CC|CXX|AR|CFLAGS|CXXFLAGS|CPPFLAGS|LDFLAGS|ARFLAGS|CXXSTDLIB)_[A-Za-z0-9_.-]+"),
    re.compile(r"(?:HOST|TARGET)_(?:CC|CXX|AR|CFLAGS|CXXFLAGS|CPPFLAGS|LDFLAGS|ARFLAGS|CXXSTDLIB)"),
)
KEPT_PROOF_TOOL_ROUTES = frozenset({"TCG_SOLVER_PATH", "TCG_EXTERNAL_CLEAN_CHECKER", "TCG_CLEAN_CHECKER"})
# The values every child gets. RUST_MIN_STACK is the root .cargo/config.toml
# value, which Cargo would otherwise supply to test processes only.
# RUSTUP_AUTO_INSTALL=0: a missing pinned nightly is reported, never downloaded.
PINNED_ENVIRONMENT = {
    "RUST_MIN_STACK": "16777216",
    "RUST_BACKTRACE": "0",
    "RUSTUP_AUTO_INSTALL": "0",
    # STOCK EXCEPTION (see STABLE_TOOLCHAIN): the rustup proxies would otherwise
    # follow the repository's Trust pin.
    "RUSTUP_TOOLCHAIN": STABLE_TOOLCHAIN,
}
# The instrumented libFuzzer binaries' sanitizer runtime, stated in full.
LIBFUZZER_ENVIRONMENT = {
    "ASAN_OPTIONS": "detect_leaks=1:halt_on_error=1:abort_on_error=0:allocator_may_return_null=0",
}

# libFuzzer's status line: "#123\tNEW    cov: 45 ft: 67 corp: 8/90b ...".
LIBFUZZER_STATUS = re.compile(
    r"^#(\d+)\s+(INITED|NEW|REDUCE|pulse|DONE|RELOAD)\s+cov: (\d+) ft: (\d+) corp: (\d+)/(\d+)([bKM]?)b?",
    re.MULTILINE,
)
LIBFUZZER_DONE = re.compile(r"^Done (\d+) runs in (\d+) second\(s\)\s*$", re.MULTILINE)
LIBFUZZER_STAT = re.compile(r"^stat::([a-z_]+):\s+(\d+(?:\.\d+)?)\s*$", re.MULTILINE)
# A report that fails the target whatever the exit status says.
LIBFUZZER_FAILURES = (
    ("crash", re.compile(r"ERROR: libFuzzer: deadly signal|panicked at|ERROR: AddressSanitizer")),
    ("timeout", re.compile(r"ERROR: libFuzzer: timeout")),
    ("oom", re.compile(r"ERROR: libFuzzer: out-of-memory|ERROR: libFuzzer: malloc\(")),
    ("leak", re.compile(r"ERROR: LeakSanitizer")),
    ("exit", re.compile(r"ERROR: libFuzzer: fuzz target exited")),
)
FAILURE_ARTIFACT = re.compile(r"(crash|timeout|oom|leak)-[0-9a-f]+")
# libFuzzer writes a slow-unit artifact for an input slower than
# -report_slow_units seconds. It fails the target: a campaign input that takes
# that long is a hostile-input performance defect (the first qualifying run
# found a 10 s Mach-O relocation walk this way), and no legitimate unit of
# these targets comes near it (their slowest are under a second).
SLOW_ARTIFACT = re.compile(r"slow-unit-[0-9a-f]+")
SIZE_UNITS = {"": 1, "b": 1, "K": 1024, "M": 1024 * 1024}


def load_floor():
    """The Linux floor module: provenance, test-suite classification and minimums."""
    spec = importlib.util.spec_from_file_location("_linux_fuzz_lane_floor", FLOOR_SCRIPT)
    if spec is None or spec.loader is None or not FLOOR_SCRIPT.is_file():
        raise RuntimeError(f"required Linux floor module is missing: {FLOOR_SCRIPT}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


FLOOR = load_floor()
# The Cargo config audit both Linux AArch64 runners share (scripts/cargo_config_audit.py).
CONFIG_AUDIT = FLOOR.cargo_config_auditor()


def config_audit(environment: dict, tool: str) -> dict:
    """The shared Cargo config audit of what `tool`, run from the checkout in
    `environment`, would read. It runs git only (for the committed config)."""
    git = shutil.which("git", path=environment.get("PATH"))
    committed = CONFIG_AUDIT.committed_config(ROOT, git) if git else None
    return CONFIG_AUDIT.audit(ROOT, environment, committed, tool)


def sha256_file(path: Path) -> dict:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1 << 20), b""):
            digest.update(chunk)
    return {"sha256": digest.hexdigest(), "bytes": path.stat().st_size}


def scrubbed(name: str, prefixes: Sequence[str] = ("CARGO_",)) -> bool:
    """Whether an ambient variable is removed from the lane's children.

    Besides the lane's own list, every config variable the shared Cargo config
    audit would refuse under the build tool's `prefixes`, and every variable
    Cargo sets for its children, is removed.
    """
    if name in KEPT_PROOF_TOOL_ROUTES:
        return False
    return (
        name in SCRUBBED_NAMES or name.startswith(SCRUBBED_PREFIXES)
        or any(pattern.fullmatch(name) for pattern in SCRUBBED_PATTERNS)
        or bool(CONFIG_AUDIT.environment_problems({name: ""}, prefixes))
        or CONFIG_AUDIT.child_variable(name, prefixes)
    )


def controlled_environment(
    ambient: dict, *, offline: bool, prefixes: Sequence[str] = ("CARGO_",),
) -> tuple[dict, dict]:
    """The children's environment and the ambient variables it removed."""
    removed = {name: value for name, value in ambient.items() if scrubbed(name, prefixes)}
    environment = {name: value for name, value in ambient.items() if name not in removed}
    environment.update(PINNED_ENVIRONMENT)
    if offline:
        environment["CARGO_NET_OFFLINE"] = "true"
    return environment, removed


def parse_libfuzzer(transcript: str) -> dict:
    """Extract libFuzzer's completion line, last status line and final statistics."""
    statuses = list(LIBFUZZER_STATUS.finditer(transcript))
    last = statuses[-1] if statuses else None
    done = LIBFUZZER_DONE.search(transcript)
    stats = {
        name: (float(value) if "." in value else int(value))
        for name, value in LIBFUZZER_STAT.findall(transcript)
    }
    parsed = {
        "done_runs": int(done.group(1)) if done else None,
        "done_seconds": int(done.group(2)) if done else None,
        "stats": stats,
        "executions": stats.get("number_of_executed_units"),
        "exec_per_second": stats.get("average_exec_per_sec"),
        "new_units": stats.get("new_units_added"),
        "peak_rss_mb": stats.get("peak_rss_mb"),
        "slowest_unit_seconds": stats.get("slowest_unit_time_sec"),
        "coverage": None, "features": None, "corpus_units": None, "corpus_bytes": None,
        "last_status_event": None,
    }
    if last is not None:
        parsed.update({
            "coverage": int(last.group(3)), "features": int(last.group(4)),
            "corpus_units": int(last.group(5)),
            "corpus_bytes": int(last.group(6)) * SIZE_UNITS[last.group(7)],
            "last_status_event": last.group(2),
        })
    return parsed


def classify_libfuzzer(
    returncode: int, transcript: str, artifacts: Sequence[str], budget_seconds: int | None = None,
) -> dict:
    """Judge one libFuzzer run: any failure report or artifact, or an incomplete run, fails.

    With `budget_seconds` the run must also report having spent its budget: a
    run that stops early fuzzed less than it claims.
    """
    parsed = parse_libfuzzer(transcript)
    errors = []
    kinds = [kind for kind, pattern in LIBFUZZER_FAILURES if pattern.search(transcript)]
    failure_artifacts = sorted(name for name in artifacts if FAILURE_ARTIFACT.fullmatch(name))
    slow_artifacts = sorted(name for name in artifacts if SLOW_ARTIFACT.fullmatch(name))
    unknown = sorted(
        name for name in artifacts
        if not FAILURE_ARTIFACT.fullmatch(name) and not SLOW_ARTIFACT.fullmatch(name)
    )
    kinds.extend(
        kind for kind in (name.split("-", 1)[0] for name in failure_artifacts) if kind not in kinds
    )
    if returncode != 0:
        errors.append(f"libFuzzer exited {returncode}")
    if kinds:
        errors.append(f"libFuzzer reported {', '.join(kinds)}")
    if failure_artifacts:
        errors.append(f"failure artifacts: {', '.join(failure_artifacts)}")
    if slow_artifacts:
        kinds.append("slow")
        errors.append(f"slow-unit artifacts: {', '.join(slow_artifacts)}")
    if unknown:
        errors.append(f"unrecognized artifacts: {', '.join(unknown)}")
    if parsed["done_runs"] is None:
        errors.append("no 'Done N runs in T second(s)' completion line")
    elif budget_seconds is not None and parsed["done_seconds"] < budget_seconds - LIBFUZZER_BUDGET_TOLERANCE_SECONDS:
        errors.append(f"ran {parsed['done_seconds']} s of its {budget_seconds} s budget")
    if not parsed["executions"]:
        errors.append("final statistics report no executed units")
    if parsed["coverage"] is None:
        errors.append("no libFuzzer status line with coverage and features")
    return {
        "status": "fail" if errors else "pass", "errors": errors,
        "failure_kinds": kinds, "failure_artifacts": failure_artifacts,
        "slow_unit_artifacts": slow_artifacts, "budget_seconds": budget_seconds, **parsed,
    }


def count(value) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def jit_expected_rows(seed_start: int, runs: int) -> tuple[int, int, int]:
    """(scalar, consumer-shape, control-shape) rows trust-ir-jit-diff checks over seeds seed_start..+runs.

    Each seed checks JIT_SCALAR_ROWS_PER_SEED scalar rows and the same rows on
    its control-shape module (JIT_CONTROL_ROWS_PER_SEED); every seed that is a
    multiple of JIT_CONSUMER_EVERY also checks JIT_CONSUMER_ROWS consumer-shape
    rows (the driver's `seed % 8 == 0` branch).
    """
    last = seed_start + runs - 1
    consumer_seeds = (last // JIT_CONSUMER_EVERY - (seed_start - 1) // JIT_CONSUMER_EVERY) if runs else 0
    return (
        runs * JIT_SCALAR_ROWS_PER_SEED,
        consumer_seeds * JIT_CONSUMER_ROWS,
        runs * JIT_CONTROL_ROWS_PER_SEED,
    )


def jit_minimum_interpreter_rows(scalar_rows: int) -> int:
    """The documented floor of scalar rows that must have an interpreter value."""
    return max(1, -(-scalar_rows * JIT_MINIMUM_INTERPRETER_PERCENT // 100))


def classify_jit_diff(
    returncode: int, runlog: dict | None, seed_start: int, runs: int,
    planted_seed: int | None = None,
) -> dict:
    """Judge one trust-ir-jit-diff run over a fixed seed range.

    The campaign (planted_seed None) passes only when every seed ran and
    checked all of its rows, every row executed at every JIT level, and no
    defect or repro was recorded; a run log that carries a planted seed can
    never pass as a campaign. A planted run's log must name the planted seed.
    """
    errors = []
    if returncode != 0:
        errors.append(f"{JIT_DRIVER} exited {returncode}")
    if not isinstance(runlog, dict):
        errors.append("no run log was written")
        return {"status": "fail", "errors": errors, "planted_detected": False, "genuine_repros": []}
    if runlog.get("driver") != JIT_DRIVER:
        errors.append(f"run log names driver {runlog.get('driver')!r}")
    if runlog.get("status") != "ok":
        errors.append(f"driver status {runlog.get('status')!r}: {runlog.get('reason')}")
    if runlog.get("seed_start") != seed_start:
        errors.append(f"run log seed_start {runlog.get('seed_start')!r} is not {seed_start}")
    if runlog.get("requested_runs") != runs:
        errors.append(f"run log requested_runs {runlog.get('requested_runs')!r} is not {runs}")
    if runlog.get("runs") != runs:
        errors.append(f"{runlog.get('runs')!r} of {runs} seeds ran before the deadline")
    if runlog.get("planted_miscompile_seed") != planted_seed:
        errors.append(
            f"run log planted_miscompile_seed {runlog.get('planted_miscompile_seed')!r} is not {planted_seed!r}"
        )
    counts = {key: runlog.get(key) for key in ("miscompiles", "crashes", "timeouts")}
    repros = runlog.get("repros")
    if not isinstance(repros, list) or not all(count(value) for value in counts.values()):
        errors.append("run log counts or repros are malformed")
        repros = []
    planted = [
        repro for repro in repros
        if isinstance(repro, dict) and planted_seed is not None
        and repro.get("seed") == planted_seed and JIT_CONTROL_TAG in str(repro.get("summary", ""))
    ]
    genuine = [repro for repro in repros if repro not in planted]
    # A refused JIT level compared nothing: every row must execute at O0, O2
    # and O3, and every seed must check all of its scalar rows.
    rows = {
        key: runlog.get(key)
        for key in (
            "rows_checked", "rows_executed", "rows_refused", "rows_oracle_compared",
            "rows_cross_level_only", "scalar_rows_per_seed", "seeds_incomplete",
        )
    }
    if not all(count(value) for value in rows.values()):
        errors.append("run log has no row execution counts")
    else:
        # The lane derives the rows the seed range must produce itself rather
        # than trusting the driver's per-seed figure.
        scalar_rows, consumer_rows, control_rows = jit_expected_rows(seed_start, runs)
        if rows["scalar_rows_per_seed"] != JIT_SCALAR_ROWS_PER_SEED:
            errors.append(
                f"run log checks {rows['scalar_rows_per_seed']} scalar rows per seed, not {JIT_SCALAR_ROWS_PER_SEED}"
            )
        if rows["rows_checked"] != scalar_rows + consumer_rows + control_rows:
            errors.append(
                f"{rows['rows_checked']} rows checked; seeds {seed_start}..+{runs} must check exactly "
                f"{scalar_rows} scalar, {control_rows} control-shape and {consumer_rows} consumer-shape rows"
            )
        if rows["seeds_incomplete"]:
            samples = ", ".join(str(seed) for seed in runlog.get("incomplete_seed_samples") or [])
            errors.append(
                f"{rows['seeds_incomplete']} seeds checked fewer than {rows['scalar_rows_per_seed']} rows"
                + (f" (first: {samples})" if samples else "")
            )
        if rows["rows_refused"]:
            samples = "; ".join(str(sample) for sample in runlog.get("refusal_samples") or [])[:600]
            errors.append(f"{rows['rows_refused']} rows had a refused JIT level: {samples}")
        if rows["rows_executed"] != rows["rows_checked"]:
            errors.append(
                f"{rows['rows_executed']} of {rows['rows_checked']} rows executed at every JIT level"
            )
        if rows["rows_oracle_compared"] + rows["rows_cross_level_only"] != rows["rows_checked"]:
            errors.append("interpreter-compared and cross-level-only rows do not add up to the rows checked")
        # Consumer-shape rows always have their closed-form oracle, and a
        # control-shape program is defined on every row (no division; every
        # loop has a constant trip count), so the rest of the compared rows
        # are scalar rows with an interpreter value. Should a control row ever
        # lack one, this undercounts the scalar rows: the floor only tightens.
        interpreter_rows = rows["rows_oracle_compared"] - consumer_rows - control_rows
        minimum = jit_minimum_interpreter_rows(scalar_rows)
        if interpreter_rows < minimum:
            errors.append(
                f"{interpreter_rows} of {scalar_rows} scalar rows were compared against the interpreter; "
                f"at least {minimum} must be"
            )
        rows["scalar_rows_expected"] = scalar_rows
        rows["consumer_rows_expected"] = consumer_rows
        rows["control_rows_expected"] = control_rows
        rows["interpreter_compared_scalar_rows"] = interpreter_rows
    defects = sum(value for value in counts.values() if count(value))
    if defects or repros:
        errors.append(
            "defects recorded: " + ", ".join(f"{key}={value}" for key, value in counts.items())
            + f", repros={len(repros)}"
        )
    return {
        "status": "fail" if errors else "pass", "errors": errors, **counts, **rows,
        "oracle_error_samples": list(runlog.get("oracle_error_samples") or []),
        "runs": runlog.get("runs"),
        "planted_detected": bool(planted) and count(counts["miscompiles"]) and counts["miscompiles"] >= 1,
        "genuine_repros": genuine,
    }


def classify_negative_control(kind: str, verdict: dict, transcript: str = "", artifacts: dict | None = None) -> dict:
    """A control passes only when its detector judged the planted failure as FAIL for the planted reason."""
    errors = []
    if verdict.get("status") != "fail":
        errors.append(f"the {kind} detector passed a run with a planted failure")
    if kind == "panic-fuzz":
        if PROPTEST_CONTROL_SIGNATURE not in transcript:
            errors.append("the deliberate-panic signature is absent")
        counts = verdict.get("counts") or {}
        if counts.get("failed") != 1:
            errors.append(f"expected exactly one failed test, observed {counts.get('failed')!r}")
    elif kind in LIBFUZZER_CONTROLS:
        marker, failure_kind, signature = LIBFUZZER_CONTROLS[kind]
        if failure_kind not in verdict.get("failure_kinds", []):
            errors.append(f"libFuzzer did not report a {failure_kind}")
        if signature not in transcript:
            errors.append(f"the planted failure's report {signature!r} is absent")
        planted_inputs = [
            name for name, data in (artifacts or {}).items()
            if name.startswith(f"{failure_kind}-") and data.startswith(marker)
        ]
        if not planted_inputs:
            errors.append(f"no {failure_kind} artifact holds the planted marker input")
    elif kind == "jit-diff":
        if not verdict.get("planted_detected"):
            errors.append("the planted seed is not reported as a miscompile")
        if verdict.get("genuine_repros"):
            errors.append("the control run also recorded defects other than the planted one")
    else:
        errors.append(f"unknown negative control {kind!r}")
    return {"status": "fail" if errors else "pass", "errors": errors}


def qualification_problems(settings: dict, provenance: dict | None) -> list[str]:
    """Why a passing run would not be qualifying; empty when it is."""
    problems = [
        f"{name} {settings[name]} < {minimum}"
        for name, minimum in QUALIFYING_MINIMUMS.items() if settings[name] < minimum
    ]
    problems.extend(
        f"{name} {settings[name]} > {maximum}"
        for name, maximum in QUALIFYING_MAXIMUMS.items() if settings[name] > maximum
    )
    if settings["toolchain"] != FUZZ_TOOLCHAIN:
        problems.append(f"toolchain {settings['toolchain']} is not the pinned {FUZZ_TOOLCHAIN}")
    if provenance is None:
        problems.append("no provenance was recorded")
        return problems
    if provenance.get("nightly_commit") != FUZZ_TOOLCHAIN_COMMIT:
        problems.append(
            f"the nightly reports commit {provenance.get('nightly_commit')!r}, not the pinned {FUZZ_TOOLCHAIN_COMMIT}"
        )
    if (provenance.get("source") or {}).get("dirty") is not False:
        problems.append("the source tree is dirty")
    stable = provenance.get("stable_toolchain") or {}
    channel = stable.get("pinned_channel")
    if channel != STABLE_TOOLCHAIN:
        problems.append(f"the lane's stock channel is {channel!r}, not {STABLE_TOOLCHAIN}")
    elif stable.get("rustc_release") != channel or stable.get("rustc_commit") != STABLE_RUSTC_COMMIT:
        problems.append(
            f"stable rustc {stable.get('rustc_release')!r} at {stable.get('rustc_commit')!r} is not "
            f"{channel} at {STABLE_RUSTC_COMMIT}"
        )
    elif not str(stable.get("cargo", "")).startswith(f"cargo {channel} "):
        problems.append(f"stable {stable.get('cargo')!r} is not the lane's pinned {channel!r}")
    if ((provenance.get("cargo_config") or {}).get("problems")) != []:
        problems.append("the Cargo configuration was not audited clean")
    return problems


def overall_status(report: dict) -> str:
    sections = [
        *report.get("builds", []), *report.get("panic_fuzz", []), *report.get("libfuzzer", []),
        *([report["jit_diff"]] if report.get("jit_diff") else []),
        *report.get("negative_controls", {}).values(),
    ]
    complete = (
        len(report.get("panic_fuzz", [])) == len(PANIC_FUZZ_FAMILIES)
        and len(report.get("libfuzzer", [])) == len(LIBFUZZER_TARGETS)
        and bool(report.get("jit_diff"))
        and set(report.get("negative_controls", {})) == set(NEGATIVE_CONTROLS)
    )
    if not complete or report.get("errors") or any(row.get("status") != "pass" for row in sections):
        return "fail"
    return "pass"


def exit_code(report: dict) -> int:
    if report.get("status") != "pass":
        return 1
    return 0 if report.get("qualifying") else 3


def positive_int(value: str) -> int:
    try:
        number = int(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("expected a positive integer") from error
    if number <= 0:
        raise argparse.ArgumentTypeError("expected a positive integer")
    return number


def nonnegative_int(value: str) -> int:
    try:
        number = int(value)
    except ValueError as error:
        raise argparse.ArgumentTypeError("expected a non-negative integer") from error
    if number < 0:
        raise argparse.ArgumentTypeError("expected a non-negative integer")
    return number


def parallel_count(value: str) -> int:
    number = positive_int(value)
    if number > MAX_PARALLEL:
        raise argparse.ArgumentTypeError(f"at most {MAX_PARALLEL} libFuzzer processes run at once")
    return number


def probe(command: Sequence[str], environment: dict | None = None) -> str:
    result = subprocess.run(
        command, cwd=ROOT, capture_output=True, text=True, timeout=60, check=False, env=environment,
    )
    if result.returncode != 0:
        raise RuntimeError(f"probe {list(command)!r} exited {result.returncode}: {result.stderr.strip()}")
    return result.stdout.strip()


def bounded(timeout_seconds: float, command: Sequence[str], max_rss_gib: float | None) -> list[str]:
    ceiling = [] if max_rss_gib is None else ["--max-rss-gib", repr(max_rss_gib)]
    return [sys.executable, str(TIMEOUT_RUNNER), "--grace-seconds", "5", *ceiling, str(timeout_seconds), *command]


def launch(command: Sequence[str], log_path: Path, environment: dict, cwd: Path = ROOT) -> tuple[subprocess.Popen, object]:
    log = log_path.open("x", encoding="utf-8")
    try:
        process = subprocess.Popen(
            list(command), cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
            start_new_session=True, env=environment,
        )
    except OSError:
        log.close()
        raise
    return process, log


def run_logged(
    name: str, command: Sequence[str], log_path: Path, timeout_seconds: float,
    environment: dict, max_rss_gib: float | None,
) -> tuple[dict, str]:
    """Run one bounded process to completion and return its record and transcript."""
    started = time.monotonic()
    wrapped = bounded(timeout_seconds, command, max_rss_gib)
    try:
        process, log = launch(wrapped, log_path, environment)
        try:
            returncode = process.wait()
        except KeyboardInterrupt:
            process.terminate()
            process.wait()
            raise
        finally:
            log.close()
    except OSError as error:
        log_path.write_text(f"launch error: {error}\n", encoding="utf-8")
        returncode = 125
    data = log_path.read_bytes()
    record = {
        "name": name, "command": list(command), "bounded_command": wrapped,
        "timeout_seconds": timeout_seconds, "returncode": returncode,
        "elapsed_seconds": round(time.monotonic() - started, 3), "log": log_path.name,
        "log_sha256": hashlib.sha256(data).hexdigest(),
    }
    return record, data.decode("utf-8", errors="replace")


def rss_errors(record: dict, transcript: str, max_rss_gib: float | None) -> list[str]:
    if max_rss_gib is None:
        return []
    receipt, errors = FLOOR.rss_receipt(transcript, max_rss_gib)
    record["rss"] = receipt
    return errors


def cargo_target_directory(cargo: str, environment: dict) -> Path:
    metadata = json.loads(probe(
        [cargo, "metadata", "--format-version", "1", "--no-deps", "--locked", "--offline"], environment,
    ))
    return Path(metadata["target_directory"])


def nightly_identity(rustc: str, toolchain: str, environment: dict) -> dict:
    """The toolchain's `rustc -vV`, commit and sysroot, and its own linker."""
    verbose = probe([rustc, f"+{toolchain}", "-vV"], environment)
    if "-nightly" not in verbose and "-dev" not in verbose:
        raise RuntimeError(f"--toolchain {toolchain} is not a nightly compiler: {verbose.splitlines()[0]}")
    commits = re.findall(r"^commit-hash: ([0-9a-f]{40})$", verbose, re.MULTILINE)
    sysroot = Path(probe([rustc, f"+{toolchain}", "--print", "sysroot"], environment))
    return {
        "toolchain": toolchain, "rustc": verbose, "commit": commits[0] if len(commits) == 1 else None,
        "sysroot": str(sysroot), "linker": nightly_linker(sysroot, environment),
    }


def nightly_linker(sysroot: Path, environment: dict | None = None) -> dict:
    """The nightly toolchain's own LLD, which links the instrumented targets.

    GNU ld 2.42 cannot: the AddressSanitizer- and coverage-instrumented
    trust-cg code puts callers and callees more than the +-128 MiB reach of
    R_AARCH64_CALL26 apart, and it stops with "relocation truncated to fit"
    where LLD inserts range-extension thunks. `-fuse-ld=lld` with the
    toolchain's gcc-ld directory first on the driver's search path selects
    the rust-lld shipped with that nightly.
    """
    gcc_ld = sysroot / "lib" / "rustlib" / HOST / "bin" / "gcc-ld"
    rust_lld = gcc_ld.parent / "rust-lld"
    for path in (gcc_ld / "ld.lld", rust_lld):
        if not path.is_file():
            raise RuntimeError(f"the nightly toolchain has no {path.name}: {path}")
    return {
        "rustflags": f"-Clink-arg=-fuse-ld=lld -Clink-arg=-B{gcc_ld}",
        "rust_lld": str(rust_lld), **sha256_file(rust_lld),
        "version": probe([str(rust_lld), "-flavor", "gnu", "--version"], environment),
    }


def prerequisite_problems(toolchain: str, environment: dict) -> tuple[list[str], dict]:
    """Whether the pinned nightly, its rust-lld and cargo-fuzz are installed."""
    problems = []
    found = {}
    cargo = shutil.which("cargo", path=environment.get("PATH"))
    rustc = shutil.which("rustc", path=environment.get("PATH"))
    if cargo is None or rustc is None:
        return ["cargo and rustc must be on PATH"], found
    try:
        found["cargo_fuzz"] = probe([cargo, "fuzz", "--version"], environment)
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        problems.append(f"cargo-fuzz is not installed ({error}); install it with `cargo install cargo-fuzz --locked`")
    if toolchain != FUZZ_TOOLCHAIN:
        problems.append(f"toolchain {toolchain} is not the pinned {FUZZ_TOOLCHAIN}")
    try:
        identity = nightly_identity(rustc, toolchain, environment)
        found["nightly_commit"] = identity["commit"]
        if identity["commit"] != FUZZ_TOOLCHAIN_COMMIT:
            problems.append(f"{toolchain} reports commit {identity['commit']}, not {FUZZ_TOOLCHAIN_COMMIT}")
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        problems.append(
            f"{toolchain} is not usable ({error}); install it with "
            f"`rustup toolchain install {FUZZ_TOOLCHAIN} --profile minimal`"
        )
    return problems, found


def is_trust_build(verbose_version: str) -> bool:
    """Whether a `cargo -vV` report is a Trust build's (a `trust:` line).

    The lane's stock Cargo (STOCK EXCEPTION) must not be one: a Trust build of
    Cargo also reads TARGO_* config variables, which this lane's audit does not
    cover.
    """
    return re.search(r"^trust: ", verbose_version, re.MULTILINE) is not None


def pinned_stable_channel() -> str | None:
    """The stock channel this lane pins for its non-fuzz builds (STOCK EXCEPTION).

    The repository's rust-toolchain.toml pins the Trust toolchain; the lane's
    stock channel is its own constant, exported as RUSTUP_TOOLCHAIN.
    """
    return STABLE_TOOLCHAIN


def stable_identity(rustc_verbose: str, cargo_version: str) -> dict:
    """The stable rustc/cargo the rustup proxies resolved, against the pinned channel."""
    release = re.findall(r"^release: (\S+)$", rustc_verbose, re.MULTILINE)
    commit = re.findall(r"^commit-hash: ([0-9a-f]{40})$", rustc_verbose, re.MULTILINE)
    return {
        "pinned_channel": pinned_stable_channel(),
        "rustc_release": release[0] if len(release) == 1 else None,
        "rustc_commit": commit[0] if len(commit) == 1 else None,
        "cargo": cargo_version,
    }


def preflight(toolchain: str, environment: dict) -> dict:
    tools = {}
    for name in ("git", "cargo", "rustc", "rustup"):
        path = shutil.which(name, path=environment.get("PATH"))
        if path is None:
            raise RuntimeError(f"required tool is missing: {name}")
        tools[name] = path
    if not TIMEOUT_RUNNER.is_file():
        raise RuntimeError(f"required timeout runner is missing: {TIMEOUT_RUNNER}")
    rustc = probe([tools["rustc"], "-vV"], environment)
    hosts = re.findall(r"^host: (\S+)$", rustc, re.MULTILINE)
    if sys.platform != "linux" or hosts != [HOST]:
        raise RuntimeError(f"required Linux host is {HOST}, observed {hosts!r} on {sys.platform}")
    cargo_verbose = probe([tools["cargo"], "-vV"], environment)
    if is_trust_build(cargo_verbose):
        # A Trust build of Cargo also reads TARGO_* config variables.
        raise RuntimeError("the lane's cargo is a Trust build of Cargo; the lane runs stock Cargo only")
    fuzz_version = probe([tools["cargo"], "fuzz", "--version"], environment)
    nightly = nightly_identity(tools["rustc"], toolchain, environment)
    cargo = probe([tools["cargo"], "--version"], environment)
    return {
        "source": FLOOR.source_provenance(tools["git"]),
        "host": hosts[0], "tools": tools,
        "tool_sha256": {name: sha256_file(Path(path).resolve()) for name, path in tools.items()},
        "rustc": rustc, "cargo": cargo, "cargo_verbose": cargo_verbose,
        # The stable toolchain that builds everything but the libFuzzer targets.
        "stable_toolchain": stable_identity(rustc, cargo),
        "nightly_toolchain": toolchain, "nightly_rustc": nightly["rustc"],
        "nightly_commit": nightly["commit"], "nightly_sysroot": nightly["sysroot"],
        "pinned_nightly": {"toolchain": FUZZ_TOOLCHAIN, "commit": FUZZ_TOOLCHAIN_COMMIT},
        "nightly_cargo": probe([tools["cargo"], f"+{toolchain}", "--version"], environment),
        "cargo_fuzz": fuzz_version, "libfuzzer_linker": nightly["linker"],
        # Identity only: the lane does not require AY or Clean, but the JIT and
        # verifier paths it exercises resolve them the way the floor records.
        "proof_tools": FLOOR.proof_tool_identities(environment),
        "lockfiles": {
            "Cargo.lock": sha256_file(ROOT / "Cargo.lock"),
            "fuzz/Cargo.lock": sha256_file(FUZZ_DIR / "Cargo.lock"),
        },
        "configuration": {
            name: environment[name]
            for name in ("CARGO_TARGET_DIR", "CARGO_HOME", "RUSTUP_HOME", "CARGO_INCREMENTAL", "CARGO_NET_OFFLINE")
            if name in environment
        },
    }


def libfuzzer_build(
    tools: dict, toolchain: str, fuzz_target_dir: Path, output: Path, jobs: int,
    environment: dict, timeout_seconds: float, rustflags: str, *, target: str | None = None,
    features: Sequence[str] = (), name: str = "libfuzzer-build",
) -> dict:
    command = [
        tools["cargo"], f"+{toolchain}", "fuzz", "build", "--fuzz-dir", str(FUZZ_DIR),
        "--target-dir", str(fuzz_target_dir),
        *(["--features", ",".join(features)] if features else []),
        *([target] if target else []),
    ]
    # cargo-fuzz appends RUSTFLAGS to its own instrumentation flags; the only
    # value it sees is the lane's linker selection (ambient values are scrubbed).
    build_environment = dict(environment, CARGO_BUILD_JOBS=str(jobs), RUSTFLAGS=rustflags)
    record, _ = run_logged(name, command, output / f"{name}.log", timeout_seconds, build_environment, None)
    record["rustflags"] = rustflags
    record["status"] = "pass" if record["returncode"] == 0 else "fail"
    record["errors"] = [] if record["returncode"] == 0 else [f"cargo fuzz build exited {record['returncode']}"]
    return record


def libfuzzer_binary(fuzz_target_dir: Path, target: str) -> Path:
    return fuzz_target_dir / HOST / "release" / target


def libfuzzer_command(binary: Path, workdir: Path, args: argparse.Namespace, seconds: int) -> list[str]:
    return [
        str(binary), f"-seed={args.libfuzzer_seed}", f"-max_total_time={seconds}",
        f"-timeout={args.libfuzzer_timeout_seconds}", f"-report_slow_units={args.libfuzzer_slow_unit_seconds}",
        f"-rss_limit_mb={args.libfuzzer_rss_limit_mb}", "-detect_leaks=1",
        "-print_final_stats=1", f"-artifact_prefix={workdir / 'artifacts'}/", str(workdir / "corpus"),
    ]


def libfuzzer_workdir(root: Path, target: str, seed_inputs: dict[str, bytes] | None = None) -> Path:
    workdir = root / target
    (workdir / "artifacts").mkdir(parents=True)
    (workdir / "corpus").mkdir()
    for name, data in (seed_inputs or {}).items():
        (workdir / "corpus" / name).write_bytes(data)
    return workdir


def finish_libfuzzer(
    record: dict, transcript: str, workdir: Path, max_rss_gib: float | None, budget_seconds: int | None,
) -> dict:
    artifacts = sorted(path.name for path in (workdir / "artifacts").iterdir())
    verdict = classify_libfuzzer(record["returncode"], transcript, artifacts, budget_seconds)
    verdict["errors"].extend(rss_errors(record, transcript, max_rss_gib))
    if verdict["errors"]:
        verdict["status"] = "fail"
    corpus = [path for path in (workdir / "corpus").iterdir() if path.is_file()]
    record.update(verdict)
    record["corpus_files"] = len(corpus)
    record["corpus_file_bytes"] = sum(path.stat().st_size for path in corpus)
    record["artifacts"] = {
        name: sha256_file(workdir / "artifacts" / name) for name in artifacts
    }
    return record


def run_libfuzzer_campaign(
    binaries: dict, output: Path, args: argparse.Namespace, environment: dict,
) -> list[dict]:
    """Run each target for the fixed budget, at most args.parallel at once, in LIBFUZZER_TARGETS order."""
    root = output / "libfuzzer"
    pending = list(LIBFUZZER_TARGETS)
    running: list[tuple[str, subprocess.Popen, object, dict, Path, float]] = []
    finished = {}
    try:
        while pending or running:
            while pending and len(running) < args.parallel:
                target = pending.pop(0)
                workdir = libfuzzer_workdir(root, target)
                command = libfuzzer_command(binaries[target], workdir, args, args.fuzz_seconds)
                timeout = float(args.fuzz_seconds + 600)
                wrapped = bounded(timeout, command, args.max_rss_gib)
                log_path = output / f"libfuzzer-{target}.log"
                process, log = launch(wrapped, log_path, environment)
                record = {
                    "name": target, "command": command, "bounded_command": wrapped,
                    "timeout_seconds": timeout, "log": log_path.name,
                    "binary": str(binaries[target]), **sha256_file(binaries[target]),
                    "seed": args.libfuzzer_seed,
                }
                print(f"Running libFuzzer {target} for {args.fuzz_seconds} s", flush=True)
                running.append((target, process, log, record, workdir, time.monotonic()))
            time.sleep(1)
            for entry in list(running):
                target, process, log, record, workdir, started = entry
                if process.poll() is None:
                    continue
                log.close()
                running.remove(entry)
                data = (output / record["log"]).read_bytes()
                record["returncode"] = process.returncode
                record["elapsed_seconds"] = round(time.monotonic() - started, 3)
                record["log_sha256"] = hashlib.sha256(data).hexdigest()
                finished[target] = finish_libfuzzer(
                    record, data.decode("utf-8", errors="replace"), workdir, args.max_rss_gib, args.fuzz_seconds,
                )
                print(f"{finished[target]['status'].upper()}: libFuzzer {target}", flush=True)
    finally:
        for _, process, log, _, _, _ in running:
            process.terminate()
            process.wait()
            log.close()
    return [finished[target] for target in LIBFUZZER_TARGETS if target in finished]


def run_libfuzzer_control(
    kind: str, binary: Path, output: Path, args: argparse.Namespace, environment: dict,
) -> dict:
    """Seed the negative-control build with one planted input and require the planted failure."""
    marker = LIBFUZZER_CONTROLS[kind][0]
    name = f"negative-control-{kind}"
    workdir = libfuzzer_workdir(output / name, LIBFUZZER_CONTROL_TARGET, {"planted-marker": marker + b"\x00"})
    record, transcript = run_logged(
        name, libfuzzer_command(binary, workdir, args, LIBFUZZER_CONTROL_SECONDS),
        output / f"{name}.log", float(LIBFUZZER_CONTROL_SECONDS + 600), environment, args.max_rss_gib,
    )
    record.update({"binary": str(binary), **sha256_file(binary)})
    detector = finish_libfuzzer(dict(record), transcript, workdir, args.max_rss_gib, LIBFUZZER_CONTROL_SECONDS)
    artifacts = {path.name: path.read_bytes() for path in (workdir / "artifacts").iterdir() if path.is_file()}
    record["detector"] = {
        key: detector[key] for key in ("status", "errors", "failure_kinds", "failure_artifacts", "artifacts")
    }
    record.update(classify_negative_control(kind, detector, transcript, artifacts))
    return record


def panic_fuzz_command(tools: dict, jobs: int, offline: bool, package: str, target: str, *tail: str) -> list[str]:
    return [
        tools["cargo"], "test", "--locked", *(["--offline"] if offline else []), "--color", "never",
        "-j", str(jobs), "-p", package, "--test", target, *tail,
    ]


def proptest_probe_lines(package: str, target: str, cases: int) -> tuple[str, ...]:
    """The case-count probe line `package`/`target` must print at `cases` cases."""
    return (FLOOR.proptest_case_line(cases),) if (package, target) in FLOOR.PROPTEST_CASE_DEFAULTS else ()


def run_panic_fuzz(tools: dict, output: Path, args: argparse.Namespace, environment: dict) -> list[dict]:
    rows = []
    family_environment = dict(
        environment, PROPTEST_CASES=str(args.proptest_cases), PROPTEST_RNG_SEED=str(args.proptest_seed),
        PROPTEST_DISABLE_FAILURE_PERSISTENCE="true",
    )
    for package, target in PANIC_FUZZ_FAMILIES:
        print(f"Running panic-fuzz {package}/{target}", flush=True)
        command = panic_fuzz_command(
            tools, args.jobs, args.require_offline_deps, package, target, "--", "--nocapture", "--test-threads=1",
        )
        record, transcript = run_logged(
            f"{package}/{target}", command, output / f"panic-fuzz-{package}--{target}.log",
            args.timeout_seconds, family_environment, args.max_rss_gib,
        )
        minimum = FLOOR.target_minimum_passes(package, target)
        verdict = FLOOR.classify_result(record["returncode"], transcript, minimum)
        verdict["errors"].extend(rss_errors(record, transcript, args.max_rss_gib))
        # The case-count positive control must report the count this lane set.
        required = proptest_probe_lines(package, target, args.proptest_cases)
        verdict["errors"].extend(
            f"required transcript line is missing: {line!r}"
            for line in required if not FLOOR.transcript_has_line(transcript, line)
        )
        record["required_lines"] = list(required)
        if verdict["errors"]:
            verdict["status"] = "fail"
        record.update(verdict)
        record.update({
            "package": package, "target": target, "proptest_cases": args.proptest_cases,
            "proptest_rng_seed": args.proptest_seed,
        })
        rows.append(record)
        print(f"{record['status'].upper()}: panic-fuzz {package}/{target}", flush=True)
    return rows


def run_jit(
    binary: Path, output: Path, name: str, seed_start: int, runs: int, duration: int,
    environment: dict, max_rss_gib: float | None, planted_seed: int | None = None,
) -> tuple[dict, dict | None]:
    out_dir = output / name
    command = [
        str(binary), "--seed-start", str(seed_start), "--runs", str(runs),
        "--duration", str(duration), "--out", str(out_dir),
        *(["--plant-miscompile-seed", str(planted_seed)] if planted_seed is not None else []),
    ]
    record, transcript = run_logged(
        name, command, output / f"{name}.log", float(duration + 600), environment, max_rss_gib,
    )
    runlog = None
    runlog_path = out_dir / f"{JIT_DRIVER}.json"
    if runlog_path.is_file():
        try:
            runlog = json.loads(runlog_path.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            runlog = None
        record["runlog"] = runlog_path.relative_to(output).as_posix()
        record["runlog_sha256"] = sha256_file(runlog_path)["sha256"]
    verdict = classify_jit_diff(record["returncode"], runlog, seed_start, runs, planted_seed)
    verdict["errors"].extend(rss_errors(record, transcript, max_rss_gib))
    if verdict["errors"]:
        verdict["status"] = "fail"
    record.update(verdict)
    record.update({"binary": str(binary), **sha256_file(binary), "seed_start": seed_start, "requested_runs": runs})
    return record, runlog


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter, allow_abbrev=False)
    parser.add_argument("--list", action="store_true", help="print the lane inventory without probing or executing")
    parser.add_argument(
        "--check-prerequisites", action="store_true",
        help="exit 0 when the pinned nightly, its rust-lld and cargo-fuzz are installed, 1 naming what is missing",
    )
    parser.add_argument("--out", type=Path, help="new output directory outside the source tree")
    parser.add_argument("--fuzz-target-dir", type=Path, help="cargo-fuzz target directory (default: <cargo target dir>/cargo-fuzz)")
    parser.add_argument("--toolchain", default=DEFAULTS["toolchain"], help=f"rustup nightly for cargo-fuzz (default and only qualifying value: {FUZZ_TOOLCHAIN})")
    parser.add_argument("--fuzz-seconds", type=positive_int, default=DEFAULTS["fuzz_seconds"], help="libFuzzer seconds per target")
    parser.add_argument("--libfuzzer-seed", type=nonnegative_int, default=DEFAULTS["libfuzzer_seed"])
    parser.add_argument("--libfuzzer-timeout-seconds", type=positive_int, default=DEFAULTS["libfuzzer_timeout_seconds"], help="libFuzzer per-input -timeout")
    parser.add_argument("--libfuzzer-slow-unit-seconds", type=positive_int, default=DEFAULTS["libfuzzer_slow_unit_seconds"], help="libFuzzer -report_slow_units; a slower input fails the target")
    parser.add_argument("--libfuzzer-rss-limit-mb", type=positive_int, default=DEFAULTS["libfuzzer_rss_limit_mb"])
    parser.add_argument("--parallel", type=parallel_count, default=DEFAULTS["parallel"], help=f"libFuzzer processes at once (at most {MAX_PARALLEL})")
    parser.add_argument("--proptest-cases", type=positive_int, default=DEFAULTS["proptest_cases"])
    parser.add_argument("--proptest-seed", type=nonnegative_int, default=DEFAULTS["proptest_seed"])
    parser.add_argument("--jit-seed-start", type=nonnegative_int, default=DEFAULTS["jit_seed_start"])
    parser.add_argument("--jit-runs", type=positive_int, default=DEFAULTS["jit_runs"], help="seeds the JIT differential must cover")
    parser.add_argument("--jit-duration", type=positive_int, default=7200, help="deadline in seconds for the JIT seed range")
    parser.add_argument("--jit-control-seed", type=nonnegative_int, default=DEFAULTS["jit_control_seed"])
    parser.add_argument("--jobs", type=positive_int, default=DEFAULTS["jobs"], help="Cargo build jobs")
    parser.add_argument("--timeout-seconds", type=positive_int, default=3600, help="bound for each build and panic-fuzz invocation")
    parser.add_argument("--max-rss-gib", type=FLOOR.positive_gib, metavar="GIB", help="sampled process-group resident-set ceiling for every command")
    parser.add_argument("--require-clean", action="store_true", help="refuse a tree with tracked edits or untracked non-ignored files")
    parser.add_argument("--require-offline-deps", action="store_true", help="run Cargo offline (--offline, CARGO_NET_OFFLINE)")
    args = parser.parse_args(argv)
    if args.list:
        print("negative-control panic-fuzz " + "/".join(PROPTEST_CONTROL))
        for kind, (marker, failure_kind, _) in LIBFUZZER_CONTROLS.items():
            print(f"negative-control {kind} {LIBFUZZER_CONTROL_TARGET} --features {LIBFUZZER_CONTROL_FEATURE} "
                  f"{marker.decode()} -> {failure_kind}")
        print(f"negative-control jit-diff {JIT_DRIVER} --plant-miscompile-seed")
        for package, target in PANIC_FUZZ_FAMILIES:
            print(f"panic-fuzz {package} {target} minimum={FLOOR.target_minimum_passes(package, target)}")
        for target in LIBFUZZER_TARGETS:
            print(f"libfuzzer {target}")
        print(f"jit-diff {JIT_DRIVER}")
        print(f"toolchain {FUZZ_TOOLCHAIN} {FUZZ_TOOLCHAIN_COMMIT}")
        return 0
    ambient = dict(os.environ)
    # The build tool every lane Cargo command runs, and the variable prefixes
    # it maps onto config keys; nothing is executed yet.
    build_tool = shutil.which("cargo", path=ambient.get("PATH")) or "cargo"
    prefixes = CONFIG_AUDIT.environment_prefixes(build_tool)
    environment, removed = controlled_environment(ambient, offline=args.require_offline_deps, prefixes=prefixes)
    # Cargo reads its configuration on every invocation, version probes
    # included, and a config [alias] could run anything: audit it first.
    cargo_config = config_audit(environment, build_tool)
    if args.check_prerequisites:
        if cargo_config["problems"]:
            print("Linux fuzz lane: a Cargo config would change what the lane runs: "
                  + "; ".join(cargo_config["problems"]))
            return 1
        problems, found = prerequisite_problems(args.toolchain, environment)
        if problems:
            print("Linux fuzz lane prerequisites missing: " + "; ".join(problems))
            return 1
        print(f"Linux fuzz lane prerequisites: {args.toolchain} ({found['nightly_commit'][:9]}), {found['cargo_fuzz']}")
        return 0
    try:
        if args.out is None:
            output = Path(tempfile.mkdtemp(prefix=OUTPUT_PREFIX))
        else:
            output = args.out.absolute()
            if output.resolve().is_relative_to(ROOT):
                raise OSError("output must be outside the source tree so logs cannot change source provenance")
            output.mkdir(mode=0o700)
    except OSError as error:
        print(f"Linux fuzz lane: output directory error: {error}", file=sys.stderr)
        return 1
    settings = {
        "fuzz_seconds": args.fuzz_seconds, "proptest_cases": args.proptest_cases, "jit_runs": args.jit_runs,
        "libfuzzer_timeout_seconds": args.libfuzzer_timeout_seconds,
        "libfuzzer_slow_unit_seconds": args.libfuzzer_slow_unit_seconds,
        "libfuzzer_rss_limit_mb": args.libfuzzer_rss_limit_mb, "toolchain": args.toolchain,
    }
    libfuzzer_environment = dict(environment, **LIBFUZZER_ENVIRONMENT)
    report = {
        "schema": SCHEMA,
        "scope": "fuzz and differential testing lane; not proof, completeness or release qualification",
        "started_utc": datetime.now(timezone.utc).isoformat(), "status": "incomplete",
        "qualifying": False, "non_qualifying_reasons": qualification_problems(settings, None),
        "controls": {
            "require_clean": args.require_clean, "require_offline_deps": args.require_offline_deps,
            "max_rss_gib": args.max_rss_gib, "jobs": args.jobs, "parallel": args.parallel,
            "fuzz_seconds": args.fuzz_seconds, "libfuzzer_seed": args.libfuzzer_seed,
            "libfuzzer_timeout_seconds": args.libfuzzer_timeout_seconds,
            "libfuzzer_slow_unit_seconds": args.libfuzzer_slow_unit_seconds,
            "libfuzzer_rss_limit_mb": args.libfuzzer_rss_limit_mb, "toolchain": args.toolchain,
            "proptest_cases": args.proptest_cases, "proptest_rng_seed": args.proptest_seed,
            "jit_seed_start": args.jit_seed_start, "jit_runs": args.jit_runs,
            "jit_duration_seconds": args.jit_duration, "jit_control_seed": args.jit_control_seed,
            "jit_control_runs": DEFAULTS["jit_control_runs"],
            "libfuzzer_control_seconds": LIBFUZZER_CONTROL_SECONDS,
            "qualifying_minimums": QUALIFYING_MINIMUMS, "qualifying_maximums": QUALIFYING_MAXIMUMS,
        },
        "environment": {
            "scrubbed": removed, "pinned": PINNED_ENVIRONMENT, "libfuzzer": LIBFUZZER_ENVIRONMENT,
            "offline": args.require_offline_deps,
        },
        "inventory": {
            "panic_fuzz": [list(row) for row in PANIC_FUZZ_FAMILIES],
            "libfuzzer": list(LIBFUZZER_TARGETS), "jit_diff": JIT_DRIVER,
            "negative_controls": list(NEGATIVE_CONTROLS),
        },
        "cargo_config": cargo_config,
        "builds": [], "panic_fuzz": [], "libfuzzer": [], "jit_diff": None,
        "negative_controls": {}, "errors": [],
    }
    report_path = output / "report.json"
    FLOOR.write_report(report_path, report)
    print(f"Linux fuzz lane logs: {output}", flush=True)
    if removed:
        print(f"Linux fuzz lane: removed ambient {', '.join(sorted(removed))} (recorded)", file=sys.stderr)
    try:
        # Cargo applies its config files to every build and test the lane
        # runs; environment scrubbing cannot reach them.
        if cargo_config["problems"]:
            report["errors"].extend(f"cargo config: {problem}" for problem in cargo_config["problems"])
            raise RuntimeError("refusing to run any Cargo command: a Cargo config would change what the lane "
                               "builds or runs; see cargo_config")
        report["provenance"] = preflight(args.toolchain, environment)
        report["provenance"]["cargo_config"] = cargo_config
        FLOOR.write_report(report_path, report)
        tools = report["provenance"]["tools"]
        if report["provenance"]["source"].get("dirty") is not False:
            if args.require_clean:
                report["errors"].append("--require-clean: source tree has tracked modifications or untracked non-ignored files")
                raise RuntimeError("--require-clean refuses this source tree")
            print("Linux fuzz lane: source tree is dirty; this run cannot be qualifying", file=sys.stderr)
        target_dir = cargo_target_directory(tools["cargo"], environment)
        fuzz_target_dir = (args.fuzz_target_dir or target_dir / "cargo-fuzz").absolute()
        report["provenance"]["cargo_target_dir"] = str(target_dir)
        report["provenance"]["fuzz_target_dir"] = str(fuzz_target_dir)
        build_timeout = float(args.timeout_seconds)

        # Negative controls first: a detector that cannot see a planted failure
        # makes every later clean result meaningless.
        print("Running negative control: panic-fuzz", flush=True)
        package, target, test = PROPTEST_CONTROL
        record, transcript = run_logged(
            "negative-control-panic-fuzz",
            panic_fuzz_command(tools, args.jobs, args.require_offline_deps, package, target,
                               "--", "--exact", test, "--nocapture", "--test-threads=1"),
            output / "negative-control-panic-fuzz.log", build_timeout,
            dict(environment, **{PROPTEST_CONTROL_ENV: "1"}), args.max_rss_gib,
        )
        detector = FLOOR.classify_result(record["returncode"], transcript)
        record["detector"] = detector
        record.update(classify_negative_control("panic-fuzz", detector, transcript))
        report["negative_controls"]["panic-fuzz"] = record
        FLOOR.write_report(report_path, report)

        rustflags = report["provenance"]["libfuzzer_linker"]["rustflags"]
        build = libfuzzer_build(
            tools, args.toolchain, fuzz_target_dir, output, args.jobs, environment, build_timeout, rustflags,
            target=LIBFUZZER_CONTROL_TARGET, features=(LIBFUZZER_CONTROL_FEATURE,),
            name="negative-control-libfuzzer-build",
        )
        report["builds"].append(build)
        FLOOR.write_report(report_path, report)
        control_binary = libfuzzer_binary(fuzz_target_dir, LIBFUZZER_CONTROL_TARGET)
        for kind in LIBFUZZER_CONTROLS:
            print(f"Running negative control: {kind}", flush=True)
            if build["status"] == "pass":
                record = run_libfuzzer_control(kind, control_binary, output, args, libfuzzer_environment)
            else:
                record = {"status": "fail", "errors": ["the negative-control build failed"]}
            report["negative_controls"][kind] = record
            FLOOR.write_report(report_path, report)

        # The JIT driver and its planted control share one dev-profile build.
        jit_build = [
            tools["cargo"], "build", "--locked", *(["--offline"] if args.require_offline_deps else []),
            "--color", "never", "-j", str(args.jobs), "-p", "trust-cg-fuzz", "--bin", JIT_DRIVER,
        ]
        record, _ = run_logged("jit-diff-build", jit_build, output / "jit-diff-build.log", build_timeout, environment, None)
        record["status"] = "pass" if record["returncode"] == 0 else "fail"
        record["errors"] = [] if record["returncode"] == 0 else [f"cargo build exited {record['returncode']}"]
        report["builds"].append(record)
        FLOOR.write_report(report_path, report)
        jit_binary = target_dir / "debug" / JIT_DRIVER
        jit_built = record["status"] == "pass" and jit_binary.is_file()
        if jit_built:
            print("Running negative control: JIT differential", flush=True)
            record, _ = run_jit(
                jit_binary, output, "negative-control-jit-diff", args.jit_control_seed,
                DEFAULTS["jit_control_runs"], args.jit_duration, environment, args.max_rss_gib,
                planted_seed=args.jit_control_seed,
            )
            detector = {key: record[key] for key in ("status", "errors", "planted_detected", "genuine_repros")}
            record["detector"] = detector
            record.update(classify_negative_control("jit-diff", detector))
        else:
            record = {"status": "fail", "errors": ["the JIT driver build failed"]}
        report["negative_controls"]["jit-diff"] = record
        FLOOR.write_report(report_path, report)

        report["panic_fuzz"] = run_panic_fuzz(tools, output, args, environment)
        FLOOR.write_report(report_path, report)

        build = libfuzzer_build(
            tools, args.toolchain, fuzz_target_dir, output, args.jobs, environment, build_timeout, rustflags,
        )
        report["builds"].append(build)
        FLOOR.write_report(report_path, report)
        if build["status"] == "pass":
            binaries = {target: libfuzzer_binary(fuzz_target_dir, target) for target in LIBFUZZER_TARGETS}
            report["libfuzzer"] = run_libfuzzer_campaign(binaries, output, args, libfuzzer_environment)
            FLOOR.write_report(report_path, report)

        if jit_built:
            print(f"Running JIT differential seeds {args.jit_seed_start}..+{args.jit_runs}", flush=True)
            record, _ = run_jit(
                jit_binary, output, "jit-diff", args.jit_seed_start, args.jit_runs, args.jit_duration,
                environment, args.max_rss_gib,
            )
            report["jit_diff"] = record
            print(f"{record['status'].upper()}: JIT differential", flush=True)
        report["final_source"] = FLOOR.source_provenance(tools["git"])
        if report["final_source"]["source_fingerprint"] != report["provenance"]["source"]["source_fingerprint"]:
            report["errors"].append("source changed while the lane was running")
        report["final_cargo_config"] = config_audit(environment, build_tool)
        report["errors"].extend(
            f"Cargo config changed while the lane was running: {change}"
            for change in CONFIG_AUDIT.changes(cargo_config, report["final_cargo_config"])
        )
    except (OSError, RuntimeError, subprocess.TimeoutExpired, ValueError) as error:
        report["errors"].append(str(error))
    except KeyboardInterrupt:
        report["errors"].append("interrupted; the lane is incomplete")
    report["status"] = overall_status(report)
    report["non_qualifying_reasons"] = qualification_problems(settings, report.get("provenance"))
    report["qualifying"] = report["status"] == "pass" and not report["non_qualifying_reasons"]
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    FLOOR.write_report(report_path, report)
    code = exit_code(report)
    label = report["status"].upper()
    if report["status"] == "pass" and not report["qualifying"]:
        label += " (NON-QUALIFYING: " + "; ".join(report["non_qualifying_reasons"]) + ")"
    print(f"Linux fuzz lane: {label} ({report_path})")
    for error in report["errors"]:
        print(error, file=sys.stderr)
    return code


if __name__ == "__main__":
    raise SystemExit(main())
