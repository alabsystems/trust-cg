#!/usr/bin/env python3
"""Require the bounded Linux AArch64 rustc-bridge native regressions.

Nine targets are required: the C aggregate ABI regression, the ELF
thread-local (TLS) lane, Rust panic unwind/cleanup, panic-hook effects, and
executable trap-stub refusals, plus scalar-owner zero-size field addresses,
and the Linux runtime twins of the Darwin static-data, Box/Vec drop and heap,
and coroutine-generator fixtures (CG and LLVM executables at O0-O3 with
exactly equal outputs; certificates off, so testing evidence). This is
separate from check_linux_aarch64.py's root-workspace targets. It always asks
pinned Cargo to build the current standalone backend before testing the exact
resulting library with every target. Passing is native regression evidence,
not complete FnAbi, TLS or unwind support, frontend qualification, proof
authority, or Trust self-hosting.
The cross-backend ABI differential (scripts/check_linux_aarch64_xback.py:
abi-xback, the AAPCS64 signature families, regclass-xback and sret-xback,
LLVM and this backend on either side of every call at O0-O3) is required
too: it runs against the same backend snapshot, and its report must pass
that runner's own verdict, bound to the snapshot's hash and this compiler.
The AY solver and Clean checker that the backend's proof replay will see are
recorded as proof_tools/final_proof_tools with executable hashes;
--require-proof-tools refuses to run unless both resolve through a pinned
route (see scripts/check_linux_aarch64.py).
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
import stat
import subprocess
import sys
import tempfile
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "crates/rustc-codegen-trust-cg/Cargo.toml"
PIN = MANIFEST.parent / "rust-toolchain.toml"
TARGET = "aarch64_c_fnabi_aggregate_linux"
TLS_TARGET = "tls_thread_local_linux"
UNWIND_TARGET = "unwind_cleanup_linux"
PANIC_TARGET = "panic_hook_differential"
TRAP_TARGET = "executable_trap_stub_routes_aarch64"
ZST_TARGET = "scalar_zst_field_differential"
STATIC_TARGET = "static_data_linux"
HEAP_TARGET = "drop_heap_linux"
COROUTINE_TARGET = "coroutine_generator_linux"
REQUIRED_TARGETS = (
    TARGET, TLS_TARGET, UNWIND_TARGET, PANIC_TARGET, TRAP_TARGET, ZST_TARGET,
    STATIC_TARGET, HEAP_TARGET, COROUTINE_TARGET,
)
HOST = "aarch64-unknown-linux-gnu"
BACKEND_NAME = "librustc_codegen_trust_cg.so"
MARKER = "TCG_BRIDGE_NATIVE_EXECUTION "
TLS_MARKER = "TCG_BRIDGE_TLS_EXECUTION "
UNWIND_MARKER = "TCG_BRIDGE_UNWIND_EXECUTION "
ZST_MARKER = "TCG_BRIDGE_SCALAR_ZST_EXECUTION "
STATIC_MARKER = "TCG_BRIDGE_STATIC_DATA_EXECUTION "
HEAP_MARKER = "TCG_BRIDGE_DROP_HEAP_EXECUTION "
COROUTINE_MARKER = "TCG_BRIDGE_COROUTINE_EXECUTION "
# The runtime twins' native obligations (tests/support/linux_runtime_twin.rs).
# Each lane is one linked executable, (fixture, compiler, level), run at least
# RUNTIME_RUNS_FLOOR times; every run's ending ("exit:N" / "signal:N") is the
# fixture's and its stdout digest is the fixture's model digest, so the CG and
# LLVM executables of a twinned fixture agree exactly. Every bridge compile
# is certificates-off (no-proof-certs) and every compile frontend-verify-off:
# the markers must say so, and the knob traces must be exactly these.
RUNTIME_RUNS_FLOOR = 3
RUNTIME_LANE_KEYS = frozenset({
    "fixture", "compiler", "opt_level", "runs", "passes", "ending", "stdout_sha256",
})
BOTH = ("cg", "llvm")
# fixture -> (compilers, levels, ending)
STATIC_LANES = {
    "immutable": (BOTH, range(4), "exit:0"),
    "readonly_store": (BOTH, range(4), "signal:11"),
    "mutable": (BOTH, range(4), "exit:0"),
    "overaligned": (BOTH, range(4), "exit:0"),
    "misaligned_exclusive": (BOTH, range(4), "signal:7"),
    "externs": (BOTH, range(4), "exit:0"),
    "layout": (BOTH, range(4), "exit:0"),
    "out_of_bounds": (BOTH, range(4), "signal:6"),
}
# The independently counted storage classes of the static target's 21
# #[no_mangle] statics, and its pointer slots (8 in those statics, 4 naming
# the extern statics).
STATIC_STORAGE_COUNTS = {"ReadOnly": 9, "Data": 6, "Bss": 1, "Relocated": 5}
STATIC_POINTER_RELOCATIONS = 12
HEAP_LANES = {
    "hooked": (("cg",), range(4), "exit:0"),
    "hooked_per_function": (("cg",), range(1), "exit:0"),
    "indirect": (("cg",), range(4), "exit:0"),
    "archive_c1": (BOTH, range(4), "exit:0"),
    "archive_c4": (BOTH, range(4), "exit:0"),
    "events": (BOTH, range(4), "exit:0"),
    "refused": (("llvm",), range(4), "exit:0"),
}
COROUTINE_LANES = {
    "sequence": (BOTH, range(4), "exit:0"),
    "resume_after_complete": (BOTH, range(4), "signal:6"),
    "shapes": (BOTH, range(4), "exit:0"),
    "refused": (("llvm",), range(4), "exit:0"),
}
# name -> (control name, refusal rows) of each target's per-level refusal
# control: the bridge refuses the crate by exact row and defines none of the
# refused functions; LLVM runs the same crate to its model.
RUNTIME_REFUSAL_CONTROLS = {
    HEAP_TARGET: ("refused_drop_glue", 2),
    COROUTINE_TARGET: ("refused_coroutines", 3),
}
# target -> (exact libtest passes, exact knob trace lines)
RUNTIME_SUITES = {
    STATIC_TARGET: (3, ["TCG_BRIDGE_BACKEND_KNOBS knobs=no-proof-certs"] * 20),
    HEAP_TARGET: (3, ["TCG_BRIDGE_BACKEND_KNOBS knobs=no-proof-certs"] * 24
                  + ["TCG_BRIDGE_BACKEND_KNOBS knobs=no-proof-certs batch-cgu=0"]),
    COROUTINE_TARGET: (3, ["TCG_BRIDGE_BACKEND_KNOBS knobs=no-proof-certs"] * 16),
}
# The TLS target's native obligations: CG and LLVM executables of the same
# #[thread_local] crate at O0-O3, each executed at least TLS_RUNS_FLOOR times;
# the plain-static shared-storage control for both compilers at every level;
# and the #[link_section] refusal control at every level. The accessor's
# observed ELF TLS access model is recorded, and at every level the CG objects
# must carry exactly the TLS relocation kinds of the LLVM twin: the model
# follows the session's relocation model (target-default PIC for this
# staticlib, hence the TLS descriptor), and the bridge must not choose another.
TLS_COMPILERS = ("cg", "llvm")
TLS_RUNS_FLOOR = 5
# The complete AArch64 ELF relocation sequence of each access model.
TLS_ACCESS_MODELS = {
    "general-dynamic-tlsdesc": (
        "R_AARCH64_TLSDESC_ADR_PAGE21", "R_AARCH64_TLSDESC_LD64_LO12",
        "R_AARCH64_TLSDESC_ADD_LO12", "R_AARCH64_TLSDESC_CALL",
    ),
    "initial-exec": ("R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21", "R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC"),
    "local-exec": ("R_AARCH64_TLSLE_ADD_TPREL_HI12", "R_AARCH64_TLSLE_ADD_TPREL_LO12_NC"),
}
# read_x and bump_x each reach the thread-local at least once.
TLS_ACCESS_SEQUENCE_FLOOR = 2
TLS_DEFINITION_SECTIONS = (".tdata", ".tbss")
TLS_UNSUPPORTED_CONTROLS = ("link_section",)
TLS_SHARED_STORAGE_EXIT = 3
TLS_LANE_KEYS = frozenset({
    "compiler", "opt_level", "runs", "passes", "tls_definers", "linked_objects",
    "excluded_objects", "abort_stubs", "tls_relocations",
})
TLS_CG_LANE_KEYS = TLS_LANE_KEYS | {
    "definition_section", "accessor_objects", "access_model", "access_sequences",
}
# The unwind target's native obligations: CG and LLVM executables of the same
# crate at O0-O3, each run at least UNWIND_RUNS_FLOOR times with the exact
# per-run driver totals below; for every bridge fixture function at every
# level, a missing-landing-pad control losing exactly that frame's drops and
# frees; and the `disable-unwind` refusal naming every fixture function.
UNWIND_COMPILERS = ("cg", "llvm")
UNWIND_RUNS_FLOOR = 3
UNWIND_PER_RUN = {"calls": 5, "panics": 3, "caught": 3, "drop_events": 10, "box_frees": 7}
# function -> (the callee its landing pad protects, lost drop events, lost box frees)
UNWIND_FIXTURES = {
    "box_across_unwind": ("ay_may_unwind", 0, 1),
    "guards_across_unwind": ("ay_unwind_if", 4, 2),
    "nested_unwind": ("guards_across_unwind", 1, 1),
}
UNWIND_PERSONALITY = "rust_eh_personality"
# LLVM may remove the allocation of the fixture's never-read boxes (one
# Box<i32> and two Box<i64> per run); a bridge lane must show every free.
UNWIND_ELIDABLE_BOX_FREES = 3
UNWIND_LANE_KEYS = frozenset({
    "compiler", "opt_level", "runs", "passes", "linked_objects", "excluded_objects",
    "elided_box_frees", *UNWIND_PER_RUN,
})
UNWIND_CG_LANE_KEYS = UNWIND_LANE_KEYS | {"eh_functions", "personality", "resume_calls"}
UNWIND_CONTROL_KEYS = frozenset({
    "function", "callee", "opt_level", "lsda_rows", "landing_pad", "mutated_rows", "exit_code",
    "lost_drops", "lost_frees",
})
UNWIND_REFUSAL_KEYS = frozenset({
    "name", "opt_level", "cg_refusals", "refused_functions", "fixture_definitions",
})
# Minimum native (calls, checks) for EACH compiler/optimization lane. These
# independently counted floors preserve the bit-pattern/repetition corpus, not
# merely the presence of each family name. They exclude the separate HFA matrix.
SCALAR_CELL_FLOORS = {
    "aliased_f32_read": (17, 238), "aliased_f32_write": (17, 238),
    "aliased_f64_read": (17, 238), "aliased_f64_write": (17, 238),
    "local_cell_read": (17, 238), "local_cell_read_f32": (17, 238),
    "projected_cell_result": (17, 357),
    "repeated_cell_f32": (17, 680), "repeated_cell_f64": (17, 680),
    "repeated_cell_u64": (17, 680),
    "branch_loop_cell_f32": (102, 3808), "branch_loop_cell_f64": (102, 3808),
    # A promoted certificates-on positive on its own C driver (4,001 calls),
    # no longer a refusal control (ruling LD-93).
    "zst_sibling_cell": (4001, 4001),
}
SCALAR_CELL_FAMILIES = tuple(SCALAR_CELL_FLOORS)
UNSUPPORTED_SCALAR_CELL_BOUNDARIES = (
    "mixed_return", "projected_borrow", "overaligned_cell",
    "packed_cell", "hfa_middle_borrow",
)

_spec = importlib.util.spec_from_file_location(
    "_linux_aarch64_bridge_shared", ROOT / "scripts/check_linux_aarch64.py"
)
assert _spec is not None and _spec.loader is not None
SHARED = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(SHARED)


def _load_trust_toolchain():
    spec = importlib.util.spec_from_file_location(
        "trust_cg_trust_toolchain_for_bridge_gate", ROOT / "scripts" / "trust_toolchain.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def pinned_toolchain(path: Path = PIN) -> str:
    # Shared [toolchain] reader: tomllib where available, a bounded fallback on
    # Python < 3.11, so the gate and its tests run on the system python3.
    toolchain = _load_trust_toolchain()
    try:
        channel = toolchain._toolchain_table(path.read_text()).get("channel")
    except toolchain.ToolchainError as error:
        raise ValueError(str(error)) from error
    if channel == "trust":
        return channel
    # The backend is built by and loaded into the installed Trust package; the
    # retired stock nightly-2026-04-20 lane (and every other stock channel) is
    # refused, never driven through rustup.
    raise ValueError(f"bridge toolchain must pin exactly channel = \"trust\", found {channel!r}")


def backend_identity(path: Path) -> dict:
    before = path.lstat()
    if not stat.S_ISREG(before.st_mode):
        raise RuntimeError(f"backend must be a regular file, not a symlink: {path}")
    digest = hashlib.sha256()
    # Do not follow a replacement symlink, or block on a replacement FIFO,
    # between the path check and opening the actual bytes.
    with os.fdopen(os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK), "rb") as source:
        if backend_stat(before) != backend_stat(os.fstat(source.fileno())):
            raise RuntimeError(f"backend changed while opening: {path}")
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
        if backend_stat(before) != backend_stat(os.fstat(source.fileno())):
            raise RuntimeError(f"backend changed while hashing: {path}")
    after = path.lstat()
    if backend_stat(before) != backend_stat(after) or before.st_size == 0:
        raise RuntimeError(f"backend is empty or changed while hashing: {path}")
    return {
        "path": str(path), "sha256": digest.hexdigest(), "size": before.st_size,
        "stat": backend_stat(before),
    }


def backend_stat(info: os.stat_result) -> dict:
    return {
        "device": info.st_dev, "inode": info.st_ino, "mode": info.st_mode,
        "links": info.st_nlink, "size": info.st_size,
        "modified_ns": info.st_mtime_ns, "changed_ns": info.st_ctime_ns,
    }


def snapshot_backend(source: Path, destination: Path, expected: dict) -> dict:
    """Copy the identified successful-build artifact, never a Cargo cache alias."""
    before = source.lstat()
    if expected["path"] != str(source) or backend_stat(before) != expected["stat"]:
        raise RuntimeError("built backend changed before snapshot creation")
    digest = hashlib.sha256()
    size = 0
    with os.fdopen(os.open(source, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK), "rb") as reader:
        if backend_stat(os.fstat(reader.fileno())) != expected["stat"]:
            raise RuntimeError("built backend changed while opening snapshot source")
        # Exclusive creation also refuses preexisting files and symlinks. This
        # is a separate inode, not a hard link into Cargo's mutable build cache.
        with destination.open("xb") as writer:
            copied_stat = os.fstat(writer.fileno())
            if (not stat.S_ISREG(copied_stat.st_mode) or copied_stat.st_nlink != 1
                    or (copied_stat.st_dev, copied_stat.st_ino) == (before.st_dev, before.st_ino)):
                raise RuntimeError("backend snapshot must be a new independent regular file")
            for chunk in iter(lambda: reader.read(1024 * 1024), b""):
                writer.write(chunk)
                digest.update(chunk)
                size += len(chunk)
            writer.flush()
            os.fchmod(writer.fileno(), 0o444)
            os.fsync(writer.fileno())
        if backend_stat(os.fstat(reader.fileno())) != expected["stat"]:
            raise RuntimeError("built backend changed during snapshot copy")
    if digest.hexdigest() != expected["sha256"] or size != expected["size"]:
        raise RuntimeError("backend snapshot bytes do not match the identified build")
    if backend_identity(source) != expected:
        raise RuntimeError("built backend changed during snapshot creation")
    observed = backend_identity(destination)
    if (observed["sha256"] != expected["sha256"] or observed["size"] != expected["size"]
            or observed["stat"]["mode"] != (stat.S_IFREG | 0o444)
            or observed["stat"]["links"] != 1):
        raise RuntimeError("backend snapshot identity changed after copying")
    return observed


def classify_build(returncode: int, transcript: str, manifest: Path, backend: Path) -> dict:
    errors = []
    records = []
    for line in transcript.splitlines():
        if not line.startswith("{"):
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict):
            records.append(value)
    finished = [row for row in records if row.get("reason") == "build-finished"]
    artifacts = [
        row for row in records
        if row.get("reason") == "compiler-artifact"
        and row.get("manifest_path") == str(manifest)
        and isinstance(row.get("target"), dict)
        and row["target"].get("name") == "rustc_codegen_trust_cg"
        and row["target"].get("kind") == ["dylib"]
    ]
    if returncode != 0:
        errors.append(f"locked backend build exited {returncode}")
    if len(finished) != 1 or finished[0].get("success") is not True:
        errors.append("expected exactly one successful Cargo build-finished record")
    if len(artifacts) != 1 or artifacts[0].get("filenames") != [str(backend)]:
        errors.append("Cargo did not identify exactly the required release backend artifact")
    return {
        "status": "fail" if errors else "pass", "errors": errors,
        "cargo_artifact": artifacts[0] if len(artifacts) == 1 else None,
    }


def classify_test_build(returncode: int, transcript: str, target_dir: Path) -> dict:
    """Select exactly one test executable per required target from a successful Cargo build."""
    records = []
    for line in transcript.splitlines():
        if not line.startswith("{"):
            continue
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict):
            records.append(value)
    finished = [row for row in records if row.get("reason") == "build-finished"]
    errors = []
    identities = {}
    if returncode != 0:
        errors.append(f"locked test build exited {returncode}")
    if len(finished) != 1 or finished[0].get("success") is not True:
        errors.append("expected exactly one successful Cargo test build-finished record")
    for target in REQUIRED_TARGETS:
        artifacts = [row for row in records
                     if row.get("reason") == "compiler-artifact"
                     and row.get("manifest_path") == str(MANIFEST)
                     and isinstance(row.get("target"), dict)
                     and row.get("target", {}).get("name") == target
                     and row.get("target", {}).get("kind") == ["test"]
                     and isinstance(row.get("profile"), dict)
                     and row.get("profile", {}).get("test") is True]
        if len(artifacts) != 1:
            errors.append(f"Cargo did not identify exactly the required native test executable: {target}")
            continue
        executable = artifacts[0].get("executable")
        if not isinstance(executable, str) or not executable:
            errors.append(f"required native test artifact has no executable: {target}")
            continue
        path = Path(executable)
        if (not path.is_absolute() or path.parent != target_dir / "release/deps"
                or not path.name.startswith(target + "-")
                or artifacts[0].get("filenames") != [executable]
                or not os.access(path, os.X_OK)):
            errors.append(f"native test executable is not the required release artifact: {target}")
        else:
            identities[target] = backend_identity(path)
    return {"status": "fail" if errors else "pass", "errors": errors,
            "executable_identities": identities}


def scalar_cell_errors(execution: dict) -> list[str]:
    """Require every named native lane; refusals cannot substitute for execution."""
    errors = []
    coverage = execution.get("scalar_cell")
    if not isinstance(coverage, dict) or type(coverage.get("schema")) is not int or coverage["schema"] != 1:
        return ["expected scalar_cell coverage schema 1"]
    required_native = {
        (family, compiler, opt)
        for family in SCALAR_CELL_FAMILIES for compiler in ("cg", "llvm") for opt in range(4)
    }
    seen_native = set()
    native = coverage.get("native")
    if not isinstance(native, list):
        errors.append("scalar_cell.native must list every required native lane")
        native = []
    projected_calls = projected_checks = 0
    for row in native:
        if not isinstance(row, dict) or set(row) != {"family", "compiler", "opt_level", "calls", "checks"}:
            errors.append("malformed scalar-cell native lane")
            continue
        if (not isinstance(row["family"], str) or not isinstance(row["compiler"], str)
                or type(row["opt_level"]) is not int):
            errors.append("scalar-cell native lane requires a named family/compiler and integer optimization level")
            continue
        key = (row["family"], row["compiler"], row["opt_level"])
        if key not in required_native or key in seen_native:
            errors.append(f"unexpected or duplicate scalar-cell native lane: {key}")
        seen_native.add(key)
        if any(type(row[name]) is not int or row[name] <= 0 for name in ("calls", "checks")):
            errors.append(f"scalar-cell native lane must execute positive calls and checks: {key}")
        else:
            floor = SCALAR_CELL_FLOORS.get(row["family"])
            if floor is not None:
                for name, minimum in zip(("calls", "checks"), floor):
                    if row[name] < minimum:
                        errors.append(f"scalar-cell native lane must preserve its {name} floor ({minimum}): {key}")
            if row["family"] == "projected_cell_result":
                projected_calls += row["calls"]
                projected_checks += row["checks"]
    missing = required_native - seen_native
    if missing:
        errors.append(f"missing required scalar-cell native lanes: {sorted(missing)}")

    required_unsupported = {
        (name, opt) for name in UNSUPPORTED_SCALAR_CELL_BOUNDARIES for opt in range(4)
    }
    seen_unsupported = set()
    unsupported = coverage.get("unsupported")
    if not isinstance(unsupported, list):
        errors.append("scalar_cell.unsupported must list every retained refusal control")
        unsupported = []
    for row in unsupported:
        if not isinstance(row, dict) or set(row) != {"name", "opt_level", "cg_refusals", "llvm_objects"}:
            errors.append("malformed scalar-cell unsupported control")
            continue
        if not isinstance(row["name"], str) or type(row["opt_level"]) is not int:
            errors.append("scalar-cell unsupported control requires a name and integer optimization level")
            continue
        key = (row["name"], row["opt_level"])
        if key not in required_unsupported or key in seen_unsupported:
            errors.append(f"unexpected or duplicate scalar-cell unsupported control: {key}")
        seen_unsupported.add(key)
        if any(type(row[name]) is not int or row[name] != 1 for name in ("cg_refusals", "llvm_objects")):
            errors.append(f"unsupported control requires one exact CG refusal and valid LLVM object control: {key}")
    missing = required_unsupported - seen_unsupported
    if missing:
        errors.append(f"missing retained scalar-cell unsupported controls: {sorted(missing)}")
    # Retain the existing summaries, but bind them to the explicit obligations
    # instead of accepting an aggregate refusal/control denominator as coverage.
    summaries = {
        "refusals": len(required_unsupported), "projected_cell_controls": 4,
        "projected_cell_refusals": 0, "projected_cell_native_executions": 8,
        "projected_cell_native_calls": projected_calls,
        "projected_cell_native_checks": projected_checks,
    }
    for name, required in summaries.items():
        if type(execution.get(name)) is not int or execution[name] != required:
            errors.append(f"native execution summary {name} must match required scalar-cell coverage ({required})")
    return errors


def classify_native(returncode: int, transcript: str, backend_sha256: str) -> dict:
    verdict = SHARED.classify_result(returncode, transcript)
    errors = verdict["errors"]
    markers = [line[len(MARKER):] for line in transcript.splitlines() if line.startswith(MARKER)]
    execution = None
    if len(markers) != 1:
        errors.append("expected exactly one structured native-execution marker")
    else:
        try:
            execution = json.loads(markers[0])
        except json.JSONDecodeError:
            errors.append("malformed native-execution marker")
        if not isinstance(execution, dict):
            errors.append("native-execution marker must be an object")
        else:
            levels = execution.get("opt_levels")
            if (execution.get("target") != HOST or levels != [0, 1, 2, 3]
                    or not isinstance(levels, list)
                    or any(type(level) is not int for level in levels)):
                errors.append("native execution must cover exact Linux AArch64 and O0-O3")
            for key in ("executions", "calls", "checks"):
                if type(execution.get(key)) is not int or execution[key] <= 0:
                    errors.append(f"native execution must report a positive integer {key} count")
            if type(execution.get("executions")) is int and execution["executions"] < 8:
                errors.append("native execution requires both CG and LLVM twins at all four optimization levels")
            floors = {"matrix_calls": 9216, "matrix_checks": 149376, "mutation_calls": 512, "mutation_checks": 2560}
            for name, minimum in floors.items():
                if type(execution.get(name)) is not int or execution[name] < minimum:
                    errors.append(f"native execution must preserve the original {name} floor ({minimum})")
            for name in ("calls", "checks"):
                components = [execution.get(f"matrix_{name}"), execution.get(f"mutation_{name}")]
                if all(type(value) is int for value in components) and execution.get(name) != sum(components):
                    errors.append(f"native execution {name} must equal its matrix and mutation components")
            errors.extend(scalar_cell_errors(execution))
            if execution.get("backend_sha256") != backend_sha256:
                errors.append("native-execution marker does not bind the built backend hash")
    verdict.update(status="fail" if errors else "pass", execution=execution)
    return verdict


def _count(value) -> bool:
    return type(value) is int and value >= 0


def tls_execution_errors(execution: dict, backend_sha256: str) -> list[str]:
    """Require every named TLS lane, control and refusal; none substitutes for another."""
    if type(execution.get("schema")) is not int or execution["schema"] != 1:
        return ["expected TLS execution schema 1"]
    errors = []
    levels = execution.get("opt_levels")
    if (execution.get("target") != HOST or not isinstance(levels, list)
            or any(type(level) is not int for level in levels) or levels != [0, 1, 2, 3]):
        errors.append("TLS execution must cover exact Linux AArch64 and O0-O3")
    runs = execution.get("runs_per_lane")
    if type(runs) is not int or runs < TLS_RUNS_FLOOR:
        errors.append(f"TLS execution must run every lane at least {TLS_RUNS_FLOOR} times")
    if execution.get("backend_sha256") != backend_sha256:
        errors.append("TLS execution marker does not bind the built backend hash")

    required = {(compiler, opt) for compiler in TLS_COMPILERS for opt in range(4)}
    seen = set()
    observed_relocations = {}
    lanes = execution.get("lanes")
    if not isinstance(lanes, list):
        errors.append("TLS lanes must list every required compiler and optimization level")
        lanes = []
    for row in lanes:
        if (not isinstance(row, dict) or row.get("compiler") not in TLS_COMPILERS
                or set(row) != (TLS_CG_LANE_KEYS if row["compiler"] == "cg" else TLS_LANE_KEYS)
                or type(row["opt_level"]) is not int):
            errors.append("malformed TLS lane")
            continue
        key = (row["compiler"], row["opt_level"])
        if key not in required or key in seen:
            errors.append(f"unexpected or duplicate TLS lane: {key}")
        seen.add(key)
        if not all(_count(row[name]) for name in (
                "runs", "passes", "tls_definers", "linked_objects", "excluded_objects", "abort_stubs")):
            errors.append(f"TLS lane counts must be nonnegative integers: {key}")
            continue
        if row["runs"] < TLS_RUNS_FLOOR or row["passes"] != row["runs"] or row["runs"] != runs:
            errors.append(f"TLS lane must pass every one of at least {TLS_RUNS_FLOOR} native runs: {key}")
        if row["tls_definers"] != 1 or row["linked_objects"] < 1:
            errors.append(f"TLS lane must link exactly one thread-local definition: {key}")
        relocations = row["tls_relocations"]
        if (not isinstance(relocations, list) or not relocations
                or any(not isinstance(name, str) or not name.startswith("R_AARCH64_TLS")
                       for name in relocations)):
            errors.append(f"TLS lane must record its observed TLS relocations: {key}")
            continue
        observed_relocations[key] = sorted(relocations)
        if row["compiler"] != "cg":
            continue
        model = row["access_model"]
        if not isinstance(model, str) or model not in TLS_ACCESS_MODELS:
            errors.append(f"CG TLS lane must use a complete ELF TLS access model: {key}")
        elif sorted(relocations) != sorted(TLS_ACCESS_MODELS[model]):
            errors.append(f"CG TLS relocations must be exactly the {model} sequence: {key}")
        if row["definition_section"] not in TLS_DEFINITION_SECTIONS:
            errors.append(f"CG thread-local must be defined in .tdata or .tbss: {key}")
        if type(row["accessor_objects"]) is not int or row["accessor_objects"] < 1:
            errors.append(f"CG TLS lane must inspect its accessor objects: {key}")
        sequences = row["access_sequences"]
        if type(sequences) is not int or sequences < TLS_ACCESS_SEQUENCE_FLOOR:
            errors.append(
                f"CG TLS lane must preserve its access-sequence floor ({TLS_ACCESS_SEQUENCE_FLOOR}): {key}")
    if required - seen:
        errors.append(f"missing required TLS lanes: {sorted(required - seen)}")
    for opt in range(4):
        cg, llvm = observed_relocations.get(("cg", opt)), observed_relocations.get(("llvm", opt))
        if cg is not None and llvm is not None and cg != llvm:
            errors.append(f"CG TLS relocations must match the LLVM twin's access model: O{opt}")

    seen = set()
    controls = execution.get("shared_storage_controls")
    if not isinstance(controls, list):
        errors.append("TLS shared-storage controls must list every compiler and optimization level")
        controls = []
    for row in controls:
        if (not isinstance(row, dict) or set(row) != {"compiler", "opt_level", "exit_code"}
                or not isinstance(row["compiler"], str) or type(row["opt_level"]) is not int):
            errors.append("malformed TLS shared-storage control")
            continue
        key = (row["compiler"], row["opt_level"])
        if key not in required or key in seen:
            errors.append(f"unexpected or duplicate TLS shared-storage control: {key}")
        seen.add(key)
        if type(row["exit_code"]) is not int or row["exit_code"] != TLS_SHARED_STORAGE_EXIT:
            errors.append(f"shared-storage control must be detected by the driver: {key}")
    if required - seen:
        errors.append(f"missing TLS shared-storage controls: {sorted(required - seen)}")

    required = {(name, opt) for name in TLS_UNSUPPORTED_CONTROLS for opt in range(4)}
    seen = set()
    unsupported = execution.get("unsupported")
    if not isinstance(unsupported, list):
        errors.append("TLS unsupported controls must list every retained refusal")
        unsupported = []
    keys = {"name", "opt_level", "cg_refusals", "cg_item_definitions", "cg_leftover_objects", "llvm_objects"}
    for row in unsupported:
        if (not isinstance(row, dict) or set(row) != keys or not isinstance(row["name"], str)
                or type(row["opt_level"]) is not int):
            errors.append("malformed TLS unsupported control")
            continue
        key = (row["name"], row["opt_level"])
        if key not in required or key in seen:
            errors.append(f"unexpected or duplicate TLS unsupported control: {key}")
        seen.add(key)
        if (type(row["cg_refusals"]) is not int or row["cg_refusals"] != 1
                or type(row["llvm_objects"]) is not int or row["llvm_objects"] != 1
                or type(row["cg_item_definitions"]) is not int or row["cg_item_definitions"] != 0
                or not _count(row["cg_leftover_objects"])):
            errors.append(f"TLS refusal requires one exact CG refusal, no item object and a valid LLVM control: {key}")
    if required - seen:
        errors.append(f"missing TLS unsupported controls: {sorted(required - seen)}")
    return errors


def classify_tls_native(returncode: int, transcript: str, backend_sha256: str) -> dict:
    verdict = SHARED.classify_result(returncode, transcript)
    errors = verdict["errors"]
    markers = [line[len(TLS_MARKER):] for line in transcript.splitlines() if line.startswith(TLS_MARKER)]
    execution = None
    if len(markers) != 1:
        errors.append("expected exactly one structured TLS execution marker")
    else:
        try:
            execution = json.loads(markers[0])
        except json.JSONDecodeError:
            errors.append("malformed TLS execution marker")
        if not isinstance(execution, dict):
            errors.append("TLS execution marker must be an object")
        else:
            errors.extend(tls_execution_errors(execution, backend_sha256))
    verdict.update(status="fail" if errors else "pass", execution=execution)
    return verdict


def unwind_execution_errors(execution: dict, backend_sha256: str) -> list[str]:
    """Require every unwind lane, missing-pad control and refusal; none substitutes for another."""
    if type(execution.get("schema")) is not int or execution["schema"] != 1:
        return ["expected unwind execution schema 1"]
    errors = []
    levels = execution.get("opt_levels")
    if (execution.get("target") != HOST or not isinstance(levels, list)
            or any(type(level) is not int for level in levels) or levels != [0, 1, 2, 3]):
        errors.append("unwind execution must cover exact Linux AArch64 and O0-O3")
    runs = execution.get("runs_per_lane")
    if type(runs) is not int or runs < UNWIND_RUNS_FLOOR:
        errors.append(f"unwind execution must run every lane at least {UNWIND_RUNS_FLOOR} times")
    if execution.get("backend_sha256") != backend_sha256:
        errors.append("unwind execution marker does not bind the built backend hash")
    mir = execution.get("mir_cleanup_functions")
    if type(mir) is not int or mir != len(UNWIND_FIXTURES):
        errors.append("every fixture function's MIR must carry a cleanup edge")

    required = {(compiler, opt) for compiler in UNWIND_COMPILERS for opt in range(4)}
    seen = set()
    lanes = execution.get("lanes")
    if not isinstance(lanes, list):
        errors.append("unwind lanes must list every required compiler and optimization level")
        lanes = []
    for row in lanes:
        if (not isinstance(row, dict) or row.get("compiler") not in UNWIND_COMPILERS
                or set(row) != (UNWIND_CG_LANE_KEYS if row["compiler"] == "cg" else UNWIND_LANE_KEYS)
                or type(row["opt_level"]) is not int):
            errors.append("malformed unwind lane")
            continue
        key = (row["compiler"], row["opt_level"])
        if key not in required or key in seen:
            errors.append(f"unexpected or duplicate unwind lane: {key}")
        seen.add(key)
        counts = ("runs", "passes", "linked_objects", "excluded_objects", "elided_box_frees", *UNWIND_PER_RUN)
        if not all(_count(row[name]) for name in counts):
            errors.append(f"unwind lane counts must be nonnegative integers: {key}")
            continue
        if row["runs"] < UNWIND_RUNS_FLOOR or row["passes"] != row["runs"] or row["runs"] != runs:
            errors.append(f"unwind lane must pass every one of at least {UNWIND_RUNS_FLOOR} native runs: {key}")
        elided = row["elided_box_frees"]
        if elided > (0 if row["compiler"] == "cg" else UNWIND_ELIDABLE_BOX_FREES):
            errors.append(f"unwind lane may not omit a modelled box free: {key}")
        for name, per_run in UNWIND_PER_RUN.items():
            if name == "box_frees":
                per_run -= elided
            if row[name] != per_run * row["runs"]:
                errors.append(f"unwind lane {name} must be {per_run} per run: {key}")
        if row["linked_objects"] < 1 or row["excluded_objects"] > 1:
            errors.append(f"unwind lane may exclude only the allocator shim: {key}")
        if row["compiler"] != "cg":
            continue
        if type(row["eh_functions"]) is not int or row["eh_functions"] != len(UNWIND_FIXTURES):
            errors.append(f"CG unwind lane must inspect every fixture function's EH object: {key}")
        if row["personality"] != UNWIND_PERSONALITY:
            errors.append(f"CG unwind lane must use {UNWIND_PERSONALITY}: {key}")
        if type(row["resume_calls"]) is not int or row["resume_calls"] < len(UNWIND_FIXTURES):
            errors.append(f"every CG fixture function must call _Unwind_Resume: {key}")
    if required - seen:
        errors.append(f"missing required unwind lanes: {sorted(required - seen)}")

    required = {(function, opt) for function in UNWIND_FIXTURES for opt in range(4)}
    seen = set()
    controls = execution.get("missing_landing_pad_controls")
    if not isinstance(controls, list):
        errors.append("missing-landing-pad controls must list every fixture function and level")
        controls = []
    for row in controls:
        if (not isinstance(row, dict) or set(row) != UNWIND_CONTROL_KEYS
                or not isinstance(row["function"], str) or type(row["opt_level"]) is not int):
            errors.append("malformed missing-landing-pad control")
            continue
        key = (row["function"], row["opt_level"])
        if key not in required or key in seen:
            errors.append(f"unexpected or duplicate missing-landing-pad control: {key}")
            continue
        seen.add(key)
        callee, lost_drops, lost_frees = UNWIND_FIXTURES[row["function"]]
        if row["callee"] != callee:
            errors.append(f"missing-landing-pad control must remove the pad protecting {callee}: {key}")
        if (type(row["mutated_rows"]) is not int or row["mutated_rows"] != 1
                or type(row["landing_pad"]) is not int or row["landing_pad"] <= 0
                or type(row["lsda_rows"]) is not int or row["lsda_rows"] < 2):
            errors.append(f"missing-landing-pad control must zero exactly one real cleanup row: {key}")
        if type(row["exit_code"]) is not int or row["exit_code"] != 0:
            errors.append(f"missing-landing-pad control must still catch the panic: {key}")
        if ((row["lost_drops"], row["lost_frees"]) != (lost_drops, lost_frees)
                or any(type(row[name]) is not int for name in ("lost_drops", "lost_frees"))):
            errors.append(f"missing-landing-pad control must lose exactly the frame's modelled "
                          f"cleanups ({lost_drops} drops, {lost_frees} frees): {key}")
    if required - seen:
        errors.append(f"missing missing-landing-pad controls: {sorted(required - seen)}")

    required = {("disable_unwind", opt) for opt in range(4)}
    seen = set()
    unsupported = execution.get("unsupported")
    if not isinstance(unsupported, list):
        errors.append("unwind unsupported controls must list every retained refusal")
        unsupported = []
    for row in unsupported:
        if (not isinstance(row, dict) or set(row) != UNWIND_REFUSAL_KEYS or not isinstance(row["name"], str)
                or type(row["opt_level"]) is not int):
            errors.append("malformed unwind unsupported control")
            continue
        key = (row["name"], row["opt_level"])
        if key not in required or key in seen:
            errors.append(f"unexpected or duplicate unwind unsupported control: {key}")
        seen.add(key)
        if (type(row["cg_refusals"]) is not int or row["cg_refusals"] != 1
                or type(row["refused_functions"]) is not int or row["refused_functions"] != len(UNWIND_FIXTURES)
                or type(row["fixture_definitions"]) is not int or row["fixture_definitions"] != 0):
            errors.append(f"disable-unwind must refuse every fixture function and emit none: {key}")
    if required - seen:
        errors.append(f"missing unwind unsupported controls: {sorted(required - seen)}")
    return errors


def classify_unwind_native(returncode: int, transcript: str, backend_sha256: str) -> dict:
    verdict = SHARED.classify_result(returncode, transcript)
    errors = verdict["errors"]
    markers = [line[len(UNWIND_MARKER):] for line in transcript.splitlines() if line.startswith(UNWIND_MARKER)]
    execution = None
    if len(markers) != 1:
        errors.append("expected exactly one structured unwind execution marker")
    else:
        try:
            execution = json.loads(markers[0])
        except json.JSONDecodeError:
            errors.append("malformed unwind execution marker")
        if not isinstance(execution, dict):
            errors.append("unwind execution marker must be an object")
        else:
            errors.extend(unwind_execution_errors(execution, backend_sha256))
    verdict.update(status="fail" if errors else "pass", execution=execution)
    return verdict


def portable_bridge_gate():
    # Positive evidence, knob traces and exact outcome accounting are host
    # independent; reuse their owner instead of weakening Linux to pass counts.
    spec = importlib.util.spec_from_file_location(
        "_linux_portable_bridge_positive", ROOT / "scripts/check_darwin_aarch64_bridge.py")
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def classify_portable_bridge(name: str, returncode: int, transcript: str) -> dict:
    gate = portable_bridge_gate()
    target = next(row for row in gate.TARGETS if row.name == name)
    return gate.classify_target(target, returncode, transcript)


def classify_panic_native(returncode: int, transcript: str, backend_sha256: str) -> dict:
    return classify_portable_bridge(PANIC_TARGET, returncode, transcript)


def classify_trap_native(returncode: int, transcript: str, backend_sha256: str) -> dict:
    return classify_portable_bridge(TRAP_TARGET, returncode, transcript)


def classify_zst_native(returncode: int, transcript: str, backend_sha256: str) -> dict:
    """Require every independently called LLVM/CG layout and alias lane."""
    verdict = SHARED.classify_result(returncode, transcript)
    errors = verdict["errors"]
    if verdict["counts"] is not None and verdict["counts"]["passed"] != 1:
        errors.append("scalar ZST field suite must execute exactly its one required test")
    markers = [line[len(ZST_MARKER):] for line in transcript.splitlines() if line.startswith(ZST_MARKER)]
    execution = None
    if len(markers) != 1:
        errors.append("expected exactly one scalar ZST field execution marker")
    else:
        try:
            execution = json.loads(markers[0])
        except json.JSONDecodeError:
            errors.append("malformed scalar ZST field execution marker")
        if not isinstance(execution, dict):
            errors.append("scalar ZST field execution marker must be an object")
        else:
            if (type(execution.get("schema")) is not int or execution["schema"] != 1
                    or execution.get("target") != HOST
                    or type(execution.get("comparisons")) is not int or execution["comparisons"] != 8):
                errors.append("scalar ZST field execution requires schema 1 and all eight Linux comparisons")
            if execution.get("backend_sha256") != backend_sha256:
                errors.append("scalar ZST field execution must bind the current backend hash")
            if not isinstance(execution.get("compiler_sha256"), str) or not re.fullmatch(
                    r"[0-9a-f]{64}", execution["compiler_sha256"]):
                errors.append("scalar ZST field execution must record the compiler digest")
            if execution.get("certificates") != "off" or execution.get("frontend_verify") != "off":
                errors.append("scalar ZST field native diagnostics require explicit verification-off scope")
            required = {(compiler, panic, opt) for compiler in ("cg", "llvm")
                        for panic in ("abort", "unwind") for opt in range(4)}
            seen = set()
            lanes = execution.get("lanes")
            if not isinstance(lanes, list):
                errors.append("scalar ZST field execution must list every native lane")
                lanes = []
            keys = {"compiler", "panic", "opt_level", "executions", "driver_checks", "layout_checks", "callback_checks", "address_observations"}
            for lane in lanes:
                if not isinstance(lane, dict) or set(lane) != keys:
                    errors.append("scalar ZST field native lane has invalid fields")
                    continue
                if (lane["compiler"] not in ("cg", "llvm") or lane["panic"] not in ("abort", "unwind")
                        or type(lane["opt_level"]) is not int or lane["opt_level"] not in range(4)):
                    errors.append("scalar ZST field native lane has invalid compiler/panic/optimization")
                    continue
                key = (lane["compiler"], lane["panic"], lane["opt_level"])
                if key in seen:
                    errors.append("scalar ZST field native lane is duplicated")
                seen.add(key)
                for name, count in (("executions", 1), ("driver_checks", 57), ("layout_checks", 16), ("callback_checks", 10), ("address_observations", 40)):
                    if type(lane[name]) is not int or lane[name] != count:
                        errors.append(f"scalar ZST field lane must retain its exact {name} count ({count})")
            if seen != required:
                errors.append("scalar ZST field execution omitted a required native lane")
    knobs = [line for line in transcript.splitlines() if line.startswith("TCG_BRIDGE_BACKEND_KNOBS ")]
    if knobs != ["TCG_BRIDGE_BACKEND_KNOBS knobs=no-proof-certs"] * 8:
        errors.append("scalar ZST field execution requires eight exact certificates-off compiler traces")
    native = "TCG_NATIVE_RUNTIME_TEST NativeRun scalar_zst_field_matches_llvm certificates=off frontend_verify=off"
    if transcript.splitlines().count(native) != 1:
        errors.append("scalar ZST field execution requires its named native verification-off marker")
    verdict.update(status="fail" if errors else "pass", execution=execution)
    return verdict


def _sha256_text(value) -> bool:
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def runtime_lane_errors(execution: dict, backend_sha256: str, label: str, required: dict) -> list[str]:
    """The obligations every runtime twin shares; `required` maps each fixture
    to (compilers, levels, ending). No lane substitutes for another."""
    if type(execution.get("schema")) is not int or execution["schema"] != 1:
        return [f"expected {label} execution schema 1"]
    errors = []
    levels = execution.get("opt_levels")
    if (execution.get("target") != HOST or not isinstance(levels, list)
            or any(type(level) is not int for level in levels) or levels != [0, 1, 2, 3]):
        errors.append(f"{label} execution must cover exact Linux AArch64 and O0-O3")
    if execution.get("backend_sha256") != backend_sha256:
        errors.append(f"{label} execution marker does not bind the built backend hash")
    if execution.get("certificates") != "off" or execution.get("frontend_verify") != "off":
        errors.append(f"{label} native testing evidence must declare certificates and frontend verify off")
    runs = execution.get("runs_per_lane")
    if type(runs) is not int or runs < RUNTIME_RUNS_FLOOR:
        errors.append(f"{label} execution must run every lane at least {RUNTIME_RUNS_FLOOR} times")
    models = execution.get("model_sha256")
    if (not isinstance(models, dict) or set(models) != set(required)
            or not all(_sha256_text(value) for value in models.values())):
        errors.append(f"{label} execution must give one model digest per required fixture")
        models = {}
    wanted = {(fixture, compiler, opt) for fixture, (compilers, levels, _) in required.items()
              for compiler in compilers for opt in levels}
    seen = set()
    lanes = execution.get("lanes")
    if not isinstance(lanes, list):
        errors.append(f"{label} lanes must list every required fixture, compiler and level")
        lanes = []
    for row in lanes:
        if (not isinstance(row, dict) or set(row) != RUNTIME_LANE_KEYS
                or not isinstance(row["fixture"], str) or not isinstance(row["compiler"], str)
                or type(row["opt_level"]) is not int):
            errors.append(f"malformed {label} lane")
            continue
        key = (row["fixture"], row["compiler"], row["opt_level"])
        if key not in wanted or key in seen:
            errors.append(f"unexpected or duplicate {label} lane: {key}")
            continue
        seen.add(key)
        if (type(row["runs"]) is not int or type(row["passes"]) is not int
                or row["runs"] != runs or row["passes"] != row["runs"]):
            errors.append(f"{label} lane must pass every one of its {runs} native runs: {key}")
        if row["ending"] != required[row["fixture"]][2]:
            errors.append(f"{label} lane must end {required[row['fixture']][2]}: {key}")
        if not _sha256_text(row["stdout_sha256"]) or row["stdout_sha256"] != models.get(row["fixture"]):
            errors.append(f"{label} lane stdout must be the fixture's model: {key}")
    if wanted - seen:
        errors.append(f"missing required {label} lanes: {sorted(wanted - seen)}")
    return errors


def runtime_refusal_errors(execution: dict, label: str, name: str, rows: int) -> list[str]:
    """One exact bridge refusal per level, no refused definition, and the LLVM
    twin of the refused crate run to its model (its lanes are required above)."""
    errors = []
    seen = set()
    controls = execution.get("refusal_controls")
    if not isinstance(controls, list):
        return [f"{label} refusal controls must list every level"]
    keys = {"name", "opt_level", "cg_refusals", "refusal_rows", "cg_definitions", "llvm_runs"}
    for row in controls:
        if (not isinstance(row, dict) or set(row) != keys or row["name"] != name
                or type(row["opt_level"]) is not int or row["opt_level"] not in range(4)
                or row["opt_level"] in seen):
            errors.append(f"malformed, unexpected or duplicate {label} refusal control")
            continue
        seen.add(row["opt_level"])
        if (type(row["cg_refusals"]) is not int or row["cg_refusals"] != 1
                or type(row["refusal_rows"]) is not int or row["refusal_rows"] != rows
                or type(row["cg_definitions"]) is not int or row["cg_definitions"] != 0
                or type(row["llvm_runs"]) is not int or row["llvm_runs"] < RUNTIME_RUNS_FLOOR):
            errors.append(f"{label} refusal control requires {rows} exact refusal rows, no refused "
                          f"definition and an LLVM twin run: O{row['opt_level']}")
    if seen != set(range(4)):
        errors.append(f"missing {label} refusal controls: {sorted(set(range(4)) - seen)}")
    return errors


def static_object_errors(execution: dict) -> list[str]:
    errors = []
    objects = execution.get("objects")
    if not isinstance(objects, list):
        return ["static-data object facts must list every compiler and level"]
    keys = {"compiler", "opt_level", "statics", "pointer_relocations", "extern_imports",
            "abort_stubs", "storage"}
    storage = {}
    for row in objects:
        if (not isinstance(row, dict) or set(row) != keys or row["compiler"] not in BOTH
                or type(row["opt_level"]) is not int or row["opt_level"] not in range(4)):
            errors.append("malformed static-data object facts")
            continue
        key = (row["compiler"], row["opt_level"])
        if key in storage:
            errors.append(f"duplicate static-data object facts: {key}")
            continue
        classes = row["storage"]
        if (not isinstance(classes, dict) or len(classes) != sum(STATIC_STORAGE_COUNTS.values())
                or row["statics"] != len(classes)
                or {value: list(classes.values()).count(value) for value in set(classes.values())}
                != STATIC_STORAGE_COUNTS):
            errors.append(f"static-data storage classes must be the 21 statics' {STATIC_STORAGE_COUNTS}: {key}")
        if (row["pointer_relocations"] != STATIC_POINTER_RELOCATIONS or row["extern_imports"] != 2
                or not _count(row["abort_stubs"])):
            errors.append(f"static-data relocation slots must be {STATIC_POINTER_RELOCATIONS}: {key}")
        storage[key] = classes
    for opt in range(4):
        if ("cg", opt) not in storage or ("llvm", opt) not in storage:
            errors.append(f"missing static-data object facts: O{opt}")
        elif storage[("cg", opt)] != storage[("llvm", opt)]:
            errors.append(f"CG static storage classes must equal the LLVM twin's: O{opt}")
    return errors


def runtime_twin_errors(target: str, execution: dict, backend_sha256: str) -> list[str]:
    if target == STATIC_TARGET:
        errors = runtime_lane_errors(execution, backend_sha256, "static-data", STATIC_LANES)
        return errors + static_object_errors(execution)
    if target == HEAP_TARGET:
        errors = runtime_lane_errors(execution, backend_sha256, "drop-heap", HEAP_LANES)
        partitions = execution.get("partitions")
        if (not isinstance(partitions, list) or len(partitions) != 1 or not isinstance(partitions[0], dict)
                or set(partitions[0]) != {"opt_level", "batched_objects", "per_function_objects",
                                          "per_function_shared_entry_object"}
                or partitions[0]["opt_level"] != 0
                or type(partitions[0]["batched_objects"]) is not int
                or type(partitions[0]["per_function_objects"]) is not int
                or not partitions[0]["batched_objects"] < partitions[0]["per_function_objects"]
                or partitions[0]["per_function_shared_entry_object"] is not False):
            errors.append("drop-heap must run the batched and the per-function partitions at O0")
        return errors + runtime_refusal_errors(execution, "drop-heap", *RUNTIME_REFUSAL_CONTROLS[target])
    errors = runtime_lane_errors(execution, backend_sha256, "coroutine", COROUTINE_LANES)
    if execution.get("mir") != {"coroutine_frame": True, "set_discriminant": True, "yield_terminators": 0}:
        errors.append("coroutine MIR must be rustc's post-StateTransform state machine")
    refused = execution.get("refused_lanes")
    if not isinstance(refused, list):
        errors.append("coroutine execution must list the bridge's refused lanes")
    else:
        for row in refused:
            errors.append(f"the bridge refused a required coroutine lane (fail-closed, not a pass): {row}")
    return errors + runtime_refusal_errors(execution, "coroutine", *RUNTIME_REFUSAL_CONTROLS[target])


def classify_runtime_twin(target: str, marker: str, returncode: int, transcript: str,
                          backend_sha256: str) -> dict:
    passes, knobs = RUNTIME_SUITES[target]
    verdict = SHARED.classify_result(returncode, transcript, minimum=passes)
    errors = verdict["errors"]
    if verdict["counts"] is not None and verdict["counts"]["passed"] != passes:
        errors.append(f"{target} must execute exactly its {passes} tests")
    traces = sorted(line for line in transcript.splitlines() if line.startswith("TCG_BRIDGE_BACKEND_KNOBS "))
    if traces != sorted(knobs):
        errors.append(f"{target} requires exactly its {len(knobs)} certificates-off compiler knob traces")
    markers = [line[len(marker):] for line in transcript.splitlines() if line.startswith(marker)]
    execution = None
    if len(markers) != 1:
        errors.append(f"expected exactly one structured {target} execution marker")
    else:
        try:
            execution = json.loads(markers[0])
        except json.JSONDecodeError:
            errors.append(f"malformed {target} execution marker")
        if not isinstance(execution, dict):
            errors.append(f"{target} execution marker must be an object")
        else:
            errors.extend(runtime_twin_errors(target, execution, backend_sha256))
    verdict.update(status="fail" if errors else "pass", execution=execution)
    return verdict


def classify_static_native(returncode: int, transcript: str, backend_sha256: str) -> dict:
    return classify_runtime_twin(STATIC_TARGET, STATIC_MARKER, returncode, transcript, backend_sha256)


def classify_heap_native(returncode: int, transcript: str, backend_sha256: str) -> dict:
    return classify_runtime_twin(HEAP_TARGET, HEAP_MARKER, returncode, transcript, backend_sha256)


def classify_coroutine_native(returncode: int, transcript: str, backend_sha256: str) -> dict:
    return classify_runtime_twin(COROUTINE_TARGET, COROUTINE_MARKER, returncode, transcript, backend_sha256)


# The verdict always comes from the committed runner module; the command path
# is separate only so orchestration tests can stand in for the long run.
XBACK_VERDICT_MODULE = ROOT / "scripts/check_linux_aarch64_xback.py"
XBACK_RUNNER = XBACK_VERDICT_MODULE
XBACK_KEY = "cross_backend_abi"


def xback_gate():
    """The cross-backend runner, whose verdict this lane re-applies."""
    spec = importlib.util.spec_from_file_location("_linux_aarch64_xback_gate", XBACK_VERDICT_MODULE)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def classify_xback(returncode: int, report_path: Path, backend_sha256: str, compiler_path: str) -> dict:
    """Re-derive the cross-backend verdict from the runner's report.

    The runner's own status is necessary, not sufficient: its pinned verdict is
    applied again here with the snapshot hash this lane qualified, and the
    report must name the same compiler. Declines are carried into this lane's
    report by name.
    """
    errors = []
    try:
        data = json.loads(report_path.read_text())
    except (OSError, ValueError) as error:
        return {"status": "fail", "errors": [f"cross-backend report unreadable: {error}"]}
    if not isinstance(data, dict):
        return {"status": "fail", "errors": ["cross-backend report must be an object"]}
    if returncode != 0:
        errors.append(f"cross-backend runner exited {returncode}")
    if data.get("status") != "pass":
        errors.append(f"cross-backend runner status is {data.get('status')!r}, not 'pass'")
    gate = xback_gate()
    declines = None
    try:
        errors.extend(gate.verdict_errors(data, backend_sha256))
        # Listed from the cells themselves, not from the runner's own summary.
        declines = gate.decline_rows(gate.cell_records(data))
    except (KeyError, TypeError, AttributeError) as error:
        errors.append(f"malformed cross-backend report: {error!r}")
    if not isinstance(data.get("compiler"), dict) or data["compiler"].get("path") != compiler_path:
        errors.append("cross-backend report was produced by another compiler")
    return {
        "status": "fail" if errors else "pass", "errors": errors,
        "summary": data.get("summary"), "declines": declines,
        "report": str(report_path),
    }


# (target, report key, log name, classifier), in execution order.
TARGET_RUNS = (
    (TARGET, "test", "native.log", classify_native),
    (TLS_TARGET, "tls_test", "tls-native.log", classify_tls_native),
    (UNWIND_TARGET, "unwind_test", "unwind-native.log", classify_unwind_native),
    (PANIC_TARGET, "panic_test", "panic-hook-native.log", classify_panic_native),
    (TRAP_TARGET, "trap_test", "executable-trap-native.log", classify_trap_native),
    (ZST_TARGET, "zst_test", "scalar-zst-field-native.log", classify_zst_native),
    (STATIC_TARGET, "static_test", "static-data-native.log", classify_static_native),
    (HEAP_TARGET, "heap_test", "drop-heap-native.log", classify_heap_native),
    (COROUTINE_TARGET, "coroutine_test", "coroutine-native.log", classify_coroutine_native),
)


def preflight(target_dir: Path) -> dict:
    channel = pinned_toolchain()
    tools = {}
    names = ("git", "env", "cc", "readelf", "objdump", "sha256sum", "timeout", "mktemp")
    names += ("trustc", "targo")
    for name in names:
        tools[name] = shutil.which(name)
        if tools[name] is None:
            raise RuntimeError(f"required tool is missing: {name}")
    # A supplied backend is never an authority input to this runner. Cargo must
    # identify one after the current-source build, and the runner supplies the
    # test's complete path/hash contract itself.
    forbidden = (
        "TCG_TEST_BACKEND_PATH", "TCG_TEST_BACKEND_SHA256", "TCG_NO_PROOF_CERTS",
        "TCG_JIT_UNCHECKED", "RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
        "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_RUSTC",
        "CARGO_BUILD_RUSTC_WRAPPER", "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "CARGO_BUILD_TARGET",
        "TCG_OPT_LEVEL", "TRUST_CG_DISABLE_PASSES", "TRUST_CG_DISABLE_CFGSIMPLIFY_SUBPASSES",
        "TCG_DATAFLOW_INTEGRITY",
    )
    present = [name for name in forbidden if name in os.environ]
    if present:
        raise RuntimeError(f"bridge qualification rejects ambient compiler/backend/proof overrides: {present}")
    driver = "trustc"
    build_tool = "targo"
    launcher_target = _load_trust_toolchain().launcher_target
    for name in ("trustc", "targo"):
        path = Path(tools[name]).resolve(strict=True)
        # An atpkg launcher shim is followed to the package file it execs.
        target = launcher_target(path)
        if target is not None:
            path = target.resolve(strict=True)
        if not path.is_file() or not os.access(path, os.X_OK):
            raise RuntimeError(f"Trust tool is not an executable file: {path}")
        tools[name] = str(path)
    if Path(tools["trustc"]).parent != Path(tools["targo"]).parent:
        raise RuntimeError("PATH trustc and targo must resolve to the same installed package")
    compiler_command = [tools["trustc"]]
    build_command = [tools["targo"], "--unverified"]
    rustc = SHARED.probe([*compiler_command, "-vV"])
    hosts = re.findall(r"^host: (\S+)$", rustc, re.MULTILINE)
    if sys.platform != "linux" or hosts != [HOST]:
        raise RuntimeError(f"required pinned Linux host is {HOST}, observed {hosts!r} on {sys.platform}")
    if not re.search(r"^commit-hash: [0-9a-f]{40}$", rustc, re.MULTILINE):
        raise RuntimeError("pinned compiler did not provide a commit identity")
    if not re.search(r"^binary: trustc$", rustc, re.MULTILINE):
        raise RuntimeError("the trust channel must resolve the branded trustc driver")
    sysroot = SHARED.probe([*compiler_command, "--print", "sysroot"]).strip()
    sysroot = str(Path(sysroot).resolve(strict=True))
    if Path(sysroot) != Path(tools["trustc"]).parent.parent:
        raise RuntimeError("Trust compiler/sysroot package mismatch")
    target_lib = Path(sysroot) / "lib" / "rustlib" / HOST / "lib"
    if not target_lib.is_dir():
        raise RuntimeError(f"pinned Trust sysroot lacks native target libraries: {target_lib}")
    for component in ("rustc_middle", "rustc_codegen_ssa"):
        if not any(path.is_file() for path in target_lib.glob(f"lib{component}-*")):
            raise RuntimeError(f"Trust sysroot private crate missing: {component}")
    for target in REQUIRED_TARGETS:
        if not (MANIFEST.parent / "tests" / f"{target}.rs").is_file():
            raise RuntimeError(f"required complete bridge target is missing: {target}")
    if not XBACK_RUNNER.is_file():
        raise RuntimeError(f"required cross-backend ABI runner is missing: {XBACK_RUNNER}")
    if target_dir == ROOT or target_dir in ROOT.parents:
        raise RuntimeError("backend target directory must not be the source root or its ancestor")
    return {
        **SHARED.source_provenance(tools["git"]), "host": HOST, "tools": tools,
        "toolchain": channel, "toolchain_file_sha256": hashlib.sha256(PIN.read_bytes()).hexdigest(),
        "rustc": rustc,
        "compiler_driver": driver, "build_tool": build_tool,
        "compiler_command": compiler_command, "build_command": build_command,
        "compiler_path": tools.get("trustc"),
        "compiler_commit": re.search(r"^commit-hash: ([0-9a-f]{40})$", rustc, re.MULTILINE).group(1),
        "lane": "unverified",
        "cargo": SHARED.probe([*build_command, "--version"]),
        "sysroot": sysroot,
        # The Trust driver selects this exact host library directory.
        "target_lib_dir": str(target_lib),
        "installed_components": None,
        "cc": SHARED.probe([tools["cc"], "--version"]),
        "readelf": SHARED.probe([tools["readelf"], "--version"]),
        "objdump": SHARED.probe([tools["objdump"], "--version"]),
        "target_dir": str(target_dir), "manifest": str(MANIFEST),
        "configuration": {
            key: os.environ[key] for key in (
                "CARGO_TARGET_DIR", "CARGO_BUILD_TARGET_DIR", "CARGO_HOME", "RUSTUP_TOOLCHAIN",
                "TCG_SOLVER_PATH", "AY_SOLVER_PATH", "TCG_EXTERNAL_CLEAN_CHECKER", "TCG_CLEAN_CHECKER",
                "TCG_REFINE_SOLVER", "TCG_NO_PROOF_CACHE", "TCG_NO_CERT_STORE", "TCG_PROOF_CERT_STORE",
                "RUST_MIN_STACK", "XDG_CACHE_HOME",
            ) if key in os.environ
        },
    }


def ensure_unchanged_source(report: dict, name: str) -> None:
    observed = SHARED.source_provenance(report["provenance"]["tools"]["git"])
    report[name] = observed
    if observed["source_fingerprint"] != report["provenance"]["source_fingerprint"]:
        raise RuntimeError(f"source changed during bridge qualification ({name})")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--list", action="store_true", help="inspect the required targets; do not probe or build")
    parser.add_argument("--out", type=Path, help="new report directory outside the source tree")
    parser.add_argument("--target-dir", type=Path, default=MANIFEST.parent / "target", help="explicit Cargo cache directory; a locked build is always required")
    parser.add_argument("--timeout-seconds", type=SHARED.positive_seconds, default=1200.0, help="per-build/test process-group bound")
    parser.add_argument("--jobs", type=SHARED.positive_jobs, default=2)
    parser.add_argument(
        "--require-proof-tools", action="store_true",
        help="refuse to build or test unless the AY solver and the Clean checker both resolve through a "
             "pinned route (explicit override or aterm-style package prefix on PATH); without it an absent "
             "or unpinned tool is labelled and proof-replay refusals may stem from provisioning alone",
    )
    parser.add_argument(
        "--xback-timeout-seconds", type=SHARED.positive_seconds, default=14400.0,
        help="bound on the whole cross-backend ABI differential (each compile and run has its own bound)",
    )
    args = parser.parse_args(argv)
    if args.list:
        for target in REQUIRED_TARGETS:
            print(f"{MANIFEST} {target} (pinned locked release build required)")
        print(f"{XBACK_RUNNER} {XBACK_KEY} (the same backend snapshot, O0-O3, pinned counts)")
        return 0
    try:
        if args.out is None:
            output = Path(tempfile.mkdtemp(prefix="trust-cg-linux-aarch64-bridge-"))
        else:
            output = args.out.absolute()
            if output.resolve().is_relative_to(ROOT):
                raise OSError("report directory must be outside the source tree")
            output.mkdir(mode=0o700)
    except OSError as error:
        print(f"Linux AArch64 bridge gate: output error: {error}", file=sys.stderr)
        return 1
    report = {
        "schema": "trust-cg-linux-aarch64-bridge-v1",
        "scope": ("bounded native C HFA ABI, ELF thread-local and Rust panic unwind/cleanup "
                  "regressions, static-data, Box/Vec drop and heap and coroutine runtime twins "
                  "(certificates off: testing evidence) and the cross-backend ABI differential; not "
                  "full FnAbi, TLS, unwind, frontend, proof or self-host qualification"),
        "required_target": TARGET, "required_targets": list(REQUIRED_TARGETS),
        "status": "incomplete", "errors": [],
        "started_utc": datetime.now(timezone.utc).isoformat(),
    }
    report_path = output / "report.json"
    SHARED.write_report(report_path, report)
    print(f"Linux AArch64 bridge logs: {output}", flush=True)
    try:
        target_dir = args.target_dir.resolve()
        report["provenance"] = preflight(target_dir)
        provenance = report["provenance"]
        report["controls"] = {"require_proof_tools": args.require_proof_tools}
        report["proof_tools"] = SHARED.proof_tool_identities()
        tool_problems = SHARED.proof_tool_problems(report["proof_tools"])
        if tool_problems and args.require_proof_tools:
            raise RuntimeError("--require-proof-tools: " + "; ".join(tool_problems))
        for problem in tool_problems:
            print(f"Linux AArch64 bridge gate: proof tool not pinned, so proof-replay refusals may stem "
                  f"from provisioning alone: {problem}", file=sys.stderr)
        backend = target_dir / "release" / BACKEND_NAME
        prefix = [provenance["tools"]["env"], f"CARGO_TARGET_DIR={target_dir}"]
        # build.rs records this exact canonical RUSTC for native test drivers;
        # neither stage can drift to a stale rustup Trust link.
        prefix += [f"RUSTC={provenance['compiler_path']}", provenance["tools"]["targo"], "--unverified"]
        common = [
            "--manifest-path", str(MANIFEST), "--target-dir", str(target_dir),
            "--release", "--locked", "--color", "never", "-j", str(args.jobs),
        ]
        report["backend_before_build"] = backend_identity(backend) if backend.exists() else None
        SHARED.write_report(report_path, report)
        print("Building the current pinned release backend", flush=True)
        build_log = output / "build.log"
        result = SHARED.run_target(
            [*prefix, "build", *common, "--message-format=json-render-diagnostics"],
            build_log, args.timeout_seconds,
        )
        result.pop("counts", None)
        result.update(classify_build(result["returncode"], build_log.read_text(errors="replace"), MANIFEST, backend))
        if result["interrupted_signal"] is not None:
            result["status"] = "fail"
            result["errors"].append(f"build interrupted by signal {result['interrupted_signal']}")
        report["build"] = result
        ensure_unchanged_source(report, "source_after_build")
        SHARED.write_report(report_path, report)
        if result["status"] != "pass":
            raise RuntimeError("required current-source backend build failed; preexisting libraries cannot be reused")
        report["backend_after_build"] = backend_identity(backend)
        expected_sha = report["backend_after_build"]["sha256"]
        # Cargo test can legitimately rebuild the cache's release dylib for a
        # different build/test graph. Retain and test the exact successful-build
        # bytes in the fresh report directory instead. Read-only mode is an
        # accident guard; before/after identity checks remain mandatory.
        snapshot = output / BACKEND_NAME
        report["backend_snapshot"] = snapshot_backend(backend, snapshot, report["backend_after_build"])
        SHARED.write_report(report_path, report)
        # Test-only backend selection must never enter a compiler environment:
        # Trust correctly refuses untracked TCG_* codegen controls. Build first,
        # identify Cargo's exact executable, then set the pair only for that test.
        test_build_log = output / "test-build.log"
        test_targets = [argument for target in REQUIRED_TARGETS for argument in ("--test", target)]
        test_build = SHARED.run_target(
            [*prefix, "test", *common, *test_targets, "--no-run",
             "--message-format=json-render-diagnostics"],
            test_build_log, args.timeout_seconds,
        )
        test_build.pop("counts", None)
        test_build.update(classify_test_build(
            test_build["returncode"], test_build_log.read_text(errors="replace"), target_dir,
        ))
        if test_build["interrupted_signal"] is not None:
            test_build["status"] = "fail"
            test_build["errors"].append(f"test build interrupted by signal {test_build['interrupted_signal']}")
        report["test_build"] = test_build
        ensure_unchanged_source(report, "source_after_test_build")
        SHARED.write_report(report_path, report)
        if test_build["status"] != "pass":
            raise RuntimeError("required current-source native test build failed")
        identities = test_build["executable_identities"]
        for target in REQUIRED_TARGETS:
            if backend_identity(Path(identities[target]["path"])) != identities[target]:
                raise RuntimeError(f"native test executable changed before execution: {target}")
        # Portable fixtures select the backend beside their own executable.
        # Give them fresh independent copies beside a byte-identical snapshot;
        # the old override pair alone cannot bind their artifact selection.
        runtime_deps = output / "portable-runtime" / "deps"
        runtime_deps.mkdir(parents=True)
        runtime_backend = runtime_deps / BACKEND_NAME
        report["portable_backend_snapshot"] = snapshot_backend(
            snapshot, runtime_backend, report["backend_snapshot"],
        )
        runtime_executables = {}
        for target in (PANIC_TARGET, TRAP_TARGET, ZST_TARGET):
            original = identities[target]
            destination = runtime_deps / Path(original["path"]).name
            snapshot_backend(Path(original["path"]), destination, original)
            destination.chmod(0o555)
            runtime_executables[target] = backend_identity(destination)
        report["portable_runtime_executables"] = runtime_executables
        # Each required target runs to completion against the same snapshot,
        # whatever the others' verdicts; a failure of one never skips another.
        for target, key, log_name, classify in TARGET_RUNS:
            executable_identity = runtime_executables.get(target, identities[target])
            executable = Path(executable_identity["path"])
            command = [
                prefix[0], f"CARGO_TARGET_DIR={target_dir}",
                f"TCG_TEST_BACKEND_PATH={snapshot}", f"TCG_TEST_BACKEND_SHA256={expected_sha}",
                str(executable), "--show-output" if target in runtime_executables else "--nocapture",
                "--test-threads=1",
            ]
            print(f"Running the complete {target} target with backend {expected_sha}", flush=True)
            test_log = output / log_name
            if backend_identity(runtime_backend) != report["portable_backend_snapshot"]:
                raise RuntimeError(f"portable backend snapshot changed before native testing: {target}")
            report[f"backend_snapshot_before_{key}"] = backend_identity(snapshot)
            if report[f"backend_snapshot_before_{key}"] != report["backend_snapshot"]:
                raise RuntimeError(f"backend snapshot changed before native testing: {target}")
            result = SHARED.run_target(command, test_log, args.timeout_seconds)
            result.update(classify(result["returncode"], test_log.read_text(errors="replace"), expected_sha))
            if result["interrupted_signal"] is not None:
                result["status"] = "fail"
                result["errors"].append(f"test interrupted by signal {result['interrupted_signal']}")
            report[key] = result
            report[f"{key}_executable_after_test"] = backend_identity(executable)
            if report[f"{key}_executable_after_test"] != executable_identity:
                raise RuntimeError(f"native test executable changed during execution: {target}")
            if backend_identity(runtime_backend) != report["portable_backend_snapshot"]:
                raise RuntimeError(f"portable backend snapshot changed during native testing: {target}")
            report[f"backend_snapshot_after_{key}"] = backend_identity(snapshot)
            if report[f"backend_snapshot_after_{key}"] != report["backend_snapshot"]:
                raise RuntimeError(f"backend snapshot changed during native testing: {target}")
            SHARED.write_report(report_path, report)
        # The cross-backend ABI differential loads the same snapshot into the
        # same compiler; it runs whatever the native targets' verdicts were.
        xback_out = output / "cross-backend-abi"
        xback_command = [
            sys.executable, str(XBACK_RUNNER), "--backend", str(snapshot),
            "--backend-sha256", expected_sha, "--trustc", provenance["compiler_path"],
            "--out", str(xback_out), "--jobs", str(args.jobs),
        ]
        print(f"Running the cross-backend ABI differential with backend {expected_sha}", flush=True)
        xback_run = SHARED.run_bounded(xback_command, output / "cross-backend-abi.log",
                                       args.xback_timeout_seconds)
        xback = classify_xback(xback_run["returncode"], xback_out / "report.json", expected_sha,
                               provenance["compiler_path"])
        if xback_run["interrupted_signal"] is not None:
            xback["status"] = "fail"
            xback["errors"].append(f"cross-backend run interrupted by signal {xback_run['interrupted_signal']}")
        report[XBACK_KEY] = {"command": xback_command, "returncode": xback_run["returncode"], **xback}
        report[f"backend_snapshot_after_{XBACK_KEY}"] = backend_identity(snapshot)
        if report[f"backend_snapshot_after_{XBACK_KEY}"] != report["backend_snapshot"]:
            raise RuntimeError("backend snapshot changed during the cross-backend ABI differential")
        SHARED.write_report(report_path, report)
        report["backend_after_test"] = backend_identity(backend)
        report["cache_backend_changed_during_test"] = report["backend_after_test"] != report["backend_after_build"]
        ensure_unchanged_source(report, "source_after_test")
        report["final_proof_tools"] = SHARED.proof_tool_identities()
        tool_changes = SHARED.proof_tool_changes(report["proof_tools"], report["final_proof_tools"])
        if tool_changes:
            raise RuntimeError("proof tool identity changed during bridge qualification: " + "; ".join(tool_changes))
        report["target_status"] = {target: report[key]["status"] for target, key, _, _ in TARGET_RUNS}
        report["target_status"][XBACK_KEY] = report[XBACK_KEY]["status"]
        report["status"] = "pass" if set(report["target_status"].values()) == {"pass"} else "fail"
    except (OSError, RuntimeError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
        report["errors"].append(str(error))
        report["status"] = "fail"
    except KeyboardInterrupt:
        report["errors"].append("interrupted; required bridge qualification is incomplete")
        report["status"] = "fail"
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    SHARED.write_report(report_path, report)
    print(f"Linux AArch64 bridge gate: {report['status'].upper()} ({report_path})")
    return 0 if report["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
