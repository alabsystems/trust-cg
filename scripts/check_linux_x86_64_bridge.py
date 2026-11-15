#!/usr/bin/env python3
"""Run bounded native Linux x86-64 rustc-bridge diagnostics.

This is separate from the root-workspace floor and public-release gates. It
builds the current bridge with pinned Trust tools in the explicit unverified
lane, runs complete test executables against one copied backend, and rejects
missing tests, runtime skips, changed artifacts, or a non-native host. The
broad differential corpus permits named fail-closed compile outcomes; those
are reported, not counted as admitted programs or proof evidence.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Sequence


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "crates/rustc-codegen-trust-cg/Cargo.toml"
PIN = MANIFEST.parent / "rust-toolchain.toml"
HOST = "x86_64-unknown-linux-gnu"
BACKEND_NAME = "librustc_codegen_trust_cg.so"
SCHEMA = "trust-cg-linux-x86-64-bridge-diagnostic-v1"
CORPUS_CASE_FLOOR = 125

# Complete integration targets, not libtest name filters. These minima are the
# current #[test] counts; additions require an intentional inventory update.
TARGETS = (
    ("bridge_differential_x86", 21),
    ("m140_x86_scalar_pair_return_xback", 1),
    ("m141_x86_scalar_pair_arg_xback", 1),
    ("m144_x86_pair_arg_exhaustion_xback", 1),
    ("m145_x86_indirect_arg_xback", 2),
    ("m136_x86_c_abi_sse_aggregate", 2),
    ("m137_x86_c_abi_zst_packed_union", 4),
)
TEST_ATTRIBUTE = re.compile(r"^\s*#\[test\]\s*$", re.MULTILINE)
CORPUS_CASE = re.compile(r'^\s*name: "([^"]+)"', re.MULTILINE)
REFUSAL = re.compile(r"\bskip(?:s|ped|ping)?\b|TCG-PROOF-465", re.IGNORECASE)
FAIL_CLOSED_NOTE = re.compile(r"note: .*trust-cg failed closed", re.IGNORECASE)
FORBIDDEN_ENVIRONMENT = (
    "RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER", "RUSTFLAGS",
    "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_RUSTC", "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "CARGO_BUILD_RUSTFLAGS",
    "CARGO_BUILD_TARGET", "CARGO_BUILD_TARGET_DIR", "CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUNNER",
    "TCG_TEST_BACKEND_PATH", "TCG_TEST_BACKEND_SHA256", "TCG_NO_PROOF_CERTS",
    "TCG_JIT_UNCHECKED", "TCG_OPT_LEVEL", "TCG_DATAFLOW_INTEGRITY",
    "TRUST_CG_DISABLE_PASSES", "TRUST_CG_DISABLE_CFGSIMPLIFY_SUBPASSES",
)


def load_helper(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"required helper is missing: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


BRIDGE = load_helper("_linux_x86_bridge_artifacts", ROOT / "scripts/check_linux_aarch64_bridge.py")
SHARED = BRIDGE.SHARED
SHARED.HOST = HOST
SHARED.FLOOR_NAME = "Linux x86-64 bridge diagnostic"
TOOLCHAIN = load_helper("_linux_x86_bridge_toolchain", ROOT / "scripts/trust_toolchain.py")
MATRIX = load_helper("_linux_x86_bridge_matrix", ROOT / "scripts/matrix_results.py")


def inventory_problems(tests_dir: Path = MANIFEST.parent / "tests") -> list[str]:
    problems = []
    for name, minimum in TARGETS:
        path = tests_dir / f"{name}.rs"
        if not path.is_file():
            problems.append(f"missing required bridge test target: {name}")
            continue
        source = path.read_text(encoding="utf-8")
        found = len(TEST_ATTRIBUTE.findall(source))
        if found != minimum:
            problems.append(f"{name}: pinned minimum {minimum} differs from {found} #[test] functions")
        if "#[ignore" in source:
            problems.append(f"{name}: ignored tests are not native execution")
        if "host_target_support::X86_64_TARGET" not in source:
            problems.append(f"{name}: host-derived x86-64 target is missing")
        if name == "bridge_differential_x86":
            cases = CORPUS_CASE.findall(source)
            if len(cases) < CORPUS_CASE_FLOOR or len(cases) != len(set(cases)):
                problems.append(
                    f"{name}: corpus case inventory must retain at least {CORPUS_CASE_FLOOR} distinct names"
                )
    host_support = tests_dir / "support/host_target.rs"
    if not host_support.is_file() or f'"{HOST}"' not in host_support.read_text(encoding="utf-8"):
        problems.append("bridge host target helper no longer names Linux x86-64")
    return problems


def cargo_records(transcript: str) -> list[dict]:
    records = []
    for line in transcript.splitlines():
        if line.startswith("{"):
            try:
                value = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(value, dict):
                records.append(value)
    return records


def classify_test_build(returncode: int, transcript: str, target_dir: Path) -> dict:
    records = cargo_records(transcript)
    finished = [row for row in records if row.get("reason") == "build-finished"]
    errors = []
    identities = {}
    if returncode != 0:
        errors.append(f"locked bridge test build exited {returncode}")
    if len(finished) != 1 or finished[0].get("success") is not True:
        errors.append("expected exactly one successful Cargo build-finished record")
    for name, _ in TARGETS:
        artifacts = [
            row for row in records
            if row.get("reason") == "compiler-artifact"
            and row.get("manifest_path") == str(MANIFEST)
            and isinstance(row.get("target"), dict)
            and row["target"].get("name") == name
            and row["target"].get("kind") == ["test"]
            and isinstance(row.get("profile"), dict)
            and row["profile"].get("test") is True
        ]
        if len(artifacts) != 1:
            errors.append(f"Cargo did not identify exactly one required test executable: {name}")
            continue
        executable = artifacts[0].get("executable")
        if not isinstance(executable, str) or not executable:
            errors.append(f"required test artifact has no executable: {name}")
            continue
        path = Path(executable)
        if (not path.is_absolute() or path.parent != target_dir / "release/deps"
                or not path.name.startswith(name + "-")
                or artifacts[0].get("filenames") != [executable]
                or not os.access(path, os.X_OK)):
            errors.append(f"test executable is not the required release artifact: {name}")
            continue
        try:
            identities[name] = BRIDGE.backend_identity(path)
        except (OSError, RuntimeError) as error:
            errors.append(f"cannot identify test executable {name}: {error}")
    return {"status": "fail" if errors else "pass", "errors": errors, "executables": identities}


def classify_target(name: str, minimum: int, returncode: int, transcript: str) -> dict:
    parsed = MATRIX.parse_log(transcript.splitlines(), mode="plain", rc=returncode, capture_available=True)
    errors = []
    if parsed["status"] != "pass":
        errors.append(f"captured libtest result is {parsed['status']}")
    if parsed["suites"] != 1 or parsed["incomplete_suites"]:
        errors.append("expected exactly one complete, captured test suite")
    if parsed["passed"] < minimum:
        errors.append(f"executed passes {parsed['passed']} are below the pinned minimum {minimum}")
    if parsed["failed"] or parsed["ignored"] or parsed["filtered"]:
        errors.append("failed, ignored or filtered tests are not permitted")
    refusals = [line.strip() for line in transcript.splitlines() if REFUSAL.search(line)]
    if refusals:
        errors.append(f"runtime skip or proof-refusal line: {refusals[0][:200]}")
    errors.extend(f"libtest parse problem: {problem}" for problem in parsed["parse_problems"])
    return {
        "target": name, "minimum": minimum,
        "status": "fail" if errors else "pass", "errors": errors,
        "counts": {key: parsed[key] for key in (
            "passed", "libtest_passed", "failed", "ignored", "filtered", "runtime_skipped",
            "suites", "incomplete_suites", "unclassified_passes",
        )},
        "refusal_lines": refusals,
        "corpus_fail_closed_notes": sum(bool(FAIL_CLOSED_NOTE.search(line)) for line in transcript.splitlines())
        if name == "bridge_differential_x86" else 0,
    }


def preflight(target_dir: Path, driver: str | None = None) -> dict:
    if sys.platform != "linux" or platform.machine() != "x86_64":
        raise RuntimeError(f"native bridge host must be Linux x86_64, observed {sys.platform}/{platform.machine()}")
    present = sorted(name for name in FORBIDDEN_ENVIRONMENT if name in os.environ)
    if present:
        raise RuntimeError(f"bridge diagnostic rejects ambient compiler/backend overrides: {present}")
    problems = inventory_problems()
    if problems:
        raise RuntimeError("bridge test inventory changed: " + "; ".join(problems))
    tools = {}
    for name in ("git", "env", "cc", "clang"):
        found = shutil.which(name)
        if found is None:
            raise RuntimeError(f"required native host tool is missing: {name}")
        tools[name] = str(Path(found).resolve(strict=True))
    toolchain = TOOLCHAIN.resolve(driver, pin=PIN)
    if toolchain["host"] != HOST:
        raise RuntimeError(f"pinned Trust compiler host must be {HOST}, observed {toolchain['host']}")
    # The --unverified flag is the discriminator for a real targo, not cargo
    # installed under that name by a stale stage.
    targo_unverified = SHARED.probe([toolchain["targo"], "--unverified", "--version"])
    target_lib = Path(toolchain["target_lib_dir"])
    if not any(path.is_file() for path in target_lib.glob("libstd-*.rlib")):
        raise RuntimeError(f"pinned Trust sysroot lacks native rust-std: {target_lib}")
    for path in (ROOT, *ROOT.parents):
        if target_dir == path:
            raise RuntimeError("backend target directory must not be the source root or its ancestor")
    return {
        **SHARED.source_provenance(tools["git"]), "host": HOST, "machine": platform.machine(),
        "tools": tools, "toolchain": toolchain, "targo_unverified_version": targo_unverified,
        "clang": SHARED.probe([tools["clang"], "--version"]),
        "cc": SHARED.probe([tools["cc"], "--version"]),
        "target_dir": str(target_dir), "manifest": str(MANIFEST),
        "configuration": {name: os.environ[name] for name in (
            "CARGO_TARGET_DIR", "CARGO_HOME", "RUSTUP_TOOLCHAIN", "AY_SOLVER_PATH",
            "TCG_SOLVER_PATH", "TCG_EXTERNAL_CLEAN_CHECKER", "TCG_CLEAN_CHECKER",
            "RUST_MIN_STACK", "XDG_CACHE_HOME",
        ) if name in os.environ},
    }


def ensure_unchanged_source(report: dict, name: str) -> None:
    observed = SHARED.source_provenance(report["provenance"]["tools"]["git"])
    report[name] = observed
    if observed["source_fingerprint"] != report["provenance"]["source_fingerprint"]:
        raise RuntimeError(f"source changed during Linux x86-64 bridge diagnostics ({name})")


def runtime_entries(path: Path) -> list[str]:
    return sorted(str(entry.relative_to(path)) for entry in path.rglob("*"))


def run_step(command: Sequence[str], log: Path, timeout_seconds: float) -> dict:
    result = SHARED.run_target(command, log, timeout_seconds)
    result.pop("counts", None)
    result.pop("inventory_skip_labels", None)
    result.pop("minimum", None)
    return result


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--list", action="store_true", help="print required test targets without probing or building")
    parser.add_argument("--out", type=Path, help="new report directory outside the source tree")
    parser.add_argument("--target-dir", type=Path, default=MANIFEST.parent / "target/linux-x86-64-bridge-diagnostic")
    parser.add_argument("--driver", help="explicit pinned package trustc; default is the PATH trustc/targo pair")
    parser.add_argument("--timeout-seconds", type=SHARED.positive_seconds, default=3600.0)
    parser.add_argument("--jobs", type=SHARED.positive_jobs, default=2)
    parser.add_argument("--require-clean", action="store_true", help="refuse a dirty source worktree")
    parser.add_argument("--require-proof-tools", action="store_true", help="require pinned AY and Clean routes")
    args = parser.parse_args(argv)
    if args.list:
        for name, minimum in TARGETS:
            print(f"{name}: {minimum} required native passes")
        print(f"bridge_differential_x86: at least {CORPUS_CASE_FLOOR} named corpus cases in source")
        problems = inventory_problems()
        for problem in problems:
            print(problem, file=sys.stderr)
        return 1 if problems else 0
    try:
        if args.out is None:
            output = Path(tempfile.mkdtemp(prefix="trust-cg-linux-x86-64-bridge-"))
        else:
            output = args.out.absolute()
            if output.resolve().is_relative_to(ROOT):
                raise OSError("report directory must be outside the source tree")
            output.mkdir(mode=0o700)
    except OSError as error:
        print(f"Linux x86-64 bridge diagnostic: output error: {error}", file=sys.stderr)
        return 1
    report = {
        "schema": SCHEMA, "scope": "bounded native bridge diagnostics, not release or proof qualification",
        "host": HOST, "required_targets": {name: minimum for name, minimum in TARGETS},
        "required_minimum_passes": sum(minimum for _, minimum in TARGETS),
        "required_corpus_case_floor": CORPUS_CASE_FLOOR,
        "lane": "unverified Trust backend build and -Ztrust-verify=off fixture compiles",
        "status": "incomplete", "errors": [], "targets": [],
        "started_utc": datetime.now(timezone.utc).isoformat(),
    }
    report_path = output / "report.json"
    SHARED.write_report(report_path, report)
    print(f"Linux x86-64 bridge diagnostic logs: {output}", flush=True)
    try:
        target_dir = args.target_dir.resolve()
        if output == target_dir or output in target_dir.parents or target_dir in output.parents:
            raise RuntimeError("report and Cargo target directories must be separate")
        report["provenance"] = preflight(target_dir, args.driver)
        provenance = report["provenance"]
        if args.require_clean and provenance["dirty"]:
            raise RuntimeError("--require-clean refuses a dirty source tree")
        report["controls"] = {"require_clean": args.require_clean, "require_proof_tools": args.require_proof_tools}
        report["proof_tools"] = SHARED.proof_tool_identities()
        tool_problems = SHARED.proof_tool_problems(report["proof_tools"])
        report["proof_tool_problems"] = tool_problems
        if args.require_proof_tools and tool_problems:
            raise RuntimeError("--require-proof-tools: " + "; ".join(tool_problems))
        toolchain = provenance["toolchain"]
        backend = target_dir / "release" / BACKEND_NAME
        prefix = [
            provenance["tools"]["env"], f"CARGO_TARGET_DIR={target_dir}",
            f"RUSTC={toolchain['compiler']}", "RUSTUP_AUTO_INSTALL=0",
            toolchain["targo"], "--unverified",
        ]
        common = [
            "--manifest-path", str(MANIFEST), "--target-dir", str(target_dir),
            "--release", "--locked", "--color", "never", "-j", str(args.jobs),
            "--message-format=json-render-diagnostics",
        ]
        report["backend_before_build"] = BRIDGE.backend_identity(backend) if backend.exists() else None
        SHARED.write_report(report_path, report)
        build_log = output / "build.log"
        build = run_step([*prefix, "build", *common], build_log, args.timeout_seconds)
        build.update(BRIDGE.classify_build(build["returncode"], build_log.read_text(errors="replace"), MANIFEST, backend))
        if build["interrupted_signal"] is not None:
            build["status"] = "fail"
            build["errors"].append("backend build interrupted")
        report["build"] = build
        ensure_unchanged_source(report, "source_after_build")
        SHARED.write_report(report_path, report)
        if build["status"] != "pass":
            raise RuntimeError("required current-source backend build failed; cached libraries cannot substitute")
        report["backend_after_build"] = BRIDGE.backend_identity(backend)
        runtime_target = output / "runtime-target"
        (runtime_target / "release").mkdir(parents=True)
        snapshot = runtime_target / "release" / BACKEND_NAME
        report["backend_snapshot"] = BRIDGE.snapshot_backend(backend, snapshot, report["backend_after_build"])
        expected_entries = runtime_entries(runtime_target)
        SHARED.write_report(report_path, report)

        test_build_log = output / "test-build.log"
        test_args = [arg for name, _ in TARGETS for arg in ("--test", name)]
        test_build = run_step(
            [*prefix, "test", *common, *test_args, "--no-run"], test_build_log, args.timeout_seconds,
        )
        test_build.update(classify_test_build(
            test_build["returncode"], test_build_log.read_text(errors="replace"), target_dir,
        ))
        if test_build["interrupted_signal"] is not None:
            test_build["status"] = "fail"
            test_build["errors"].append("test build interrupted")
        report["test_build"] = test_build
        ensure_unchanged_source(report, "source_after_test_build")
        SHARED.write_report(report_path, report)
        if test_build["status"] != "pass":
            raise RuntimeError("required current-source bridge test build failed")

        for name, minimum in TARGETS:
            executable_identity = test_build["executables"][name]
            executable = Path(executable_identity["path"])
            if BRIDGE.backend_identity(executable) != executable_identity:
                raise RuntimeError(f"test executable changed before execution: {name}")
            if BRIDGE.backend_identity(snapshot) != report["backend_snapshot"]:
                raise RuntimeError(f"backend snapshot changed before execution: {name}")
            command = [
                provenance["tools"]["env"], f"CARGO_TARGET_DIR={runtime_target}",
                f"CARGO_MANIFEST_DIR={MANIFEST.parent}", "RUST_MIN_STACK=16777216",
                "RUSTUP_AUTO_INSTALL=0", str(executable), "--show-output", "--test-threads=1",
            ]
            print(f"Running {name} with backend {report['backend_snapshot']['sha256']}", flush=True)
            log = output / f"{name}.log"
            result = run_step(command, log, args.timeout_seconds)
            result.update(classify_target(name, minimum, result["returncode"], log.read_text(errors="replace")))
            if result["interrupted_signal"] is not None:
                result["status"] = "fail"
                result["errors"].append("native test interrupted")
            report["targets"].append(result)
            SHARED.write_report(report_path, report)
            if BRIDGE.backend_identity(executable) != executable_identity:
                raise RuntimeError(f"test executable changed during execution: {name}")
            if BRIDGE.backend_identity(snapshot) != report["backend_snapshot"]:
                raise RuntimeError(f"backend snapshot changed during execution: {name}")
            if runtime_entries(runtime_target) != expected_entries:
                raise RuntimeError(f"runtime target directory changed during {name}; fixture may have rebuilt backend")
        report["cache_backend_after_tests"] = BRIDGE.backend_identity(backend)
        ensure_unchanged_source(report, "source_after_tests")
        report["final_proof_tools"] = SHARED.proof_tool_identities()
        changes = SHARED.proof_tool_changes(report["proof_tools"], report["final_proof_tools"])
        if changes:
            raise RuntimeError("proof tool identity changed during bridge diagnostics: " + "; ".join(changes))
        report["status"] = "pass" if all(row["status"] == "pass" for row in report["targets"]) else "fail"
    except (OSError, RuntimeError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
        report["errors"].append(str(error))
        report["status"] = "fail"
    except KeyboardInterrupt:
        report["errors"].append("interrupted; required native diagnostics are incomplete")
        report["status"] = "fail"
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    SHARED.write_report(report_path, report)
    print(f"Linux x86-64 bridge diagnostic: {report['status'].upper()} ({report_path})")
    return 0 if report["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
