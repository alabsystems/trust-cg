#!/usr/bin/env python3
"""Run unmeasured, full-state LLVM/CG/Clang checks for three real kernels.

All 18 original rows are accounted for. Generated validation clones qualify
only their own bytes; this runner never emits a performance/superiority row.
"""

import argparse
import importlib.util
import json
import os
import platform
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent.parent / "scripts"))
from trust_toolchain import ToolchainError, resource_fds
from full_output import (BASE_REVISION, LANES, SUPPORTED, OutputError, compare_lanes,
                         counts, decode_output, digest, empty_accounting,
                         load_manifest, render_validation)

SCHEMA = "trust-cg-benchmark-full-output-diagnostic-v1"
ENVIRONMENT_KEYS = ("SDKROOT", "MACOSX_DEPLOYMENT_TARGET", "CPATH", "C_INCLUDE_PATH",
                    "LIBRARY_PATH", "CCC_OVERRIDE_OPTIONS", "CLANG_CONFIG_FILE")


def file_digest(path):
    return digest(Path(path).read_bytes())


def load_helper(repo, name):
    spec = importlib.util.spec_from_file_location("full_output_" + name, Path(repo) / "scripts" / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def capture(command, timeout, env=None, *, trust_compiler=False):
    """Keep Trust's inherited admission for compilers and close it for executions."""
    try:
        descriptors = resource_fds(os.environ if env is None else env) if trust_compiler else ()
        result = subprocess.run(command, capture_output=True, env=env, timeout=timeout,
                                pass_fds=descriptors)
        return {"status": "EXITED", "returncode": result.returncode,
                "stdout": result.stdout, "stderr": result.stderr}
    except subprocess.TimeoutExpired as error:
        return {"status": "TIMEOUT", "returncode": None,
                "stdout": error.stdout or b"", "stderr": error.stderr or b""}
    except (OSError, ToolchainError) as error:
        return {"status": "EXECUTION_UNAVAILABLE", "returncode": None,
                "stdout": b"", "stderr": str(error).encode("utf-8")}


def retain_capture(directory, name, result):
    directory = Path(directory)
    record = {key: value for key, value in result.items() if key not in ("stdout", "stderr")}
    for channel in ("stdout", "stderr"):
        data = result[channel]
        path = directory / (name + "." + channel)
        path.write_bytes(data)
        record[channel] = {"path": path.name, "bytes": len(data), "sha256": digest(data)}
    return record


def native_arch(triple):
    arch = triple.split("-")[0]
    return "aarch64" if arch == "arm64" else arch


def resolve_tools(args, repo):
    controls = sorted(key for key in os.environ if key.startswith(("TCG_", "TRUST_CG_")))
    if controls:
        raise OutputError("untracked backend environment controls are present: " + ", ".join(controls))
    if (sys.platform not in ("darwin", "linux") or sys.byteorder != "little"
            or native_arch(platform.machine()) not in ("aarch64", "x86_64")):
        raise OutputError("native host is outside the bounded little-endian 64-bit scope")
    trust = load_helper(repo, "trust_toolchain")
    driver = trust.resolve(args.driver, pin=Path(repo) / trust.PIN_RELATIVE)
    target = args.target or driver["host"]
    if target != driver["host"] or native_arch(target) != native_arch(platform.machine()):
        raise OutputError("cross-target execution is outside this native full-output scope")
    backend = load_helper(repo, "bridge_backend")
    dylib, _ = backend.resolve(Path(repo), Path(args.dylib) if args.dylib else None)
    clang = Path(args.clang)
    if not clang.is_absolute() or not clang.is_file() or not os.access(clang, os.X_OK):
        raise OutputError("--clang must name an existing absolute executable")
    version = capture([str(clang), "--version"], 30)
    if version["status"] != "EXITED" or version["returncode"] != 0:
        raise OutputError("named Clang did not complete its version query")
    banner = (version["stdout"] + version["stderr"]).decode("utf-8", "replace")
    if "clang version" not in banner:
        raise OutputError("named C compiler did not identify itself as Clang")
    return {"driver": driver, "target": target, "dylib": str(dylib),
            "dylib_sha256": file_digest(dylib), "trustc_sha256": file_digest(driver["compiler"]),
            "clang": str(clang), "clang_sha256": file_digest(clang), "clang_version": banner,
            "helper_sources": {name: file_digest(Path(repo) / "scripts" / (name + ".py"))
                               for name in ("trust_toolchain", "bridge_backend")},
            "resource_custody_source_sha256": file_digest(resource_fds.__code__.co_filename),
            "environment": {key: os.environ.get(key) for key in ENVIRONMENT_KEYS},
            "isa_parity_qualified": False,
            "identity_limit": "command/file identities and declared native target; loaded compiler/source/default-feature adequacy remains a qualification obligation"}


def compiler_command(tools, lane, source, output):
    if lane == "clang":
        return [tools["clang"], "--target=" + tools["target"], "-std=c11", "-O3",
                "-o", str(output), str(source)]
    driver = tools["driver"]
    command = [driver["compiler"], *driver["compiler_flags"], "--edition=2021", "--crate-type", "bin",
               "-Cpanic=abort", "-Copt-level=3",
               "-o", str(output), str(source)]
    if lane == "bridge":
        command.insert(1, "-Zcodegen-backend=" + tools["dylib"])
    return command


def tools_unchanged(tools):
    return (file_digest(tools["driver"]["compiler"]) == tools["trustc_sha256"]
            and file_digest(tools["clang"]) == tools["clang_sha256"]
            and file_digest(tools["dylib"]) == tools["dylib_sha256"])


def check_kernel(here, directory, stem, row, tools, args):
    sources = {}
    row["original_sources"] = {}
    for language, folder, suffix in (("rust", "progs", ".rs"), ("c", "progs_c", ".c")):
        original = here / folder / (stem + suffix)
        data = original.read_bytes()
        rendered = render_validation(stem, language, data)
        source = directory / (stem + "_validation" + suffix)
        source.write_bytes(rendered)
        sources[language] = source
        row["original_sources"][language] = {"path": str(original), "sha256": digest(data)}
    row["validation_sources"] = {language: {"path": source.name, "sha256": file_digest(source)}
                                 for language, source in sources.items()}
    row["iterations"] = SUPPORTED[stem]["iterations"]
    row["fields"] = list(SUPPORTED[stem]["fields"])
    states = {}
    observed_state = None
    mismatch = False
    incomplete = False
    for lane in LANES:
        source = sources["c" if lane == "clang" else "rust"]
        output = directory / (stem + "_" + lane)
        command = compiler_command(tools, lane, source, output)
        expected_source = row["validation_sources"]["c" if lane == "clang" else "rust"]["sha256"]
        if file_digest(source) != expected_source:
            raise OutputError("validation source changed before compilation")
        compiled = capture(command, args.compile_timeout, trust_compiler=(lane != "clang"))
        record = row["lanes"][lane] = {"compile_command": command,
                    "source_sha256": file_digest(source),
                    "compile": retain_capture(directory, stem + "_" + lane + "_compile", compiled),
                    "runs": [], "status": "INCOMPLETE"}
        if not tools_unchanged(tools):
            raise OutputError("compiler/backend bytes changed during the check")
        if file_digest(source) != expected_source:
            raise OutputError("validation source changed during compilation")
        if (compiled["status"] != "EXITED" or compiled["returncode"] != 0 or not output.is_file()):
            record["reason"] = "compile unavailable, timed out or refused; raw outcome retained"
            incomplete = True
            continue
        if "verification is DEGRADED" in compiled["stderr"].decode("utf-8", "replace"):
            record["reason"] = "backend reported degraded proof checking; no qualified lane"
            incomplete = True
            continue
        binary_hash = file_digest(output)
        record["binary"] = {"path": output.name, "sha256": binary_hash, "bytes": output.stat().st_size}
        lane_states = []
        for repeat in range(args.repeat):
            if file_digest(output) != binary_hash:
                raise OutputError("compiled artifact changed before execution")
            result = capture([str(output)], args.run_timeout)
            sample = retain_capture(directory, stem + "_" + lane + "_run" + str(repeat), result)
            record["runs"].append(sample)
            if (file_digest(output) != binary_hash or not tools_unchanged(tools)
                    or file_digest(source) != expected_source):
                raise OutputError("artifact/compiler/backend bytes changed during execution")
            if result["status"] != "EXITED" or result["returncode"] is None or result["returncode"] < 0:
                sample["reason"] = "execution unavailable, timed out or signaled"
                incomplete = True
                continue
            try:
                state = decode_output(stem, result["stdout"], result["stderr"],
                                      result["returncode"], row["expected_exit"])
            except OutputError as error:
                sample["reason"] = str(error)
                mismatch = True
                row.update(verdict="MISMATCH", reason=str(error))
                continue
            sample["state_hex"] = [f"{value:016x}" for value in state]
            # A missing lane cannot erase disagreement already observed in
            # admitted samples, including a lane with a later timeout.
            if observed_state is not None and state != observed_state:
                mismatch = True
                row.update(verdict="MISMATCH", reason="admitted complete state tuples differ")
            else:
                observed_state = state
            lane_states.append(state)
        if len(lane_states) == args.repeat:
            record["status"] = "COMPLETE_STATE_OBSERVED"
            states[lane] = lane_states
    if mismatch or (not incomplete and not compare_lanes(states)):
        row.update(verdict="MISMATCH", reason="full state, output transport, exit or repeated execution differs")
    elif incomplete:
        row.update(verdict="INCOMPLETE", reason="at least one required lane did not complete every check")
    else:
        row.update(verdict="FULL_OUTPUT_AGREEMENT", reason="all three complete state tuples and every repeat agree")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--repo", type=Path, default=HERE.parent.parent)
    parser.add_argument("--driver", help="explicit installed Trust package trustc")
    parser.add_argument("--dylib", help="actual fresh bridge backend to load")
    parser.add_argument("--clang", required=True, help="absolute actual Clang executable")
    parser.add_argument("--target", help="assert the native Trust host target; does not override compiler target")
    parser.add_argument("--output-dir", required=True, type=Path, help="new capture directory; existing directories refuse")
    parser.add_argument("--repeat", type=int, default=3)
    parser.add_argument("--compile-timeout", type=int, default=900)
    parser.add_argument("--run-timeout", type=int, default=300)
    args = parser.parse_args(argv)
    if args.repeat < 3 or args.compile_timeout <= 0 or args.run_timeout <= 0:
        parser.error("at least three repeats and positive timeouts are required")
    repo = args.repo.resolve()
    here = repo / "benchmarks" / "beat-llvm"
    try:
        manifest = load_manifest(here)
        directory = args.output_dir.resolve()
        directory.mkdir(parents=True, exist_ok=False, mode=0o700)
    except (OSError, OutputError, ValueError, KeyError) as error:
        print("full-output: " + str(error), file=sys.stderr)
        return 2
    programs = empty_accounting(manifest)
    report = {"schema": SCHEMA, "timestamp_utc": datetime.now(timezone.utc).isoformat(),
              "fixture_base_revision": BASE_REVISION,
              "manifest_sha256": file_digest(here / "progs" / "manifest.json"),
              "original_timing_runner_sha256": file_digest(here / "run.py"),
              "original_corpus_sources": {stem: {"rust_sha256": file_digest(here / "progs" / (stem + ".rs")),
                                                   "c_sha256": file_digest(here / "progs_c" / (stem + ".c"))
                                                   if (here / "progs_c" / (stem + ".c")).is_file() else None}
                                          for stem in manifest},
              "renderer_sha256": file_digest(Path(__file__).with_name("full_output.py")),
              "runner_sha256": file_digest(__file__), "programs": programs,
              "repeat": args.repeat, "timing_measured": False, "superiority_eligible": False,
              "formal_credit": False, "full_original_corpus_qualified": False,
              "original_timed_binary_qualified": False,
              "authority_limit": "finite deterministic three-lane output checks on separately generated validation artifacts; no transfer to original timed binaries, no compiler/proof theorem or performance claim"}
    try:
        tools = resolve_tools(args, repo)
        report["tools"] = tools
        for stem in SUPPORTED:
            try:
                check_kernel(here, directory, stem, programs[stem], tools, args)
            except (OSError, OutputError, ValueError) as error:
                if programs[stem]["verdict"] == "MISMATCH":
                    programs[stem]["interruption_reason"] = str(error)
                else:
                    programs[stem].update(verdict="INCOMPLETE", reason=str(error))
    except (OSError, OutputError, RuntimeError) as error:
        report["tooling_error"] = str(error)
        for stem in SUPPORTED:
            programs[stem]["reason"] = "tool/environment admission unavailable: " + str(error)
            for lane in LANES:
                programs[stem]["lanes"][lane] = {"status": "INCOMPLETE", "reason": "tool/environment admission unavailable; lane not launched"}
    report["counts"] = counts(programs)
    report["inventory"] = {path.name: {"bytes": path.stat().st_size, "sha256": file_digest(path)}
                           for path in sorted(directory.iterdir()) if path.is_file()}
    (directory / "full-output-results.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report["counts"], sort_keys=True))
    if report["counts"]["mismatch_count"]:
        return 1
    return 2 if report["counts"]["incomplete_count"] else 0


if __name__ == "__main__":
    sys.exit(main())
