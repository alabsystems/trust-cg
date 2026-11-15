#!/usr/bin/env python3
# Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
"""Qualify the bounded Linux AArch64 native/max/Cortex-A53 execution matrix.

Always builds both complete targets into a fresh, isolated target directory,
then runs all tests on all three profiles. Both parent and generated ELF
children use the explicit emulator. The parent-only negative control must
detect an escaping child. Emulation is never native-silicon evidence, a
memory-order proof, default verified compilation or acceptance-row closure.
Use build-slot for resource scheduling, as for the other host runners.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import resource
import shutil
import subprocess
import sys
import tempfile
import time

import check_linux_aarch64 as floor
import trust_toolchain

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "trust-cg-aarch64-cpu-profiles-v1"
TARGETS = {"aarch64_cpu_profile": 3, "e2e_aarch64_llsc_atomics": 12}
PROFILES = (("native-host", None), ("qemu-max", "max"), ("qemu-cortex-a53", "cortex-a53"))
FEATURES = ("lse", "fp16_scalar", "fp16_simd", "dotprod")
SUMMARY = re.compile(
    r"^test result: ok\. (\d+) passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;",
    re.MULTILINE,
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def sha(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def no_core() -> None:
    # Optional instructions deliberately raise SIGILL in two profiles/controls.
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def feature_census(text: str, cpu: str | None) -> dict:
    rows = re.findall(r"AARCH64_CPU_PROFILE checks=5 profile=(\S+) CPU_FEATURES ([^\n]+)", text)
    require(len(rows) == 1, "missing or duplicate actual CPU fingerprint")
    flags = dict(word.split("=", 1) for word in rows[0][1].split())
    require(all(flags.get(key) in ("0", "1") for key in FEATURES), "incomplete CPU feature flags")
    require(all(re.fullmatch(r"[0-9a-f]+", flags.get(key, "")) for key in ("hwcap", "hwcap2")),
            "missing raw Linux HWCAP/HWCAP2")
    if cpu:
        require(all(flags[key] == ("0" if cpu == "cortex-a53" else "1") for key in FEATURES),
                f"emulator did not implement the requested {cpu} feature contract")
    implemented = (int(flags["lse"]) + int(flags["fp16_scalar"] == flags["fp16_simd"] == "1")
                   + int(flags["dotprod"]))
    matched, refused = 4 * (1 + implemented), 4 * (3 - implemented)
    require(re.findall(r"AARCH64_JIT_CPU_PROFILE cells=16 matched=(\d+) refused=(\d+)", text)
            == [(str(matched), str(refused))], "JIT admission denominator/outcomes changed")
    require(text.count("AARCH64_EMULATION_CONTRACT controls=8") == 1, "missing execution controls")
    return {"cpu_flags": flags, "isa_profile": rows[0][0], "jit_matched": matched, "jit_refused": refused}


def qualify(args: argparse.Namespace, output: Path, report: dict) -> None:
    require(sys.platform == "linux" and platform.machine() == "aarch64", "requires Linux AArch64 host")
    git = shutil.which("git")
    require(git is not None, "git is required")
    source = floor.source_provenance(git)
    report["source"] = source
    require(not source["dirty"], "qualification requires a clean committed source tree")
    # Audit before *any* Cargo/Targo probe. The explicit compiler's package is
    # resolved afterwards; no PATH launcher is executed to select it.
    audit = floor.cargo_config_record(git, tool="targo")
    report["cargo_config"] = audit
    require(not audit["problems"], f"Cargo configuration rejected: {audit['problems']}")
    toolchain = trust_toolchain.resolve(args.trust_driver, purpose="workspace")
    report["toolchain"] = toolchain
    require(toolchain["host"] == floor.HOST, "Trust compiler has the wrong host")
    emulator = args.emulator.absolute()
    require(args.emulator.is_absolute() and emulator.is_file() and not emulator.is_symlink()
            and os.access(emulator, os.X_OK), "emulator must be an absolute executable regular file")
    env = dict(os.environ)
    removed = set(floor.scrubbed_environment(env)) | {
        key for key in env if key.startswith(("TCG_", "TRUST_CG_", "RUSTUP_", "RUSTC_"))
    } | {"RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC", "RUSTDOC", "CARGO_TARGET_DIR",
         "LD_PRELOAD", "LD_LIBRARY_PATH", "QEMU_CPU", "QEMU_LD_PREFIX"}
    # QEMU_* can also rewrite argv, environment, ELF loading and guest auxv.
    removed.update(key for key in env if key.startswith("QEMU_"))
    for key in removed:
        env.pop(key, None)
    package = Path(toolchain["sysroot"])
    doc = package / "bin/trustdoc"
    require(doc.is_file(), "selected Trust package lacks trustdoc")
    env.update(RUSTC=toolchain["compiler"], RUSTDOC=str(doc),
               PATH=str(package / "bin") + os.pathsep + env.get("PATH", ""),
               LD_LIBRARY_PATH=os.pathsep.join((str(package / "lib"), toolchain["target_lib_dir"])))
    report["scrubbed_environment"] = sorted(key for key in removed if key in os.environ)
    cc = shutil.which("cc", path=env["PATH"])
    require(cc is not None, "native C compiler cc is required")
    identities = {str(path): floor.executable_digest(path) for path in (
        Path(toolchain["compiler"]), Path(toolchain["targo"]), doc, emulator, Path(cc), Path(sys.executable),
    )}
    report["tool_identities"] = identities
    probe = subprocess.run([str(emulator), "--version"], env=env, cwd=ROOT,
                           capture_output=True, text=True, timeout=20, check=True)
    require(probe.stdout.startswith("qemu-aarch64 version "), "selected emulator is not qemu-aarch64")
    report["emulator"] = {"path": str(emulator), "version": probe.stdout.strip(),
                          "sha256": sha(emulator), "models": ["max", "cortex-a53"]}
    dependency = floor.dependency_identity(git, env)
    report["dependency_identity"] = dependency
    require(not floor.dependency_recorder().offline_problems(dependency), "pinned Git dependencies not offline-ready")
    report["host"] = {"uname": list(platform.uname()), "execution": "native Linux AArch64"}
    report_path = output / "report.json"

    def save() -> None:
        floor.write_report(report_path, report)

    def run(name: str, command: list[str], local: dict, *, build: bool = False) -> tuple[dict, str]:
        log = output / (name + ".log")
        bounded = [sys.executable, str(ROOT / "scripts/run_with_timeout.py")]
        if args.max_rss_gib is not None:
            bounded += ["--max-rss-gib", str(args.max_rss_gib)]
        bounded += [str(args.timeout_seconds), *command]
        started = time.monotonic()
        print(f"RUN {name}", flush=True)
        with log.open("w") as stream:
            result = subprocess.run(bounded, cwd=ROOT, env=local, stdout=stream,
                                    stderr=subprocess.STDOUT, preexec_fn=no_core)
        text = log.read_text(errors="replace")
        row = {"name": name, "command": bounded, "exit": result.returncode,
               "seconds": time.monotonic() - started, "log": str(log), "log_sha256": sha(log)}
        if args.max_rss_gib is not None:
            receipt, problems = floor.rss_receipt(text, args.max_rss_gib)
            row["rss_receipt"] = receipt
            require(not problems, f"{name}: RSS supervision failed: {problems}")
        report["build" if build else "last_execution"] = row
        save()
        print(f"{name}: exit {result.returncode}", flush=True)
        return row, text

    # Fresh target prevents cross-worktree build-script cache reuse. Offline
    # locked compilation does not change dependency selection or contact remote.
    target = output / "target"
    env["CARGO_TARGET_DIR"] = str(target)
    command = [*toolchain["build_command"], "test", "--locked", "--offline", "--no-run",
               "--message-format=json", "-j", str(args.jobs), "-p", "trust-cg-codegen"]
    for name in TARGETS:
        command += ["--test", name]
    build, transcript = run("build", command, env, build=True)
    require(build["exit"] == 0, "test build failed; see build.log")
    messages = []
    for line in transcript.splitlines():
        try:
            messages.append(json.loads(line))
        except ValueError:
            pass
    require(any(item.get("reason") == "build-finished" and item.get("success") is True for item in messages),
            "missing successful terminal Cargo build record")
    artifacts = {}
    for item in messages:
        name = item.get("target", {}).get("name")
        if (item.get("reason") == "compiler-artifact" and name in TARGETS and item.get("executable")
                and item.get("profile", {}).get("test")):
            require(name not in artifacts, f"ambiguous test executable for {name}")
            original = Path(item["executable"])
            require(original.resolve().is_relative_to(target.resolve()), "artifact escaped the fresh target directory")
            saved = output / name
            shutil.copyfile(original, saved)
            saved.chmod(0o500)
            artifacts[name] = {"original": str(original), "binary": str(saved), "sha256": sha(saved)}
    require(set(artifacts) == set(TARGETS), "incomplete compiled target inventory")
    report["compiled_artifacts"] = artifacts
    save()
    for profile, cpu in PROFILES:
        features = None
        for name, count in TARGETS.items():
            local = env.copy()
            command = [artifacts[name]["binary"], "--nocapture", "--test-threads=1"]
            if cpu:
                local.update(TCG_TEST_AARCH64_EMULATOR=str(emulator), TCG_TEST_AARCH64_CPU=cpu)
                command = [str(emulator), "-cpu", cpu, *command]
            row, text = run(profile + "-" + name, command, local)
            row.update(profile=profile, cpu_model=cpu, target=name,
                       execution="native" if cpu is None else "emulated",
                       child_executor={key: local[key] for key in ("TCG_TEST_AARCH64_EMULATOR", "TCG_TEST_AARCH64_CPU")
                                       if key in local})
            report["runs"].append(row)
            save()
            require(row["exit"] == 0, f"{profile}/{name} failed; see {row['log']}")
            require(SUMMARY.findall(text) == [str(count)], f"{profile}/{name}: full test inventory changed")
            require(not re.search(r"\bskip(?:ped|ping)?\b", text, re.IGNORECASE), "test transcript reported a skip")
            if name == "aarch64_cpu_profile":
                features = feature_census(text, cpu)
                row.update(features)
            else:
                require(features is not None, "CPU probe must precede atomic execution")
                lse = features["cpu_flags"]["lse"] == "1"
                expected = ("8", "0") if lse else ("4", "4")
                require(re.findall(r"AARCH64_BOOL_CPU_PROFILE cells=8 matched=(\d+) unsupported_lse_sigill=(\d+)", text)
                        == [expected], "forced-LSE outcomes do not match actual CPU features")
                row.update(bool_matched=int(expected[0]), bool_sigill=int(expected[1]))
            save()
    # Choose a model whose auxv differs from the native child even on a
    # baseline host. Omit ONLY child routing, retaining the emulated parent.
    native_flags = report["runs"][0]["cpu_flags"]
    cpu = "cortex-a53" if any(native_flags[key] == "1" for key in FEATURES) else "max"
    row, text = run("parent-only-emulation-control", [str(emulator), "-cpu", cpu,
        artifacts["aarch64_cpu_profile"]["binary"], "--exact",
        "actual_cpu_and_child_executor_agree_on_optional_instruction_availability", "--nocapture", "--test-threads=1"], env)
    report["parent_only_control"] = row
    require(row["exit"] == 101 and "parent/child CPU mismatch" in text
            and "0 passed; 1 failed; 0 ignored;" in text,
            "parent-only emulation did not detect the escaping native child")
    final_source = floor.source_provenance(git)
    report["final_source"] = final_source
    require(final_source["source_fingerprint"] == source["source_fingerprint"], "source changed during qualification")
    final_audit = floor.cargo_config_record(git, tool="targo")
    report["final_cargo_config"] = final_audit
    require(not floor.cargo_config_auditor().changes(audit, final_audit), "Cargo configuration changed")
    final_dependency = floor.dependency_identity(git, env)
    report["final_dependency_identity"] = final_dependency
    require(not floor.dependency_recorder().identity_changes(dependency, final_dependency), "dependency identities changed")
    require(not floor.dependency_recorder().offline_problems(final_dependency), "final dependencies not pinned and clean")
    report["final_tool_identities"] = {path: floor.executable_digest(Path(path)) for path in identities}
    require(report["final_tool_identities"] == identities, "compiler/emulator/C tool bytes changed")
    require(all(sha(Path(item["binary"])) == item["sha256"] for item in artifacts.values()), "test executable changed")
    # Profile identity participates in the fingerprint; max and baseline can
    # never share a receipt just because they used the same source/compiler.
    identity = {"source_fingerprint": source["source_fingerprint"], "tools": identities,
                "dependency_identity": final_dependency, "compiled_artifacts": artifacts,
                "profiles": [{key: row[key] for key in ("profile", "cpu_model", "execution", "cpu_flags", "isa_profile")}
                             for row in report["runs"] if row["target"] == "aarch64_cpu_profile"]}
    report.update(profile_identity=identity, profile_fingerprint=hashlib.sha256(
        json.dumps(identity, sort_keys=True).encode()).hexdigest(),
        test_method_executions=45, jit_cells=48, parent_only_leak_control_detected=True, status="pass")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--out", type=Path, help="new output directory outside the source tree")
    parser.add_argument("--emulator", required=True, type=Path, help="absolute qemu-aarch64 executable")
    parser.add_argument("--trust-driver", help="Trust workspace compiler (never a stock compiler)")
    parser.add_argument("--jobs", type=floor.positive_jobs, default=2)
    parser.add_argument("--timeout-seconds", type=floor.positive_seconds, default=1500.0)
    parser.add_argument("--max-rss-gib", type=floor.positive_gib)
    args = parser.parse_args(argv)
    try:
        output = args.out.absolute() if args.out else Path(tempfile.mkdtemp(prefix="trust-cg-cpu-profiles-"))
        require(not output.resolve().is_relative_to(ROOT), "output must be outside the source tree")
        if args.out:
            output.mkdir(mode=0o700)
    except (OSError, RuntimeError) as error:
        print(f"CPU profiles: {error}", file=sys.stderr)
        return 1
    report = {"schema": SCHEMA, "status": "incomplete", "started_utc": datetime.now(timezone.utc).isoformat(),
              "scope": "bounded CPU execution matrix; emulation is not native silicon, proof or acceptance closure",
              "required_targets": TARGETS, "required_profiles": [name for name, _ in PROFILES],
              "controls": {"clean_committed_source": True, "locked_offline": True,
                           "fresh_target_directory": True, "jobs": args.jobs,
                           "timeout_seconds": args.timeout_seconds, "max_rss_gib": args.max_rss_gib},
              "runs": [], "errors": []}
    floor.write_report(output / "report.json", report)
    try:
        qualify(args, output, report)
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError, trust_toolchain.ToolchainError) as error:
        report["errors"].append(str(error))
        report["status"] = "fail"
    except KeyboardInterrupt:
        report["errors"].append("interrupted; matrix incomplete")
        report["status"] = "fail"
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    floor.write_report(output / "report.json", report)
    print(f"CPU profiles: {report['status'].upper()} ({output / 'report.json'})", flush=True)
    for error in report["errors"]:
        print(error, file=sys.stderr)
    return 0 if report["status"] == "pass" else 1


if __name__ == "__main__":
    sys.exit(main())
