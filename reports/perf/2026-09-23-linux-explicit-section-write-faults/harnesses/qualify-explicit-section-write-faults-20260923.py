#!/usr/bin/env python3
"""Qualifying Linux AArch64 run for the L02-P3 explicit-section placement
repair (default-link write faults; touches L02-P7), 2026-09-23.

Runs, on a clean checkout, e2e_aarch64_elf_sections (with a private TMPDIR,
TCG_RETAIN_TEST_EVIDENCE=1 so the native rows keep their objects, drivers,
linker diagnostics and run records, and TCG_REQUIRE_LLD=1 so the LLD legs
cannot be skipped), the other ELF global/section targets the task names,
the whole trust-cg-codegen library suite, `cargo check --features verify`
and the script gates. Records tool and source identities before and after.
Writes everything under --out, which must be outside the source tree.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

PKG = Path.home() / ".local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23"

# (log name, command, native evidence retained)
CARGO_TARGETS = [
    ("codegen--e2e_aarch64_elf_sections",
     ["-p", "trust-cg-codegen", "--test", "e2e_aarch64_elf_sections"], True),
    ("codegen--e2e_aarch64_elf_stack_zero_fill",
     ["-p", "trust-cg-codegen", "--test", "e2e_aarch64_elf_stack_zero_fill"], False),
    ("codegen--e2e_aarch64_globals_linux",
     ["-p", "trust-cg-codegen", "--test", "e2e_aarch64_globals_linux"], False),
    ("codegen--e2e_aarch64_elf_tlsie", ["-p", "trust-cg-codegen", "--test", "e2e_aarch64_elf_tlsie"], False),
    ("codegen--v41_global_linkage", ["-p", "trust-cg-codegen", "--test", "v41_global_linkage"], False),
    ("codegen--aarch64_elf_symbol_binding",
     ["-p", "trust-cg-codegen", "--test", "aarch64_elf_symbol_binding"], False),
    ("codegen--e2e_aarch64_elf_relocation_model",
     ["-p", "trust-cg-codegen", "--test", "e2e_aarch64_elf_relocation_model"], False),
    ("codegen--e2e_aarch64_elf_link", ["-p", "trust-cg-codegen", "--test", "e2e_aarch64_elf_link"], False),
    ("codegen--lib", ["-p", "trust-cg-codegen", "--lib"], False),
]

# `cargo check` gates (not libtest).
CARGO_CHECKS = [
    ("codegen--check-verify", ["-p", "trust-cg-codegen", "--features", "verify"]),
]

SCRIPT_GATES = [
    ("script--gate-unittests",
     ["python3", "-B", "-m", "unittest", "scripts/tests/test_linux_aarch64_gate.py",
      "scripts/tests/test_darwin_aarch64_gate.py", "scripts/tests/test_linux_aarch64_bridge_gate.py"]),
    ("script--native-test-host-matrix", ["python3", "scripts/native_test_host_matrix.py", "--check"]),
    ("script--check-documentation", ["python3", "scripts/check_documentation.py", "--check"]),
    ("script--diagnostics-inventory", ["python3", "scripts/generate_diagnostics_inventory.py", "--check"]),
    ("script--check-fmt", ["bash", "scripts/check_fmt.sh"]),
    ("script--darwin-floor-list", ["python3", "scripts/check_darwin_aarch64.py", "--list"]),
    ("script--linux-floor-list", ["python3", "scripts/check_linux_aarch64.py", "--list"]),
]

TOOLS = ["cc", "gcc", "ld", "ld.bfd", "ld.lld", "readelf", "nm", "llvm-readelf", "rustc", "cargo"]
LIBS = ["/lib/aarch64-linux-gnu/libc.so.6", "/lib/ld-linux-aarch64.so.1"]


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def capture(command: list[str], cwd: Path | None = None, env: dict | None = None) -> str:
    return subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True, check=False).stdout


def identities(source: Path, env: dict) -> dict:
    tools = {}
    for tool in TOOLS:
        resolved = shutil.which(tool, path=env["PATH"])
        if resolved is None:
            continue
        real = Path(resolved).resolve()
        version = capture([resolved, "--version"], env=env).splitlines()[:1]
        tools[tool] = {"path": resolved, "resolved": str(real), "sha256": sha256(real),
                       "version": version[0] if version else ""}
    sysroot = capture(["rustc", "--print", "sysroot"], cwd=source, env=env).strip()
    real_rustc = Path(sysroot) / "bin" / "rustc"
    tools["rustc(toolchain)"] = {"path": str(real_rustc), "sha256": sha256(real_rustc),
                                 "version": capture([str(real_rustc), "-V"], env=env).strip()}
    libs = {lib: {"resolved": str(Path(lib).resolve()), "sha256": sha256(Path(lib).resolve())}
            for lib in LIBS if Path(lib).exists()}
    glibc = capture(["ldd", "--version"], env=env).splitlines()[:1]
    return {
        "tools": tools,
        "libraries": libs,
        "glibc": glibc[0] if glibc else "",
        "uname": capture(["uname", "-srvmo"]).strip(),
    }


def source_identity(source: Path) -> dict:
    head = capture(["git", "rev-parse", "HEAD"], cwd=source).strip()
    status = capture(["git", "status", "--porcelain", "--untracked-files=all"], cwd=source)
    tree = capture(["git", "rev-parse", "HEAD^{tree}"], cwd=source).strip()
    lock = sha256(source / "Cargo.lock")
    trust_ir = re.search(r'name = "trust-ir"\nversion = "[^"]+"\nsource = "([^"]+)"',
                         (source / "Cargo.lock").read_text())
    return {"head": head, "tree": tree, "clean": status == "", "porcelain": status,
            "cargo_lock_sha256": lock, "trust_ir_source": trust_ir.group(1) if trust_ir else None}


def run_logged(name: str, command: list[str], cwd: Path, env: dict, logs: Path) -> dict:
    start = time.monotonic()
    with open(logs / f"{name}.log", "w") as handle:
        code = subprocess.run(command, cwd=cwd, env=env, stdout=handle, stderr=subprocess.STDOUT,
                              timeout=3600, check=False).returncode
    elapsed = round(time.monotonic() - start, 1)
    text = (logs / f"{name}.log").read_text(errors="replace")
    lines = [line for line in text.splitlines() if line.startswith("test result:")]
    print(f"{name}: exit={code} {lines}", flush=True)
    return {"name": name, "command": command, "tmpdir": env.get("TMPDIR"),
            "retain_evidence": env.get("TCG_RETAIN_TEST_EVIDENCE"), "exit": code,
            "seconds": elapsed, "result_lines": lines}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=8)
    args = parser.parse_args()
    source, out = args.source.resolve(), args.out.resolve()
    if out.is_relative_to(source):
        parser.error("--out must be outside the source tree")
    logs, tmp = out / "logs", out / "tmp"
    logs.mkdir(parents=True, exist_ok=False)
    tmp.mkdir()
    env = dict(os.environ)
    env["PATH"] = f"{PKG / 'bin'}:{Path.home() / '.cargo/bin'}:{env['PATH']}"
    env["LC_ALL"] = "C"
    env.pop("TCG_RETAIN_TEST_EVIDENCE", None)

    before = source_identity(source)
    if not before["clean"]:
        print("source tree is not clean", file=sys.stderr)
        return 2
    results = {"started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
               "source_before": before, "identities": identities(source, env), "runs": []}
    ok = True
    for name, cargo_args, native in CARGO_TARGETS:
        run_env = dict(env)
        if native:
            run_env["TMPDIR"] = str(tmp)
            run_env["TCG_RETAIN_TEST_EVIDENCE"] = "1"
            run_env["TCG_REQUIRE_LLD"] = "1"
        command = ["cargo", "test", "--locked", "--offline", "-j", str(args.jobs), *cargo_args]
        if native:
            command += ["--", "--nocapture"]
        record = run_logged(name, command, source, run_env, logs)
        results["runs"].append(record)
        ok &= record["exit"] == 0
    for name, cargo_args in CARGO_CHECKS:
        command = ["cargo", "check", "--locked", "--offline", "-j", str(args.jobs), *cargo_args]
        record = run_logged(name, command, source, env, logs)
        results["runs"].append(record)
        ok &= record["exit"] == 0
    for name, command in SCRIPT_GATES:
        record = run_logged(name, command, source, env, logs)
        results["runs"].append(record)
        ok &= record["exit"] == 0
    after = source_identity(source)
    results["source_after"] = after
    results["finished"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    results["verdict"] = "PASS" if ok and after == before else "FAIL"
    (out / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"verdict: {results['verdict']}")
    return 0 if results["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
