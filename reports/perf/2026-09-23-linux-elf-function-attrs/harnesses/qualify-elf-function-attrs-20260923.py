#!/usr/bin/env python3
"""Qualifying Linux run for trust-ir v45 function visibility and sections on
AArch64 ELF (audit rows L02-P1, L02-P3), 2026-09-23.

Runs, on a clean checkout, the test targets the change adds to or touches, the
whole trust-cg-codegen and trust-cg-lower library suites, and records tool and
source identities. The two native test targets run with a private TMPDIR so
their evidence directories (objects, readelf output, linker output, run
output) can be harvested afterwards. Writes everything under --out, which must
be outside the source tree.
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

TARGETS = [
    ("codegen--aarch64_elf_symbol_binding",
     ["-p", "trust-cg-codegen", "--test", "aarch64_elf_symbol_binding", "--", "--test-threads=1"], True),
    ("codegen--e2e_aarch64_elf_sections",
     ["-p", "trust-cg-codegen", "--test", "e2e_aarch64_elf_sections", "--", "--test-threads=1"], True),
    ("codegen--aarch64_elf_dwarf", ["-p", "trust-cg-codegen", "--test", "aarch64_elf_dwarf"], False),
    ("codegen--e2e_aarch64_elf_relocation_model",
     ["-p", "trust-cg-codegen", "--test", "e2e_aarch64_elf_relocation_model"], False),
    ("codegen--v41_abi_residue_objects", ["-p", "trust-cg-codegen", "--test", "v41_abi_residue_objects"], False),
    ("lower--pin_move_floor", ["-p", "trust-cg-lower", "--test", "pin_move_floor"], False),
    ("lower--v41_contract_surface", ["-p", "trust-cg-lower", "--test", "v41_contract_surface"], False),
    ("codegen--lib", ["-p", "trust-cg-codegen", "--lib"], False),
    ("lower--lib", ["-p", "trust-cg-lower", "--lib"], False),
]

TOOLS = ["cc", "gcc", "ld", "ld.bfd", "readelf", "nm", "rustc", "cargo"]
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

    before = source_identity(source)
    if not before["clean"]:
        print("source tree is not clean", file=sys.stderr)
        return 2
    results = {"started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
               "source_before": before, "identities": identities(source, env), "runs": []}
    ok = True
    for name, cargo_args, native in TARGETS:
        run_env = dict(env)
        if native:
            run_env["TMPDIR"] = str(tmp)
        command = ["cargo", "test", "--locked", "--offline", "-j", str(args.jobs), *cargo_args]
        start = time.monotonic()
        with open(logs / f"{name}.log", "w") as handle:
            code = subprocess.run(command, cwd=source, env=run_env, stdout=handle,
                                  stderr=subprocess.STDOUT, timeout=3600, check=False).returncode
        elapsed = round(time.monotonic() - start, 1)
        text = (logs / f"{name}.log").read_text(errors="replace")
        lines = [line for line in text.splitlines() if line.startswith("test result:")]
        passed = [line for line in text.splitlines() if re.match(r"^test .* \.\.\. ok$", line)
                  or re.match(r"^test .* \.\.\. .*passed:", line)]
        results["runs"].append({"name": name, "command": command, "tmpdir": run_env.get("TMPDIR"),
                                "exit": code, "seconds": elapsed, "result_lines": lines})
        print(f"{name}: exit={code} {lines}")
        ok &= code == 0
    after = source_identity(source)
    results["source_after"] = after
    results["finished"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    results["verdict"] = "PASS" if ok and after == before else "FAIL"
    (out / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"verdict: {results['verdict']}")
    return 0 if results["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
