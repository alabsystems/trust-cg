#!/usr/bin/env python3
"""Qualifying run for the L05-P3 ARC-op increment on Linux AArch64 (2026-09-23).

Runs, on a clean checkout, the new `e2e_aarch64_arc_ops_linux` target (with
ARC_OPS_LINUX_RETAIN_DIR so each level's object, driver and binaries are kept),
the `e2e_aarch64_heap_dealloc_linux` twin and the trust-ir construct inventory
target, then `readelf -rW` and `llvm-objdump -dr` on every retained object. It
records source identity (HEAD, tree, porcelain status before and after the
runs), tool identities and one capture.json per command, and assembles the
archive directory with gzip-compressed objects and an inventory.json that
scripts/check_evidence_archive.py verifies.

    qualify-arc-ops-20260923.py --repo REPO --scratch DIR --archive DIR

The archive directory must not exist. Nothing here decides that a claim is
true: the libtest results and the driver verdicts in the logs are the evidence.
"""

from __future__ import annotations

import argparse
import datetime as dt
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

LEVELS = ("O0", "O1", "O2", "O3")
RC = ("clean_inc", "clean_dec", "clean_is_exclusive")
ALLOC = ("malloc", "free", "__rust_alloc", "__rust_dealloc")
ENV_KEYS = ("PATH", "ARC_OPS_LINUX_RETAIN_DIR", "CARGO_TARGET_DIR", "RUST_MIN_STACK")


def now() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_id(path: Path) -> dict:
    data = path.read_bytes()
    return {"sha256": sha(data), "bytes": len(data)}


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True,
                          text=True).stdout


def run(name: str, argv: list[str], cwd: Path, env: dict, logs: Path, timeout: int) -> dict:
    """Run one command, keeping its combined output and a capture record."""
    start = now()
    proc = subprocess.run(argv, cwd=cwd, env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, timeout=timeout)
    end = now()
    log = logs / f"{name}.log"
    log.write_bytes(proc.stdout)
    capture = {
        "name": name, "argv": argv, "cwd": str(cwd),
        "environment": {key: env.get(key) for key in ENV_KEYS},
        "started": start, "finished": end, "returncode": proc.returncode,
        "log": log.name, "log_sha256": sha(proc.stdout), "log_bytes": len(proc.stdout),
    }
    (logs / f"{name}.capture.json").write_text(json.dumps(capture, indent=2) + "\n")
    print(f"{name}: exit {proc.returncode}", flush=True)
    return capture


def result_lines(text: str) -> list[str]:
    return [line.strip() for line in text.splitlines() if line.startswith("test result:")]


def tool_identity(env: dict) -> dict:
    tools = {}
    probes = {
        "cc": ["cc", "--version"], "ld": ["ld", "--version"], "readelf": ["readelf", "--version"],
        "rustc": ["rustc", "-vV"], "cargo": ["cargo", "-V"], "uname": ["uname", "-a"],
        "llvm-objdump": [str(Path.home() / ".local/bin/llvm-objdump"), "--version"],
        "ldd": ["ldd", "--version"],
    }
    for name, argv in probes.items():
        resolved = shutil.which(argv[0], path=env["PATH"]) if "/" not in argv[0] else argv[0]
        out = subprocess.run(argv, env=env, capture_output=True, text=True)
        entry = {"argv": argv, "resolved": resolved,
                 "output_head": (out.stdout or out.stderr).splitlines()[:3]}
        if resolved:
            real = Path(resolved).resolve()
            entry["realpath"] = str(real)
            entry["sha256"] = sha(real.read_bytes())
        tools[name] = entry
    return tools


def call26_counts(readelf_text: str) -> dict:
    counts = {name: 0 for name in RC + ALLOC}
    for line in readelf_text.splitlines():
        fields = line.split()
        if len(fields) >= 5 and fields[2] == "R_AARCH64_CALL26" and fields[4] in counts:
            counts[fields[4]] += 1
    return counts


def is_exclusive_normalization(objdump_text: str) -> dict:
    """Per `clean_is_exclusive` call site: is `uxtb wN, w0` among the next
    four instructions (the byte normalization of the u8 result)?"""
    lines = objdump_text.splitlines()
    sites, normalized = 0, 0
    for index, line in enumerate(lines):
        if "R_AARCH64_CALL26" in line and line.split()[-1] == "clean_is_exclusive":
            sites += 1
            window = [text for text in lines[index + 1:index + 5] if "R_AARCH64" not in text]
            if any(re.search(r"\buxtb\s+w\d+, w0\b", text) for text in window):
                normalized += 1
    return {"call_sites": sites, "uxtb_w0_within_4": normalized}


def gz(src: Path, dst: Path) -> dict:
    data = src.read_bytes()
    dst.parent.mkdir(parents=True, exist_ok=True)
    stored = gzip.compress(data, compresslevel=9, mtime=0)
    dst.write_bytes(stored)
    return {"sha256": sha(data), "bytes": len(data), "stored_sha256": sha(stored),
            "stored_bytes": len(stored)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--scratch", type=Path, required=True)
    parser.add_argument("--archive", type=Path, required=True)
    args = parser.parse_args()
    repo, scratch, archive = args.repo.resolve(), args.scratch.resolve(), args.archive.resolve()
    if archive.exists():
        raise SystemExit(f"{archive} exists")
    if scratch.exists():
        raise SystemExit(f"{scratch} exists")
    scratch.mkdir(parents=True)
    logs = scratch / "logs"
    logs.mkdir()
    retain = scratch / "retain"

    status_before = git(repo, "status", "--porcelain", "--untracked-files=all")
    if status_before:
        raise SystemExit(f"checkout is not clean:\n{status_before}")
    source = {
        "head": git(repo, "rev-parse", "HEAD").strip(),
        "tree": git(repo, "rev-parse", "HEAD^{tree}").strip(),
        "status_before": status_before,
    }
    env = dict(os.environ)
    home = Path.home()
    env["PATH"] = os.pathsep.join([
        str(home / ".local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin"),
        str(home / ".cargo/bin"), env.get("PATH", ""),
    ])
    for key in list(env):
        if key.startswith(("TCG_", "TRUST_CG_")):
            del env[key]
    tools = tool_identity(env)

    cargo = ["cargo", "test", "--locked", "--offline", "-j", "8"]
    captures = []
    arc_env = dict(env, ARC_OPS_LINUX_RETAIN_DIR=str(retain))
    captures.append(run("arc_ops_linux", cargo + [
        "-p", "trust-cg-codegen", "--test", "e2e_aarch64_arc_ops_linux", "--",
        "--nocapture", "--test-threads=1"], repo, arc_env, logs, 1800))
    captures.append(run("heap_dealloc_linux", cargo + [
        "-p", "trust-cg-codegen", "--test", "e2e_aarch64_heap_dealloc_linux", "--",
        "--nocapture", "--test-threads=1"], repo, env, logs, 1800))
    captures.append(run("construct_inventory", cargo + [
        "-p", "trust-cg-lower", "--test", "trust_ir_construct_inventory", "--",
        "--test-threads=1"], repo, env, logs, 1800))
    objdump = str(home / ".local/bin/llvm-objdump")
    # Re-run each retained binary to keep the driver's own output (its
    # per-step traces); the test prints it only on failure. The two
    # self-check builds must fail.
    expect_failure = set()
    for level in LEVELS:
        obj = retain / f"arc-ops-{level}" / "module.o"
        captures.append(run(f"readelf-rW-{level}", ["readelf", "-rW", str(obj)], repo, env, logs, 120))
        captures.append(run(f"objdump-dr-{level}", [objdump, "-dr", str(obj)], repo, env, logs, 120))
        captures.append(run(f"driver-{level}", [str(retain / f"arc-ops-{level}" / "driver")],
                            repo, env, logs, 120))
        for variant in ("driver-inverted", "driver-never-free"):
            name = f"{variant}-{level}"
            expect_failure.add(name)
            captures.append(run(name, [str(retain / f"self-check-{level}" / variant)],
                                repo, env, logs, 120))
    status_after = git(repo, "status", "--porcelain", "--untracked-files=all")
    source["status_after"] = status_after

    # Assemble the archive.
    archive.mkdir(parents=True)
    entries: list[dict] = []

    def add_plain(src: Path, rel: str) -> None:
        dst = archive / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src, dst)
        entries.append({"path": rel, **file_id(dst)})

    def add_gz(src: Path, rel: str) -> dict:
        record = gz(src, archive / rel)
        entries.append({"path": rel, **record})
        return record

    levels = {}
    driver_hashes = set()
    for level in LEVELS:
        run_dir = retain / f"arc-ops-{level}"
        check_dir = retain / f"self-check-{level}"
        obj = add_gz(run_dir / "module.o", f"records/objects/arc-ops-{level}/module.o.gz")
        driver_hashes.add(file_id(run_dir / "driver.c")["sha256"])
        driver_hashes.add(file_id(check_dir / "driver.c")["sha256"])
        if file_id(check_dir / "module.o") != file_id(run_dir / "module.o"):
            raise SystemExit(f"{level}: self-check object differs from the positive run's")
        readelf_log = (logs / f"readelf-rW-{level}.log").read_text()
        levels[level] = {
            "object": {"sha256": obj["sha256"], "bytes": obj["bytes"]},
            "binaries": {
                "driver": file_id(run_dir / "driver"),
                "driver-inverted": file_id(check_dir / "driver-inverted"),
                "driver-never-free": file_id(check_dir / "driver-never-free"),
            },
            "call26_from_readelf": call26_counts(readelf_log),
            "is_exclusive_result": is_exclusive_normalization(
                (logs / f"objdump-dr-{level}.log").read_text()),
            "driver_last_line": (logs / f"driver-{level}.log").read_text().strip().splitlines()[-1],
        }
    if len(driver_hashes) != 1:
        raise SystemExit("driver.c differs between levels")
    add_plain(retain / "arc-ops-O0" / "driver.c", "records/objects/driver.c")
    logs_out = {}
    for capture in captures:
        name = capture["name"]
        log = logs / capture["log"]
        if name.startswith("objdump"):
            add_gz(log, f"records/commands/{name}.log.gz")
        else:
            add_plain(log, f"records/commands/{name}.log")
        add_plain(logs / f"{name}.capture.json", f"records/commands/{name}.capture.json")
        text = log.read_text(errors="replace")
        logs_out[name] = {"returncode": capture["returncode"],
                          "expected_to_fail": name in expect_failure,
                          "test_results": result_lines(text),
                          "last_line": (text.strip().splitlines() or [""])[-1]}
    arc_log = (logs / "arc_ops_linux.log").read_text()
    results = {
        "schema": "trust-cg-linux-arc-ops-v1",
        "source": source,
        "host": tools["uname"]["output_head"],
        "commands": logs_out,
        "levels": levels,
        "driver_c_sha256": driver_hashes.pop(),
        # libtest prints a test's first output line after `test NAME ... `,
        # so these are not anchored at the start of a line.
        "native_verdicts": re.findall(r"(O[0-3]: PASS \d+ arc checks[^\n]*)", arc_log),
        "self_checks": re.findall(r"(O[0-3]: inverted polarity fails[^\n]*)", arc_log),
        "interpreter": re.findall(r"interpreter ([^\n]*)", arc_log),
        "call26_sites_test": re.findall(r"(O[0-3]: CALL26 BL sites [^\n]*)", arc_log),
    }
    for name, data in (("results.json", results), ("source.json", source), ("tools.json", tools)):
        path = scratch / name
        path.write_text(json.dumps(data, indent=2) + "\n")
        add_plain(path, f"records/{name}")
    add_plain(Path(__file__).resolve(), "harnesses/qualify-arc-ops-20260923.py")
    print(json.dumps({"head": source["head"], "status_after_empty": not status_after,
                      "commands": logs_out}, indent=2))
    (scratch / "entries.json").write_text(json.dumps(entries, indent=2) + "\n")
    verdicts_ok = all((c["returncode"] != 0) == (c["name"] in expect_failure) for c in captures)
    return 0 if verdicts_ok and not status_after else 1


if __name__ == "__main__":
    sys.exit(main())
