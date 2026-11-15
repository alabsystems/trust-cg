#!/usr/bin/env python3
"""Qualify the X-OPCODES-P11 NEON LD1/ST1 post-index target on a clean tree.

usage: qualify-neon-ld1-st1-20260923.py ROOT OUT

ROOT is a clean trust-cg checkout; OUT is a new directory outside it. The
script refuses a dirty tree, then runs, with its output captured under
OUT/logs:

- `neon_ld1_st1_post_execution` with the Linux floor's exact arguments, once
  with `TRUST_CG_LD1_ST1_RECORD_DIR=OUT/objects` (the test writes the objects
  it compiled and executed, the C oracle and the mutant outcomes there) and
  once without it; the Linux floor's own `classify_result` then judges the
  plain transcript;
- `cargo check -p trust-cg-codegen` with and without `verify`, the whole
  codegen library suite, the rustfmt gate, the three gate-script suites, the
  native host matrix, documentation and diagnostics census checks and the
  floor's `--list`.

It then disassembles every retained object with LLVM objdump (and GNU objdump
for ELF), counts LD1/ST1 post-index lines per function, dumps the ELF symbol
tables with GNU readelf, and writes OUT/results.json. The tree must still be
clean afterwards. Nothing here decides the gap; it records what ran.
"""
from __future__ import annotations

import collections
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time

ROOT = Path(sys.argv[1]).resolve()
OUT = Path(sys.argv[2]).resolve()
if OUT.exists():
    sys.exit(f"{OUT} exists")
if OUT.is_relative_to(ROOT):
    sys.exit("OUT must be outside ROOT")
HOME = Path.home()
TOOLS = HOME / ".local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin"
LLVM_OBJDUMP = HOME / ".local/bin/llvm-objdump"
GNU_OBJDUMP = Path("/usr/bin/objdump")
READELF = Path("/usr/bin/readelf")
ENV = dict(os.environ)
ENV["PATH"] = f"{TOOLS}:{HOME / '.cargo/bin'}:{ENV.get('PATH', '/usr/bin:/bin')}"
for key in ("TRUST_CG_LD1_ST1_RECORD_DIR", "TRUST_CG_DISABLE_PASSES", "TCG_NO_FMAP_LOOP_ROTATE",
            "RUST_TEST_THREADS", "RUST_TEST_NOCAPTURE", "CARGO_TARGET_DIR"):
    ENV.pop(key, None)
TARGET = ["cargo", "test", "--locked", "--offline", "--color", "never", "-j", "8",
          "-p", "trust-cg-codegen", "--test", "neon_ld1_st1_post_execution",
          "--", "--nocapture", "--test-threads=1"]
RESULT = re.compile(r"^test result: .*$", re.MULTILINE)


def git(*args: str) -> str:
    return subprocess.run(["git", "-C", str(ROOT), *args], capture_output=True, text=True,
                          check=True).stdout.strip()


def status() -> str:
    return git("status", "--porcelain", "--untracked-files=all")


def probe(command: list[str]) -> str:
    try:
        done = subprocess.run(command, capture_output=True, text=True, env=ENV, timeout=60)
        return (done.stdout or done.stderr).strip().splitlines()[0]
    except (OSError, IndexError, subprocess.TimeoutExpired) as error:
        return f"unavailable: {error}"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(name: str, command: list[str], extra: dict | None = None, timeout: int = 1800) -> dict:
    log = OUT / "logs" / f"{name}.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    env = dict(ENV, **(extra or {}))
    started = time.time()
    with log.open("wb") as handle:
        done = subprocess.run(command, cwd=ROOT, env=env, stdout=handle, stderr=subprocess.STDOUT,
                              timeout=timeout)
    text = log.read_text(errors="replace")
    record = {
        "name": name, "command": command, "environment": extra or {}, "exit": done.returncode,
        "seconds": round(time.time() - started, 1), "log": f"logs/{name}.log",
        "test_results": RESULT.findall(text),
    }
    print(f"{name}: exit {done.returncode} {record['test_results']}", flush=True)
    return record


if status():
    sys.exit("the tree is dirty; refusing to qualify")
OUT.mkdir(parents=True)
head = git("rev-parse", "HEAD")
results: dict = {
    "schema": "trust-cg-neon-ld1-st1-qualification-v2",
    "source": {"head": head, "tree": git("rev-parse", "HEAD^{tree}"), "clean_before": True},
    "host": {
        "uname": " ".join(platform.uname()),
        "cpu_features": next((line.split(":", 1)[1].strip() for line in
                              Path("/proc/cpuinfo").read_text().splitlines()
                              if line.startswith("Features")), None),
        "cc": probe(["cc", "--version"]),
        "rustc": probe(["rustc", "--version"]),
        "cargo": probe(["cargo", "--version"]),
        "llvm_objdump": probe([str(LLVM_OBJDUMP), "--version"]) + " " + str(LLVM_OBJDUMP),
        "gnu_objdump": probe([str(GNU_OBJDUMP), "--version"]),
        "readelf": probe([str(READELF), "--version"]),
        "ay": probe(["ay", "--version"]),
    },
    "commands": [],
}
commands = results["commands"]
objects = OUT / "objects"
commands.append(run("neon_ld1_st1_post_execution-recorded", TARGET,
                    {"TRUST_CG_LD1_ST1_RECORD_DIR": str(objects)}))
commands.append(run("neon_ld1_st1_post_execution", TARGET))
spec = importlib.util.spec_from_file_location("linux_floor", ROOT / "scripts/check_linux_aarch64.py")
floor = importlib.util.module_from_spec(spec)
sys.modules["linux_floor"] = floor
spec.loader.exec_module(floor)
plain = commands[-1]
results["floor_classification"] = floor.classify_result(
    plain["exit"], (OUT / plain["log"]).read_text(errors="replace"))
results["floor_contains_target"] = ("trust-cg-codegen", "neon_ld1_st1_post_execution") in floor.TARGETS
results["floor_target_count"] = len(floor.TARGETS)
cargo = ["cargo", "--color", "never"]
commands.append(run("codegen-check", [*cargo, "check", "--locked", "--offline", "-j", "8",
                                      "-p", "trust-cg-codegen"]))
commands.append(run("codegen-check-verify", [*cargo, "check", "--locked", "--offline", "-j", "8",
                                             "-p", "trust-cg-codegen", "--features", "verify"]))
commands.append(run("codegen-lib", [*cargo, "test", "--locked", "--offline", "-j", "8",
                                    "-p", "trust-cg-codegen", "--lib"], timeout=3600))
commands.append(run("check_fmt", ["bash", "scripts/check_fmt.sh"]))
commands.append(run("gate-script-tests", [sys.executable, "-B", "-m", "unittest",
                                          "scripts/tests/test_linux_aarch64_gate.py",
                                          "scripts/tests/test_darwin_aarch64_gate.py",
                                          "scripts/tests/test_linux_aarch64_bridge_gate.py"]))
commands.append(run("native-host-matrix", [sys.executable, "scripts/native_test_host_matrix.py", "--check"]))
commands.append(run("documentation", [sys.executable, "scripts/check_documentation.py", "--check"]))
commands.append(run("diagnostics", [sys.executable, "scripts/generate_diagnostics_inventory.py", "--check"]))
commands.append(run("linux-floor-list", [sys.executable, "scripts/check_linux_aarch64.py", "--list"]))

# External disassemblers over every retained object.
LINE = {
    "llvm": re.compile(r"\s(ld1|st1)\s+\{ v\d+\.(4s|2d) \}, \[x\d+\], #16$"),
    "llvm-apple": re.compile(r"\s(ld1|st1)\.(4s|2d)\s+\{ v\d+ \}, \[x\d+\], #16$"),
    "gnu": re.compile(r"\s(ld1|st1)\s+\{v\d+\.(4s|2d)\}, \[x\d+\], #16$"),
}
FUNCTION = re.compile(r"^[0-9a-f]+ <([^>]+)>:$")
external: dict = {}
for path in sorted(objects.glob("*.o")):
    elf = path.read_bytes().startswith(b"\x7fELF")
    entry: dict = {"sha256": sha256(path), "bytes": path.stat().st_size,
                   "format": "ELF" if elf else "Mach-O", "disassembly": {}}
    tools = [("llvm", [str(LLVM_OBJDUMP), "-d", "--no-show-raw-insn"])]
    if elf:
        tools.append(("gnu", [str(GNU_OBJDUMP), "-d"]))
    for tool, command in tools:
        text = subprocess.run(command + [str(path)], capture_output=True, text=True, check=True).stdout
        listing = OUT / "disasm" / f"{path.stem}.{tool}-objdump.txt"
        listing.parent.mkdir(parents=True, exist_ok=True)
        listing.write_text(text)
        pattern = LINE["gnu"] if tool == "gnu" else LINE["llvm" if elf else "llvm-apple"]
        per = collections.defaultdict(lambda: {"ld1": 0, "st1": 0})
        function = None
        for line in text.splitlines():
            match = FUNCTION.match(line)
            if match:
                function = match.group(1).removeprefix("_")
                continue
            match = pattern.search(line)
            if match:
                per[function][match.group(1)] += 1
        entry["disassembly"][tool] = {
            "listing": listing.relative_to(OUT).as_posix(),
            "ld1": sum(count["ld1"] for count in per.values()),
            "st1": sum(count["st1"] for count in per.values()),
            "per_function": dict(sorted(per.items())),
        }
    if elf:
        symbols = subprocess.run([str(READELF), "-sW", str(path)], capture_output=True, text=True,
                                 check=True).stdout
        listing = OUT / "symbols" / f"{path.stem}.readelf-sW.txt"
        listing.parent.mkdir(parents=True, exist_ok=True)
        listing.write_text(symbols)
        entry["symbols"] = listing.relative_to(OUT).as_posix()
    external[path.name] = entry
results["objects"] = external

mutants: dict = {}
for tsv in sorted(objects.glob("mutants-*.tsv")):
    rows = [line.split("\t") for line in tsv.read_text().splitlines()[1:]]
    mutants[tsv.name] = {
        "rows": len(rows),
        "by_mutation": dict(collections.Counter(row[2] for row in rows)),
        "exit_statuses": dict(collections.Counter(row[6] for row in rows)),
        "oracle_mismatch_lines": sum(row[7].startswith(f"MISMATCH {row[1]} ") for row in rows),
        # Columns 8-9 (added with the writeback-only class): the decode gate's
        # verdict and whether the oracle must catch the mutant.
        "decode_gate": dict(collections.Counter(row[8] for row in rows)),
        "oracle_expected": dict(collections.Counter(row[9] for row in rows)),
        "writeback_only_passing_oracle_and_refused": sum(
            row[9] == "pass" and row[6] == "Some(0)" and row[8] == "refused"
            and row[7].startswith("NEON_LD1_ST1_POST_CASES=") for row in rows),
    }
results["mutants"] = mutants
results["source"]["clean_after"] = not status()
results["source"]["head_after"] = git("rev-parse", "HEAD")
(OUT / "results.json").write_text(json.dumps(results, indent=2) + "\n")
failed = [command["name"] for command in commands if command["exit"] != 0]
print(json.dumps({"failed": failed, "floor": results["floor_classification"].get("status"),
                  "clean_after": results["source"]["clean_after"]}))
sys.exit(1 if failed or not results["source"]["clean_after"] else 0)
