#!/usr/bin/env python3
"""Qualify the X-OPCODES-P11 live LD1/ST1 writeback target on a clean tree.

usage: qualify-neon-butterfly-writeback-20260923.py ROOT OUT

ROOT is a clean trust-cg checkout; OUT is a new directory outside it. The
script refuses a dirty tree, then runs, with its output captured under
OUT/logs:

- `neon_butterfly_writeback_execution` with the Linux floor's exact
  arguments, once with `TRUST_CG_BUTTERFLY_RECORD_DIR=OUT/objects` (the test
  writes the objects it compiled and executed, its liveness reports, the C
  oracle and the mutant outcomes there) and once without it; the Linux
  floor's own `classify_result` then judges the plain transcript;
- the sibling target `neon_ld1_st1_post_execution` (its header now points at
  this target), also judged by `classify_result`;
- `cargo check -p trust-cg-codegen` with and without `verify`, the whole
  codegen library suite, the rustfmt gate, the three gate-script suites, the
  native host matrix, documentation and diagnostics census checks and the
  floor's `--list`.

It then disassembles every retained object with LLVM objdump (and GNU objdump
for ELF), counts LD1/ST1 post-index lines per function and, for each
butterfly kernel of the O2/O3 objects, checks in the external listing that
the vector loop's backward branch targets the first LD1 and that each of the
four base registers appears in the loop body only as the base of its own
post-index LD1/ST1. It dumps the ELF symbol tables with GNU readelf and
writes OUT/results.json. The tree must still be clean afterwards. Nothing
here decides the gap; it records what ran.
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
for key in ("TRUST_CG_BUTTERFLY_RECORD_DIR", "TRUST_CG_LD1_ST1_RECORD_DIR",
            "TRUST_CG_DISABLE_PASSES", "TRUST_CG_DUMP_MIR", "TRUST_CG_DUMP_NEONBUTTERFLY",
            "RUST_TEST_THREADS", "RUST_TEST_NOCAPTURE", "CARGO_TARGET_DIR"):
    ENV.pop(key, None)
KERNELS = ("bfly_nested_e0", "bfly_nested_e8", "bfly_hoisted_e8")


def target(name: str) -> list[str]:
    return ["cargo", "test", "--locked", "--offline", "--color", "never", "-j", "8",
            "-p", "trust-cg-codegen", "--test", name, "--", "--nocapture", "--test-threads=1"]


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
    "schema": "trust-cg-neon-butterfly-writeback-qualification-v1",
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
commands.append(run("neon_butterfly_writeback_execution-recorded",
                    target("neon_butterfly_writeback_execution"),
                    {"TRUST_CG_BUTTERFLY_RECORD_DIR": str(objects)}))
commands.append(run("neon_butterfly_writeback_execution",
                    target("neon_butterfly_writeback_execution")))
plain = commands[-1]
commands.append(run("neon_ld1_st1_post_execution", target("neon_ld1_st1_post_execution")))
sibling = commands[-1]
spec = importlib.util.spec_from_file_location("linux_floor", ROOT / "scripts/check_linux_aarch64.py")
floor = importlib.util.module_from_spec(spec)
sys.modules["linux_floor"] = floor
spec.loader.exec_module(floor)
results["floor_classification"] = floor.classify_result(
    plain["exit"], (OUT / plain["log"]).read_text(errors="replace"))
results["floor_classification_sibling"] = floor.classify_result(
    sibling["exit"], (OUT / sibling["log"]).read_text(errors="replace"))
results["floor_contains_target"] = (
    ("trust-cg-codegen", "neon_butterfly_writeback_execution") in floor.TARGETS)
results["floor_target_count"] = len(floor.TARGETS)
spec = importlib.util.spec_from_file_location("darwin_floor", ROOT / "scripts/check_darwin_aarch64.py")
darwin = importlib.util.module_from_spec(spec)
sys.modules["darwin_floor"] = darwin
spec.loader.exec_module(darwin)
results["darwin_rows"] = [list(row) for row in darwin.TARGETS
                          if row[1] == "neon_butterfly_writeback_execution"]
results["darwin_row_count"] = len(darwin.TARGETS)
results["darwin_minimum_total"] = sum(row[2] for row in darwin.TARGETS)
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
POST = {
    "llvm": re.compile(r"^\s*([0-9a-f]+):\s+(ld1|st1)\s+\{ v\d+\.4s \}, \[x(\d+)\], #16$"),
    "llvm-apple": re.compile(r"^\s*([0-9a-f]+):\s+(ld1|st1)\.4s\s+\{ v\d+ \}, \[x(\d+)\], #16$"),
    "gnu": re.compile(r"^\s*([0-9a-f]+):\s+[0-9a-f]{8}\s+(ld1|st1)\s+\{v\d+\.4s\}, \[x(\d+)\], #16$"),
}
INSN = {
    "llvm": re.compile(r"^\s*([0-9a-f]+):\s+(\S+)\s*(.*)$"),
    "gnu": re.compile(r"^\s*([0-9a-f]+):\s+[0-9a-f]{8}\s+(\S+)\s*(.*)$"),
}
FUNCTION = re.compile(r"^[0-9a-f]+ <([^>]+)>:$")


def listing_functions(text: str, tool: str) -> dict:
    """Function name -> [(address, mnemonic, operands)] from an objdump listing."""
    functions: dict = {}
    current = None
    pattern = INSN["gnu" if tool == "gnu" else "llvm"]
    for line in text.splitlines():
        match = FUNCTION.match(line)
        if match:
            current = functions.setdefault(match.group(1).removeprefix("_"), [])
            continue
        match = pattern.match(line)
        if match and current is not None:
            current.append((int(match.group(1), 16), match.group(2), match.group(3)))
    return functions


def loop_check(instructions: list, posts: list) -> dict:
    """The external liveness cross-check for one butterfly kernel."""
    top = min(address for address, _, _ in posts)
    back = [address for address, mnemonic, operands in instructions
            if mnemonic.startswith("b.") and re.match(rf"(0x)?{top:x}\b", operands)]
    if len(back) != 1:
        return {"ok": False, "why": f"{len(back)} conditional branches to the loop top {top:#x}"}
    body = [row for row in instructions if top <= row[0] <= back[0]]
    bases = sorted({int(register) for _, _, register in posts})
    offenders = []
    for register in bases:
        spelled = re.compile(rf"\b[xw]{register}\b")
        users = [(address, mnemonic, operands) for address, mnemonic, operands in body
                 if spelled.search(operands)]
        own = [row for row in users
               if row[1].split(".")[0] in ("ld1", "st1") and f"[x{register}], #16" in row[2]]
        if users != own or len(own) != 1:
            offenders.append({"register": f"x{register}", "users": users})
    return {"ok": not offenders and len(bases) == 4, "loop_top": f"{top:#x}",
            "back_edge": f"{back[0]:#x}", "body_words": len(body),
            "bases": [f"x{register}" for register in bases], "offenders": offenders}


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
        pattern = POST["gnu"] if tool == "gnu" else POST["llvm" if elf else "llvm-apple"]
        per = collections.defaultdict(lambda: {"ld1": 0, "st1": 0})
        posts = collections.defaultdict(list)
        function = None
        for line in text.splitlines():
            match = FUNCTION.match(line)
            if match:
                function = match.group(1).removeprefix("_")
                continue
            match = pattern.match(line)
            if match:
                per[function][match.group(2)] += 1
                posts[function].append((int(match.group(1), 16), match.group(2), match.group(3)))
        functions = listing_functions(text, tool)
        loops = {name: loop_check(functions[name], posts[name])
                 for name in KERNELS if name in functions and posts.get(name)}
        entry["disassembly"][tool] = {
            "listing": listing.relative_to(OUT).as_posix(),
            "ld1": sum(count["ld1"] for count in per.values()),
            "st1": sum(count["st1"] for count in per.values()),
            "per_function": dict(sorted(per.items())),
            "butterfly_loops": loops,
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
    lines = tsv.read_text().splitlines()
    header = lines[0].split("\t")
    rows = [dict(zip(header, line.split("\t"))) for line in lines[1:]]
    writeback = [row for row in rows if row["mutation"].split(" ", 1)[1]
                 in ("no writeback", "wrong-stride register post-index")]
    transfer = [row for row in rows if row not in writeback]
    number = lambda row, key: int(row[key])  # noqa: E731
    mutants[tsv.name] = {
        "rows": len(rows),
        "by_mutation": dict(collections.Counter(row["mutation"] for row in rows)),
        "exit_statuses": dict(collections.Counter(row["status"] for row in rows)),
        "decode_gate": dict(collections.Counter(row["decode_gate"] for row in rows)),
        "all_failed_the_oracle": all(row["status"] == "Some(1)" and number(row, "mismatched") > 0
                                     for row in rows),
        "scalar_path_mismatches": sum(number(row, "mismatched_scalar") for row in rows),
        "writeback_only": {
            "rows": len(writeback),
            "one_pair_mismatches": sum(number(row, "mismatched_vec_single") for row in writeback),
            "multi_pair_mismatches_min": min(number(row, "mismatched_vec_multi") for row in writeback),
            "multi_pair_mismatches_max": max(number(row, "mismatched_vec_multi") for row in writeback),
            "finite_multi_pair_all_failed": all(
                row["multi_p0"] == row["mismatched_multi_p0"] for row in writeback),
        },
        "transfer": {
            "rows": len(transfer),
            "one_pair_mismatches_min": min(number(row, "mismatched_vec_single") for row in transfer),
            "one_pair_mismatches_max": max(number(row, "mismatched_vec_single") for row in transfer),
        },
    }
results["mutants"] = mutants
results["source"]["clean_after"] = not status()
results["source"]["head_after"] = git("rev-parse", "HEAD")
(OUT / "results.json").write_text(json.dumps(results, indent=2) + "\n")
failed = [command["name"] for command in commands if command["exit"] != 0]
loops_ok = all(loop["ok"] for entry in external.values()
               for tool in entry["disassembly"].values()
               for loop in tool["butterfly_loops"].values())
print(json.dumps({"failed": failed, "floor": results["floor_classification"].get("status"),
                  "sibling": results["floor_classification_sibling"].get("status"),
                  "external_loops_ok": loops_ok,
                  "clean_after": results["source"]["clean_after"]}))
sys.exit(1 if failed or not loops_ok or not results["source"]["clean_after"] else 0)
