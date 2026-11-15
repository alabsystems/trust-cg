#!/usr/bin/env python3
"""Qualifying run for the L02-P10 `.eh_frame` window check (Linux AArch64, 2026-09-23).

The 2026-09-23 closure audit of L02-P10 at 5ddb13664 found that trust-cg's
`.eh_frame` pointers (DW_EH_PE_pcrel|sdata4 through R_AARCH64_PREL32,
-2^31 <= X < 2^31) were left to the linker, and LLD 22.1.6 and gold 2.42
write [2^31, 2^32). This harness qualifies the change on a clean checkout, in
phases, each writing RUN/records/results-<phase>.json:

- gates: the requested test targets and repository gates (records/logs), with
  TCG_REQUIRE_LLD and TCG_REQUIRE_GOLD set so no linker leg can skip;
- direct: the auditor's probe (b1_scalars.tmbc, bt.o, the far placement)
  through LLD, gold and GNU ld with the CLI built from this source and with
  the CLI built with the prior link driver and reloc.rs (PRIOR); the near and
  window-edge twins; LLD's and gold's own far programs; the section-header-less
  table path; records/direct and records/inputs;
- survey: the check over every ELF executable and shared object on the host
  (a temporary test appended to link_driver.rs, then restored) and a seeded
  comparison of the decoded FDEs with GNU readelf; records/survey;
- mutation: source mutants of the check, each run against the link_driver
  unit tests and the native link_options control; records/mutation;
- timing: a plain --nostdlib link (newly staged) and a default link through
  PRIOR, this source's CLI and an identical copy of it; records/timing;
- finish: merge the phase results into records/results.json and require a
  clean tree.

Every phase that edits the checkout restores it and checks the file hashes.
RUN/work is scratch and is not archived.

Usage: qualify-eh-frame-window-20260923.py WORKTREE RUN PHASE
"""

from __future__ import annotations

import hashlib
import json
import os
import platform
import random
import re
import shutil
import statistics
import struct
import subprocess
import sys
import time
from pathlib import Path

WORKTREE = Path(sys.argv[1]).resolve()
RUN = Path(sys.argv[2]).resolve()
PHASE = sys.argv[3]
RECORDS = RUN / "records"
LOGS = RECORDS / "logs"
DIRECT = RECORDS / "direct"
INPUTS = RECORDS / "inputs"
SURVEY = RECORDS / "survey"
MUTATION = RECORDS / "mutation"
TIMING = RECORDS / "timing"
WORK = RUN / "work"
HOME = Path.home()
PATH = os.pathsep.join(
    [
        str(HOME / ".local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin"),
        str(HOME / ".cargo/bin"),
        os.environ["PATH"],
    ]
)
ENV = dict(os.environ, PATH=PATH)
# Only the CLI tests read these; trust-cg-codegen's admission refuses any
# ambient TCG_* control, so the library tests must not see them.
CLI_ENV = dict(ENV, TCG_REQUIRE_LLD="1", TCG_REQUIRE_GOLD="1")
RESULT = re.compile(r"^test result: .*$", re.M)
RAN = re.compile(r"^(Ran \d+ tests.*|OK.*|FAILED.*)$", re.M)
TEST_LINE = re.compile(r"^test (\S+) \.\.\. (ok|FAILED|ignored)$", re.M)
LOCKED = ["--locked", "--offline", "-j", "8"]
PRIOR = "5ddb13664"
LINK_DRIVER = WORKTREE / "crates/trust-cg-codegen/src/link_driver.rs"
RELOC = WORKTREE / "crates/trust-cg-codegen/src/elf/reloc.rs"
B1 = WORKTREE / "tests/fixtures/trust_ir_binary_container/conformance/b1_scalars.tmbc"
CLI = WORKTREE / "target/debug/trust-cg"
FAR = (
    "-Wl,--section-start=.eh_frame=0x10000000,--section-start=.eh_frame_hdr=0x0fff0000,"
    "--section-start=.text=0xd0000000"
)
EDGE = (
    "-Wl,--section-start=.eh_frame=0x10000000,--section-start=.eh_frame_hdr=0x0fff0000,"
    "--section-start=.text=0x8ffe0000"
)
# The auditor's bt.o: a C object that calls backtrace() and a trust-cg function.
BT_C = """#include <execinfo.h>
#include <stdio.h>
extern long isize_add_one(long);
__attribute__((noinline)) int depth(void) { void *b[64]; return backtrace(b, 64); }
__attribute__((noinline)) int mid(void) { return depth() + 0; }
int main(void) { long v = isize_add_one(41); int n = mid(); printf("frames=%d v=%ld\\n", n, v); return v == 42 ? 0 : 1; }
"""
NATIVE_TEST = "an_eh_frame_pointer_out_of_the_prel32_window_is_refused_and_its_near_twin_backtraces"
EH_TEST = "eh_frame_personality_and_lsda_pointers_out_of_window_are_refused_by_run_link"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(WORKTREE), *args], check=True, capture_output=True, text=True
    ).stdout.strip()


def clean() -> bool:
    return git("status", "--porcelain", "--untracked-files=all") == ""


def shown(text: str) -> str:
    return (
        text.replace(str(WORK), "$WORK")
        .replace(str(RUN), "$RUN")
        .replace(str(WORKTREE), "$WORKTREE")
        .replace(str(HOME), "$HOME")
    )


def panics(stdout: str) -> list[str]:
    lines = stdout.splitlines()
    found = []
    for index, line in enumerate(lines):
        if "panicked at" in line:
            message = lines[index + 1] if index + 1 < len(lines) else ""
            found.append(f"{line.strip()} {message.strip()}")
    return found


def run(name: str, argv: list[str], *, directory: Path = LOGS, cwd: Path = WORKTREE,
        timeout: int = 1150, env: dict | None = None) -> dict:
    """Run one command and keep its complete output as DIRECTORY/NAME.log."""
    directory.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    completed = subprocess.run(argv, cwd=cwd, env=env or ENV, capture_output=True, text=True,
                               timeout=timeout)
    seconds = round(time.monotonic() - started, 1)
    text = (
        f"$ {' '.join(argv)}\n(cwd {shown(str(cwd))})\n--- stdout ---\n{completed.stdout}"
        f"--- stderr ---\n{completed.stderr}--- exit {completed.returncode} ({seconds} s) ---\n"
    )
    (directory / f"{name}.log").write_text(shown(text))
    both = completed.stdout + completed.stderr
    record = {
        "name": name,
        "argv": [shown(a) for a in argv],
        "exit": completed.returncode,
        "seconds": seconds,
        "test_results": RESULT.findall(both) or RAN.findall(both),
        "failed_tests": [t for t, status in TEST_LINE.findall(both) if status == "FAILED"],
        "panics": panics(completed.stdout),
    }
    print(f"{name}: exit {completed.returncode} {record['test_results']} {record['failed_tests']}",
          flush=True)
    return record


def save(phase: str, payload: dict) -> None:
    RECORDS.mkdir(parents=True, exist_ok=True)
    (RECORDS / f"results-{phase}.json").write_text(json.dumps(payload, indent=1) + "\n")


def tool(argv: list[str]) -> str:
    completed = subprocess.run(argv, capture_output=True, text=True, env=ENV)
    return (completed.stdout or completed.stderr).splitlines()[0] if (completed.stdout or completed.stderr) else ""


def which(name: str) -> str:
    return shutil.which(name, path=PATH) or ""


def build_cli(name: str) -> dict:
    return run(name, ["cargo", "build", *LOCKED, "-p", "trust-cg-cli"])


def with_files(replacements: dict[Path, bytes], action):
    """Run `action` with each file's bytes replaced, then restore it exactly."""
    saved = {path: path.read_bytes() for path in replacements}
    try:
        for path, data in replacements.items():
            path.write_bytes(data)
        return action()
    finally:
        for path, data in saved.items():
            path.write_bytes(data)
        for path, data in saved.items():
            assert path.read_bytes() == data, f"{path} not restored"


def phase_gates() -> None:
    assert clean(), "the checkout must be clean"
    head = git("rev-parse", "HEAD")
    records = []
    gates = [
        ("test-cli", ["cargo", "test", *LOCKED, "-p", "trust-cg-cli", "--test", "link_options",
                      "--test", "output_paths", "--bin", "trust-cg"]),
        ("test-native-eh-frame", ["cargo", "test", *LOCKED, "-p", "trust-cg-cli", "--test",
                                  "link_options", NATIVE_TEST, "--", "--nocapture"]),
        ("test-eh-catch-eh-frame", ["cargo", "test", *LOCKED, "-p", "trust-cg-codegen", "--test",
                                    "e2e_aarch64_eh_catch", EH_TEST, "--", "--nocapture"]),
        ("test-codegen-lib", ["cargo", "test", *LOCKED, "-p", "trust-cg-codegen", "--lib"]),
        ("test-codegen-e2e", ["cargo", "test", *LOCKED, "-p", "trust-cg-codegen",
                              "--test", "e2e_aarch64_link_runtime", "--test", "e2e_aarch64_elf_tlsie",
                              "--test", "e2e_aarch64_eh_linux", "--test", "e2e_aarch64_eh_catch",
                              "--test", "aarch64_elf_cfi_differential", "--test", "e2e_aarch64_elf_link"]),
        ("check-codegen-verify", ["cargo", "check", *LOCKED, "-p", "trust-cg-codegen", "--features", "verify"]),
        ("check-codegen", ["cargo", "check", *LOCKED, "-p", "trust-cg-codegen"]),
        ("check-fmt", ["bash", "scripts/check_fmt.sh"]),
        ("check-documentation-write", ["python3", "scripts/check_documentation.py", "--write"]),
        ("check-documentation", ["python3", "scripts/check_documentation.py", "--check"]),
        ("diagnostics-inventory", ["python3", "scripts/generate_diagnostics_inventory.py", "--check"]),
        ("script-gate-tests", ["python3", "-B", "-m", "unittest", "scripts/tests/test_linux_aarch64_gate.py",
                               "scripts/tests/test_darwin_aarch64_gate.py",
                               "scripts/tests/test_linux_aarch64_bridge_gate.py"]),
    ]
    for name, argv in gates:
        records.append(run(name, argv, env=CLI_ENV if name.startswith("test-cli") or
                           name == "test-native-eh-frame" else ENV))
        records[-1]["tree_clean_after"] = clean()
    cli_sha = sha256(CLI)
    tools = {
        "uname": platform.uname()._asdict(),
        "rustc": tool(["rustc", "--version"]),
        "cargo": tool(["cargo", "--version"]),
        "cc": tool(["cc", "--version"]),
        "ld.bfd": tool(["ld.bfd", "--version"]),
        "ld.gold": tool(["ld.gold", "--version"]),
        "ld.lld": tool([str(HOME / ".local/bin/ld.lld"), "--version"]),
        "readelf": tool(["readelf", "--version"]),
        "nm": tool(["nm", "--version"]),
        "sha256": {
            "ld.bfd": sha256(Path(os.path.realpath(which("ld.bfd")))),
            "ld.gold": sha256(Path(os.path.realpath(which("ld.gold")))),
            "ld.lld": sha256(Path(os.path.realpath(HOME / ".local/bin/ld.lld"))),
            "cc": sha256(Path(os.path.realpath(which("cc")))),
            "trust-cg (target/debug, gates build)": cli_sha,
        },
    }
    save("gates", {"head": head, "tree": git("rev-parse", "HEAD^{tree}"), "clean_before": True,
                   "clean_after": clean(), "cli_sha256": cli_sha, "tools": tools, "gates": records})


def wrappers(work: Path) -> dict[str, Path | None]:
    tools = work / "lld-tools"
    tools.mkdir(parents=True, exist_ok=True)
    if not (tools / "ld.lld").exists():
        (tools / "ld.lld").symlink_to(HOME / ".local/bin/ld.lld")
    host_cc = which("cc")
    made = {}
    for name, flags in (("lld", f"-fuse-ld=lld -B{tools}/"), ("gold", "-fuse-ld=gold")):
        directory = work / f"{name}-cc"
        directory.mkdir(exist_ok=True)
        script = directory / "cc"
        script.write_text(f"#!/bin/sh\nexec '{host_cc}' {flags} \"$@\"\n")
        script.chmod(0o755)
        made[name] = directory
    made["gnu"] = None
    return made


def listing(directory: Path) -> list[str]:
    return sorted(p.name for p in directory.iterdir())


def cli_run(binary: Path, work: Path, bin_dir: Path | None, args: list[str]) -> dict:
    env = dict(ENV)
    if bin_dir:
        env["PATH"] = f"{bin_dir}{os.pathsep}{env['PATH']}"
    before = listing(work)
    completed = subprocess.run([str(binary), *args], cwd=work, env=env, capture_output=True,
                               text=True, timeout=600)
    after = listing(work)
    return {
        "argv": ["trust-cg", *args],
        "exit": completed.returncode,
        "stderr": shown(completed.stderr),
        "error_lines": [line for line in completed.stderr.splitlines() if "error[link:" in line],
        "listing_unchanged": before == after,
        "new_files": sorted(set(after) - set(before)),
    }


def program(work: Path, name: str) -> dict:
    path = work / name
    if not path.exists():
        return {"exists": False}
    completed = subprocess.run([str(path)], cwd=work, capture_output=True, text=True, timeout=60)
    frames = subprocess.run(["readelf", "--debug-dump=frames", str(path)], capture_output=True,
                            text=True).stdout
    fdes = [line for line in frames.splitlines() if " FDE cie=" in line]
    return {"exists": True, "exit": completed.returncode, "stdout": completed.stdout.strip(),
            "fde_lines": fdes, "bytes": path.stat().st_size}


def write_direct(name: str, record: dict) -> None:
    DIRECT.mkdir(parents=True, exist_ok=True)
    (DIRECT / f"{name}.json").write_text(json.dumps(record, indent=1) + "\n")


def phase_direct() -> None:
    assert clean(), "the checkout must be clean"
    WORK.mkdir(parents=True, exist_ok=True)
    INPUTS.mkdir(parents=True, exist_ok=True)
    # The prior CLI: this source with 5ddb13664's link driver and reloc.rs.
    prior_files = {
        path: subprocess.run(
            ["git", "-C", str(WORKTREE), "show", f"{PRIOR}:{path.relative_to(WORKTREE)}"],
            capture_output=True, check=True).stdout
        for path in (LINK_DRIVER, RELOC)
    }
    prior_build = with_files(prior_files, lambda: build_cli("build-prior-cli"))
    prior = WORK / "prior-trust-cg"
    shutil.copy(CLI, prior)
    current_build = build_cli("build-current-cli")
    current = WORK / "trust-cg"
    shutil.copy(CLI, current)
    gates = json.loads((RECORDS / "results-gates.json").read_text()) if (RECORDS / "results-gates.json").exists() else {}
    identity = {
        "prior_sha256": sha256(prior),
        "current_sha256": sha256(current),
        "current_equals_gates_build": sha256(current) == gates.get("cli_sha256"),
        "prior_build": prior_build,
        "current_build": current_build,
    }
    assert clean()
    shutil.copy(B1, WORK / "b1_scalars.tmbc")
    (WORK / "bt.c").write_text(BT_C)
    subprocess.run(["cc", "-c", "-O1", "-o", "bt.o", "bt.c"], cwd=WORK, check=True, env=ENV)
    for name in ("b1_scalars.tmbc", "bt.c", "bt.o"):
        shutil.copy(WORK / name, INPUTS / name)
    bins = wrappers(WORK)
    for name in ("lld", "gold"):
        shutil.copy(bins[name] / "cc", INPUTS / f"{name}-cc.sh")
    rows = {}
    for linker in ("lld", "gold", "gnu"):
        for label, binary in (("prior", prior), ("current", current)):
            key = f"{label}-far-{linker}"
            output = f"btfar_{label}_{linker}"
            record = cli_run(binary, WORK, bins[linker], ["-o", output, "b1_scalars.tmbc", "-Wl,bt.o", FAR])
            record["program"] = program(WORK, output)
            rows[key] = record
            write_direct(key, record)
            key = f"{label}-near-{linker}"
            output = f"btnear_{label}_{linker}"
            record = cli_run(binary, WORK, bins[linker], ["-o", output, "b1_scalars.tmbc", "-Wl,bt.o"])
            record["program"] = program(WORK, output)
            rows[key] = record
            write_direct(key, record)
        key = f"current-edge-{linker}"
        output = f"btedge_{linker}"
        record = cli_run(current, WORK, bins[linker], ["-o", output, "b1_scalars.tmbc", "-Wl,bt.o", EDGE])
        record["program"] = program(WORK, output)
        rows[key] = record
        write_direct(key, record)
        # A file already at the output keeps its bytes.
        precious = WORK / f"kept_{linker}"
        precious.write_bytes(b"precious\n")
        record = cli_run(current, WORK, bins[linker], ["-o", precious.name, "b1_scalars.tmbc", "-Wl,bt.o", FAR])
        record["kept"] = precious.read_bytes() == b"precious\n"
        rows[f"current-far-kept-{linker}"] = record
        write_direct(f"current-far-kept-{linker}", record)
    # LLD's and gold's own far programs.
    compiled = cli_run(current, WORK, None, ["-c", "-o", "b1_scalars.o", "b1_scalars.tmbc"])
    rows["compile-b1"] = compiled
    for linker in ("lld", "gold"):
        output = f"btraw_{linker}"
        completed = subprocess.run([str(bins[linker] / "cc"), "-o", output, "b1_scalars.o", "bt.o",
                                    "-Wl,-z,noexecstack", FAR], cwd=WORK, env=ENV,
                                   capture_output=True, text=True)
        record = {"exit": completed.returncode, "stderr": shown(completed.stderr),
                  "program": program(WORK, output)}
        rows[f"raw-far-{linker}"] = record
        write_direct(f"raw-far-{linker}", record)
    # trust-cg's own zPLR object (the EH catch fixture) with its LSDA and
    # personality slot placed far: the personality and LSDA pointers.
    eh_dump = WORK / "eh"
    dumped = run("dump-eh-object", ["cargo", "test", *LOCKED, "-p", "trust-cg-codegen", "--test",
                                    "e2e_aarch64_eh_catch", "e2e_aarch64_elf_eh_catch_object_emit"],
                 directory=DIRECT, env=dict(ENV, TCG_ELF_EH_DUMP=str(eh_dump)))
    rows["dump-eh-object"] = dumped
    subprocess.run(["c++", "-c", "-O1", "-o", "driver.o", "driver.cpp"], cwd=eh_dump, check=True, env=ENV)
    for name in ("tc_try_elf.o", "driver.cpp", "driver.o"):
        shutil.copy(eh_dump / name, WORK / name)
        shutil.copy(eh_dump / name, INPUTS / name)
    far_lsda = ("-Wl,--section-start=.eh_frame=0x10000000,--section-start=.eh_frame_hdr=0x0fff0000,"
                "--section-start=.text=0x10010000,--section-start=.gcc_except_table=0xd0000000")
    for linker in ("lld", "gold", "gnu"):
        for label, binary in (("prior", prior), ("current", current)):
            for placement, extra in (("far", [far_lsda]), ("near", [])):
                key = f"{label}-eh-{placement}-{linker}"
                output = f"eh_{label}_{placement}_{linker}"
                record = cli_run(binary, WORK, bins[linker], ["-o", output, "b1_scalars.tmbc",
                                                               "-Wl,tc_try_elf.o,driver.o,-lstdc++", *extra])
                record["program"] = program(WORK, output)
                rows[key] = record
                write_direct(key, record)
    # The section-header-less path (PT_GNU_EH_FRAME's table) through LLD.
    for label, binary in (("prior", prior), ("current", current)):
        output = f"libns_{label}.so"
        record = cli_run(binary, WORK, bins["lld"], ["--shared", "--nostdlib", "--relocation-model",
                                                      "pic", "-o", output, "b1_scalars.tmbc",
                                                      f"-Wl,-z,nosectionheader,{FAR[4:]}"])
        record["program"] = program(WORK, output)
        rows[f"{label}-nosectionheader-far-lld"] = record
        write_direct(f"{label}-nosectionheader-far-lld", record)
    save("direct", {"identity": identity, "rows": rows, "clean_after": clean()})


def phase_survey() -> None:
    assert clean(), "the checkout must be clean"
    SURVEY.mkdir(parents=True, exist_ok=True)
    WORK.mkdir(parents=True, exist_ok=True)
    test = Path(__file__).resolve().with_name("survey_test.rs").read_text()
    shutil.copy(Path(__file__).resolve().with_name("survey_test.rs"), SURVEY / "survey_test.rs")
    images = []
    seen = set()
    for root in ("/usr/bin", "/usr/sbin", "/usr/lib", "/usr/libexec", "/usr/local/bin"):
        for directory, _, files in os.walk(root):
            for name in files:
                path = os.path.join(directory, name)
                try:
                    if os.path.islink(path) or not os.path.isfile(path):
                        continue
                    real = os.path.realpath(path)
                    if real in seen:
                        continue
                    with open(path, "rb") as handle:
                        head = handle.read(20)
                except OSError:
                    continue
                if len(head) == 20 and head[:6] == b"\x7fELF\x02\x01" and struct.unpack_from("<H", head, 16)[0] in (2, 3):
                    seen.add(real)
                    images.append(path)
    images.sort()
    listing_file = WORK / "images.txt"
    listing_file.write_text("\n".join(images) + "\n")
    output = WORK / "survey.out"
    source = LINK_DRIVER.read_text()
    assert source.endswith("}\n")
    env = dict(ENV, TCG_EH_SURVEY_LIST=str(listing_file), TCG_EH_SURVEY_OUT=str(output))
    record = with_files({LINK_DRIVER: (source[:-2] + test).encode()}, lambda: run(
        "survey-test", ["cargo", "test", *LOCKED, "-p", "trust-cg-codegen", "--lib",
                        "survey_eh_frame_check_over_host_images", "--", "--ignored"],
        directory=SURVEY, env=env))
    assert clean()
    verdicts = []
    fdes: dict[str, list[tuple[int, int, int]]] = {}
    current = None
    for line in output.read_text().splitlines():
        if line.startswith("IMAGE "):
            current = line[6:]
            fdes[current] = []
            verdicts.append(line)
        elif line.startswith(("VERDICT", "DIAG", "WALKERR", "SKIP")):
            verdicts.append(line)
        elif line.startswith("FDE ") and current:
            offset, begin, end = (int(x, 16) for x in line.split()[1:])
            fdes[current].append((offset, begin, end))
    (SURVEY / "verdicts.txt").write_text("\n".join(verdicts) + "\n")
    summary: dict[str, int] = {}
    debug_files = 0
    unproven_other = []
    failing = []
    total_fdes = 0
    for index, line in enumerate(verdicts):
        if not line.startswith("VERDICT"):
            continue
        image = verdicts[index - 1][6:]
        is_debug = image.startswith("/usr/lib/debug/")
        debug_files += is_debug
        fields = dict(part.split("=", 1) for part in line[8:].split(" ", 4))
        total_fdes += int(fields["fdes"])
        ok = fields["outside_code"] == "0" and fields["outside_memory"] == "0" and \
            (fields["table"] == "none" or fields["table"].endswith(":0")) and fields["unproven"] == ""
        summary["passed" if ok else ("unproven-debug-file" if is_debug else "refused")] = \
            summary.get("passed" if ok else ("unproven-debug-file" if is_debug else "refused"), 0) + 1
        if not ok and not is_debug:
            failing.append(line)
    # The decoded FDEs against GNU readelf on a seeded sample and the largest images.
    candidates = sorted(p for p, f in fdes.items() if f and not p.startswith("/usr/lib/debug/"))
    largest = sorted(candidates, key=lambda p: -len(fdes[p]))[:10]
    random.seed(20260923)
    sample = sorted(set(random.sample(candidates, min(400, len(candidates))) + largest))
    pattern = re.compile(r"^([0-9a-f]+) [0-9a-f]+ [0-9a-f]+ FDE cie=[0-9a-f]+ pc=([0-9a-f]+)\.\.([0-9a-f]+)$")
    mismatches = []
    compared = 0
    for path in sample:
        dump = subprocess.run(["readelf", "--debug-dump=frames", path], capture_output=True, text=True).stdout
        section = None
        theirs = []
        for line in dump.splitlines():
            if line.startswith("Contents of the "):
                section = line
            elif section and (section == "Contents of the .eh_frame section:" or
                              section.startswith("Contents of the .eh_frame section (loaded from ")):
                match = pattern.match(line.strip())
                if match:
                    theirs.append(tuple(int(x, 16) for x in match.groups()))
        compared += len(fdes[path])
        if theirs != fdes[path]:
            mismatches.append({"image": path, "ours": len(fdes[path]), "readelf": len(theirs)})
    comparison = {"candidates": len(candidates), "sampled": len(sample), "fdes_compared": compared,
                  "mismatches": mismatches, "sample": sample}
    (SURVEY / "readelf-comparison.json").write_text(json.dumps(comparison, indent=1) + "\n")
    save("survey", {"test": record, "images": len(images), "debug_files": debug_files,
                    "verdicts": summary, "refused_non_debug": failing, "fdes_decoded": total_fdes,
                    "readelf": {k: v for k, v in comparison.items() if k != "sample"},
                    "clean_after": clean()})


# (name, file, old, new, what): each old text must occur exactly once.
MUTANTS = [
    ("skip-eh-frame-check", LINK_DRIVER,
     "    if request.operating_system() == TargetOperatingSystem::Linux {\n        diagnostics.extend(eh_frame_diagnostics(request, image));",
     "    if false {\n        diagnostics.extend(eh_frame_diagnostics(request, image));",
     "staged_image_refusals never runs the .eh_frame check"),
    ("plain-link-unstaged", LINK_DRIVER,
     "    let linux = request.operating_system() == TargetOperatingSystem::Linux;",
     "    let linux = false && request.operating_system() == TargetOperatingSystem::Linux;",
     "a plain -nostdlib Linux link is linked directly again"),
    ("sdata4-unsigned", LINK_DRIVER,
     "        0x0b => cursor\n            .uint(4)\n            .map(|value| i64::from(value as u32 as i32) as u64),",
     "        0x0b => cursor.uint(4),",
     "DW_EH_PE_sdata4 read as unsigned (the reading gold and LLD assume)"),
    ("begin-only", LINK_DRIVER,
     "        let high = u128::from(fde.pc_begin.resolved) + u128::from(fde.range);",
     "        let high = u128::from(fde.pc_begin.resolved);",
     "only pc_begin, not pc_begin + pc_range, must be executable"),
    ("pointers-always-allocated", LINK_DRIVER,
     "    fn allocated(&self, pointer: &EhPointer) -> bool {\n        if pointer.raw == 0 {",
     "    fn allocated(&self, pointer: &EhPointer) -> bool {\n        if pointer.raw == 0 || pointer.width != 0 {",
     "personality and LSDA pointers are never checked"),
    ("unknown-augmentation-ignored", LINK_DRIVER,
     "            b'S' | b'B' | b'G' => {}",
     "            b'S' | b'B' | b'G' | b'X' => {}",
     "an unknown augmentation letter (X) is skipped"),
    ("no-table-check", LINK_DRIVER,
     "            encoding: *encoding,\n            problems,\n        });",
     "            encoding: *encoding,\n            problems: problems.into_iter().take(0).collect(),\n        });",
     "the .eh_frame_hdr table is never compared with the FDEs"),
    ("no-table-coverage", LINK_DRIVER,
     "        if headers.is_some() {\n            let located",
     "        if headers.is_none() {\n            let located",
     "a live FDE may be missing from the table"),
    ("table-sort-ignored", LINK_DRIVER,
     "                && *location < previous\n",
     "                && *location < previous\n                && false\n",
     "an unsorted table is accepted"),
    ("no-dynamic-relocation-check", LINK_DRIVER,
     "    if !read.is_empty() {\n        let read = eh_spans(read);",
     "    if read.is_empty() {\n        let read = eh_spans(read);",
     "a dynamic relocation into .eh_frame is not seen"),
]


def phase_mutation() -> None:
    assert clean(), "the checkout must be clean"
    MUTATION.mkdir(parents=True, exist_ok=True)
    only = sys.argv[4:]
    results = []
    for name, path, old, new, what in MUTANTS:
        if only and name not in only:
            continue
        text = path.read_text()
        assert text.count(old) == 1, f"{name}: {text.count(old)} matches"
        directory = MUTATION / name
        directory.mkdir(parents=True, exist_ok=True)

        def legs():
            diff = subprocess.run(["git", "-C", str(WORKTREE), "diff"], capture_output=True, text=True).stdout
            (directory / "mutant.diff").write_text(diff)
            unit = run("lib-link-driver", ["cargo", "test", *LOCKED, "-p", "trust-cg-codegen", "--lib",
                                           "link_driver"], directory=directory)
            native = run("link_options-eh-frame", ["cargo", "test", *LOCKED, "-p", "trust-cg-cli",
                                                   "--test", "link_options", NATIVE_TEST],
                         directory=directory, env=CLI_ENV)
            eh = run("e2e-eh-catch-eh-frame", ["cargo", "test", *LOCKED, "-p", "trust-cg-codegen",
                                               "--test", "e2e_aarch64_eh_catch", EH_TEST],
                     directory=directory)
            return [unit, native, eh]

        legs_run = with_files({path: text.replace(old, new).encode()}, legs)
        killed_by = [test for leg in legs_run for test in leg["failed_tests"]]
        built = all(leg["test_results"] for leg in legs_run)
        results.append({"mutant": name, "what": what, "legs": legs_run, "built": built,
                        "killed": bool(killed_by) and built, "killed_by": killed_by})
        print(f"MUTANT {name}: killed={bool(killed_by)} by {killed_by}", flush=True)
        assert clean(), f"{name}: tree not restored"
    save("mutation" + ("-" + "-".join(only) if only else ""), {"mutants": results, "clean_after": clean()})


def phase_timing() -> None:
    assert clean(), "the checkout must be clean"
    TIMING.mkdir(parents=True, exist_ok=True)
    prior = WORK / "prior-trust-cg"
    current = WORK / "trust-cg"
    # target/debug holds the last mutant's CLI: rebuild this source's.
    rebuild = build_cli("build-current-cli-after-mutation")
    rebuilt_same = sha256(CLI) == sha256(current)
    copy = WORK / "trust-cg-copy"
    shutil.copy(current, copy)
    assert sha256(copy) == sha256(current)
    area = WORK / "timing"
    area.mkdir(exist_ok=True)
    shutil.copy(B1, area / "b1_scalars.tmbc")
    shutil.copy(WORK / "bt.o", area / "bt.o")
    binaries = {"prior": prior, "current": current, "current-copy": copy}
    cases = {
        "plain --nostdlib executable of b1_scalars.tmbc": ["--nostdlib", "-o", "out_plain", "b1_scalars.tmbc"],
        "default executable of b1_scalars.tmbc with -Wl,bt.o": ["-o", "out_default", "b1_scalars.tmbc", "-Wl,bt.o"],
    }
    rounds = 21
    samples: dict[str, dict[str, list[float]]] = {case: {b: [] for b in binaries} for case in cases}
    order = list(binaries)
    for index in range(rounds):
        rotated = order[index % 3:] + order[:index % 3]
        for case, args in cases.items():
            for label in rotated:
                started = time.perf_counter()
                completed = subprocess.run([str(binaries[label]), *args], cwd=area, env=ENV,
                                           capture_output=True)
                elapsed = (time.perf_counter() - started) * 1000
                assert completed.returncode == 0, (label, case, completed.stderr)
                samples[case][label].append(round(elapsed, 2))
    summary = {}
    for case, by in samples.items():
        summary[case] = {}
        for label, values in by.items():
            q = statistics.quantiles(values, n=4)
            summary[case][label] = {"median": round(statistics.median(values), 2),
                                    "q1": round(q[0], 2), "q3": round(q[2], 2), "min": min(values)}
    (TIMING / "samples.json").write_text(json.dumps(samples, indent=1) + "\n")
    save("timing", {"rounds": rounds, "binaries": {k: sha256(v) for k, v in binaries.items()},
                    "rebuild": rebuild, "rebuilt_cli_equals_direct_build": rebuilt_same,
                    "summary": summary, "clean_after": clean()})


def phase_finish() -> None:
    merged = {"run": "L02-P10 .eh_frame PREL32 window check (closure audit at 5ddb13664)",
              "clean_at_finish": clean(), "head": git("rev-parse", "HEAD")}
    for part in sorted(RECORDS.glob("results-*.json")):
        merged[part.stem.removeprefix("results-")] = json.loads(part.read_text())
        part.unlink()
    (RECORDS / "results.json").write_text(json.dumps(merged, indent=1) + "\n")
    print(json.dumps({k: v for k, v in merged.items() if isinstance(v, (str, bool))}))


if __name__ == "__main__":
    {"gates": phase_gates, "direct": phase_direct, "survey": phase_survey, "mutation": phase_mutation,
     "timing": phase_timing, "finish": phase_finish}[PHASE]()
