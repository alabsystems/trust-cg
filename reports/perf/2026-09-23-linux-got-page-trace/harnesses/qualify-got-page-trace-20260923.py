#!/usr/bin/env python3
"""Qualifying run for the L02-P10 closure-audit residuals (Linux AArch64, 2026-09-23).

Runs the touched test targets and the repository gates on a clean checkout,
then the direct probes behind the change, then a timing leg and source
mutants of the new checks, and writes every log and record under
RUN/records:

- records/logs: the gate logs (touched test targets, the codegen library,
  every trust-cg-cli target, cargo check, formatting, script and
  documentation gates);
- records/direct: the audit's three commands (-Wl operand, -l :file,
  --whole-archive member) with the archived got_page.o, refused at current
  source, and GNU ld's unchecked libraries for the same inputs, whose user
  dies with SIGSEGV (with the truncated ADRPs disassembled); the eight
  routes through the CLI with .got 8 GiB away (refused) and 2 GiB away
  (linked and run); the C-runtime route (GNU ld's own trace of the start
  files, their GOT-page relocations, the unchecked executable's SIGSEGV, the
  CLI refusal and the 2 GiB twin); an unreadable trace for an image not in
  reach;
- records/timing: default and --shared links through the CLI built from
  this source and through the same CLI with the base link driver
  (dbec0925f's link_driver.rs), interleaved;
- records/mutation: each mutant's diff and the targeted tests' logs; every
  mutant must fail at least one of them (a test failure, not a build
  failure), and the file is restored after each. Each leg keeps every test
  panic (location and first message line). The no-member-bytes mutant must
  be killed at a member route of the GOT-page route test.

RUN/records/inputs holds what the probes used: got_page.o and
got_page.tmbc from reports/perf/2026-09-23-linux-got-page-region
(records/repair), desc_main.c from the same run's first records
(records/direct/cg), b1_scalars.tmbc from the conformance fixtures, and the
files this script writes. Nothing here edits the checkout except the timing
and mutation legs, which restore it; the tree must be clean before and
after.

Usage: qualify-got-page-trace-20260923.py WORKTREE RUN
"""

from __future__ import annotations

import gzip
import hashlib
import json
import os
import platform
import re
import shutil
import statistics
import subprocess
import sys
import time
from pathlib import Path

WORKTREE = Path(sys.argv[1]).resolve()
RUN = Path(sys.argv[2]).resolve()
RECORDS = RUN / "records"
LOGS = RECORDS / "logs"
DIRECT = RECORDS / "direct"
TIMING = RECORDS / "timing"
MUTATION = RECORDS / "mutation"
INPUTS = RECORDS / "inputs"
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
RESULT = re.compile(r"^test result: .*$", re.M)
RAN = re.compile(r"^(Ran \d+ tests.*|OK.*|FAILED.*)$", re.M)
TEST_LINE = re.compile(r"^test (\S+) \.\.\. (ok|FAILED|ignored)$", re.M)
CARGO = ["cargo"]
LOCKED = ["--locked", "--offline", "-j", "8"]
BASE = "dbec0925f"
PRIOR = WORKTREE / "reports/perf/2026-09-23-linux-got-page-region/records/repair"
FIXTURE = WORKTREE / "tests/fixtures/trust_ir_binary_container/conformance/b1_scalars.tmbc"
SIGSEGV_EXIT = 128 + 11
FAR = "-Wl,--section-start=.got=0x200000000,--section-start=.got.plt=0x200010000"
NEAR = "-Wl,--section-start=.got=0x80000000,--section-start=.got.plt=0x80010000"
CRT_FAR = "-Wl,--section-start=.got=0x200000000,--section-start=.data=0x80000000"
CRT_NEAR = "-Wl,--section-start=.got=0x80000000"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(WORKTREE), *args], check=True, capture_output=True, text=True
    ).stdout.strip()


def shown(text: str) -> str:
    return text.replace(str(WORK), "$WORK").replace(str(RUN), "$RUN").replace(str(WORKTREE), "$WORKTREE")


def panics(stdout: str) -> list[str]:
    """Each test panic: its location line and the message's first line."""
    lines = stdout.splitlines()
    found = []
    for index, line in enumerate(lines):
        if "panicked at" in line:
            message = lines[index + 1] if index + 1 < len(lines) else ""
            found.append(f"{line.strip()} {message.strip()}")
    return found


def run(name: str, argv: list[str], *, directory: Path = LOGS, cwd: Path = WORKTREE, timeout: int = 1500) -> dict:
    """Run one gate command, keep its complete output as DIRECTORY/NAME.log."""
    completed = subprocess.run(argv, cwd=cwd, env=ENV, capture_output=True, text=True, timeout=timeout)
    text = (
        f"$ {' '.join(argv)}\n(cwd {cwd})\n--- stdout ---\n{completed.stdout}"
        f"--- stderr ---\n{completed.stderr}--- exit {completed.returncode} ---\n"
    )
    (directory / f"{name}.log").write_text(text)
    both = completed.stdout + completed.stderr
    record = {
        "name": name,
        "argv": argv,
        "exit": completed.returncode,
        "test_results": RESULT.findall(both) or RAN.findall(both),
        "failed_tests": [test for test, status in TEST_LINE.findall(both) if status == "FAILED"],
        "panics": panics(completed.stdout),
    }
    print(f"{name}: exit {completed.returncode} {record['test_results']} {record['failed_tests']}", flush=True)
    return record


def probe(name: str, argv: list[str], cwd: Path | None = None, timeout: int = 300) -> dict:
    """Run one direct probe; keep command, exit, stdout and stderr in records/direct/NAME.txt."""
    cwd = cwd or WORK
    try:
        completed = subprocess.run(argv, cwd=cwd, env=ENV, capture_output=True, text=True, timeout=timeout)
        exit_code, stdout, stderr = completed.returncode, completed.stdout, completed.stderr
    except subprocess.TimeoutExpired:
        exit_code, stdout, stderr = "timeout", "", ""
    # A signal is reported as a negative return code; record it as a shell would.
    if isinstance(exit_code, int) and exit_code < 0:
        exit_code = 128 - exit_code
    (DIRECT / f"{name}.txt").write_text(
        f"$ {' '.join(shown(a) for a in argv)}\n(cwd {shown(str(cwd))})\n--- stdout ---\n{shown(stdout)}"
        f"--- stderr ---\n{shown(stderr)}--- exit {exit_code} ---\n"
    )
    print(f"probe {name}: exit {exit_code}", flush=True)
    return {"name": name, "argv": [shown(a) for a in argv], "exit": exit_code, "stdout": shown(stdout), "stderr": shown(stderr)}


def listing(directory: Path) -> list[str]:
    return sorted(p.name for p in directory.iterdir())


def tool(name: str, argv: list[str]) -> dict:
    path = shutil.which(argv[0], path=PATH) if "/" not in argv[0] else argv[0]
    resolved = Path(path).resolve() if path else None
    version = subprocess.run(argv, capture_output=True, text=True, env=ENV)
    text = version.stdout or version.stderr
    return {
        "name": name,
        "path": path,
        "resolved": str(resolved) if resolved else None,
        "sha256": sha256(resolved) if resolved else None,
        "version": text.splitlines()[0] if text else "",
    }


ANSWER = """; TrustIr text format v1
module "tcg_got_answer"

functy.0 = () -> (i32)

fn @main(functy.0) {
bb0:
    %0 = const i32 42
    ret %0
}
"""
CALLER = """; TrustIr text format v1
module "tcg_desc_caller"

functy.0 = () -> (i32)

fn @tcg_desc_bump(functy.0) {
}

fn @tcg_call_desc(functy.0) {
bb0:
    %0 = call @func.0()
    ret %0
}
"""


def gates() -> list[dict]:
    return [
        run("check-fmt", ["bash", "scripts/check_fmt.sh"]),
        run("check-codegen", [*CARGO, "check", "-p", "trust-cg-codegen", *LOCKED]),
        run("check-codegen-verify", [*CARGO, "check", "-p", "trust-cg-codegen", "--features", "verify", *LOCKED]),
        run("check-lower", [*CARGO, "check", "-p", "trust-cg-lower", *LOCKED]),
        run("test-codegen-lib", [*CARGO, "test", "-p", "trust-cg-codegen", "--lib", *LOCKED], timeout=2400),
        run("test-e2e_aarch64_link_runtime", [*CARGO, "test", "-p", "trust-cg-codegen", "--test", "e2e_aarch64_link_runtime", *LOCKED]),
        run("test-e2e_aarch64_elf_tlsie", [*CARGO, "test", "-p", "trust-cg-codegen", "--test", "e2e_aarch64_elf_tlsie", *LOCKED]),
        run("test-e2e_aarch64_switch", [*CARGO, "test", "-p", "trust-cg-codegen", "--test", "e2e_aarch64_switch", *LOCKED]),
        run("test-cli-all", [*CARGO, "test", "-p", "trust-cg-cli", *LOCKED], timeout=2400),
        run(
            "script-gate-tests",
            [
                "python3", "-B", "-m", "unittest",
                "scripts/tests/test_linux_aarch64_gate.py",
                "scripts/tests/test_darwin_aarch64_gate.py",
                "scripts/tests/test_linux_aarch64_bridge_gate.py",
            ],
        ),
        run("native-test-host-matrix", ["python3", "scripts/native_test_host_matrix.py", "--check"]),
        run("check-documentation", ["python3", "scripts/check_documentation.py", "--check"]),
        run("diagnostics-inventory", ["python3", "scripts/generate_diagnostics_inventory.py", "--check"]),
        run("evidence-plan-citations", ["python3", "scripts/check_evidence_archive.py", "--plan"]),
    ]


def user(P: list, library: str, name: str) -> dict:
    """Link desc_main.c against WORK/LIBRARY and run it."""
    P.append(probe(f"cc-user-{name}", ["cc", "-o", name, "desc_main.c", str(WORK / library), f"-Wl,-rpath,{WORK}"]))
    record = probe(f"run-{name}", [f"./{name}"])
    P.append(record)
    return record


def direct(trust_cg: str) -> dict:
    results: dict = {"probes": [], "checks": {}}
    P = results["probes"]
    check = results["checks"]
    for name, source in (
        ("got_page.o", PRIOR / "direct/cg/got_page.o.gz"),
        # The repair run did not re-archive the user; the first run did.
        ("desc_main.c", PRIOR.parent / "direct/cg/desc_main.c.gz"),
    ):
        data = gzip.decompress(source.read_bytes())
        (INPUTS / name).write_bytes(data)
        (WORK / name).write_bytes(data)
    data = gzip.decompress((PRIOR / "inputs/got_page.tmbc.gz").read_bytes())
    (INPUTS / "got_page.tmbc").write_bytes(data)
    (WORK / "got_page.tmbc").write_bytes(data)
    shutil.copy(FIXTURE, INPUTS / "b1_scalars.tmbc")
    shutil.copy(FIXTURE, WORK / "b1_scalars.tmbc")
    for name, text in (("answer.trust_ir", ANSWER), ("caller.trust_ir", CALLER)):
        (INPUTS / name).write_text(text)
        (WORK / name).write_text(text)
    P.append(probe("readelf-r-got_page.o", ["readelf", "-rW", "got_page.o"]))

    # 1. The audit's three commands at current source, and GNU ld's
    # unchecked libraries for the same inputs.
    (WORK / "arch").mkdir()
    shutil.copy(WORK / "got_page.o", WORK / "arch/got_page.o")
    P.append(probe("ar-libarch", ["ar", "rcs", "libarch.a", "arch/got_page.o"]))
    audit = {
        "wl": ["-Wl,got_page.o"],
        "lcolon": ["-L", ".", "-l", ":got_page.o"],
        "whole": ["-Wl,--whole-archive,libarch.a,--no-whole-archive"],
    }
    before = listing(WORK)
    for route, args in audit.items():
        P.append(probe(f"cli-audit-{route}", [trust_cg, "-shared", "-nostdlib", "--relocation-model", "pic", *args, FAR, "-o", f"libbypass_{route}.so", "b1_scalars.tmbc"]))
    check["audit_commands_refused"] = all(
        p["exit"] == 1
        and p["stderr"].count("error[link:relocation-out-of-range]") == 2
        and p["stderr"].count("error[link:") == 2
        and "[TCG-LINK-GOT-PAGE-WINDOW]" in p["stderr"]
        for p in P if p["name"].startswith("cli-audit-")
    )
    check["audit_commands_left_nothing"] = listing(WORK) == before
    P.append(probe("compile-b1-pic", [trust_cg, "-c", "--relocation-model", "pic", "-o", "b1.o", "b1_scalars.tmbc"]))
    for route, args in audit.items():
        P.append(probe(f"raw-gnu-ld-{route}", ["cc", "-shared", "-nostdlib", "-Wl,-z,noexecstack", "-o", f"libraw_{route}.so", "b1.o", *args, FAR]))
        user(P, f"libraw_{route}.so", f"user_raw_{route}")
    P.append(probe("objdump-libraw_wl", ["objdump", "-d", "--disassemble=tcg_desc_bump", "libraw_wl.so"]))
    P.append(probe("readelf-r-libraw_wl", ["readelf", "-rW", "libraw_wl.so"]))
    check["raw_audit_libraries_linked"] = all(p["exit"] == 0 for p in P if p["name"].startswith("raw-gnu-ld-"))
    check["raw_audit_users_segfault"] = all(p["exit"] == SIGSEGV_EXIT for p in P if p["name"].startswith("run-user_raw_"))
    P.append(probe("cli-audit-near", [trust_cg, "-shared", "-nostdlib", "--relocation-model", "pic", "-Wl,got_page.o", NEAR, "-o", "libnear.so", "b1_scalars.tmbc"]))
    check["audit_near_twin_runs"] = user(P, "libnear.so", "user_near")["exit"] == 0

    # 2. Eight routes through the CLI, refused at 8 GiB and run at 2 GiB.
    (WORK / "gp").mkdir()
    shutil.copy(WORK / "got_page.o", WORK / "gp/got_page.o")
    P.append(probe("ar-gp-regular", ["ar", "rcs", "gp/libtcggot.a", "gp/got_page.o"]))
    P.append(probe("ar-gp-thin", ["ar", "rcsT", "gp/libtcggotthin.a", "gp/got_page.o"]))
    (WORK / "gp/input.ld").write_text(f"INPUT({WORK}/gp/got_page.o)\n")
    (WORK / "gp/group.ld").write_text(f"GROUP({WORK}/gp/libtcggot.a)\n")
    routes = {
        "wl": ["-Wl,gp/got_page.o"],
        "colon": ["-L", "gp", "-l", ":got_page.o"],
        "member": ["-L", "gp", "-l", "tcggot"],
        "whole": ["-Wl,--whole-archive,gp/libtcggot.a,--no-whole-archive"],
        "thin": ["-Wl,--whole-archive,gp/libtcggotthin.a,--no-whole-archive"],
        "input": ["-Wl,gp/input.ld"],
        "group": ["-Wl,gp/group.ld"],
        "startgroup": ["-Wl,--start-group,gp/got_page.o,--end-group"],
    }
    before = listing(WORK)
    for route, args in routes.items():
        P.append(probe(f"cli-route-{route}", [trust_cg, "--shared", "--nostdlib", "--relocation-model", "pic", "-o", f"libgp_{route}.so", "--format=text", "caller.trust_ir", *args, FAR]))
    check["routes_refused"] = all(
        p["exit"] == 1
        and p["stderr"].count("error[link:relocation-out-of-range]") == 2
        and p["stderr"].count("error[link:") == 2
        and p["stderr"].count("the linker loaded this input although it is not a positional input") == 2
        for p in P if p["name"].startswith("cli-route-")
    )
    check["routes_left_nothing"] = listing(WORK) == before
    P.append(probe("compile-caller-pic", [trust_cg, "-c", "--relocation-model", "pic", "--format=text", "-o", "caller.o", "caller.trust_ir"]))
    for route, args in routes.items():
        P.append(probe(f"raw-route-{route}", ["cc", "-shared", "-nostdlib", "-Wl,-z,noexecstack", "-o", f"libgpraw_{route}.so", "caller.o", *args, FAR]))
        user(P, f"libgpraw_{route}.so", f"user_gpraw_{route}")
        P.append(probe(f"cli-near-{route}", [trust_cg, "--shared", "--nostdlib", "--relocation-model", "pic", "-o", f"libgpnear_{route}.so", "--format=text", "caller.trust_ir", *args, NEAR]))
        user(P, f"libgpnear_{route}.so", f"user_gpnear_{route}")
    check["raw_routes_users_segfault"] = all(p["exit"] == SIGSEGV_EXIT for p in P if p["name"].startswith("run-user_gpraw_"))
    check["near_routes_run"] = all(p["exit"] == 0 for p in P if p["name"].startswith("run-user_gpnear_"))

    # 3. The C runtime's own GOT-page ADRPs.
    P.append(probe("compile-answer", [trust_cg, "-c", "--format=text", "-o", "answer.o", "answer.trust_ir"]))
    P.append(probe("gnu-ld-trace-default-link", ["cc", "-Wl,--trace,--trace", "-Wl,-z,noexecstack", "-o", "traced_default", "answer.o"]))
    start_files = [
        line for line in P[-1]["stdout"].splitlines()
        if line.endswith(".o") and not line.startswith("(") and "answer.o" not in line
    ]
    for index, path in enumerate(start_files):
        P.append(probe(f"readelf-r-start-file-{index}", ["readelf", "-rW", path]))
    P.append(probe("raw-crt-far", ["cc", "-o", "crt_raw", "answer.o", "-Wl,-z,noexecstack", CRT_FAR]))
    P.append(probe("run-crt_raw", ["./crt_raw"]))
    before = listing(WORK)
    P.append(probe("cli-crt-far", [trust_cg, "--format=text", "-o", "crt_prog", "answer.trust_ir", CRT_FAR]))
    check["crt_far_linked_outside"] = next(p for p in P if p["name"] == "raw-crt-far")["exit"] == 0
    check["crt_far_segfaults_outside"] = next(p for p in P if p["name"] == "run-crt_raw")["exit"] == SIGSEGV_EXIT
    refused = next(p for p in P if p["name"] == "cli-crt-far")
    check["crt_far_refused"] = (
        refused["exit"] == 1
        and "Scrt1.o: R_AARCH64_ADR_GOT_PAGE against `main`" in refused["stderr"]
        and "crti.o: R_AARCH64_ADR_GOT_PAGE against `__gmon_start__`" in refused["stderr"]
    )
    check["crt_far_left_nothing"] = listing(WORK) == before
    P.append(probe("cli-crt-near", [trust_cg, "--format=text", "-o", "crt_near", "answer.trust_ir", CRT_NEAR]))
    P.append(probe("run-crt_near", ["./crt_near"]))
    check["crt_near_runs_42"] = P[-1]["exit"] == 42

    # 4. An unreadable trace for an image not in reach.
    P.append(probe("cli-crt-far-verbose", [trust_cg, "--format=text", "-o", "crt_verbose", "answer.trust_ir", CRT_FAR, "-Wl,--verbose"]))
    verbose = P[-1]
    check["unreadable_trace_refused"] = (
        verbose["exit"] == 1
        and verbose["stderr"].count("[TCG-LINK-INPUT-TRACE]") == 1
        and "the image is not shown to keep every GOT-page ADRP within the +-4 GiB page window" in verbose["stderr"]
    )
    return results


def swap_link_driver(text: str) -> None:
    (WORKTREE / "crates/trust-cg-codegen/src/link_driver.rs").write_text(text)


def timing(trust_cg: str) -> dict:
    """Default and --shared links through this source's CLI and through the
    same CLI built with the base link driver, interleaved."""
    source = WORKTREE / "crates/trust-cg-codegen/src/link_driver.rs"
    original = source.read_text()
    base_text = git("show", f"{BASE}:crates/trust-cg-codegen/src/link_driver.rs") + "\n"
    base_binary = WORK / "trust-cg-base-link-driver"
    try:
        swap_link_driver(base_text)
        build = run("build-base-link-driver", [*CARGO, "build", "-p", "trust-cg-cli", *LOCKED], directory=TIMING)
        shutil.copy(WORKTREE / "target/debug/trust-cg", base_binary)
    finally:
        source.write_text(original)
    rebuild = run("rebuild-current", [*CARGO, "build", "-p", "trust-cg-cli", *LOCKED], directory=TIMING)
    binaries = {"base": str(base_binary), "current": trust_cg}
    cases = {
        "default": lambda b, i: [b, "--format=text", "-o", f"t_default_{i}", "answer.trust_ir"],
        "shared-pic": lambda b, i: [b, "--shared", "--relocation-model", "pic", "-o", f"libt_{i}.so", "b1_scalars.tmbc"],
    }
    rounds = 21
    samples: dict = {case: {name: [] for name in binaries} for case in cases}
    for index in range(rounds):
        for case, argv in cases.items():
            for name, binary in binaries.items():
                command = argv(binary, f"{name}{index}")
                start = time.perf_counter()
                completed = subprocess.run(command, cwd=WORK, env=ENV, capture_output=True, text=True)
                elapsed = time.perf_counter() - start
                assert completed.returncode == 0, (command, completed.stderr)
                samples[case][name].append(elapsed)
    summary = {}
    for case in cases:
        medians = {name: statistics.median(samples[case][name]) for name in binaries}
        summary[case] = {
            "median_seconds": medians,
            "ratio_current_over_base": medians["current"] / medians["base"],
            "samples_seconds": samples[case],
        }
    record = {
        "base_link_driver_from": BASE,
        "rounds": rounds,
        "order": "interleaved per round: case, then base and current",
        "build_base": build,
        "rebuild_current": rebuild,
        "base_binary_sha256": sha256(base_binary),
        "summary": summary,
    }
    (TIMING / "timing.json").write_text(json.dumps(record, indent=2) + "\n")
    for case in cases:
        print(f"timing {case}: {summary[case]['median_seconds']} ratio {summary[case]['ratio_current_over_base']:.3f}", flush=True)
    return record


LINK_DRIVER = "crates/trust-cg-codegen/src/link_driver.rs"
PIPELINE = "crates/trust-cg-codegen/src/pipeline.rs"
MUTANTS = [
    (
        "no-traced-got-page",
        "the GOT-page check ignores every use the trace shows (positional uses only, as at base)",
        LINK_DRIVER,
        "                &examined.got_page_uses,\n                checked,\n",
        "                &examined.got_page_uses[..0],\n                checked,\n",
        [
            ("link_options-got-page", ["test", "-p", "trust-cg-cli", "--test", "link_options", "linux_got_page"]),
            ("lib-traced-got-page", ["test", "-p", "trust-cg-codegen", "--lib", "link_driver::tests::a_traced_got_page"]),
        ],
    ),
    (
        "got-page-check-reads-no-trace",
        "the trace is examined only when the image is not a confirmed executable (the local-exec condition), so an executable's traced GOT-page uses are never read",
        LINK_DRIVER,
        "        .filter(|_| not_executable.is_some() || unproven.is_some())\n",
        "        .filter(|_| not_executable.is_some())\n",
        [
            ("link_options-got-page", ["test", "-p", "trust-cg-cli", "--test", "link_options", "linux_got_page"]),
            ("lib-traced-got-page", ["test", "-p", "trust-cg-codegen", "--lib", "link_driver::tests::a_traced_got_page"]),
        ],
    ),
    (
        "no-member-bytes",
        "archive-member trace lines are resolved, but no copy of a member is read",
        LINK_DRIVER,
        "            for copy in copies {\n",
        "            for copy in copies.into_iter().take(0) {\n",
        [
            ("link_options-got-page-routes", ["test", "-p", "trust-cg-cli", "--test", "link_options", "got_page_objects_on_every_link_route"]),
        ],
    ),
    (
        "c-runtime-link-plain",
        "a link with the C runtime counts as plain (not traced), as at base",
        LINK_DRIVER,
        "                || !self.nostdlib\n",
        "",
        [
            ("lib-traces", ["test", "-p", "trust-cg-codegen", "--lib", "link_driver::tests::trace"]),
            ("lib-traced-got-page", ["test", "-p", "trust-cg-codegen", "--lib", "link_driver::tests::a_traced_got_page"]),
        ],
    ),
    (
        "got-page-trace-problems-ignored",
        "an unreadable trace refuses only a non-executable image (the local-exec condition)",
        LINK_DRIVER,
        "        && !examined.problems.is_empty()\n    {\n",
        "        && !examined.problems.is_empty()\n        && not_executable.is_some()\n    {\n",
        [
            ("lib-traced-got-page", ["test", "-p", "trust-cg-codegen", "--lib", "link_driver::tests::a_traced_got_page"]),
        ],
    ),
    (
        "no-traced-got-page-missing-output",
        "a traced GOT-page input does not make a link that wrote nothing [TCG-LINK-NO-OUTPUT]",
        LINK_DRIVER,
        "        let got_page_objects = objects_of(got_page, &examined.got_page_uses);\n",
        "        let got_page_objects = objects_of(got_page, &[]);\n",
        [
            ("lib-no-output", ["test", "-p", "trust-cg-codegen", "--lib", "link_driver::tests::a_traced_link_that_writes_nothing"]),
        ],
    ),
    (
        "no-imm21-check",
        "the jump-table ADR imm21 check is removed",
        PIPELINE,
        "        if !(-(1 << 20)..(1 << 20)).contains(&pc_relative) {\n",
        "        if false && !(-(1 << 20)..(1 << 20)).contains(&pc_relative) {\n",
        [
            ("lib-imm21", ["test", "-p", "trust-cg-codegen", "--lib", "text_offset_ceiling_tests::a_jump_table_adr"]),
        ],
    ),
    (
        "no-u32-block-check",
        "the u32 block-offset check is removed (a truncating conversion)",
        PIPELINE,
        "            aarch64_text_offset_u32(&func.name, code.len()).map_err(|offset| {\n                PipelineError::Encoding(format!(\n                    \"function {} block {:?}",
        "            Ok::<u32, u64>(code.len() as u32).map_err(|offset| {\n                PipelineError::Encoding(format!(\n                    \"function {} block {:?}",
        [
            ("lib-u32-block", ["test", "-p", "trust-cg-codegen", "--lib", "text_offset_ceiling_tests::the_u32_block"]),
        ],
    ),
    (
        "no-u32-instruction-check",
        "the u32 instruction-offset check is removed (a truncating conversion)",
        PIPELINE,
        "                aarch64_text_offset_u32(&func.name, code.len()).map_err(|offset| {\n                    PipelineError::Encoding(format!(\n                        \"function {} instruction",
        "                Ok::<u32, u64>(code.len() as u32).map_err(|offset| {\n                    PipelineError::Encoding(format!(\n                        \"function {} instruction",
        [
            ("lib-u32-instruction", ["test", "-p", "trust-cg-codegen", "--lib", "text_offset_ceiling_tests::the_u32_instruction"]),
        ],
    ),
    (
        "no-u32-jump-table-check",
        "the u32 jump-table offset check is removed (a truncating conversion)",
        PIPELINE,
        "        let table_offset = aarch64_text_offset_u32(&func.name, code.len()).map_err(|offset| {\n",
        "        let table_offset = Ok::<u32, u64>(code.len() as u32).map_err(|offset| {\n",
        [
            ("lib-u32-jump-table", ["test", "-p", "trust-cg-codegen", "--lib", "text_offset_ceiling_tests::the_u32_jump_table"]),
        ],
    ),
    (
        "no-u32-lsda-check",
        "the u32 LSDA code-length check is removed (a truncating conversion)",
        PIPELINE,
        "    let code_len = aarch64_text_offset_u32(&func.name, code_len).map_err(|length| {\n",
        "    let code_len = Ok::<u32, u64>(code_len as u32).map_err(|length| {\n",
        [
            ("lib-u32-lsda", ["test", "-p", "trust-cg-codegen", "--lib", "text_offset_ceiling_tests::the_u32_lsda"]),
        ],
    ),
]


def mutations() -> list[dict]:
    records = []
    for name, what, relative, old, new, runs in MUTANTS:
        source = WORKTREE / relative
        original = source.read_text()
        directory = MUTATION / name
        directory.mkdir(parents=True)
        assert original.count(old) == 1, name
        source.write_text(original.replace(old, new))
        diff = subprocess.run(["git", "-C", str(WORKTREE), "diff"], capture_output=True, text=True).stdout
        (directory / "mutant.diff").write_text(diff)
        legs = []
        try:
            for leg, args in runs:
                legs.append(run(leg, [*CARGO, *args, *LOCKED], directory=directory))
        finally:
            source.write_text(original)
        # A mutant counts as killed only when a test failed.
        killed = any(leg["failed_tests"] for leg in legs)
        records.append({"name": name, "what": what, "file": relative, "legs": legs, "killed": killed})
        print(f"mutant {name}: {'killed' if killed else 'SURVIVED'}", flush=True)
    return records


def main() -> int:
    for directory in (LOGS, DIRECT, TIMING, MUTATION, INPUTS, WORK):
        directory.mkdir(parents=True, exist_ok=True)
    head = git("rev-parse", "HEAD")
    tree = git("rev-parse", "HEAD^{tree}")
    status_before = git("status", "--porcelain", "--untracked-files=all")
    if status_before:
        print("checkout is dirty; refusing to qualify", file=sys.stderr)
        return 1
    host = {
        "uname": " ".join(platform.uname()),
        "glibc": subprocess.run(["ldd", "--version"], capture_output=True, text=True).stdout.splitlines()[0],
    }
    tools = [
        tool("cc", ["cc", "--version"]),
        tool("ld", ["ld", "--version"]),
        tool("readelf", ["readelf", "--version"]),
        tool("ar", ["ar", "--version"]),
        tool("objdump", ["objdump", "--version"]),
        tool("rustc", ["rustc", "--version"]),
        tool("cargo", ["cargo", "--version"]),
    ]
    gate_records = gates()
    trust_cg = WORKTREE / "target/debug/trust-cg"
    binary = {"path": str(trust_cg), "sha256": sha256(trust_cg)}
    direct_records = direct(str(trust_cg))
    status_mid = git("status", "--porcelain", "--untracked-files=all")
    timing_record = timing(str(trust_cg))
    status_after_timing = git("status", "--porcelain", "--untracked-files=all")
    binary_after_timing = sha256(trust_cg)
    mutation_records = mutations()
    rebuild = run("rebuild-after-mutants", [*CARGO, "build", "-p", "trust-cg-cli", *LOCKED])
    status_after = git("status", "--porcelain", "--untracked-files=all")
    member_legs = [
        leg for record in mutation_records if record["name"] == "no-member-bytes"
        for leg in record["legs"] if leg["name"] == "link_options-got-page-routes"
    ]
    member_route_kill = bool(member_legs) and any(
        re.search(r"link_options\.rs:\d+:\d+: member: ", panic) for panic in member_legs[0]["panics"]
    )
    results = {
        "run": "L02-P10 closure-audit residuals: traced GOT-page inputs and text-offset ceiling controls",
        "date": "2026-09-23",
        "source_sha": head,
        "tree_sha": tree,
        "base": BASE,
        "dirty_before": bool(status_before),
        "dirty_after_probes": bool(status_mid),
        "dirty_after_timing": bool(status_after_timing),
        "dirty_after": bool(status_after),
        "host": host,
        "tools": tools,
        "trust_cg_binary": binary,
        "trust_cg_binary_after_timing_rebuild_sha256": binary_after_timing,
        "gates": gate_records,
        "direct": direct_records,
        "timing": timing_record["summary"],
        "mutations": mutation_records,
        "member_route_kill": member_route_kill,
        "rebuild_after_mutants": rebuild,
        "inputs": {p.name: sha256(p) for p in sorted(INPUTS.rglob("*")) if p.is_file()},
    }
    (RECORDS / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    ok = (
        not status_before
        and not status_mid
        and not status_after_timing
        and not status_after
        and all(g["exit"] == 0 for g in gate_records)
        and all(m["killed"] for m in mutation_records)
        and member_route_kill
        and all(v for v in direct_records["checks"].values() if isinstance(v, bool))
    )
    print("QUALIFIED" if ok else "NOT QUALIFIED", flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
