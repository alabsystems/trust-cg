#!/usr/bin/env python3
"""Qualifying run for the second L02-P10 closure audit: linker-written PLT and
TLS descriptor trampoline ADRPs (Linux AArch64, 2026-09-23).

Runs the touched test targets and the repository gates on a clean checkout,
then the direct probes behind the change, a timing leg and source mutants of
the new check, and writes every log and record under RUN/records:

- records/logs: the gate logs (touched test targets, the codegen library,
  every trust-cg-cli target, cargo check, formatting, script and
  documentation gates);
- records/direct: the audit's PLT reproducer through the CLI built with the
  prior link driver (PRIOR, 7df1bfdf7: installed, PLT disassembled, user
  dies with SIGSEGV) and through the CLI built from this source (refused by
  name, nothing written), alone and with .got placed far too; GNU ld's
  library outside the driver (SIGSEGV); the 2 GiB twin (links, user exits
  0); the -Wl,got_page.o route, whose PLT entry and TLS descriptor
  trampoline are refused as well, with GNU ld's unchecked trampoline
  disassembled;
- records/timing: --shared and default links through this source's CLI,
  through the same CLI with the prior link driver and through an identical
  copy of this source's CLI (the scatter control), interleaved with the
  order rotated each round;
- records/mutation: each mutant's diff and the targeted tests' logs; every
  mutant must fail at least one of them (a test failure, not a build
  failure), and the file is restored after each.

RUN/records/inputs holds what the probes used. The probes run in RUN/work,
which is not archived. Nothing here edits the checkout except the timing
(the prior link driver is swapped in for one build) and mutation legs, which
restore it; the tree must be clean before and after.

Usage: qualify-got-page-plt-20260923.py WORKTREE RUN
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
PRIOR = "7df1bfdf7"
TRACE_RUN = WORKTREE / "reports/perf/2026-09-23-linux-got-page-trace/records/inputs"
SIGSEGV_EXIT = 128 + 11
FAR_PLT = "-Wl,--section-start=.got.plt=0x200010000"
FAR_BOTH = "-Wl,--section-start=.got=0x200000000,--section-start=.got.plt=0x200010000"
NEAR_PLT = "-Wl,--section-start=.got.plt=0x80010000"
DEFS = (
    "int tcg_desc_bump(void) { return 7; }\n"
    "extern int tcg_call_desc(void);\n"
    "int main(void) { return tcg_call_desc() == 7 ? 0 : 1; }\n"
)
PLT_WINDOW = (
    "error[link:relocation-out-of-range] `tcg_desc_bump` (R_AARCH64_JUMP_SLOT): "
    "[TCG-LINK-GOT-PAGE-WINDOW] linker-generated PLT (1 R_AARCH64_JUMP_SLOT slot(s), "
    "DT_JMPREL, an executable `.plt` section): the PLT entry the linker wrote for "
    "`tcg_desc_bump` addresses its slot through an ADRP page delta that no input "
    "relocation describes"
)
TRAMPOLINE_WINDOW = (
    "error[link:relocation-out-of-range]: [TCG-LINK-GOT-PAGE-WINDOW] linker-generated "
    "TLS descriptor trampoline (DT_TLSDESC_PLT at "
)


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


def gates() -> list[dict]:
    return [
        run("check-fmt", ["bash", "scripts/check_fmt.sh"]),
        run("check-codegen", [*CARGO, "check", "-p", "trust-cg-codegen", *LOCKED]),
        run("check-codegen-verify", [*CARGO, "check", "-p", "trust-cg-codegen", "--features", "verify", *LOCKED]),
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


def swap_link_driver(text: str) -> None:
    (WORKTREE / "crates/trust-cg-codegen/src/link_driver.rs").write_text(text)


def build_prior(trust_cg: Path) -> tuple[Path, dict, dict]:
    """The CLI with PRIOR's link driver (everything else from this source),
    copied out of the tree; the source is restored and the CLI rebuilt."""
    source = WORKTREE / "crates/trust-cg-codegen/src/link_driver.rs"
    original = source.read_text()
    prior_text = git("show", f"{PRIOR}:crates/trust-cg-codegen/src/link_driver.rs") + "\n"
    prior_binary = WORK / "trust-cg-prior-link-driver"
    try:
        swap_link_driver(prior_text)
        build = run("build-prior-link-driver", [*CARGO, "build", "-p", "trust-cg-cli", *LOCKED], directory=TIMING)
        shutil.copy(WORKTREE / "target/debug/trust-cg", prior_binary)
    finally:
        source.write_text(original)
    rebuild = run("rebuild-current", [*CARGO, "build", "-p", "trust-cg-cli", *LOCKED], directory=TIMING)
    rebuild["binary_sha256"] = sha256(trust_cg)
    return prior_binary, build, rebuild


def user(P: list, library: str, name: str) -> dict:
    """Link defs_main.c with -rdynamic against WORK/LIBRARY and run it."""
    P.append(probe(f"cc-user-{name}", ["cc", "-rdynamic", "-o", name, "defs_main.c", str(WORK / library), f"-Wl,-rpath,{WORK}"]))
    record = probe(f"run-{name}", [f"./{name}"])
    P.append(record)
    return record


def direct(trust_cg: str, prior: str) -> dict:
    results: dict = {"probes": [], "checks": {}}
    P = results["probes"]
    check = results["checks"]
    for name in ("caller.trust_ir", "got_page.o"):
        data = gzip.decompress((TRACE_RUN / f"{name}.gz").read_bytes())
        (INPUTS / name).write_bytes(data)
        (WORK / name).write_bytes(data)
    for directory in (INPUTS, WORK):
        (directory / "defs_main.c").write_text(DEFS)
    lib = lambda binary, output, placed, *extra: [  # noqa: E731
        binary, "--format=text", "-shared", "-nostdlib", "--relocation-model", "pic",
        "-o", output, "caller.trust_ir", *extra, placed,
    ]

    # 1. The audit's reproducer with the prior link driver: installed, and
    # its PLT ADRP is truncated.
    for name, placed in (("plt", FAR_PLT), ("both", FAR_BOTH)):
        P.append(probe(f"prior-cli-{name}", lib(prior, f"libprior_{name}.so", placed)))
        P.append(probe(f"prior-objdump-plt-{name}", ["llvm-objdump", "-d", "-j", ".plt", f"libprior_{name}.so"]))
        P.append(probe(f"prior-readelf-r-{name}", ["readelf", "-rW", f"libprior_{name}.so"]))
        user(P, f"libprior_{name}.so", f"user_prior_{name}")
    check["prior_installs_far_plt"] = all(
        p["exit"] == 0 for p in P if p["name"].startswith("prior-cli-")
    ) and all((WORK / f"libprior_{n}.so").is_file() for n in ("plt", "both"))
    check["prior_plt_adrp_truncated"] = all(
        "adrp\tx16, 0x10000" in p["stdout"] for p in P if p["name"].startswith("prior-objdump-plt-")
    )
    check["prior_jump_slot_far"] = all(
        re.search(r"^0*200010018\s+\S+\s+R_AARCH64_JUMP_SLOT\s.*tcg_desc_bump", p["stdout"], re.M) is not None
        for p in P if p["name"].startswith("prior-readelf-r-")
    )
    check["prior_users_segfault"] = all(
        p["exit"] == SIGSEGV_EXIT for p in P if p["name"].startswith("run-user_prior_")
    )

    # 2. The same commands at current source: refused by name, nothing written.
    before = listing(WORK)
    for name, placed in (("plt", FAR_PLT), ("both", FAR_BOTH)):
        P.append(probe(f"cli-{name}", lib(trust_cg, f"libplt_{name}.so", placed)))
    check["current_refuses_far_plt"] = all(
        p["exit"] == 1
        and p["stderr"].count("error[link:") == 1
        and PLT_WINDOW in p["stderr"]
        and "its R_AARCH64_JUMP_SLOT slot at 0x200010018" in p["stderr"]
        for p in P if p["name"] in ("cli-plt", "cli-both")
    )
    check["current_left_nothing"] = listing(WORK) == before

    # 3. GNU ld outside the driver, and the 2 GiB twin through the CLI.
    P.append(probe("compile-caller-pic", [trust_cg, "-c", "--relocation-model", "pic", "--format=text", "-o", "caller.o", "caller.trust_ir"]))
    for name, placed in (("plt", FAR_PLT), ("both", FAR_BOTH)):
        P.append(probe(f"raw-gnu-ld-{name}", ["cc", "-shared", "-nostdlib", "-Wl,-z,noexecstack", "-o", f"libraw_{name}.so", "caller.o", placed]))
        user(P, f"libraw_{name}.so", f"user_raw_{name}")
    check["raw_users_segfault"] = all(p["exit"] == SIGSEGV_EXIT for p in P if p["name"].startswith("run-user_raw_"))
    P.append(probe("cli-near", lib(trust_cg, "libnear.so", NEAR_PLT)))
    P.append(probe("objdump-plt-near", ["llvm-objdump", "-d", "-j", ".plt", "libnear.so"]))
    check["near_twin_links"] = next(p for p in P if p["name"] == "cli-near")["exit"] == 0
    check["near_twin_runs"] = user(P, "libnear.so", "user_near")["exit"] == 0

    # 4. The -Wl,got_page.o route: the PLT entry and the TLS descriptor
    # trampoline are refused with the two input uses; GNU ld's trampoline
    # ADRP is truncated too.
    before = listing(WORK)
    P.append(probe("cli-route-wl", lib(trust_cg, "libroute.so", FAR_BOTH, "-Wl,got_page.o")))
    route = P[-1]
    check["route_refuses_four"] = (
        route["exit"] == 1
        and route["stderr"].count("error[link:") == 4
        and PLT_WINDOW in route["stderr"]
        and TRAMPOLINE_WINDOW in route["stderr"]
        and route["stderr"].count("[TCG-LINK-GOT-PAGE-WINDOW] got_page.o: ") == 2
    )
    check["route_left_nothing"] = listing(WORK) == before
    P.append(probe("raw-gnu-ld-route", ["cc", "-shared", "-nostdlib", "-Wl,-z,noexecstack", "-o", "libraw_route.so", "caller.o", "got_page.o", FAR_BOTH]))
    P.append(probe("readelf-d-raw-route", ["readelf", "-dW", "libraw_route.so"]))
    P.append(probe("objdump-plt-raw-route", ["llvm-objdump", "-d", "-j", ".plt", "libraw_route.so"]))
    check["raw_route_has_trampoline"] = "(TLSDESC_PLT)" in P[-2]["stdout"]
    return results


def timing(trust_cg: str, prior: str) -> dict:
    """--shared and default links through this source's CLI and through the
    same CLI with the prior link driver, interleaved."""
    (WORK / "answer.trust_ir").write_text(
        "; TrustIr text format v1\nmodule \"tcg_got_answer\"\n\nfuncty.0 = () -> (i32)\n\n"
        "fn @main(functy.0) {\nbb0:\n    %0 = const i32 42\n    ret %0\n}\n"
    )
    (INPUTS / "answer.trust_ir").write_text((WORK / "answer.trust_ir").read_text())
    # An identical copy of the current CLI is the control: the spread
    # between two identical binaries is the scatter of this measurement.
    control = WORK / "trust-cg-current-copy"
    shutil.copy(trust_cg, control)
    binaries = {"prior": prior, "current": trust_cg, "current-copy": str(control)}
    cases = {
        "shared-pic-caller": lambda b, i: [b, "--format=text", "--shared", "--nostdlib", "--relocation-model", "pic", "-o", f"libt_{i}.so", "caller.trust_ir"],
        "default": lambda b, i: [b, "--format=text", "-o", f"t_default_{i}", "answer.trust_ir"],
    }
    rounds = 31
    samples: dict = {case: {name: [] for name in binaries} for case in cases}
    names = list(binaries)
    for index in range(rounds):
        for case, argv in cases.items():
            # The order rotates each round, so no binary always runs first.
            shift = index % len(names)
            for name in names[shift:] + names[:shift]:
                binary = binaries[name]
                command = argv(binary, f"{name}{index}")
                start = time.perf_counter()
                completed = subprocess.run(command, cwd=WORK, env=ENV, capture_output=True, text=True)
                elapsed = time.perf_counter() - start
                assert completed.returncode == 0, (command, completed.stderr)
                samples[case][name].append(elapsed)
    summary = {}
    for case in cases:
        medians = {name: statistics.median(samples[case][name]) for name in binaries}
        quartiles = {name: statistics.quantiles(samples[case][name], n=4) for name in binaries}
        summary[case] = {
            "median_seconds": medians,
            "quartiles_seconds": quartiles,
            "min_seconds": {name: min(samples[case][name]) for name in binaries},
            "ratio_current_over_prior": medians["current"] / medians["prior"],
            "ratio_copy_over_current": medians["current-copy"] / medians["current"],
            "samples_seconds": samples[case],
        }
    record = {
        "prior_link_driver_from": PRIOR,
        "rounds": rounds,
        "order": "interleaved per round: case, then prior, current and an identical copy of current, the order rotated each round",
        "summary": summary,
    }
    (TIMING / "timing.json").write_text(json.dumps(record, indent=2) + "\n")
    for case in cases:
        print(f"timing {case}: {summary[case]['median_seconds']} ratio {summary[case]['ratio_current_over_prior']:.3f} control {summary[case]['ratio_copy_over_current']:.3f}", flush=True)
    return record


LINK_DRIVER = "crates/trust-cg-codegen/src/link_driver.rs"
LIB_TESTS = (
    "lib-linker-code",
    ["test", "-p", "trust-cg-codegen", "--lib", "link_driver::tests::linker_generated_got_code"],
)
CLI_TESTS = ("link_options-got-page", ["test", "-p", "trust-cg-cli", "--test", "link_options", "linux_got_page"])
MUTANTS = [
    (
        "no-linker-got-code",
        "an image not in reach is refused only for an input's GOT-page use (as at 7df1bfdf7)",
        "            diagnostics.extend(linker_got_code_diagnostics(request, layout, reason));\n",
        "            diagnostics.extend(linker_got_code_diagnostics(request, layout, reason).into_iter().take(0));\n",
        [LIB_TESTS, CLI_TESTS],
    ),
    (
        "linker-code-only-with-inputs",
        "the image is checked only when a positional GOT-page use or a trace exists (the 7df1bfdf7 condition)",
        "    let unproven = got_page_unproven(image);\n",
        "    let unproven = if got_page.is_empty() && trace.is_none() {\n        None\n    } else {\n        got_page_unproven(image)\n    };\n",
        [LIB_TESTS],
    ),
    (
        "no-jump-slot-slots",
        "a PLT's JUMP_SLOT slots are not known slots (every PLT refusal is conservative)",
        "            slots: jump_slots,\n",
        "            slots: {\n                let _ = jump_slots;\n                Vec::new()\n            },\n",
        [LIB_TESTS, CLI_TESTS],
    ),
    (
        "no-tlsdesc-trampoline",
        "DT_TLSDESC_PLT is not read",
        "    if let Some(trampoline) = tag(DT_TLSDESC_PLT) {\n",
        "    if let Some(trampoline) = tag(DT_TLSDESC_PLT).filter(|_| false) {\n",
        [LIB_TESTS, CLI_TESTS],
    ),
    (
        "no-irelative",
        "R_AARCH64_IRELATIVE relocations do not show an IPLT",
        "    if irelative > 0 {\n",
        "    if false && irelative > 0 {\n",
        [LIB_TESTS],
    ),
    (
        "no-plt-section",
        "an executable .plt section does not show a PLT",
        "    if executable_section(\".plt\") {\n",
        "    if false && executable_section(\".plt\") {\n",
        [LIB_TESTS, CLI_TESTS],
    ),
    (
        "no-jmprel",
        "DT_JMPREL does not show a PLT",
        "    if tag(DT_JMPREL).is_some() && tag(DT_PLTRELSZ).is_some_and(|size| size > 0) {\n",
        "    if false && tag(DT_JMPREL).is_some() && tag(DT_PLTRELSZ).is_some_and(|size| size > 0) {\n",
        [LIB_TESTS, CLI_TESTS],
    ),
]


def mutations() -> list[dict]:
    records = []
    source = WORKTREE / LINK_DRIVER
    for name, what, old, new, runs in MUTANTS:
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
        records.append({"name": name, "what": what, "file": LINK_DRIVER, "legs": legs, "killed": killed})
        print(f"mutant {name}: {'killed' if killed else 'SURVIVED'}", flush=True)
    return records


BINARY_SHA = ""


def main() -> int:
    global BINARY_SHA
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
        tool("llvm-objdump", ["llvm-objdump", "--version"]),
        tool("rustc", ["rustc", "--version"]),
        tool("cargo", ["cargo", "--version"]),
    ]
    gate_records = gates()
    trust_cg = WORKTREE / "target/debug/trust-cg"
    BINARY_SHA = sha256(trust_cg)
    binary = {"path": str(trust_cg), "sha256": BINARY_SHA}
    prior, build_prior_record, rebuild_record = build_prior(trust_cg)
    status_after_prior = git("status", "--porcelain", "--untracked-files=all")
    direct_records = direct(str(trust_cg), str(prior))
    timing_record = timing(str(trust_cg), str(prior))
    status_mid = git("status", "--porcelain", "--untracked-files=all")
    mutation_records = mutations()
    rebuild = run("rebuild-after-mutants", [*CARGO, "build", "-p", "trust-cg-cli", *LOCKED])
    binary_after = sha256(trust_cg)
    status_after = git("status", "--porcelain", "--untracked-files=all")
    results = {
        "run": "L02-P10 second closure audit: linker-written PLT and TLS descriptor trampoline ADRPs",
        "date": "2026-09-23",
        "source_sha": head,
        "tree_sha": tree,
        "prior": PRIOR,
        "dirty_before": bool(status_before),
        "dirty_after_prior_build": bool(status_after_prior),
        "dirty_after_probes_and_timing": bool(status_mid),
        "dirty_after": bool(status_after),
        "host": host,
        "tools": tools,
        "trust_cg_binary": binary,
        "trust_cg_binary_after_mutants_sha256": binary_after,
        "prior_binary_sha256": sha256(prior),
        "build_prior": build_prior_record,
        "rebuild_current": rebuild_record,
        "gates": gate_records,
        "direct": direct_records,
        "timing": timing_record["summary"],
        "mutations": mutation_records,
        "rebuild_after_mutants": rebuild,
        "inputs": {p.name: sha256(p) for p in sorted(INPUTS.rglob("*")) if p.is_file()},
    }
    (RECORDS / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    ok = (
        not status_before
        and not status_after_prior
        and not status_mid
        and not status_after
        and binary_after == BINARY_SHA
        and rebuild_record["binary_sha256"] == BINARY_SHA
        and all(g["exit"] == 0 for g in gate_records)
        and all(m["killed"] for m in mutation_records)
        and all(v for v in direct_records["checks"].values() if isinstance(v, bool))
    )
    for key, value in direct_records["checks"].items():
        print(f"check {key}: {value}", flush=True)
    print("QUALIFIED" if ok else "NOT QUALIFIED", flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
