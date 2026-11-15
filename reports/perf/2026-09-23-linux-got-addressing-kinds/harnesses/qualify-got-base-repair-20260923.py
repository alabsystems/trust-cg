#!/usr/bin/env python3
"""Qualifying run for the L02-P10 GOT-base repair: R_AARCH64_LD64_GOTPAGE_LO15
and R_AARCH64_LD64_GOTOFF_LO15 checked from the located GOT base (Linux
AArch64, 2026-09-23).

An independent verifier found that LLD 22 writes LD64_GOTPAGE_LO15 truncated
to 15 bits and that the CLI installed its images. The run is split into
phases, each short enough to run on its own (the caller runs them in order;
each checks that the checkout is clean before and after, and writes
RUN/records/phase-<name>.json):

- gates: the gate commands of the change, logs under records/logs; the new
  native control once more with TCG_REQUIRE_LLD=1 (the LLD legs must run)
  and once with no ld.lld reachable (the LLD legs print SKIP: and the GNU ld
  legs pass);
- direct: the CLI built with the prior link driver (PRIOR, a0d5453ae) and the
  CLI built from this source run the verifier's reproducers through LLD (a
  `cc` wrapper with -fuse-ld=lld first on PATH): the 6,000-slot library,
  the PIE, and a static IFUNC GOT load; the prior installs and the image
  prints a wrong value (or dies), this source refuses by name and writes
  nothing, LLD's own images fail, GNU ld refuses or writes the slot in range,
  and the 100-slot twins link through both linkers and run; records/direct;
- kinds: probe-got-base-kinds-20260923.py (GNU ld, gold and LLD on every
  aaelf64 GOT-base kind); records/kinds;
- timing: three link cases through the prior CLI, this source's CLI and an
  identical copy of it, interleaved; records/timing;
- mutants: each source mutant's diff and targeted tests' logs (a mutant
  counts as killed only when a test failed); records/mutation;
- finish: rebuilds the CLI (its hash must equal the gates' build) and merges
  every phase into records/results.json.

RUN/records/inputs holds what the probes used; the probes run in RUN/work,
which is not archived.

Usage: qualify-got-base-repair-20260923.py WORKTREE RUN PHASE [MUTANT...]
"""

from __future__ import annotations

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
PHASE = sys.argv[3]
SELECTED = sys.argv[4:]
HARNESSES = Path(__file__).resolve().parent
RECORDS = RUN / "records"
LOGS = RECORDS / "logs"
DIRECT = RECORDS / "direct"
KINDS = RECORDS / "kinds"
TIMING = RECORDS / "timing"
MUTATION = RECORDS / "mutation"
INPUTS = RECORDS / "inputs"
WORK = RUN / "work"
HOME = Path.home()
LLD_DIR = HOME / ".local/bin"
PATH = os.pathsep.join(
    [
        str(HOME / ".local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin"),
        str(HOME / ".cargo/bin"),
        os.environ["PATH"],
    ]
)
ENV = dict(os.environ, PATH=PATH)
LLD_BIN = WORK / "lld-cc"
LLD_ENV = dict(ENV, PATH=os.pathsep.join([str(LLD_BIN), PATH]))
RESULT = re.compile(r"^test result: .*$", re.M)
RAN = re.compile(r"^(Ran \d+ tests.*|OK.*|FAILED.*)$", re.M)
TEST_LINE = re.compile(r"^test (\S+) \.\.\. (ok|FAILED|ignored)$", re.M)
CARGO = ["cargo"]
LOCKED = ["--locked", "--offline", "-j", "8"]
PRIOR = "a0d5453ae"
SIGSEGV_EXIT = 128 + 11
B1 = WORKTREE / "tests/fixtures/trust_ir_binary_container/conformance/b1_scalars.tmbc"
PRIOR_CLI = WORK / "trust-cg-prior-link-driver"
CURRENT_CLI = WORKTREE / "target/debug/trust-cg"
NEW_TEST = "an_ld64_gotpage_lo15_access_out_of_the_got_window_is_refused_and_its_near_twin_runs"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(WORKTREE), *args], check=True, capture_output=True, text=True
    ).stdout.strip()


def shown(text: str) -> str:
    return (
        text.replace(str(HARNESSES), "$HARNESSES")
        .replace(str(WORK), "$WORK")
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


def run(name: str, argv: list[str], *, directory: Path = LOGS, cwd: Path = WORKTREE, env: dict | None = None, timeout: int = 1100) -> dict:
    """Run one gate command, keep its complete output as DIRECTORY/NAME.log."""
    completed = subprocess.run(argv, cwd=cwd, env=env or ENV, capture_output=True, text=True, timeout=timeout)
    text = (
        f"$ {shown(' '.join(argv))}\n(cwd {shown(str(cwd))})\n--- stdout ---\n{shown(completed.stdout)}"
        f"--- stderr ---\n{shown(completed.stderr)}--- exit {completed.returncode} ---\n"
    )
    (directory / f"{name}.log").write_text(text)
    both = completed.stdout + completed.stderr
    record = {
        "name": name,
        "argv": [shown(a) for a in argv],
        "exit": completed.returncode,
        "test_results": RESULT.findall(both) or RAN.findall(both),
        "failed_tests": [test for test, status in TEST_LINE.findall(both) if status == "FAILED"],
        "panics": [shown(p) for p in panics(completed.stdout)],
        "skip_lines": [shown(line) for line in both.splitlines() if line.startswith("SKIP:")],
    }
    print(f"{name}: exit {completed.returncode} {record['test_results']} {record['failed_tests']}", flush=True)
    return record


def probe(name: str, argv: list[str], *, lld: bool = False, cwd: Path | None = None, timeout: int = 300) -> dict:
    """Run one direct probe; keep command, exit, stdout and stderr in records/direct/NAME.txt."""
    cwd = cwd or WORK
    try:
        completed = subprocess.run(argv, cwd=cwd, env=LLD_ENV if lld else ENV, capture_output=True, text=True, timeout=timeout)
        exit_code, stdout, stderr = completed.returncode, completed.stdout, completed.stderr
    except subprocess.TimeoutExpired:
        exit_code, stdout, stderr = "timeout", "", ""
    if isinstance(exit_code, int) and exit_code < 0:
        exit_code = 128 - exit_code
    (DIRECT / f"{name}.txt").write_text(
        f"$ {' '.join(shown(a) for a in argv)}\n(cwd {shown(str(cwd))}; PATH starts with "
        f"{'the LLD cc wrapper' if lld else 'the host tools'})\n--- stdout ---\n{shown(stdout)}"
        f"--- stderr ---\n{shown(stderr)}--- exit {exit_code} ---\n"
    )
    print(f"probe {name}: exit {exit_code}", flush=True)
    return {"name": name, "argv": [shown(a) for a in argv], "lld": lld, "exit": exit_code, "stdout": shown(stdout), "stderr": shown(stderr)}


def listing(directory: Path) -> list[str]:
    return sorted(p.name for p in directory.iterdir())


def tool(name: str, argv: list[str]) -> dict:
    path = shutil.which(argv[0], path=PATH) if "/" not in argv[0] else argv[0]
    resolved = Path(path).resolve() if path else None
    version = subprocess.run(argv, capture_output=True, text=True, env=ENV)
    text = version.stdout or version.stderr
    return {
        "name": name,
        "path": shown(path) if path else None,
        "resolved": shown(str(resolved)) if resolved else None,
        "sha256": sha256(resolved) if resolved else None,
        "version": text.splitlines()[0] if text else "",
    }


def clean() -> bool:
    return git("status", "--porcelain", "--untracked-files=all") == ""


# ---------------------------------------------------------------- gates


def phase_gates() -> dict:
    documentation_write = run("check-documentation-write", ["python3", "scripts/check_documentation.py", "--write"])
    documentation_write["tree_clean_after_write"] = clean()
    no_lld_path = os.pathsep.join(
        p for p in PATH.split(os.pathsep) if p and not (Path(p) / "ld.lld").exists()
    )
    records = [
        run("check-fmt", ["bash", "scripts/check_fmt.sh"]),
        run("check-codegen-verify", [*CARGO, "check", "-p", "trust-cg-codegen", "--features", "verify", *LOCKED]),
        run("test-codegen-lib", [*CARGO, "test", "-p", "trust-cg-codegen", "--lib", *LOCKED]),
        run(
            "test-codegen-e2e",
            [
                *CARGO, "test", "-p", "trust-cg-codegen",
                "--test", "e2e_aarch64_link_runtime",
                "--test", "e2e_aarch64_elf_tlsie",
                *LOCKED,
            ],
        ),
        run(
            "test-cli",
            [*CARGO, "test", "-p", "trust-cg-cli", "--test", "link_options", "--bin", "trust-cg", *LOCKED],
        ),
        run(
            "test-cli-got-base-lld-required",
            [*CARGO, "test", "-p", "trust-cg-cli", "--test", "link_options", *LOCKED, "--", NEW_TEST, "--nocapture"],
            env=dict(ENV, TCG_REQUIRE_LLD="1"),
        ),
        run(
            "test-cli-got-base-without-lld",
            [*CARGO, "test", "-p", "trust-cg-cli", "--test", "link_options", *LOCKED, "--", NEW_TEST, "--nocapture"],
            env=dict(ENV, PATH=no_lld_path, HOME=str(RUN / "no-home"), CARGO_HOME=str(HOME / ".cargo"), RUSTUP_HOME=str(HOME / ".rustup")),
        ),
        documentation_write,
        run("check-documentation", ["python3", "scripts/check_documentation.py", "--check"]),
        run("diagnostics-inventory", ["python3", "scripts/generate_diagnostics_inventory.py", "--check"]),
        run(
            "script-gate-tests",
            [
                "python3", "-B", "-m", "unittest",
                "scripts/tests/test_linux_aarch64_gate.py",
                "scripts/tests/test_darwin_aarch64_gate.py",
                "scripts/tests/test_linux_aarch64_bridge_gate.py",
            ],
        ),
        run("evidence-plan-citations", ["python3", "scripts/check_evidence_archive.py", "--plan"]),
        run("build-cli", [*CARGO, "build", "-p", "trust-cg-cli", *LOCKED]),
    ]
    required, without = records[5], records[6]
    checks = {
        "lld_required_leg_ran_without_skip": required["exit"] == 0 and not required["skip_lines"],
        "without_lld_the_lld_legs_skip_and_gnu_legs_pass": without["exit"] == 0 and len(without["skip_lines"]) == 1,
        "documentation_write_left_tree_clean": documentation_write["tree_clean_after_write"],
    }
    return {
        "gates": records,
        "checks": checks,
        "trust_cg_binary_sha256": sha256(CURRENT_CLI),
        "ok": all(r["exit"] == 0 for r in records) and all(checks.values()),
    }


# ---------------------------------------------------------------- direct


def got_page_lo15_source(count: int) -> str:
    source = "\t.text\n\t.globl touch\n\t.type touch, %function\ntouch:\n"
    for index in range(count):
        source += f"\tadrp x1, :got:dv_{index}\n\tldr x1, [x1, #:got_lo12:dv_{index}]\n"
    source += (
        "\tret\n\t.size touch, .-touch\n\t.globl f_gb\n\t.type f_gb, %function\nf_gb:\n"
        "\tadrp x28, _GLOBAL_OFFSET_TABLE_\n\tldr x0, [x28, #:gotpage_lo15:dv_last]\n\tldr x0, [x0]\n"
        "\tret\n\t.size f_gb, .-f_gb\n\t.data\n"
    )
    for index in range(count):
        source += f"\t.globl dv_{index}\ndv_{index}:\n\t.xword {index}\n"
    return source + "\t.globl dv_last\ndv_last:\n\t.xword 4242\n"


GB_USER = '#include <stdio.h>\nextern long f_gb(void);\nint main(void) { long v = f_gb(); printf("f_gb=%ld\\n", v); return v == 4242 ? 0 : 1; }\n'
IFUNC_GOTPAGE = (
    "\t.text\n\t.globl _start\n\t.type _start, %function\n_start:\n"
    "\tadrp x19, __rela_iplt_start\n\tadd x19, x19, :lo12:__rela_iplt_start\n"
    "\tadrp x20, __rela_iplt_end\n\tadd x20, x20, :lo12:__rela_iplt_end\n"
    "1:\tcmp x19, x20\n\tb.hs 2f\n\tldr x21, [x19]\n\tldr x0, [x19, #16]\n\tblr x0\n\tstr x0, [x21]\n"
    "\tadd x19, x19, #24\n\tb 1b\n2:\tadrp x28, _GLOBAL_OFFSET_TABLE_\n\tldr x1, [x28, #:gotpage_lo15:myfunc]\n"
    "\tblr x1\n\tmov x8, #93\n\tsvc #0\n\t.size _start, .-_start\n"
    "\t.globl myfunc\n\t.type myfunc, %gnu_indirect_function\nmyfunc:\n\tadr x0, impl\n\tret\n"
    "impl:\n\tmov x0, #42\n\tret\n"
)
HELPER = '; TrustIr text format v1\nmodule "tcg_helper"\n\nfuncty.0 = () -> (i32)\n\nfn @tcg_helper(functy.0) {\nbb0:\n    %0 = const i32 1\n    ret %0\n}\n'
ANSWER = '; TrustIr text format v1\nmodule "tcg_got_answer"\n\nfuncty.0 = () -> (i32)\n\nfn @main(functy.0) {\nbb0:\n    %0 = const i32 42\n    ret %0\n}\n'


def build_prior() -> tuple[dict, dict]:
    """The CLI with PRIOR's link driver (everything else from this source),
    copied out of the tree; the source is restored and the CLI rebuilt."""
    source = WORKTREE / "crates/trust-cg-codegen/src/link_driver.rs"
    original = source.read_text()
    prior_text = git("show", f"{PRIOR}:crates/trust-cg-codegen/src/link_driver.rs") + "\n"
    try:
        source.write_text(prior_text)
        build = run("build-prior-link-driver", [*CARGO, "build", "-p", "trust-cg-cli", *LOCKED], directory=DIRECT)
        shutil.copy(CURRENT_CLI, PRIOR_CLI)
    finally:
        source.write_text(original)
    rebuild = run("rebuild-current", [*CARGO, "build", "-p", "trust-cg-cli", *LOCKED], directory=DIRECT)
    rebuild["binary_sha256"] = sha256(CURRENT_CLI)
    build["prior_binary_sha256"] = sha256(PRIOR_CLI)
    return build, rebuild


def shared(cli: str, object_: str, output: str) -> list[str]:
    return [cli, "-shared", "-nostdlib", "--relocation-model", "pic", f"-Wl,{object_}", "-o", output, "b1_scalars.tmbc"]


def pie(cli: str, object_: str, output: str) -> list[str]:
    return [cli, "--format=text", f"-Wl,{object_},gb_user.o", "-o", output, "helper.trust_ir"]


def ifunc(cli: str, output: str) -> list[str]:
    return [cli, "--format=text", "--static", "--nostdlib", "--no-pie", "-Wl,ifunc_gotpage.o", "-o", output, "helper.trust_ir"]


def phase_direct() -> dict:
    for name, text in {
        "gb.s": got_page_lo15_source(6000),
        "gb_near.s": got_page_lo15_source(100),
        "gb_user.c": GB_USER,
        "ifunc_gotpage.s": IFUNC_GOTPAGE,
        "helper.trust_ir": HELPER,
    }.items():
        (WORK / name).write_text(text)
        (INPUTS / name).write_text(text)
    shutil.copy(B1, WORK / "b1_scalars.tmbc")
    tools = WORK / "lld-tools"
    tools.mkdir(exist_ok=True)
    LLD_BIN.mkdir(exist_ok=True)
    if not (tools / "ld.lld").exists():
        (tools / "ld.lld").symlink_to(LLD_DIR / "ld.lld")
    host_cc = shutil.which("cc", path=PATH)
    (LLD_BIN / "cc").write_text(f"#!/bin/sh\nexec '{host_cc}' -fuse-ld=lld -B'{tools}/' \"$@\"\n")
    (LLD_BIN / "cc").chmod(0o755)
    (INPUTS / "lld-cc.sh").write_text(shown((LLD_BIN / "cc").read_text()))
    P: list = []
    for source in ("gb", "gb_near", "ifunc_gotpage"):
        P.append(probe(f"as-{source}", ["as", "-o", f"{source}.o", f"{source}.s"]))
    P.append(probe("cc-gb_user.o", ["cc", "-c", "-O1", "-o", "gb_user.o", "gb_user.c"]))
    build, rebuild = build_prior()
    prior, current = str(PRIOR_CLI), str(CURRENT_CLI)
    checks: dict = {}

    def user(library: str, name: str) -> dict:
        P.append(probe(f"cc-{name}", ["cc", "-o", name, "gb_user.o", library, f"-Wl,-rpath,{WORK}"]))
        record = probe(f"run-{name}", [f"./{name}"])
        P.append(record)
        return record

    def refused(name: str, argv: list[str], output: str, prefix: str, lld: bool) -> None:
        """Run twice: into an empty directory entry and over a file."""
        before = listing(WORK)
        record = probe(name, argv, lld=lld)
        P.append(record)
        after = listing(WORK)
        (WORK / output).write_text("precious\n")
        again = probe(f"{name}-over-file", argv, lld=lld)
        P.append(again)
        kept = (WORK / output).read_text() == "precious\n"
        (WORK / output).unlink()
        lines = [line for line in record["stderr"].splitlines() if "error[link:" in line]
        checks[name] = (
            record["exit"] == 1
            and again["exit"] == 1
            and len(lines) == 1
            and lines[0].startswith(prefix)
            and before == after
            and kept
        )

    window = "trust-cg: error[link:relocation-out-of-range] `dv_last` (R_AARCH64_LD64_GOTPAGE_LO15): [TCG-LINK-GOT-PAGE-WINDOW] gb.o: R_AARCH64_LD64_GOTPAGE_LO15 against `dv_last`"
    unproven = "trust-cg: error[link:unclassified] `dv_last` (R_AARCH64_LD64_GOTPAGE_LO15): [TCG-LINK-GOT-PAGE-UNPROVEN] gb.o: R_AARCH64_LD64_GOTPAGE_LO15 against `dv_last`"
    unproven_ifunc = "trust-cg: error[link:unclassified] `myfunc` (R_AARCH64_LD64_GOTPAGE_LO15): [TCG-LINK-GOT-PAGE-UNPROVEN] ifunc_gotpage.o: R_AARCH64_LD64_GOTPAGE_LO15 against `myfunc`"

    # 1. The verifier's library through LLD.
    record = probe("prior-cli-lld-shared", shared(prior, "gb.o", "libgb_prior.so"), lld=True)
    P.append(record)
    P.append(probe("prior-objdump-lld-shared", ["objdump", "-d", "--disassemble=f_gb", "libgb_prior.so"]))
    P.append(probe("prior-readelf-r-lld-shared", ["sh", "-c", "readelf -rW libgb_prior.so | grep -E '^Relocation section| dv_last'"]))
    P.append(probe("prior-readelf-symbols-lld-shared", ["sh", "-c", "readelf -sW libgb_prior.so | grep -E '_GLOBAL_OFFSET_TABLE_| f_gb$| dv_last$'"]))
    P.append(probe("prior-readelf-sections-lld-shared", ["readelf", "-SW", "libgb_prior.so"]))
    ran = user(str(WORK / "libgb_prior.so"), "user_prior_shared")
    checks["prior_installs_lld_shared_and_user_is_wrong"] = (
        record["exit"] == 0 and ran["exit"] == 1 and ran["stdout"].startswith("f_gb=") and ran["stdout"] != "f_gb=4242\n"
    )
    refused("cli-lld-shared", shared(current, "gb.o", "libgb.so"), "libgb.so", window, True)
    # 2. The verifier's PIE through LLD.
    record = probe("prior-cli-lld-pie", pie(prior, "gb.o", "gb_pie_prior"), lld=True)
    P.append(record)
    ran = probe("run-gb_pie_prior", ["./gb_pie_prior"])
    P.append(ran)
    checks["prior_installs_lld_pie_and_it_is_wrong"] = (
        record["exit"] == 0 and ran["exit"] == 1 and ran["stdout"] != "f_gb=4242\n"
    )
    refused("cli-lld-pie", pie(current, "gb.o", "gb_pie"), "gb_pie", unproven, True)
    # 3. A static IFUNC GOT load through LLD (slot in .got.plt, 64 KiB away).
    record = probe("prior-cli-lld-ifunc", ifunc(prior, "ifunc_prior"), lld=True)
    P.append(record)
    P.append(probe("prior-objdump-lld-ifunc", ["objdump", "-d", "--disassemble=_start", "ifunc_prior"]))
    P.append(probe("prior-readelf-S-lld-ifunc", ["readelf", "-SW", "ifunc_prior"]))
    P.append(probe("prior-readelf-r-lld-ifunc", ["readelf", "-rW", "ifunc_prior"]))
    ran = probe("run-ifunc_prior", ["./ifunc_prior"])
    P.append(ran)
    checks["prior_installs_lld_ifunc_and_it_dies"] = record["exit"] == 0 and ran["exit"] == SIGSEGV_EXIT
    refused("cli-lld-ifunc", ifunc(current, "ifunc"), "ifunc", unproven_ifunc, True)
    # LLD outside the driver.
    lld_cc = str(LLD_BIN / "cc")
    raw = probe("raw-lld-shared", [lld_cc, "-shared", "-nostdlib", "-Wl,-z,noexecstack", "-o", "libgb_raw_lld.so", "gb.o"])
    P.append(raw)
    ran = user(str(WORK / "libgb_raw_lld.so"), "user_raw_lld_shared")
    checks["raw_lld_shared_is_wrong"] = raw["exit"] == 0 and ran["exit"] == 1 and ran["stdout"] != "f_gb=4242\n"
    raw = probe("raw-lld-pie", [lld_cc, "-o", "gb_raw_lld_pie", "gb.o", "gb_user.o"])
    P.append(raw)
    ran = probe("run-gb_raw_lld_pie", ["./gb_raw_lld_pie"])
    P.append(ran)
    checks["raw_lld_pie_is_wrong"] = raw["exit"] == 0 and ran["exit"] == 1 and ran["stdout"] != "f_gb=4242\n"
    raw = probe("raw-lld-ifunc", [lld_cc, "-static", "-nostdlib", "-no-pie", "-Wl,-z,noexecstack", "-o", "ifunc_raw_lld", "ifunc_gotpage.o"])
    P.append(raw)
    ran = probe("run-ifunc_raw_lld", ["./ifunc_raw_lld"])
    P.append(ran)
    checks["raw_lld_ifunc_dies"] = raw["exit"] == 0 and ran["exit"] == SIGSEGV_EXIT
    # GNU ld: refuses or writes the slot in range; the driver refuses its
    # 48 KiB-GOT library conservatively.
    raw = probe("raw-gnu-ld-shared", ["cc", "-shared", "-nostdlib", "-Wl,-z,noexecstack", "-o", "libgb_raw_gnu.so", "gb.o"])
    P.append(raw)
    ran = user(str(WORK / "libgb_raw_gnu.so"), "user_raw_gnu_shared") if raw["exit"] == 0 else {"exit": None, "stdout": ""}
    checks["raw_gnu_ld_shared_refuses_or_is_right"] = (
        (raw["exit"] == 0 and ran["exit"] == 0 and ran["stdout"] == "f_gb=4242\n")
        or "relocation truncated to fit: R_AARCH64_LD64_GOTPAGE_LO15" in raw["stderr"]
    )
    raw = probe("raw-gnu-ld-pie", ["cc", "-o", "gb_raw_gnu_pie", "gb.o", "gb_user.o"])
    P.append(raw)
    checks["raw_gnu_ld_pie_refuses"] = raw["exit"] != 0 and "relocation truncated to fit: R_AARCH64_LD64_GOTPAGE_LO15" in raw["stderr"]
    refused("cli-gnu-shared", shared(current, "gb.o", "libgb_gnu.so"), "libgb_gnu.so", unproven, False)
    before = listing(WORK)
    record = probe("cli-gnu-pie", pie(current, "gb.o", "gb_pie_gnu"))
    P.append(record)
    checks["cli-gnu-pie"] = (
        record["exit"] == 1
        and "relocation truncated to fit: R_AARCH64_LD64_GOTPAGE_LO15" in record["stderr"]
        and before == listing(WORK)
    )
    # The twins.
    for linker, lld in (("lld", True), ("gnu", False)):
        record = probe(f"cli-near-{linker}-shared", shared(current, "gb_near.o", f"libgb_near_{linker}.so"), lld=lld)
        P.append(record)
        ran = user(str(WORK / f"libgb_near_{linker}.so"), f"user_near_{linker}")
        checks[f"near_{linker}_shared_runs"] = record["exit"] == 0 and ran["exit"] == 0 and ran["stdout"] == "f_gb=4242\n"
        record = probe(f"cli-near-{linker}-pie", pie(current, "gb_near.o", f"gb_near_pie_{linker}"), lld=lld)
        P.append(record)
        ran = probe(f"run-gb_near_pie_{linker}", [f"./gb_near_pie_{linker}"])
        P.append(ran)
        checks[f"near_{linker}_pie_runs"] = record["exit"] == 0 and ran["exit"] == 0 and ran["stdout"] == "f_gb=4242\n"
    record = probe("cli-gnu-ifunc", ifunc(current, "ifunc_gnu"))
    P.append(record)
    ran = probe("run-ifunc_gnu", ["./ifunc_gnu"])
    P.append(ran)
    checks["gnu_ifunc_links_and_returns_42"] = record["exit"] == 0 and ran["exit"] == 42
    checks["prior_build_ok"] = build["exit"] == 0 and rebuild["exit"] == 0
    (DIRECT / "checks.json").write_text(json.dumps(checks, indent=2) + "\n")
    return {
        "direct": {"prior_build": build, "rebuild": rebuild, "probes": P, "checks": checks},
        "ok": all(checks.values()),
    }


# ---------------------------------------------------------------- kinds


def phase_kinds() -> dict:
    work = WORK / "kinds"
    if work.exists():
        shutil.rmtree(work)
    out = KINDS / "probe.json"
    record = run(
        "probe-got-base-kinds",
        ["python3", "-B", str(HARNESSES / "probe-got-base-kinds-20260923.py"), str(work), str(out)],
        directory=KINDS,
    )
    data = json.loads(out.read_text())
    truncated = [
        {k: row.get(k) for k in ("code", "linker", "layout", "shape", "class")}
        for section in ("far", "verifier_shape", "ifunc")
        for row in data[section]
        if "truncated" in row["class"]
    ]
    return {"kinds": record, "truncated": truncated, "ok": record["exit"] == 0}


# ---------------------------------------------------------------- timing


def phase_timing() -> dict:
    """Three link cases through the prior CLI, this source's CLI and an
    identical copy of it, interleaved with the order rotated each round."""
    (WORK / "answer.trust_ir").write_text(ANSWER)
    (INPUTS / "answer.trust_ir").write_text(ANSWER)
    control = WORK / "trust-cg-current-copy"
    shutil.copy(CURRENT_CLI, control)
    binaries = {"prior": str(PRIOR_CLI), "current": str(CURRENT_CLI), "current-copy": str(control)}
    cases = {
        "shared-b1": lambda b, i: [b, "--shared", "--nostdlib", "--relocation-model", "pic", "-o", f"libt_{i}.so", "b1_scalars.tmbc"],
        "default": lambda b, i: [b, "--format=text", "-o", f"t_default_{i}", "answer.trust_ir"],
        "static-spread": lambda b, i: [b, "--format=text", "--static", "-o", f"t_static_{i}", "answer.trust_ir", "-Wl,--section-start=.data=0x800000"],
    }
    rounds = 15
    samples: dict = {case: {name: [] for name in binaries} for case in cases}
    names = list(binaries)
    for index in range(rounds):
        for case, argv in cases.items():
            shift = index % len(names)
            for name in names[shift:] + names[:shift]:
                command = argv(binaries[name], f"{name}{index}")
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
            "quartiles_seconds": {name: statistics.quantiles(samples[case][name], n=4) for name in binaries},
            "min_seconds": {name: min(samples[case][name]) for name in binaries},
            "ratio_current_over_prior": medians["current"] / medians["prior"],
            "ratio_copy_over_current": medians["current-copy"] / medians["current"],
            "samples_seconds": samples[case],
        }
        print(
            f"timing {case}: {medians} ratio {summary[case]['ratio_current_over_prior']:.3f} "
            f"control {summary[case]['ratio_copy_over_current']:.3f}",
            flush=True,
        )
    record = {
        "prior_link_driver_from": PRIOR,
        "rounds": rounds,
        "order": "per round and case: prior, current and an identical copy of current, the order rotated each round",
        "summary": summary,
    }
    (TIMING / "timing.json").write_text(json.dumps(record, indent=2) + "\n")
    return {"timing": record["summary"], "ok": True}


# ---------------------------------------------------------------- mutants

LINK_DRIVER = "crates/trust-cg-codegen/src/link_driver.rs"
LIB = ("lib-link-driver", ["test", "-p", "trust-cg-codegen", "--lib", *LOCKED, "--", "link_driver::tests"], None)
CLI = (
    "link_options-got-base",
    ["test", "-p", "trust-cg-cli", "--test", "link_options", *LOCKED, "--", NEW_TEST],
    {"TCG_REQUIRE_LLD": "1"},
)
ROW_ANCHOR = "        .find(|(code, _)| *code == reloc_type)\n"


def drop_row(code: int) -> tuple[str, str]:
    return ROW_ANCHOR, f"        .find(|(code, _)| *code == reloc_type && *code != {code})\n"


MUTANTS = {
    "drop-gotpage-lo15": ("R_AARCH64_LD64_GOTPAGE_LO15 (313) is not collected", *drop_row(313), [LIB, CLI]),
    "drop-gotoff-lo15": ("R_AARCH64_LD64_GOTOFF_LO15 (310, refused by GNU ld, unknown to LLD) is not collected", *drop_row(310), [LIB]),
    "no-got-base-window": (
        "the GOT-base windows are never checked (every image is shown)",
        "        let base = match &self.got_base {\n            Ok(base) => base,\n            Err(why) => return Some(why.clone()),\n        };\n",
        "        if true {\n            return None;\n        }\n        let base = match &self.got_base {\n            Ok(base) => base,\n            Err(why) => return Some(why.clone()),\n        };\n",
        [LIB, CLI],
    ),
    "unlocated-base-shown": (
        "an image whose GOT base cannot be located is shown in the window",
        "            Err(why) => return Some(why.clone()),\n",
        "            Err(_) => return None,\n",
        [LIB, CLI],
    ),
    "no-irelative-slots": (
        "IRELATIVE targets are not places a GOT-base slot can lie",
        "    R_AARCH64_AUTH_GLOB_DAT,\n    R_AARCH64_IRELATIVE,\n];\n",
        "    R_AARCH64_AUTH_GLOB_DAT,\n    R_AARCH64_GLOB_DAT,\n];\n",
        [LIB, CLI],
    ),
    "base-not-page": (
        "LD64_GOTPAGE_LO15 is measured from the base, not its page",
        "            base.address & !0xfff\n",
        "            base.address & !0x0\n",
        [LIB],
    ),
    "section-from-base": (
        "the section holding the base counts only from the base up (slots below it are missed)",
        "                format!(\"`{}` (the section holding the GOT base)\", section.name),\n                section.address,\n                section.size,\n",
        "                format!(\"`{}` (the section holding the GOT base)\", section.name),\n                address,\n                section.size - (address - section.address),\n",
        [LIB],
    ),
}


def phase_mutants() -> dict:
    records = []
    source = WORKTREE / LINK_DRIVER
    for name in SELECTED or list(MUTANTS):
        what, old, new, runs = MUTANTS[name]
        original = source.read_text()
        directory = MUTATION / name
        directory.mkdir(parents=True, exist_ok=True)
        assert original.count(old) == 1, name
        source.write_text(original.replace(old, new))
        diff = subprocess.run(["git", "-C", str(WORKTREE), "diff"], capture_output=True, text=True).stdout
        (directory / "mutant.diff").write_text(diff)
        legs = []
        try:
            for leg, args, extra in runs:
                env = dict(ENV, **extra) if extra else ENV
                legs.append(run(leg, [*CARGO, *args], directory=directory, env=env))
        finally:
            source.write_text(original)
        killed = any(leg["failed_tests"] for leg in legs)
        records.append({"name": name, "what": what, "file": LINK_DRIVER, "legs": legs, "killed": killed})
        print(f"mutant {name}: {'killed' if killed else 'SURVIVED'}", flush=True)
    return {"mutations": records, "ok": all(r["killed"] for r in records)}


# ---------------------------------------------------------------- finish


def phase_finish() -> dict:
    rebuild = run("rebuild-after-mutants", [*CARGO, "build", "-p", "trust-cg-cli", *LOCKED])
    phases = {}
    for path in sorted(RECORDS.glob("phase-*.json")):
        phases[path.stem.removeprefix("phase-")] = json.loads(path.read_text())
    gates_sha = phases["gates"]["result"]["trust_cg_binary_sha256"]
    results = {
        "run": "L02-P10 GOT-base repair: LD64_GOTPAGE_LO15 and LD64_GOTOFF_LO15 checked from the located GOT base",
        "date": "2026-09-23",
        "source_sha": git("rev-parse", "HEAD"),
        "tree_sha": git("rev-parse", "HEAD^{tree}"),
        "prior": PRIOR,
        "host": {
            "uname": " ".join(platform.uname()),
            "glibc": subprocess.run(["ldd", "--version"], capture_output=True, text=True).stdout.splitlines()[0],
        },
        "tools": [
            tool("cc", ["cc", "--version"]),
            tool("ld", ["ld", "--version"]),
            tool("ld.gold", ["ld.gold", "--version"]),
            tool("as", ["as", "--version"]),
            tool("readelf", ["readelf", "--version"]),
            tool("objdump", ["objdump", "--version"]),
            tool("ld.lld", [str(LLD_DIR / "ld.lld"), "--version"]),
            tool("rustc", ["rustc", "--version"]),
            tool("cargo", ["cargo", "--version"]),
        ],
        "trust_cg_binary_sha256": gates_sha,
        "trust_cg_binary_after_mutants_sha256": sha256(CURRENT_CLI),
        "rebuild_after_mutants": rebuild,
        "phases": phases,
        "inputs": {p.name: sha256(p) for p in sorted(INPUTS.rglob("*")) if p.is_file()},
    }
    ok = (
        rebuild["exit"] == 0
        and results["trust_cg_binary_after_mutants_sha256"] == gates_sha
        and all(p["clean_before"] and p["clean_after"] and p["result"]["ok"] for p in phases.values())
    )
    results["qualified"] = ok
    (RECORDS / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    return {"ok": ok}


def main() -> int:
    for directory in (LOGS, DIRECT, KINDS, TIMING, MUTATION, INPUTS, WORK):
        directory.mkdir(parents=True, exist_ok=True)
    phases = {
        "gates": phase_gates,
        "direct": phase_direct,
        "kinds": phase_kinds,
        "timing": phase_timing,
        "mutants": phase_mutants,
        "finish": phase_finish,
    }
    before = clean()
    if not before:
        print("checkout is dirty; refusing to qualify", file=sys.stderr)
        return 1
    started = time.time()
    result = phases[PHASE]()
    after = clean()
    if PHASE == "finish":
        print("QUALIFIED" if result["ok"] and after else "NOT QUALIFIED", flush=True)
        return 0 if result["ok"] and after else 1
    name = PHASE if not SELECTED else f"{PHASE}-{'-'.join(SELECTED)}"
    record = {
        "phase": name,
        "source_sha": git("rev-parse", "HEAD"),
        "clean_before": before,
        "clean_after": after,
        "seconds": round(time.time() - started, 1),
        "result": result,
    }
    (RECORDS / f"phase-{name}.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"phase {name}: ok {result['ok']} clean {before}/{after} in {record['seconds']} s", flush=True)
    return 0 if result["ok"] and after else 1


if __name__ == "__main__":
    raise SystemExit(main())
