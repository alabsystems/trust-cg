#!/usr/bin/env python3
"""Qualifying run for the third L02-P10 closure audit: every aaelf64
GOT-addressing relocation kind in its own window, and hidden IPLTs refused
through their IFUNC definitions (Linux AArch64, 2026-09-23).

The run is split into phases, each short enough to run on its own (the
caller runs them in order; each checks that the checkout is clean before and
after, and writes RUN/records/phase-<name>.json):

- gates: the gate commands of the change (touched CLI and codegen test
  targets, the codegen library, the verify-feature check, formatting, the
  documentation, diagnostics and script gates, the plan citation check),
  logs under records/logs;
- direct: the CLI built with the prior link driver (PRIOR, 8a0f3faf8) and
  the CLI built from this source run each audit reproducer (the page
  general-dynamic TLSGD_ADR_PAGE21 library, the tiny-model
  TLSIE_LD_GOTTPREL_PREL19 library, the script-hidden and
  section-header-less static IFUNC programs) and the two further narrow
  routes (general-dynamic ADR, descriptor load literal and ADR with .got at
  16 MiB): the prior CLI installs and its image fails, this source refuses
  by name and writes nothing, GNU ld's own image fails, and the near twin
  links through this source's CLI and runs; records under records/direct;
- kinds: probe-got-kinds-20260923.py on every aaelf64 GOT kind (GNU ld near
  and far, LLD near) and the GOT-base overflow probes; records/kinds;
- timing: three link cases through the prior CLI, this source's CLI and an
  identical copy of it (the scatter control), interleaved; records/timing;
- mutants: each source mutant's diff and targeted tests' logs (a mutant
  counts as killed only when a test failed); records/mutation;
- finish: rebuilds the CLI (its hash must equal the gates' build), merges
  every phase into records/results.json.

RUN/records/inputs holds what the probes used; the probes run in RUN/work,
which is not archived.

Usage: qualify-got-addressing-kinds-20260923.py WORKTREE RUN PHASE [MUTANT...]
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
PRIOR = "8a0f3faf8"
SIGSEGV_EXIT = 128 + 11
B1 = WORKTREE / "tests/fixtures/trust_ir_binary_container/conformance/b1_scalars.tmbc"
PRIOR_CLI = WORK / "trust-cg-prior-link-driver"
CURRENT_CLI = WORKTREE / "target/debug/trust-cg"


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


def run(name: str, argv: list[str], *, directory: Path = LOGS, cwd: Path = WORKTREE, timeout: int = 1100) -> dict:
    """Run one gate command, keep its complete output as DIRECTORY/NAME.log."""
    completed = subprocess.run(argv, cwd=cwd, env=ENV, capture_output=True, text=True, timeout=timeout)
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
                "--test", "e2e_aarch64_elf_relocation_model",
                "--test", "e2e_aarch64_globals_linux",
                "--test", "aarch64_elf_symbol_binding",
                *LOCKED,
            ],
        ),
        run(
            "test-cli",
            [
                *CARGO, "test", "-p", "trust-cg-cli",
                "--test", "link_options", "--test", "output_paths", "--bin", "trust-cg",
                *LOCKED,
            ],
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
    return {
        "gates": records,
        "trust_cg_binary_sha256": sha256(CURRENT_CLI),
        "ok": all(r["exit"] == 0 for r in records) and documentation_write["tree_clean_after_write"],
    }


# ---------------------------------------------------------------- direct

TDATA = '\t.section .tdata,"awT",%progbits\n\t.globl {n}\n\t.type {n}, %object\n\t.size {n}, 4\n{n}:\n\t.word 42\n'


def function(name: str, body: str) -> str:
    return f"\t.text\n\t.globl {name}\n\t.type {name}, %function\n{name}:\n{body}\t.size {name}, .-{name}\n"


SOURCES = {
    "gd.s": function("get_gd", "\tadrp x0, :tlsgd:gdvar\n\tadd x0, x0, :tlsgd_lo12:gdvar\n\tldr x0, [x0]\n\tret\n")
    + TDATA.format(n="gdvar"),
    "tie_0x180000.s": function(
        "get_ie", "\tldr x0, :gottprel:ievar\n\tmrs x1, tpidr_el0\n\tldr w0, [x1, x0]\n\tret\n\t.skip 0x180000\n"
    )
    + TDATA.format(n="ievar"),
    "tie_0x10000.s": function(
        "get_ie", "\tldr x0, :gottprel:ievar\n\tmrs x1, tpidr_el0\n\tldr w0, [x1, x0]\n\tret\n\t.skip 0x10000\n"
    )
    + TDATA.format(n="ievar"),
    "gd21.s": function(
        "get_gd21",
        "\tstp x29, x30, [sp, -16]!\n\tmov x29, sp\n\tadr x0, :tlsgd:gdvar21\n\tbl __tls_get_addr\n"
        "\tldr w0, [x0]\n\tldp x29, x30, [sp], 16\n\tret\n",
    )
    + TDATA.format(n="gdvar21"),
    "desc21.s": function(
        "get_desc21",
        "\tstp x29, x30, [sp, -16]!\n\tmov x29, sp\n\tldr x1, :tlsdesc:dvar21\n\tadr x0, :tlsdesc:dvar21\n"
        "\t.tlsdesccall dvar21\n\tblr x1\n\tmrs x1, tpidr_el0\n\tldr w0, [x1, x0]\n\tldp x29, x30, [sp], 16\n\tret\n",
    )
    + TDATA.format(n="dvar21"),
    "ifunc.s": (
        "\t.text\n\t.globl _start\n\t.type _start, %function\n_start:\n"
        "\tadrp x19, __rela_iplt_start\n\tadd x19, x19, :lo12:__rela_iplt_start\n"
        "\tadrp x20, __rela_iplt_end\n\tadd x20, x20, :lo12:__rela_iplt_end\n"
        "1:\tcmp x19, x20\n\tb.hs 2f\n\tldr x21, [x19]\n\tldr x0, [x19, #16]\n\tblr x0\n\tstr x0, [x21]\n"
        "\tadd x19, x19, #24\n\tb 1b\n2:\tbl myfunc\n\tmov x8, #93\n\tsvc #0\n\t.size _start, .-_start\n"
        "\t.globl myfunc\n\t.type myfunc, %gnu_indirect_function\nmyfunc:\n\tadr x0, impl\n\tret\n"
        "impl:\n\tmov x0, #42\n\tret\n\t.section .rodata\n\t.globl ro_word\nro_word:\n\t.xword 0x1234\n"
    ),
}


def script(data: int) -> str:
    return (
        "ENTRY(_start)\nSECTIONS {\n  . = 0x400000;\n  .text : { *(.text*) *(.iplt) }\n"
        "  .rodata : { *(.rodata*) PROVIDE_HIDDEN(__rela_iplt_start = .); *(.rela.iplt) "
        "PROVIDE_HIDDEN(__rela_iplt_end = .); }\n  .eh_frame : { *(.eh_frame) }\n"
        f"  . = {data:#x};\n  .data : {{ *(.got.plt) *(.igot.plt) *(.got) *(.data*) }}\n"
        "  .bss : { *(.bss*) }\n}\n"
    )


USERS = {
    "gd_user.c": '#include <stdio.h>\nextern long get_gd(void);\nint main(void) { long m = get_gd(); printf("module=%ld\\n", m); return m == 0 ? 1 : 0; }\n',
    "tie_user.c": '#include <stdio.h>\nextern int get_ie(void);\nint main(void) { int v = get_ie(); printf("ievar=%d\\n", v); return v == 42 ? 0 : 1; }\n',
    "gd21_user.c": '#include <stdio.h>\nextern int get_gd21(void);\nint main(void) { int v = get_gd21(); printf("gdvar21=%d\\n", v); return v == 42 ? 0 : 1; }\n',
    "desc21_user.c": '#include <stdio.h>\nextern int get_desc21(void);\nint main(void) { int v = get_desc21(); printf("dvar21=%d\\n", v); return v == 42 ? 0 : 1; }\n',
}
HELPER = '; TrustIr text format v1\nmodule "tcg_helper"\n\nfuncty.0 = () -> (i32)\n\nfn @tcg_helper(functy.0) {\nbb0:\n    %0 = const i32 1\n    ret %0\n}\n'
ANSWER = '; TrustIr text format v1\nmodule "tcg_got_answer"\n\nfuncty.0 = () -> (i32)\n\nfn @main(functy.0) {\nbb0:\n    %0 = const i32 42\n    ret %0\n}\n'


def shared(cli: str, output: str, operand: str, *placed: str) -> list[str]:
    return [cli, "-shared", "-nostdlib", "--relocation-model", "pic", f"-Wl,{operand}", *placed, "-o", output, "b1_scalars.tmbc"]


def static(cli: str, output: str, *placed: str) -> list[str]:
    return [cli, "--format=text", "--static", "--nostdlib", "--no-pie", "-Wl,ifunc.o", *placed, "-o", output, "helper.trust_ir"]


# Each shared route: name, far operand, far placement, near operand, near
# placement, user, expected refusals (count and text), how GNU ld's and the
# prior CLI's user ends.
SHARED_ROUTES = [
    {
        "name": "gd",
        "far": ("gd.o", ["-Wl,--section-start=.got=0x200000000"]),
        "near": ("gd.o", ["-Wl,--section-start=.got=0x80000000"]),
        "user": "gd_user.c",
        "refusals": [
            "error[link:relocation-out-of-range] `gdvar` (R_AARCH64_TLSGD_ADR_PAGE21): [TCG-LINK-GOT-PAGE-WINDOW] "
            "gd.o: R_AARCH64_TLSGD_ADR_PAGE21 against `gdvar` addresses a GOT slot through an ADRP page delta"
        ],
        "fails": lambda record: record["exit"] == 1 and "module=0" in record["stdout"],
        "disasm": ("get_gd", re.compile(r"adrp\s+x0, 0 ")),
    },
    {
        "name": "tie",
        "far": ("tie_0x180000.o", []),
        "near": ("tie_0x10000.o", []),
        "user": "tie_user.c",
        "refusals": [
            "error[link:unclassified] `ievar` (R_AARCH64_TLSIE_LD_GOTTPREL_PREL19): [TCG-LINK-GOT-PAGE-UNPROVEN] "
            "tie_0x180000.o: R_AARCH64_TLSIE_LD_GOTTPREL_PREL19 against `ievar` is a GOT-addressing relocation "
            "through a load-literal (LDR) offset"
        ],
        "fails": lambda record: record["exit"] == SIGSEGV_EXIT,
        "disasm": None,
    },
    {
        "name": "gd21",
        "far": ("gd21.o", ["-Wl,--section-start=.got=0x1000000"]),
        "near": ("gd21.o", []),
        "user": "gd21_user.c",
        "refusals": [
            "error[link:relocation-out-of-range] `gdvar21` (R_AARCH64_TLSGD_ADR_PREL21): [TCG-LINK-GOT-PAGE-WINDOW] "
            "gd21.o: R_AARCH64_TLSGD_ADR_PREL21 against `gdvar21` addresses a GOT slot through an ADR offset"
        ],
        "fails": lambda record: record["exit"] == SIGSEGV_EXIT,
        "disasm": None,
    },
    {
        "name": "desc21",
        "far": ("desc21.o", ["-Wl,--section-start=.got=0x1000000"]),
        "near": ("desc21.o", []),
        "user": "desc21_user.c",
        "refusals": [
            "error[link:relocation-out-of-range] `dvar21` (R_AARCH64_TLSDESC_LD_PREL19): [TCG-LINK-GOT-PAGE-WINDOW] "
            "desc21.o: R_AARCH64_TLSDESC_LD_PREL19 against `dvar21` addresses a GOT slot through a load-literal "
            "(LDR) offset",
            "error[link:relocation-out-of-range] `dvar21` (R_AARCH64_TLSDESC_ADR_PREL21): [TCG-LINK-GOT-PAGE-WINDOW] "
            "desc21.o: R_AARCH64_TLSDESC_ADR_PREL21 against `dvar21` addresses a GOT slot through an ADR offset",
        ],
        "fails": lambda record: record["exit"] == SIGSEGV_EXIT,
        "disasm": None,
    },
]
IFUNC_REFUSAL = (
    "error[link:unclassified] `myfunc` (STT_GNU_IFUNC): [TCG-LINK-GOT-PAGE-UNPROVEN] ifunc.o: `myfunc` is an "
    "IFUNC (STT_GNU_IFUNC) it defines, whose PLT or IPLT entry the linker writes with an ADRP to the entry's "
    "GOT slot"
)
STATIC_ROUTES = [
    {"name": "script", "far": ["-Wl,-T,script_0x200000000.ld"], "near": ["-Wl,-T,script_0x80000000.ld"], "count": 1},
    {
        "name": "nsh",
        "far": ["-Wl,-z,nosectionheader", "-Wl,--section-start=.got.plt=0x200000000"],
        "near": ["-Wl,--section-start=.got.plt=0x80000000"],
        "count": 1,
    },
    {"name": "sh", "far": ["-Wl,--section-start=.got.plt=0x200000000"], "near": ["-Wl,--section-start=.got.plt=0x80000000"], "count": 3},
]


def user(P: list, source: str, library: str, name: str) -> dict:
    P.append(probe(f"cc-{name}", ["cc", "-o", name, source, str(WORK / library), f"-Wl,-rpath,{WORK}"]))
    record = probe(f"run-{name}", [f"./{name}"])
    P.append(record)
    return record


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


def phase_direct() -> dict:
    WORK.mkdir(parents=True, exist_ok=True)
    build, rebuild = build_prior()
    current, prior = str(CURRENT_CLI), str(PRIOR_CLI)
    files = dict(SOURCES)
    files.update(USERS)
    files["script_0x200000000.ld"] = script(0x2_0000_0000)
    files["script_0x80000000.ld"] = script(0x8000_0000)
    files["helper.trust_ir"] = HELPER
    for name, text in files.items():
        (WORK / name).write_text(text)
        (INPUTS / name).write_text(text)
    shutil.copy(B1, WORK / "b1_scalars.tmbc")
    shutil.copy(B1, INPUTS / "b1_scalars.tmbc")
    results: dict = {"probes": [], "checks": {}}
    P, check = results["probes"], results["checks"]
    for name in SOURCES:
        P.append(probe(f"as-{name}", ["as", "-o", name.replace(".s", ".o"), name]))

    for route in SHARED_ROUTES:
        name = route["name"]
        far_object, far_placed = route["far"]
        near_object, near_placed = route["near"]
        # The prior CLI installs the library, and its user fails.
        P.append(probe(f"prior-cli-{name}", shared(prior, f"libprior_{name}.so", far_object, *far_placed)))
        check[f"{name}_prior_installs"] = P[-1]["exit"] == 0 and (WORK / f"libprior_{name}.so").is_file()
        P.append(probe(f"prior-readelf-r-{name}", ["readelf", "-rW", f"libprior_{name}.so"]))
        P.append(probe(f"prior-objdump-{name}", ["objdump", "-d", "--no-show-raw-insn", f"libprior_{name}.so"]))
        if route["disasm"]:
            symbol, pattern = route["disasm"]
            text = P[-1]["stdout"]
            body = text.split(f"<{symbol}>:", 1)[1].split("\n\n", 1)[0] if f"<{symbol}>:" in text else ""
            check[f"{name}_prior_access_truncated"] = pattern.search(body) is not None
        check[f"{name}_prior_user_fails"] = route["fails"](user(P, route["user"], f"libprior_{name}.so", f"user_prior_{name}"))
        # This source refuses it by name and writes nothing.
        before = listing(WORK)
        P.append(probe(f"cli-{name}", shared(current, f"lib{name}.so", far_object, *far_placed)))
        record = P[-1]
        check[f"{name}_current_refuses"] = (
            record["exit"] == 1
            and record["stderr"].count("error[link:") == len(route["refusals"])
            and all(text in record["stderr"] for text in route["refusals"])
            and f"the linked output for lib{name}.so was refused and not installed" in record["stderr"]
        )
        check[f"{name}_current_left_nothing"] = listing(WORK) == before
        # GNU ld's own library outside the driver fails the same way.
        P.append(probe(f"raw-gnu-ld-{name}", ["cc", "-shared", "-nostdlib", "-Wl,-z,noexecstack", "-o", f"libraw_{name}.so", far_object, *far_placed]))
        check[f"{name}_raw_user_fails"] = route["fails"](user(P, route["user"], f"libraw_{name}.so", f"user_raw_{name}"))
        # The near twin links through this source's CLI and runs.
        P.append(probe(f"cli-near-{name}", shared(current, f"libnear_{name}.so", near_object, *near_placed)))
        check[f"{name}_near_links"] = P[-1]["exit"] == 0
        check[f"{name}_near_runs"] = user(P, route["user"], f"libnear_{name}.so", f"user_near_{name}")["exit"] == 0

    # The tiny-model library's load literal does not address its slot.
    readelf = next(p for p in P if p["name"] == "prior-readelf-r-tie")["stdout"]
    objdump = next(p for p in P if p["name"] == "prior-objdump-tie")["stdout"]
    slot = re.search(r"^0*([0-9a-f]+)\s+\S+\s+R_AARCH64_TLS_TPREL64\s", readelf, re.M)
    literal = re.search(r"<get_ie>:\n\s*[0-9a-f]+:\s+ldr\s+x0, ([0-9a-f]+)", objdump)
    check["tie_prior_literal_misses_slot"] = bool(slot and literal and int(slot[1], 16) != int(literal[1], 16))
    results["tie_prior_slot_and_literal"] = [slot[1] if slot else None, literal[1] if literal else None]

    for route in STATIC_ROUTES:
        name = route["name"]
        P.append(probe(f"prior-cli-{name}", static(prior, f"prior_{name}", *route["far"])))
        prior_record = P[-1]
        if name != "sh":
            check[f"{name}_prior_installs"] = prior_record["exit"] == 0 and (WORK / f"prior_{name}").is_file()
            if name == "script":
                # objdump cannot disassemble an image without section headers.
                P.append(probe(f"prior-objdump-{name}", ["objdump", "-d", "--no-show-raw-insn", f"prior_{name}"]))
                check[f"{name}_prior_iplt_adrp_truncated"] = re.search(r"adrp\s+x16, 0 ", P[-1]["stdout"]) is not None
            P.append(probe(f"prior-readelf-l-{name}", ["readelf", "-lW", f"prior_{name}"]))
            P.append(probe(f"run-prior-{name}", [f"./prior_{name}"]))
            check[f"{name}_prior_program_fails"] = P[-1]["exit"] == SIGSEGV_EXIT
        before = listing(WORK)
        P.append(probe(f"cli-{name}", static(current, f"prog_{name}", *route["far"])))
        record = P[-1]
        check[f"{name}_current_refuses"] = (
            record["exit"] == 1
            and record["stderr"].count("error[link:") == route["count"]
            and IFUNC_REFUSAL in record["stderr"]
            and f"the linked output for prog_{name} was refused and not installed" in record["stderr"]
        )
        check[f"{name}_current_left_nothing"] = listing(WORK) == before
        P.append(probe(f"raw-gnu-ld-{name}", ["cc", "-static", "-nostdlib", "-no-pie", "-Wl,-z,noexecstack", "-o", f"raw_{name}", "ifunc.o", *route["far"]]))
        P.append(probe(f"run-raw-{name}", [f"./raw_{name}"]))
        check[f"{name}_raw_program_fails"] = P[-1]["exit"] == SIGSEGV_EXIT
        if name != "nsh":
            P.append(probe(f"cli-near-{name}", static(current, f"near_{name}", *route["near"])))
            check[f"{name}_near_links"] = P[-1]["exit"] == 0
            P.append(probe(f"run-near-{name}", [f"./near_{name}"]))
            check[f"{name}_near_runs"] = P[-1]["exit"] == 42
    # Without a section header table the 2 GiB twin is refused as well.
    P.append(probe("cli-near-nsh", static(current, "near_nsh", "-Wl,-z,nosectionheader", "-Wl,--section-start=.got.plt=0x80000000")))
    record = P[-1]
    check["nsh_near_refused_conservatively"] = (
        record["exit"] == 1 and IFUNC_REFUSAL in record["stderr"] and "it has no section header table" in record["stderr"]
    )
    return {
        "build_prior": build,
        "rebuild_current": rebuild,
        "direct": results,
        "ok": all(results["checks"].values()) and rebuild["binary_sha256"] == sha256(CURRENT_CLI),
    }


# ---------------------------------------------------------------- kinds


def phase_kinds() -> dict:
    probe_run = run(
        "probe-got-kinds",
        ["python3", str(HARNESSES / "probe-got-kinds-20260923.py"), str(WORK / "kinds"), str(KINDS / "kinds.json")],
        directory=KINDS,
    )
    data = json.loads((KINDS / "kinds.json").read_text())
    rows = {row["code"]: row for row in data["kinds"]}
    far_links = sorted(
        code for code, row in rows.items() if row.get("gnu_ld_far", {}).get("exit") == 0 and row["class"] not in ("got-base", "low-bits")
    )
    checks = {
        # GNU ld links these place-relative kinds with the GOT out of window.
        "gnu_ld_links_far": far_links == [311, 512, 513, 541, 543, 560, 561, 562],
        "gnu_ld_refuses_far": all(rows[c]["gnu_ld_near"]["exit"] == 0 and rows[c]["gnu_ld_far"]["exit"] == 1 for c in (309, 517, 518)),
        "gnu_ld_unrecognized": all(
            "unrecognized relocation type" in rows[c]["gnu_ld_near"]["output"]
            for c in (315, 522, 588, 590, 594, 595)
        ),
        "got_base_overflow_refused": all(entry["exit"] != 0 for entry in data["got_base_overflow"]),
    }
    return {"probe": probe_run, "checks": checks, "ok": probe_run["exit"] == 0 and all(checks.values())}


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
        # .data 4 MiB above the code: not in the 1 MiB windows, so this
        # source reads the trace (libc.a included); the prior did not.
        "static-spread": lambda b, i: [b, "--format=text", "--static", "-o", f"t_static_{i}", "answer.trust_ir", "-Wl,--section-start=.data=0x800000"],
    }
    rounds = 31
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
LIB = ("lib-link-driver", ["test", "-p", "trust-cg-codegen", "--lib", "link_driver::tests"])
CLI = ("link_options-got", ["test", "-p", "trust-cg-cli", "--test", "link_options", "linux_got_page"])
ROW_ANCHOR = "        .find(|(code, _)| *code == reloc_type)\n"


def drop_row(code: int) -> tuple[str, str]:
    return ROW_ANCHOR, f"        .find(|(code, _)| *code == reloc_type && *code != {code})\n"


MUTANTS = {
    "drop-tlsgd-adr-page21": ("R_AARCH64_TLSGD_ADR_PAGE21 (513) is not collected", *drop_row(513), [LIB, CLI]),
    "drop-tlsie-ld-gottprel-prel19": ("R_AARCH64_TLSIE_LD_GOTTPREL_PREL19 (543) is not collected", *drop_row(543), [LIB, CLI]),
    "drop-tlsgd-adr-prel21": ("R_AARCH64_TLSGD_ADR_PREL21 (512) is not collected", *drop_row(512), [LIB, CLI]),
    "drop-tlsdesc-ld-prel19": ("R_AARCH64_TLSDESC_LD_PREL19 (560) is not collected", *drop_row(560), [LIB, CLI]),
    "drop-tlsdesc-adr-prel21": ("R_AARCH64_TLSDESC_ADR_PREL21 (561) is not collected", *drop_row(561), [LIB, CLI]),
    "drop-got-ld-prel19": ("R_AARCH64_GOT_LD_PREL19 (309, refused by GNU ld itself) is not collected", *drop_row(309), [LIB]),
    "drop-tlsld-adr-page21": ("R_AARCH64_TLSLD_ADR_PAGE21 (518, refused by GNU ld itself) is not collected", *drop_row(518), [LIB]),
    "drop-gotpcrel32": ("R_AARCH64_GOTPCREL32 (315, unrecognized by GNU ld) is not collected", *drop_row(315), [LIB]),
    "drop-auth-adr-got-page": ("R_AARCH64_AUTH_ADR_GOT_PAGE (590, unrecognized by GNU ld) is not collected", *drop_row(590), [LIB]),
    "no-ifunc-definition": (
        "a defined STT_GNU_IFUNC symbol is not a use",
        "        if symbol.symbol_type != STT_GNU_IFUNC || symbol.section_index == 0 {\n",
        "        if true || symbol.symbol_type != STT_GNU_IFUNC || symbol.section_index == 0 {\n",
        [LIB, CLI],
    ),
    "page-window-for-every-reach": (
        "every reach is checked with the page window",
        "            GotReach::LoadLiteral => window(-(1 << 20), (1 << 20) - 4, false),\n"
        "            GotReach::Adr => window(-(1 << 20), (1 << 20) - 1, false),\n",
        "            GotReach::LoadLiteral => window(-(1 << 32), (1 << 32) - 4096, true),\n"
        "            GotReach::Adr => window(-(1 << 32), (1 << 32) - 4096, true),\n",
        [LIB, CLI],
    ),
    "one-use-per-symbol": (
        "uses are deduplicated by symbol only (a load literal and an ADR against one symbol are one use)",
        "            use_.symbol == symbol && got_access(use_.relocation).map(|access| access.reach) == reach\n",
        "            use_.symbol == symbol && (true || got_access(use_.relocation).map(|access| access.reach) == reach)\n",
        [LIB, CLI],
    ),
    "data-word-sites-in-code": (
        "a GOTPCREL32 data word is taken to sit in code only",
        "        self != GotReach::DataWord\n",
        "        self == self\n",
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
            for leg, args in runs:
                legs.append(run(leg, [*CARGO, *args, *LOCKED], directory=directory))
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
        "run": "L02-P10 third closure audit: every aaelf64 GOT-addressing kind and hidden IPLTs",
        "date": "2026-09-23",
        "source_sha": git("rev-parse", "HEAD"),
        "tree_sha": git("rev-parse", "HEAD^{tree}"),
        "prior": PRIOR,
        "psabi": {
            "source": "https://github.com/ARM-software/abi-aa aaelf64/aaelf64.rst",
            "commit": "a5e86d3fec7342719f3bd1f939ec1b8ac6438c4f",
            "file_sha256": "7432d7d35022d00db30cd8d53ca32a39a958e4acedbb90ffa2c6d572a35ef02f",
        },
        "host": {
            "uname": " ".join(platform.uname()),
            "glibc": subprocess.run(["ldd", "--version"], capture_output=True, text=True).stdout.splitlines()[0],
        },
        "tools": [
            tool("cc", ["cc", "--version"]),
            tool("ld", ["ld", "--version"]),
            tool("as", ["as", "--version"]),
            tool("readelf", ["readelf", "--version"]),
            tool("objdump", ["objdump", "--version"]),
            tool("ld.lld", [str(HOME / ".local/bin/ld.lld"), "--version"]),
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
