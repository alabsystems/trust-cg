#!/usr/bin/env python3
"""Qualifying run for the L02-P10 GOT-page slot-region repair (Linux AArch64, 2026-09-23).

Runs the touched test targets and the repository gates on a clean checkout,
then direct probes through the trust-cg CLI and, for comparison, through
GNU ld without the driver's check:

- the verifier's INSERT script that moves the GOT's slots into `.slots` at
  8 GiB while `.got.plt` stays at 2 GiB (with and without a section header
  table), its 1 GiB twin, and the raw GNU ld library and its executable;
- the GOT placed at 8 GiB, 64 KiB past the window's upper edge, and 2 GiB;
- an executable section 8 GiB away with no GOT reference (conservative);
- a position-dependent executable whose linker-filled GOT slot the same
  INSERT script moves to 8 GiB (no dynamic relocation names it), its twin
  without the script, and the raw GNU ld executable.

Every log and probe record is written under RUN/records. Nothing here
edits the checkout; the tree must be clean before and after.

Usage: qualify-got-page-region-20260923.py WORKTREE RUN
"""

from __future__ import annotations

import hashlib
import json
import os
import platform
import re
import shutil
import subprocess
import sys
from pathlib import Path

WORKTREE = Path(sys.argv[1]).resolve()
RUN = Path(sys.argv[2]).resolve()
RECORDS = RUN / "records"
LOGS = RECORDS / "logs"
DIRECT = RECORDS / "direct"
INPUTS = RUN / "inputs"
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


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(WORKTREE), *args], check=True, capture_output=True, text=True
    ).stdout.strip()


def run(name: str, argv: list[str], *, cwd: Path = WORKTREE, timeout: int = 1150) -> dict:
    """Run one gate command, keep its complete output as records/logs/NAME.log."""
    completed = subprocess.run(argv, cwd=cwd, env=ENV, capture_output=True, text=True, timeout=timeout)
    text = (
        f"$ {' '.join(argv)}\n(cwd {cwd})\n--- stdout ---\n{completed.stdout}"
        f"--- stderr ---\n{completed.stderr}--- exit {completed.returncode} ---\n"
    )
    (LOGS / f"{name}.log").write_text(text)
    record = {
        "name": name,
        "argv": argv,
        "exit": completed.returncode,
        "test_results": RESULT.findall(completed.stdout + completed.stderr),
    }
    print(f"{name}: exit {completed.returncode} {record['test_results']}", flush=True)
    return record


def probe(name: str, argv: list[str], cwd: Path, timeout: int = 180) -> dict:
    """Run one direct probe, keep command, exit, stdout and stderr in records/direct/NAME.txt.

    A negative exit is the signal that killed the process (-11 is SIGSEGV).
    """
    try:
        completed = subprocess.run(argv, cwd=cwd, env=ENV, capture_output=True, text=True, timeout=timeout)
        exit_code, stdout, stderr = completed.returncode, completed.stdout, completed.stderr
    except subprocess.TimeoutExpired:
        exit_code, stdout, stderr = "timeout", "", ""
    hide = lambda text: text.replace(str(DIRECT), "$DIRECT").replace(str(WORKTREE), "$WORKTREE")
    shown = [hide(a) for a in argv]
    (DIRECT / f"{name}.txt").write_text(
        f"$ {' '.join(shown)}\n--- stdout ---\n{hide(stdout)}--- stderr ---\n{hide(stderr)}--- exit {exit_code} ---\n"
    )
    print(f"probe {name}: exit {exit_code}", flush=True)
    return {"name": name, "argv": shown, "exit": exit_code}


def tool(name: str, argv: list[str]) -> dict:
    path = shutil.which(argv[0], path=ENV["PATH"])
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


DESC_MAIN = "extern int tcg_desc_bump(void);\nint main(void) { return tcg_desc_bump() == 42 && tcg_desc_bump() == 44 ? 0 : 1; }\n"
START = (
    "extern int tcg_desc_bump(void);\nextern void _exit(int) __attribute__((noreturn));\n"
    "void _start(void) { _exit(tcg_desc_bump() == 42 && tcg_desc_bump() == 44 ? 0 : 1); }\n"
)
FAR_CODE = (
    '    .section .farcode,"ax",%progbits\n    .globl tcg_far_helper\n'
    "    .type tcg_far_helper,%function\ntcg_far_helper:\n    mov w0, #7\n    ret\n"
)
SLOTS_FAR = "SECTIONS { .slots 0x200000000 : { *(.got) *(.igot) } } INSERT BEFORE .got;\n"
SLOTS_NEAR = "SECTIONS { .slots 0x40000000 : { *(.got) *(.igot) } } INSERT BEFORE .got;\n"
GOT_PLT_NEAR = "--section-start=.got.plt=0x80000000"
FAR_GOT = "--section-start=.got=0x200000000,--section-start=.got.plt=0x200010000"
EDGE_GOT = "--section-start=.got=0x100010000,--section-start=.got.plt=0x100020000"
NEAR_GOT = "--section-start=.got=0x80000000,--section-start=.got.plt=0x80010000"


def main() -> int:
    for directory in (LOGS, DIRECT):
        directory.mkdir(parents=True, exist_ok=True)
    head = git("rev-parse", "HEAD")
    status_before = git("status", "--porcelain", "--untracked-files=all")
    if status_before:
        print("checkout is dirty; refusing to qualify", file=sys.stderr)
        return 1

    host = {
        "uname": " ".join(platform.uname()),
        "glibc": subprocess.run(["ldd", "--version"], capture_output=True, text=True).stdout.splitlines()[0],
        "cpu": next(
            (line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines()
             if line.startswith("CPU part")),
            "",
        ),
    }
    tools = [
        tool("cc", ["cc", "--version"]),
        tool("ld", ["ld", "--version"]),
        tool("ld.gold", ["ld.gold", "--version"]),
        tool("ld.lld", [str(HOME / ".local/bin/ld.lld"), "--version"]),
        tool("readelf", ["readelf", "--version"]),
        tool("objdump", ["objdump", "--version"]),
        tool("rustc", ["rustc", "--version"]),
        tool("cargo", ["cargo", "--version"]),
        tool("rustfmt", ["rustfmt", "--version"]),
    ]

    cargo = ["cargo"]
    common = ["--locked", "--offline", "-j", "8"]
    codegen = cargo + ["test", "-p", "trust-cg-codegen"]
    gates = [
        run("codegen_lib", codegen + ["--lib", *common]),
        run("codegen_lib_link_driver", codegen + ["--lib", *common, "--", "link_driver"]),
        run("e2e_aarch64_link_runtime", codegen + ["--test", "e2e_aarch64_link_runtime", *common, "--", "--nocapture"]),
        run("e2e_aarch64_elf_tlsie", codegen + ["--test", "e2e_aarch64_elf_tlsie", *common]),
        run("e2e_aarch64_elf_relocation_model", codegen + ["--test", "e2e_aarch64_elf_relocation_model", *common]),
        run("e2e_aarch64_globals_linux", codegen + ["--test", "e2e_aarch64_globals_linux", *common]),
        run("aarch64_elf_symbol_binding", codegen + ["--test", "aarch64_elf_symbol_binding", *common]),
        run("cli_tests", cargo + ["test", "-p", "trust-cg-cli", "--test", "link_options", "--test", "output_paths",
                                  "--bin", "trust-cg", *common]),
        run("check_codegen_verify", cargo + ["check", "-p", "trust-cg-codegen", "--features", "verify", *common]),
        run("build_cli", cargo + ["build", "-p", "trust-cg-cli", *common]),
        run("check_fmt", ["bash", "scripts/check_fmt.sh"]),
        run(
            "gate_script_tests",
            [
                "python3", "-B", "-m", "unittest",
                "scripts/tests/test_linux_aarch64_gate.py",
                "scripts/tests/test_darwin_aarch64_gate.py",
                "scripts/tests/test_linux_aarch64_bridge_gate.py",
            ],
        ),
        run("check_documentation_write", ["python3", "scripts/check_documentation.py", "--write"]),
        run("check_documentation", ["python3", "scripts/check_documentation.py", "--check"]),
        run("diagnostics_inventory", ["python3", "scripts/generate_diagnostics_inventory.py", "--check"]),
        run("evidence_plan", ["python3", "scripts/check_evidence_archive.py", "--plan"]),
        run("evidence_earlier_archives", ["python3", "scripts/check_evidence_archive.py",
                                          "reports/perf/2026-09-23-linux-reloc-kind-limits",
                                          "reports/perf/2026-09-23-linux-reloc-kind-limits-staged"]),
        run("native_test_host_matrix", ["python3", "scripts/native_test_host_matrix.py", "--check"]),
    ]

    # --- Direct probes ----------------------------------------------------------
    tc = str(WORKTREE / "target/debug/trust-cg")
    cg = DIRECT / "cg"
    cg.mkdir(exist_ok=True)
    shutil.copy(INPUTS / "got_page.tmbc", cg / "got_page.tmbc")
    (cg / "desc_main.c").write_text(DESC_MAIN)
    (cg / "start.c").write_text(START)
    (cg / "far.s").write_text(FAR_CODE)
    (cg / "slots-far.ld").write_text(SLOTS_FAR)
    (cg / "slots-near.ld").write_text(SLOTS_NEAR)
    for name in ("libslots.so", "libfar.so"):
        (cg / name).write_bytes(b"precious\n")
    pic = ["-shared", "-nostdlib", "--relocation-model", "pic"]
    exe = ["-no-pie", "-nostdlib", "--relocation-model", "pic"]
    rpath = f"-Wl,-rpath,{cg}"
    probes = [
        probe("cc-compile-desc_main", ["cc", "-c", "desc_main.c"], cg),
        probe("cc-compile-start", ["cc", "-c", "-fno-stack-protector", "start.c"], cg),
        probe("cc-assemble-far", ["cc", "-c", "far.s"], cg),
        probe("cli-compile-got_page", [tc, "-c", "--relocation-model", "pic", "-o", "got_page.o", "got_page.tmbc"], cg),
        probe("readelf-rW-got_page.o", ["readelf", "-rW", "got_page.o"], cg),
        probe("ls-before", ["ls", "-1A", "."], cg),
        # The verifier's INSERT rename: refused, libslots.so keeps its bytes.
        probe("cli-insert-rename", [tc, *pic, f"-Wl,-T,slots-far.ld,{GOT_PLT_NEAR}", "-o", "libslots.so",
                                    "got_page.tmbc"], cg),
        probe("cat-libslots-after-refusal", ["cat", "libslots.so"], cg),
        probe("cli-insert-rename-nosectionheader",
              [tc, *pic, f"-Wl,-z,nosectionheader,-T,slots-far.ld,{GOT_PLT_NEAR}", "-o", "libslots-nosh.so",
               "got_page.tmbc"], cg),
        # The same link through GNU ld without the driver: it links, and the
        # executable using the library does not pass.
        probe("raw-gnu-ld-insert-rename", ["cc", "-shared", "-nostdlib", f"-Wl,-T,slots-far.ld,{GOT_PLT_NEAR}",
                                           "-o", "libslotsraw.so", "got_page.o"], cg),
        probe("readelf-SW-libslotsraw.so", ["readelf", "-SW", "libslotsraw.so"], cg),
        probe("readelf-rW-libslotsraw.so", ["readelf", "-rW", "libslotsraw.so"], cg),
        probe("objdump-d-libslotsraw.so", ["objdump", "-d", "--no-show-raw-insn", "libslotsraw.so"], cg),
        probe("cc-desc-against-slotsraw", ["cc", "desc_main.o", "-L.", "-lslotsraw", rpath, "-o", "desc-slotsraw"], cg),
        probe("run-desc-slotsraw", ["./desc-slotsraw"], cg),
        # The same script with the slots at 1 GiB: installed and run.
        probe("cli-insert-near", [tc, *pic, f"-Wl,-T,slots-near.ld,{GOT_PLT_NEAR}", "-o", "libslotsnear.so",
                                  "got_page.tmbc"], cg),
        probe("readelf-SW-libslotsnear.so", ["readelf", "-SW", "libslotsnear.so"], cg),
        probe("cc-desc-against-slotsnear", ["cc", "desc_main.o", "-L.", "-lslotsnear", rpath, "-o", "desc-slotsnear"], cg),
        probe("run-desc-slotsnear", ["./desc-slotsnear"], cg),
        # GOT placements: 8 GiB and 64 KiB past the upper edge refused, 2 GiB run.
        probe("cli-far-got-shared", [tc, *pic, f"-Wl,{FAR_GOT}", "-o", "libfar.so", "got_page.tmbc"], cg),
        probe("cat-libfar-after-refusal", ["cat", "libfar.so"], cg),
        probe("cli-edge-got-shared", [tc, *pic, f"-Wl,{EDGE_GOT}", "-o", "libedge.so", "got_page.tmbc"], cg),
        probe("cli-near-got-shared", [tc, *pic, f"-Wl,{NEAR_GOT}", "-o", "libnear.so", "got_page.tmbc"], cg),
        probe("readelf-SW-libnear.so", ["readelf", "-SW", "libnear.so"], cg),
        probe("cc-desc-against-near", ["cc", "desc_main.o", "-L.", "-lnear", rpath, "-o", "desc-near"], cg),
        probe("run-desc-near", ["./desc-near"], cg),
        # An executable section 8 GiB away with no GOT reference: refused as
        # unproven; GNU ld's library runs.
        probe("cli-far-code", [tc, *pic, f"-Wl,{cg}/far.o,--section-start=.farcode=0x200000000", "-o",
                               "libfarcode.so", "got_page.tmbc"], cg),
        probe("raw-gnu-ld-far-code", ["cc", "-shared", "-nostdlib", "-Wl,--section-start=.farcode=0x200000000",
                                      "-o", "libfarcoderaw.so", "got_page.o", "far.o"], cg),
        probe("readelf-SW-libfarcoderaw.so", ["readelf", "-SW", "libfarcoderaw.so"], cg),
        probe("cc-desc-against-farcoderaw", ["cc", "desc_main.o", "-L.", "-lfarcoderaw", rpath, "-o",
                                             "desc-farcoderaw"], cg),
        probe("run-desc-farcoderaw", ["./desc-farcoderaw"], cg),
        # A position-dependent executable's linker-filled slot moved to 8 GiB:
        # no dynamic relocation names it. Refused; GNU ld's executable fails.
        probe("cli-static-slot-far", [tc, *exe, f"-Wl,{cg}/start.o,-lc,-T,slots-far.ld,{GOT_PLT_NEAR}", "-o",
                                      "static-far", "got_page.tmbc"], cg),
        probe("raw-gnu-ld-static-slot-far", ["cc", "-nostdlib", "-no-pie", "start.o", "got_page.o", "-lc",
                                             f"-Wl,-T,slots-far.ld,{GOT_PLT_NEAR}", "-o", "static-far-raw"], cg),
        probe("readelf-SW-static-far-raw", ["readelf", "-SW", "static-far-raw"], cg),
        probe("readelf-rW-static-far-raw", ["readelf", "-rW", "static-far-raw"], cg),
        probe("readelf-dW-static-far-raw", ["readelf", "-dW", "static-far-raw"], cg),
        probe("run-static-far-raw", ["./static-far-raw"], cg),
        probe("cli-static-slot-near", [tc, *exe, f"-Wl,{cg}/start.o,-lc", "-o", "static-near", "got_page.tmbc"], cg),
        probe("run-static-near", ["./static-near"], cg),
        probe("ls-after", ["ls", "-1A", "."], cg),
    ]

    status_after = git("status", "--porcelain", "--untracked-files=all")
    results = {
        "schema": "trust-cg.l02-p10-got-page-region.v1",
        "source": {"head": head, "tree": git("rev-parse", "HEAD^{tree}"),
                   "status_before": status_before, "status_after": status_after},
        "host": host,
        "tools": tools,
        "trust_cg_binary_sha256": sha256(Path(tc)),
        "inputs": {p.name: sha256(p) for p in sorted(INPUTS.glob("*.tmbc"))},
        "gates": gates,
        "probes": probes,
    }
    (RECORDS / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    failed = [g["name"] for g in gates if g["exit"] != 0]
    print("failed gates:", failed)
    print("status after clean:", not status_after)
    return 1 if failed or status_after else 0


if __name__ == "__main__":
    sys.exit(main())
