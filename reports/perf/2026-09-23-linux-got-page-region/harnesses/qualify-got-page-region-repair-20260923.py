#!/usr/bin/env python3
"""Qualifying run for the L02-P10 second repair: GOT slots in non-allocated sections (Linux AArch64, 2026-09-23).

Runs the touched test targets and the repository gates on a clean checkout,
then direct probes through the trust-cg CLI and, for comparison, through
GNU ld without the driver's check. The verifier's reproducer is a static
`-nostdlib` executable whose `_start` (`-fPIC`) exits 0 when the undefined
weak `tcg_weak_missing` is null, linked with the `pic` probe and a script
that lays an `INFO` (or `COPY`) section holding `.got` over `NOLOAD` zero
fill at 8 GiB or 1 GiB, with and without `-z nosectionheader`. The first
repair's INSERT rename is repeated as a regression probe.

Every log and probe record is written under RUN/records. Nothing here
edits the checkout; the tree must be clean before and after.

Usage: qualify-got-page-region-repair-20260923.py WORKTREE RUN
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


WEAK_START = r"""
extern int tcg_weak_missing __attribute__((weak));
__attribute__((noinline)) int probe(void) { return &tcg_weak_missing == 0 ? 0 : 1; }
void _start(void) {
  register long x0 __asm__("x0") = probe();
  register long x8 __asm__("x8") = 93;
  __asm__ volatile("svc 0" :: "r"(x0), "r"(x8));
  __builtin_unreachable();
}
"""
SLOTS_FAR = "SECTIONS { .slots 0x200000000 : { *(.got) *(.igot) } } INSERT BEFORE .got;\n"


def non_allocated_script(kind: str, address: int) -> str:
    return (f"SECTIONS {{\n  .farbss {address:#x} (NOLOAD) : {{ . = . + 0x1000; }}\n"
            f"  .slots {address:#x} ({kind}) : {{ *(.got) *(.igot) }}\n}} INSERT AFTER .bss;\n")


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
                                          "reports/perf/2026-09-23-linux-reloc-kind-limits-staged",
                                          "reports/perf/2026-09-23-linux-got-page-region"]),
        run("native_test_host_matrix", ["python3", "scripts/native_test_host_matrix.py", "--check"]),
    ]

    # --- Direct probes ----------------------------------------------------------
    tc = str(WORKTREE / "target/debug/trust-cg")
    cg = DIRECT / "cg"
    cg.mkdir(exist_ok=True)
    shutil.copy(INPUTS / "got_page.tmbc", cg / "got_page.tmbc")
    (cg / "weakst.c").write_text(WEAK_START)
    (cg / "slots-far.ld").write_text(SLOTS_FAR)
    for kind in ("INFO", "COPY"):
        for address in (0x200000000, 0x40000000):
            (cg / f"{kind.lower()}-{address:#x}.ld").write_text(non_allocated_script(kind, address))
    for name in ("cli-weakst-0x200000000", "cli-copy-0x200000000", "libslots.so"):
        (cg / name).write_bytes(b"precious\n")
    static = ["--static", "--nostdlib", "--relocation-model", "pic"]
    raw_static = ["cc", "-static", "-nostdlib"]

    def cli(kind: str, address: int, name: str, extra: str = "") -> list[str]:
        return [tc, *static, f"-Wl,{extra}-T,{cg}/{kind}-{address:#x}.ld,{cg}/weakst.o", "-o", name,
                "got_page.tmbc"]

    def raw(kind: str, address: int, name: str, extra: str = "") -> list[str]:
        return [*raw_static, f"-Wl,{extra}-T,{kind}-{address:#x}.ld", "weakst.o", "got_page.o", "-o", name]

    probes = [
        probe("cc-compile-weakst", ["cc", "-c", "-fPIC", "-O1", "-fno-stack-protector", "weakst.c"], cg),
        probe("cli-compile-got_page", [tc, "-c", "--relocation-model", "pic", "-o", "got_page.o", "got_page.tmbc"], cg),
        probe("readelf-rW-weakst.o", ["readelf", "-rW", "weakst.o"], cg),
        probe("ls-before", ["ls", "-1A", "."], cg),
        # The verifier's command (INFO at 8 GiB), then COPY: refused, the
        # output keeps its bytes.
        probe("cli-info-far", cli("info", 0x200000000, "cli-weakst-0x200000000"), cg),
        probe("cat-cli-weakst-after-refusal", ["cat", "cli-weakst-0x200000000"], cg),
        probe("cli-copy-far", cli("copy", 0x200000000, "cli-copy-0x200000000"), cg),
        probe("cat-cli-copy-after-refusal", ["cat", "cli-copy-0x200000000"], cg),
        # GNU ld without the driver: it links, the page delta is truncated,
        # and the executable dies.
        probe("raw-gnu-ld-info-far", raw("info", 0x200000000, "raw-info-far"), cg),
        probe("readelf-SW-raw-info-far", ["readelf", "-SW", "raw-info-far"], cg),
        probe("readelf-lW-raw-info-far", ["readelf", "-lW", "raw-info-far"], cg),
        probe("readelf-rW-raw-info-far", ["readelf", "-rW", "raw-info-far"], cg),
        probe("objdump-d-raw-info-far", ["objdump", "-d", "--no-show-raw-insn", "raw-info-far"], cg),
        probe("run-raw-info-far", ["./raw-info-far"], cg),
        probe("raw-gnu-ld-copy-far", raw("copy", 0x200000000, "raw-copy-far"), cg),
        probe("readelf-SW-raw-copy-far", ["readelf", "-SW", "raw-copy-far"], cg),
        probe("run-raw-copy-far", ["./raw-copy-far"], cg),
        # The 1 GiB twins: installed and run.
        probe("cli-info-near", cli("info", 0x40000000, "cli-weakst-0x40000000"), cg),
        probe("readelf-SW-cli-info-near", ["readelf", "-SW", "cli-weakst-0x40000000"], cg),
        probe("run-cli-info-near", ["./cli-weakst-0x40000000"], cg),
        probe("cli-copy-near", cli("copy", 0x40000000, "cli-copy-0x40000000"), cg),
        probe("run-cli-copy-near", ["./cli-copy-0x40000000"], cg),
        # Without a section header table: refused at both placements; GNU
        # ld's images die at 8 GiB and run at 1 GiB.
        probe("cli-info-far-nosh", cli("info", 0x200000000, "cli-info-far-nosh", "-z,nosectionheader,"), cg),
        probe("cli-info-near-nosh", cli("info", 0x40000000, "cli-info-near-nosh", "-z,nosectionheader,"), cg),
        probe("raw-gnu-ld-info-far-nosh", raw("info", 0x200000000, "raw-info-far-nosh", "-z,nosectionheader,"), cg),
        probe("readelf-lW-raw-info-far-nosh", ["readelf", "-hlW", "raw-info-far-nosh"], cg),
        probe("run-raw-info-far-nosh", ["./raw-info-far-nosh"], cg),
        probe("raw-gnu-ld-info-near-nosh", raw("info", 0x40000000, "raw-info-near-nosh", "-z,nosectionheader,"), cg),
        probe("run-raw-info-near-nosh", ["./raw-info-near-nosh"], cg),
        # Regression: the first repair's INSERT rename is still refused.
        probe("cli-insert-rename", [tc, "-shared", "-nostdlib", "--relocation-model", "pic",
                                    "-Wl,-T,slots-far.ld,--section-start=.got.plt=0x80000000", "-o", "libslots.so",
                                    "got_page.tmbc"], cg),
        probe("cat-libslots-after-refusal", ["cat", "libslots.so"], cg),
        probe("ls-after", ["ls", "-1A", "."], cg),
    ]

    status_after = git("status", "--porcelain", "--untracked-files=all")
    results = {
        "schema": "trust-cg.l02-p10-got-page-region-repair.v1",
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
