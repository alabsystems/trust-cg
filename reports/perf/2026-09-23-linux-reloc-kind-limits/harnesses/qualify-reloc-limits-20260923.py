#!/usr/bin/env python3
"""Qualifying run for the L02-P10 per-kind relocation limits (Linux AArch64, 2026-09-23).

Runs the touched test targets and the repository gates on a clean checkout,
then direct probes through the trust-cg CLI, the host C driver (GNU ld) and
lld, and the assembler-level linker window probe. Every log and probe record
is written under RUN/records. Nothing here edits the checkout; the tree must
be clean before and after.

Usage: qualify-reloc-limits-20260923.py WORKTREE RUN PSABI_RST
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
PSABI = Path(sys.argv[3]).resolve()
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
LLD_ENV = dict(ENV, PATH=os.pathsep.join([str(HOME / ".local/bin"), PATH]))
RESULT = re.compile(r"^test result: .*$", re.M)
PSABI_URL = "https://raw.githubusercontent.com/ARM-software/abi-aa/main/aaelf64/aaelf64.rst"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(WORKTREE), *args], check=True, capture_output=True, text=True
    ).stdout.strip()


def run(name: str, argv: list[str], *, cwd: Path = WORKTREE, timeout: int = 2400) -> dict:
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


def probe(name: str, argv: list[str], cwd: Path, timeout: int = 180, env=None) -> dict:
    """Run one direct probe, keep command, exit, stdout and stderr in records/direct/NAME.txt."""
    try:
        completed = subprocess.run(argv, cwd=cwd, env=env or ENV, capture_output=True, text=True, timeout=timeout)
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


def tool(name: str, argv: list[str], env=None) -> dict:
    env = env or ENV
    path = shutil.which(argv[0], path=env["PATH"])
    resolved = Path(path).resolve() if path else None
    version = subprocess.run(argv, capture_output=True, text=True, env=env)
    text = version.stdout or version.stderr
    return {
        "name": name,
        "path": path,
        "resolved": str(resolved) if resolved else None,
        "sha256": sha256(resolved) if resolved else None,
        "version": text.splitlines()[0] if text else "",
    }


def psabi_excerpt(out: Path) -> dict:
    """Keep the aaelf64 rows this change relies on, with the source digest."""
    text = PSABI.read_text()
    lines = text.splitlines()
    names = [
        "R\\_AARCH64\\_ABS64 ", "R\\_AARCH64\\_ABS32 ", "R\\_AARCH64\\_PREL32 ",
        "R\\_AARCH64\\_ADR\\_PREL\\_PG\\_HI21 ", "R\\_AARCH64\\_ADD\\_ABS\\_LO12\\_NC ",
        "R\\_AARCH64\\_LDST8\\_ABS\\_LO12\\_NC ", "R\\_AARCH64\\_LDST16\\_ABS\\_LO12\\_NC ",
        "R\\_AARCH64\\_LDST32\\_ABS\\_LO12\\_NC ", "R\\_AARCH64\\_LDST64\\_ABS\\_LO12\\_NC ",
        "R\\_AARCH64\\_LDST128\\_ABS\\_LO12\\_NC ", "R\\_AARCH64\\_JUMP26 ", "R\\_AARCH64\\_CALL26 ",
        "R\\_AARCH64\\_ADR\\_GOT\\_PAGE ", "R\\_AARCH64\\_LD64\\_GOT\\_LO12\\_NC ",
        "R\\_AARCH64\\_TLSIE\\_ADR\\_GOTTPREL\\_PAGE21 ", "R\\_AARCH64\\_TLSIE\\_LD64\\_GOTTPREL\\_LO12\\_NC ",
        "R\\_AARCH64\\_TLSLE\\_ADD\\_TPREL\\_HI12 ", "R\\_AARCH64\\_TLSLE\\_ADD\\_TPREL\\_LO12 ",
        "R\\_AARCH64\\_TLSLE\\_ADD\\_TPREL\\_LO12\\_NC ", "R\\_AARCH64\\_TLSDESC\\_ADR\\_PAGE21 ",
        "R\\_AARCH64\\_TLSDESC\\_LD64\\_LO12 ", "R\\_AARCH64\\_TLSDESC\\_ADD\\_LO12 ",
        "R\\_AARCH64\\_TLSDESC\\_CALL ",
    ]
    kept = []
    for index, line in enumerate(lines):
        if any(name in line for name in names) and line.lstrip().startswith("|"):
            # The row and its continuation lines up to the next rule.
            row = [line]
            for follow in lines[index + 1:index + 4]:
                if follow.lstrip().startswith("+"):
                    break
                row.append(follow)
            kept.append((index + 1, row))
    history = [l for l in lines if "2026Q2" in l or "pc-relative relocaions signed" in l
               or "|release| replace" in l or "|date-of-issue| replace" in l]
    body = [
        f"Source: {PSABI_URL}",
        f"SHA-256 of the fetched file: {sha256(PSABI)} ({PSABI.stat().st_size} bytes, fetched 2026-09-23)",
        "License of the source: CC-BY-SA-4.0, Copyright Arm Limited and its affiliates.",
        "",
        "Release lines and the 2026Q2 change-history entry:",
        *history,
        "",
        "Relocation rows (line number in the source, then the row):",
    ]
    for number, row in kept:
        body.append(f"L{number}:")
        body.extend(row)
    out.write_text("\n".join(body) + "\n")
    return {"source": PSABI_URL, "sha256": sha256(PSABI), "rows": len(kept)}


LE_MAIN = "extern long tcg_le_edge_bump(void);\nint main(void) { return tcg_le_edge_bump() == 42 && tcg_le_edge_bump() == 84 ? 0 : 1; }\n"
TLS_PAD = "    .section .tbss,\"awT\",@nobits\n    .globl tcg_c_tls_pad\n    .p2align 4\ntcg_c_tls_pad:\n    .zero 16777216\n"
DEBUG_MAIN = "extern long tcg_debug_probe(void);\nint main(void) { return tcg_debug_probe() == 42 ? 0 : 1; }\n"
DESC_MAIN = "extern int tcg_desc_bump(void);\nint main(void) { return tcg_desc_bump() == 42 && tcg_desc_bump() == 44 ? 0 : 1; }\n"
Q_MAIN = """#include <stdint.h>
extern uint32_t tcg_lo12_q[4];
extern uint32_t tcg_lo12_q_out[4];
void tcg_lo12_q_double(void);
int main(void) {
    tcg_lo12_q_double();
    for (int lane = 0; lane < 4; lane++)
        if (tcg_lo12_q_out[lane] != 2u * (uint32_t)(lane + 1)) return 31 + lane;
    tcg_lo12_q[0] = 0x40000000u;
    tcg_lo12_q[3] = 7;
    tcg_lo12_q_double();
    if (tcg_lo12_q_out[0] != 0x80000000u || tcg_lo12_q_out[1] != 4 ||
        tcg_lo12_q_out[2] != 6 || tcg_lo12_q_out[3] != 14) return 35;
    return 0;
}
"""
FAR_GOT = "--section-start=.got=0x200000000,--section-start=.got.plt=0x200010000"
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
        tool("as", ["as", "--version"]),
        tool("ld", ["ld", "--version"]),
        tool("ld.gold", ["ld.gold", "--version"]),
        tool("ld.lld", ["ld.lld", "--version"], env=LLD_ENV),
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
        run("codegen_lib_reloc_limits", codegen + ["--lib", *common, "--", "elf::reloc", "elf::dwarf",
                                                   "link_driver", "pipeline::tests::local_exec",
                                                   "pipeline::tests::intra_object"]),
        run("e2e_aarch64_link_runtime", codegen + ["--test", "e2e_aarch64_link_runtime", *common, "--", "--nocapture"]),
        run("aarch64_elf_dwarf", codegen + ["--test", "aarch64_elf_dwarf", *common]),
        run("e2e_aarch64_elf_tlsie", codegen + ["--test", "e2e_aarch64_elf_tlsie", *common]),
        run("e2e_aarch64_elf_relocation_model", codegen + ["--test", "e2e_aarch64_elf_relocation_model", *common]),
        run("cli_link_options", cargo + ["test", "-p", "trust-cg-cli", "--test", "link_options", *common]),
        run("cli_bin_unit", cargo + ["test", "-p", "trust-cg-cli", "--bin", "trust-cg", *common]),
        run("verify_reloc_units", cargo + ["test", "-p", "trust-cg-verify", "--lib", *common, "--",
                                           "aarch64_elf_reloc_proofs", "aarch64_elf_tls_reloc_proofs",
                                           "object_inventory"]),
        run("check_codegen", cargo + ["check", "-p", "trust-cg-codegen", *common]),
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
        run("native_test_host_matrix", ["python3", "scripts/native_test_host_matrix.py", "--check"]),
        run("check_documentation", ["python3", "scripts/check_documentation.py", "--check"]),
        run("diagnostics_inventory", ["python3", "scripts/generate_diagnostics_inventory.py", "--check"]),
        run("evidence_plan", ["python3", "scripts/check_evidence_archive.py", "--plan"]),
    ]

    # --- Direct probes through the CLI, GNU ld and lld -------------------------
    trust_cg = WORKTREE / "target/debug/trust-cg"
    tc = str(trust_cg)
    cg = DIRECT / "cg"
    cg.mkdir(exist_ok=True)
    for source in sorted(INPUTS.glob("*.tmbc")):
        shutil.copy(source, cg / source.name)
    for name, text in [("le_main.c", LE_MAIN), ("tls_pad.s", TLS_PAD), ("debug_main.c", DEBUG_MAIN),
                       ("desc_main.c", DESC_MAIN), ("lo12_q_main.c", Q_MAIN)]:
        (cg / name).write_text(text)
    rpath = f"-Wl,-rpath,{cg}"
    probes = [
        probe("cc-compile-mains", ["cc", "-c", "le_main.c", "debug_main.c", "desc_main.c", "lo12_q_main.c"], cg),
        probe("as-tls_pad", ["as", "tls_pad.s", "-o", "tls_pad.o"], cg),
        # GOT-page kinds: TLSDESC and ADR_GOT_PAGE from a pic object.
        probe("cli-compile-got_page", [tc, "-c", "--relocation-model", "pic", "-o", "got_page.o", "got_page.tmbc"], cg),
        probe("readelf-rW-got_page.o", ["readelf", "-rW", "got_page.o"], cg),
        probe("objdump-dr-got_page.o", ["objdump", "-dr", "got_page.o"], cg),
        probe("gnu-far-got-shared", ["cc", "-shared", "-nostdlib", f"-Wl,{FAR_GOT}", "got_page.o", "-o", "libfar_bfd.so"], cg),
        probe("gnu-far-got-readelf-SW", ["readelf", "-SW", "libfar_bfd.so"], cg),
        probe("gnu-far-got-readelf-rW", ["readelf", "-rW", "libfar_bfd.so"], cg),
        probe("gnu-far-got-objdump-d", ["objdump", "-d", "libfar_bfd.so"], cg),
        probe("lld-far-got-shared", ["cc", "-fuse-ld=lld", "-shared", "-nostdlib", "-Wl,-z,norelro",
                                     f"-Wl,--section-start=.text=0x100000,{FAR_GOT}", "got_page.o",
                                     "-o", "libfar_lld.so"], cg, env=LLD_ENV),
        probe("cli-far-got-shared", [tc, "-shared", "-nostdlib", "--relocation-model", "pic", f"-Wl,{FAR_GOT}",
                                     "-o", "libfar.so", "got_page.tmbc"], cg),
        probe("cli-far-got-output-absent", ["ls", "-1", "."], cg),
        probe("cli-near-got-shared", [tc, "-shared", "-nostdlib", "--relocation-model", "pic", f"-Wl,{NEAR_GOT}",
                                      "-o", "libnear.so", "got_page.tmbc"], cg),
        probe("cli-near-got-readelf-SW", ["readelf", "-SW", "libnear.so"], cg),
        probe("cc-desc-against-near", ["cc", "desc_main.o", "-L.", "-lnear", rpath, "-o", "desc"], cg),
        probe("run-desc", ["./desc"], cg),
        # TLSLE_ADD_TPREL_HI12.
        probe("cli-compile-le_over", [tc, "-c", "-o", "le_over.o", "le_over.tmbc"], cg),
        probe("cli-compile-le_edge", [tc, "-c", "-o", "le_edge.o", "le_edge.tmbc"], cg),
        probe("readelf-sSW-le_edge.o", ["readelf", "-sSW", "le_edge.o"], cg),
        probe("objdump-dr-le_edge.o", ["objdump", "-dr", "le_edge.o"], cg),
        probe("cc-edge", ["cc", "le_main.o", "le_edge.o", "-o", "edge"], cg),
        probe("readelf-lW-edge", ["readelf", "-lW", "edge"], cg),
        probe("objdump-d-edge", ["objdump", "-d", "--disassemble=tcg_le_edge_bump", "edge"], cg),
        probe("run-edge", ["./edge"], cg),
        probe("cli-compile-le_small", [tc, "-c", "-o", "le_small.o", "le_small.tmbc"], cg),
        probe("gnu-le-behind-pad", ["cc", "le_main.o", "tls_pad.o", "le_small.o", "-o", "behind"], cg),
        probe("lld-le-behind-pad", ["cc", "-fuse-ld=lld", "le_main.o", "tls_pad.o", "le_small.o", "-o", "behind_lld"], cg, env=LLD_ENV),
        probe("gnu-le-ahead-of-pad", ["cc", "le_main.o", "le_small.o", "tls_pad.o", "-o", "ahead"], cg),
        probe("run-ahead", ["./ahead"], cg),
        # ABS32 (DWARF32 section offsets).
        probe("cli-compile-debug_probe", [tc, "-c", "-g", "-o", "debug_probe.o", "debug_probe.tmbc"], cg),
        probe("readelf-rW-debug_probe.o", ["readelf", "-rW", "debug_probe.o"], cg),
        probe("gnu-debug-str-far", ["cc", "debug_main.o", "debug_probe.o",
                                    "-Wl,--section-start=.debug_str=0x100000000", "-o", "debug_far"], cg),
        probe("gnu-debug-str-near", ["cc", "debug_main.o", "debug_probe.o",
                                     "-Wl,--section-start=.debug_str=0x7fff0000", "-o", "debug_near"], cg),
        probe("run-debug_near", ["./debug_near"], cg),
        probe("lld-debug-str-far", ["cc", "-fuse-ld=lld", "debug_main.o", "debug_probe.o",
                                    "-Wl,--section-start=.debug_str=0x100000000", "-o", "debug_far_lld"], cg, env=LLD_ENV),
        probe("lld-debug-str-far-readelf-SW", ["readelf", "-SW", "debug_far_lld"], cg),
        # LDST128 fused Q-register accesses.
        probe("cli-compile-lo12_q", [tc, "-c", "-O2", "-o", "lo12_q.o", "lo12_q.tmbc"], cg),
        probe("objdump-dr-lo12_q.o", ["objdump", "-dr", "lo12_q.o"], cg),
        probe("cc-lo12_q", ["cc", "lo12_q_main.o", "lo12_q.o", "-o", "lo12_q"], cg),
        probe("objdump-d-lo12_q", ["objdump", "-d", "--disassemble=tcg_lo12_q_double", "lo12_q"], cg),
        probe("run-lo12_q", ["./lo12_q"], cg),
    ]

    # --- Assembler-level linker window probe -----------------------------------
    windows = RECORDS / "linker-windows"
    probes.append(probe("linker-window-probe", ["python3", str(RUN / "harnesses/probe-linker-windows-20260923.py"),
                                                str(windows)], RUN, timeout=900))
    psabi = psabi_excerpt(RECORDS / "psabi-aaelf64-excerpt.txt")

    status_after = git("status", "--porcelain", "--untracked-files=all")
    results = {
        "schema": "trust-cg.l02-p10-reloc-kind-limits.v1",
        "source": {"head": head, "tree": git("rev-parse", "HEAD^{tree}"),
                   "status_before": status_before, "status_after": status_after},
        "host": host,
        "tools": tools,
        "trust_cg_binary_sha256": sha256(trust_cg),
        "inputs": {p.name: sha256(p) for p in sorted(INPUTS.glob("*.tmbc"))},
        "psabi": psabi,
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
