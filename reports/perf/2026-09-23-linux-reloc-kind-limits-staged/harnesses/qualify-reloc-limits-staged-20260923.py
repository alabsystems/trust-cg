#!/usr/bin/env python3
"""Qualifying run for L02-P10 after the merge with the L02-P9 second repair (Linux AArch64, 2026-09-23).

Runs the touched test targets and the repository gates on a clean checkout of
the merged head, then direct probes through the trust-cg CLI for the staged
GOT-page window check: the far-GOT refusal against an existing output, the
near-GOT twin and its run, a pic link that writes nothing (-Wl,--version),
and outputs that are not regular files (/dev/null, a FIFO the CLI blocks on
before linking). Every log and
probe record is written under RUN/records. Nothing here edits the checkout;
the tree must be clean before and after.

Usage: qualify-reloc-limits-staged-20260923.py WORKTREE RUN
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


def probe(name: str, argv: list[str], cwd: Path, timeout: int = 180) -> dict:
    """Run one direct probe, keep command, exit, stdout and stderr in records/direct/NAME.txt."""
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
        tool("ld", ["ld", "--version"]),
        tool("readelf", ["readelf", "--version"]),
        tool("rustc", ["rustc", "--version"]),
        tool("cargo", ["cargo", "--version"]),
        tool("rustfmt", ["rustfmt", "--version"]),
    ]

    cargo = ["cargo"]
    common = ["--locked", "--offline", "-j", "8"]
    codegen = cargo + ["test", "-p", "trust-cg-codegen"]
    gates = [
        run("codegen_lib", codegen + ["--lib", *common]),
        run("codegen_lib_link_driver_reloc", codegen + ["--lib", *common, "--", "link_driver", "elf::reloc",
                                                        "elf::dwarf", "pipeline::tests::local_exec",
                                                        "pipeline::tests::intra_object"]),
        run("e2e_aarch64_link_runtime", codegen + ["--test", "e2e_aarch64_link_runtime", *common, "--", "--nocapture"]),
        run("e2e_aarch64_elf_tlsie", codegen + ["--test", "e2e_aarch64_elf_tlsie", *common]),
        run("aarch64_elf_dwarf", codegen + ["--test", "aarch64_elf_dwarf", *common]),
        run("e2e_aarch64_elf_relocation_model", codegen + ["--test", "e2e_aarch64_elf_relocation_model", *common]),
        run("cli_link_options", cargo + ["test", "-p", "trust-cg-cli", "--test", "link_options", *common]),
        run("cli_bin_unit", cargo + ["test", "-p", "trust-cg-cli", "--bin", "trust-cg", *common]),
        run("cli_output_paths", cargo + ["test", "-p", "trust-cg-cli", "--test", "output_paths", *common]),
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

    # --- Direct probes through the CLI ------------------------------------------
    trust_cg = WORKTREE / "target/debug/trust-cg"
    tc = str(trust_cg)
    cg = DIRECT / "cg"
    cg.mkdir(exist_ok=True)
    shutil.copy(INPUTS / "got_page.tmbc", cg / "got_page.tmbc")
    (cg / "desc_main.c").write_text(DESC_MAIN)
    (cg / "libfar.so").write_bytes(b"precious\n")
    os.mkfifo(cg / "out.fifo")
    pic = ["-shared", "-nostdlib", "--relocation-model", "pic"]
    probes = [
        probe("cc-compile-desc_main", ["cc", "-c", "desc_main.c"], cg),
        probe("ls-before", ["ls", "-1A", "."], cg),
        # Far GOT against an existing output: GNU ld links it, trust-cg refuses
        # the staged image and leaves libfar.so as it was.
        probe("cli-far-got-shared", [tc, *pic, f"-Wl,{FAR_GOT}", "-o", "libfar.so", "got_page.tmbc"], cg),
        probe("cat-libfar-after-refusal", ["cat", "libfar.so"], cg),
        probe("ls-after-far", ["ls", "-1A", "."], cg),
        # Near GOT: installed and run.
        probe("cli-near-got-shared", [tc, *pic, f"-Wl,{NEAR_GOT}", "-o", "libnear.so", "got_page.tmbc"], cg),
        probe("readelf-SW-libnear.so", ["readelf", "-SW", "libnear.so"], cg),
        probe("cc-desc-against-near", ["cc", "desc_main.o", "-L.", "-lnear", f"-Wl,-rpath,{cg}", "-o", "desc"], cg),
        probe("run-desc", ["./desc"], cg),
        # A pic link that writes nothing is refused by name.
        probe("cli-pic-version", [tc, "-Wl,--version", *pic, "-o", "libfar.so", "got_page.tmbc"], cg),
        probe("cat-libfar-after-version", ["cat", "libfar.so"], cg),
        # Outputs that are not regular files are not replaced.
        probe("cli-pic-dev-null", [tc, *pic, "-o", "/dev/null", "got_page.tmbc"], cg),
        probe("stat-dev-null", ["stat", "-c", "%F %t:%T", "/dev/null"], cg),
        # An existing FIFO output: the CLI's output-alias check opens it and
        # blocks before any compile or link, with or without a staged link
        # (a compile-only twin shows the same), so these are bounded at 10 s.
        probe("cli-pic-fifo", [tc, *pic, "-o", "out.fifo", "got_page.tmbc"], cg, timeout=10),
        probe("cli-compile-only-fifo", [tc, "-c", "-o", "out.fifo", "got_page.tmbc"], cg, timeout=10),
        probe("stat-fifo", ["stat", "-c", "%F", "out.fifo"], cg),
        probe("ls-after", ["ls", "-1A", "."], cg),
    ]
    (cg / "out.fifo").unlink()

    status_after = git("status", "--porcelain", "--untracked-files=all")
    results = {
        "schema": "trust-cg.l02-p10-reloc-kind-limits-staged.v1",
        "source": {"head": head, "tree": git("rev-parse", "HEAD^{tree}"),
                   "status_before": status_before, "status_after": status_after},
        "host": host,
        "tools": tools,
        "trust_cg_binary_sha256": sha256(trust_cg),
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
