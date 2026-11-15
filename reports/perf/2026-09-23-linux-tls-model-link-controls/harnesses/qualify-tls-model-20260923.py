#!/usr/bin/env python3
"""Qualifying run for the L02-P9 TLS-model link controls (Linux AArch64, 2026-09-23).

Runs the touched test targets and the repository gates on a clean checkout,
then the direct linker probes that motivate the link driver's local-exec
refusal, and writes every log and probe record under RUN/records. Nothing here
edits the checkout; the tree must be clean before and after.

Usage: qualify-tls-model-20260923.py WORKTREE RUN
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


def run(name: str, argv: list[str], *, cwd: Path = WORKTREE, timeout: int = 1500, env=None) -> dict:
    """Run one gate command, keep its complete output as records/logs/NAME.log."""
    completed = subprocess.run(
        argv, cwd=cwd, env=env or ENV, capture_output=True, text=True, timeout=timeout
    )
    text = f"$ {' '.join(argv)}\n(cwd {cwd})\n--- stdout ---\n{completed.stdout}--- stderr ---\n{completed.stderr}--- exit {completed.returncode} ---\n"
    (LOGS / f"{name}.log").write_text(text)
    record = {
        "name": name,
        "argv": argv,
        "exit": completed.returncode,
        "test_results": RESULT.findall(completed.stdout + completed.stderr),
    }
    print(f"{name}: exit {completed.returncode} {record['test_results']}", flush=True)
    return record


def probe(name: str, argv: list[str], cwd: Path, timeout: int = 120, env=None) -> dict:
    """Run one direct probe, keep command, exit, stdout and stderr in records/direct/NAME.txt."""
    try:
        completed = subprocess.run(
            argv, cwd=cwd, env=env or ENV, capture_output=True, text=True, timeout=timeout
        )
        exit_code, stdout, stderr = completed.returncode, completed.stdout, completed.stderr
    except subprocess.TimeoutExpired:
        exit_code, stdout, stderr = "timeout", "", ""
    shown = [a.replace(str(DIRECT), "$DIRECT") for a in argv]
    stdout_shown = stdout.replace(str(DIRECT), "$DIRECT")
    stderr_shown = stderr.replace(str(DIRECT), "$DIRECT")
    (DIRECT / f"{name}.txt").write_text(
        f"$ {' '.join(shown)}\n--- stdout ---\n{stdout_shown}--- stderr ---\n{stderr_shown}--- exit {exit_code} ---\n"
    )
    print(f"probe {name}: exit {exit_code}", flush=True)
    return {"name": name, "argv": shown, "exit": exit_code}


def tool(name: str, argv: list[str]) -> dict:
    path = shutil.which(argv[0], path=PATH)
    resolved = Path(path).resolve() if path else None
    version = subprocess.run(argv, capture_output=True, text=True, env=ENV)
    return {
        "name": name,
        "path": path,
        "resolved": str(resolved) if resolved else None,
        "sha256": sha256(resolved) if resolved else None,
        "version": (version.stdout or version.stderr).splitlines()[0] if (version.stdout or version.stderr) else "",
    }


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
            (line.split(":", 1)[1].strip() for line in Path("/proc/cpuinfo").read_text().splitlines() if line.startswith("CPU part")),
            "",
        ),
    }
    tools = [
        tool("cc", ["cc", "--version"]),
        tool("ld", ["ld", "--version"]),
        tool("ld.lld", ["ld.lld", "--version"]),
        tool("readelf", ["readelf", "--version"]),
        tool("objdump", ["objdump", "--version"]),
        tool("rustc", ["rustc", "--version"]),
        tool("cargo", ["cargo", "--version"]),
        tool("rustfmt", ["rustfmt", "--version"]),
    ]

    cargo = ["cargo"]
    common = ["--locked", "--offline", "-j", "8"]
    gates = [
        run("codegen_lib", cargo + ["test", "-p", "trust-cg-codegen", "--lib", *common]),
        run("link_driver_unit", cargo + ["test", "-p", "trust-cg-codegen", "--lib", *common, "--", "link_driver"]),
        run("cli_link_options", cargo + ["test", "-p", "trust-cg-cli", "--test", "link_options", *common]),
        run("cli_bin_unit", cargo + ["test", "-p", "trust-cg-cli", "--bin", "trust-cg", *common]),
        run("e2e_aarch64_elf_tlsie", cargo + ["test", "-p", "trust-cg-codegen", "--test", "e2e_aarch64_elf_tlsie", *common]),
        run("e2e_aarch64_link_runtime", cargo + ["test", "-p", "trust-cg-codegen", "--test", "e2e_aarch64_link_runtime", *common]),
        run("check_codegen", cargo + ["check", "-p", "trust-cg-codegen", *common]),
        run("check_codegen_verify", cargo + ["check", "-p", "trust-cg-codegen", "--features", "verify", *common]),
        run("check_lower_cli", cargo + ["check", "-p", "trust-cg-lower", "-p", "trust-cg-cli", *common]),
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
    ]

    # --- Direct probes: trust-cg objects -------------------------------------
    trust_cg = WORKTREE / "target/debug/trust-cg"
    cg = DIRECT / "cg"
    cg.mkdir(exist_ok=True)
    for name in ("tls_lib", "tls_prog", "tls_user", "tls_reader_plain", "tls_reader_thread"):
        shutil.copy(INPUTS / f"{name}.tmbc", cg / f"{name}.tmbc")
    lld_env = dict(ENV, PATH=os.pathsep.join([str(HOME / ".local/bin"), PATH]))
    tc = str(trust_cg)
    probes = [
        probe("cg-emit-trust_ir-tls_lib", [tc, "--emit-trust_ir", "tls_lib.trust_ir", "-c", "-o", "tls_lib.o", "tls_lib.tmbc"], cg),
        probe("cg-cat-tls_lib.trust_ir", ["cat", "tls_lib.trust_ir"], cg),
        probe("cg-emit-trust_ir-tls_user", [tc, "--emit-trust_ir", "tls_user.trust_ir", "-c", "-o", "tls_user.o", "tls_user.tmbc"], cg),
        probe("cg-cat-tls_user.trust_ir", ["cat", "tls_user.trust_ir"], cg),
        probe("cg-objdump-dr-tls_lib.o", ["objdump", "-dr", "tls_lib.o"], cg),
        probe("cg-readelf-sW-tls_lib.o", ["readelf", "-sW", "tls_lib.o"], cg),
        probe("cg-readelf-rW-tls_lib.o", ["readelf", "-rW", "tls_lib.o"], cg),
        # The refusal through the CLI (static and pie), no linker run.
        probe("cli-shared-static", [tc, "-shared", "-o", "libtcgtls_static.so", "tls_lib.tmbc"], cg),
        probe("cli-shared-pie", [tc, "-shared", "--relocation-model", "pie", "-o", "libtcgtls_pie.so", "tls_lib.tmbc"], cg),
        probe("cli-shared-outputs-absent", ["ls", "-1", "."], cg),
        # GNU ld 2.42 on the same static-model object, outside the driver.
        probe("gnu-cc-shared-static-object", ["cc", "-shared", "tls_lib.o", "-o", "libtcgtls_bfd.so"], cg),
        probe("gnu-readelf-dW-libtcgtls_bfd.so", ["readelf", "-dW", "libtcgtls_bfd.so"], cg),
        probe("gnu-readelf-rW-libtcgtls_bfd.so", ["readelf", "-rW", "libtcgtls_bfd.so"], cg),
        probe("gnu-objdump-d-libtcgtls_bfd.so", ["objdump", "-d", "--disassemble=tcg_cli_tls_bump", "libtcgtls_bfd.so"], cg),
        probe("gnu-cc-user-against-bfd-library", ["cc", "tls_user.o", "-L.", "-ltcgtls_bfd", f"-Wl,-rpath,{cg}", "-o", "user_bfd"], cg),
        probe("run-user_bfd", ["./user_bfd"], cg),
        # lld on the same object.
        probe("lld-cc-shared-static-object", ["cc", "-fuse-ld=lld", "-shared", "tls_lib.o", "-o", "libtcgtls_lld.so"], cg, env=lld_env),
        # Positive twins through the CLI.
        probe("cli-shared-pic", [tc, "-shared", "--relocation-model", "pic", "-o", "libtcgtls.so", "tls_lib.tmbc"], cg),
        probe("pic-readelf-rW-libtcgtls.so", ["readelf", "-rW", "libtcgtls.so"], cg),
        probe("cli-user-against-pic-library", [tc, "-o", "user_pic", "-L", ".", "-l", "tcgtls", "--rpath", str(cg), "tls_user.tmbc"], cg),
        probe("run-user_pic", ["./user_pic"], cg),
        probe("cli-executable-static", [tc, "-o", "prog", "tls_prog.tmbc"], cg),
        probe("run-prog", ["./prog"], cg),
        # TLS/non-TLS clash through the CLI, and its thread-local twin.
        probe("cli-clash-plain-reader", [tc, "-o", "clash", "tls_lib.tmbc", "tls_reader_plain.tmbc"], cg),
        probe("cli-thread-reader", [tc, "-o", "reader", "tls_lib.tmbc", "tls_reader_thread.tmbc"], cg),
        probe("run-reader", ["./reader"], cg),
    ]

    # --- Direct probes: gcc objects (message shapes the unit tests pin) ------
    gcc = DIRECT / "gcc"
    gcc.mkdir(exist_ok=True)
    sources = {
        "le.c": "__thread int tcg_tls_var = 40;\nint bump(void) { return ++tcg_tls_var; }\n",
        "le_ext.c": 'extern __thread int tcg_tls_ext __attribute__((tls_model("local-exec")));\nint bump_ext(void) { return ++tcg_tls_ext; }\n',
        "tdef.c": "__thread int clash = 7;\n",
        "nref.c": "extern int clash;\nint main(void) { return clash; }\n",
        "ndef.c": "int clash = 7;\n",
        "tref.c": "extern __thread int clash;\nint main(void) { return clash; }\n",
        "tref2.c": "extern __thread int clash;\nint use_tls(void) { return clash; }\n",
        "main_only.c": "int main(void) { return 0; }\n",
    }
    for name, text in sources.items():
        (gcc / name).write_text(text)
    gcc_probes = [
        probe("gcc-compile-le", ["gcc", "-O1", "-ftls-model=local-exec", "-c", "le.c", "-o", "le.o"], gcc),
        probe("gcc-compile-le_ext", ["gcc", "-O1", "-c", "le_ext.c", "-o", "le_ext.o"], gcc),
        *[
            probe(f"gcc-compile-{stem}", ["gcc", "-O1", "-c", f"{stem}.c", "-o", f"{stem}.o"], gcc)
            for stem in ("tdef", "nref", "ndef", "tref", "main_only")
        ],
        probe("gcc-compile-tref2", ["gcc", "-O1", "-fPIC", "-c", "tref2.c", "-o", "tref2.o"], gcc),
        probe("gcc-libtdef", ["gcc", "-shared", "-fPIC", "tdef.c", "-o", "libtdef.so"], gcc),
        probe("gnu-le-defined-shared", ["cc", "-shared", "le.o", "-o", "lible.so"], gcc),
        probe("gnu-le-undefined-shared", ["cc", "-shared", "le_ext.o", "-o", "lible_ext.so"], gcc),
        probe("lld-le-defined-shared", ["cc", "-fuse-ld=lld", "-shared", "le.o", "-o", "lible_lld.so"], gcc, env=lld_env),
        probe("lld-le-undefined-shared", ["cc", "-fuse-ld=lld", "-shared", "le_ext.o", "-o", "lible_ext_lld.so"], gcc, env=lld_env),
        probe("gnu-clash-tdef-nref", ["cc", "tdef.o", "nref.o", "-o", "clash1"], gcc),
        probe("gnu-clash-ndef-tref", ["cc", "ndef.o", "tref.o", "-o", "clash2"], gcc),
        probe("gnu-clash-tdef-ndef", ["cc", "main_only.o", "tdef.o", "ndef.o", "-o", "clash3"], gcc),
        probe("gnu-clash-tref2-nref", ["cc", "tref2.o", "nref.o", "-L.", "-ltdef", "-o", "clash4"], gcc),
        probe("lld-clash-tdef-nref", ["cc", "-fuse-ld=lld", "tdef.o", "nref.o", "-o", "clash5"], gcc, env=lld_env),
        probe("lld-clash-ndef-tref", ["cc", "-fuse-ld=lld", "ndef.o", "tref.o", "-o", "clash6"], gcc, env=lld_env),
    ]

    status_after = git("status", "--porcelain", "--untracked-files=all")
    results = {
        "schema": "trust-cg.l02-p9-tls-model-link-controls.v1",
        "source": {"head": head, "tree": git("rev-parse", "HEAD^{tree}"), "status_before": status_before, "status_after": status_after},
        "host": host,
        "tools": tools,
        "trust_cg_binary_sha256": sha256(trust_cg),
        "inputs": {p.name: sha256(p) for p in sorted(INPUTS.glob("*.tmbc"))},
        "gates": gates,
        "probes": probes,
        "gcc_probes": gcc_probes,
    }
    (RECORDS / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    failed = [g["name"] for g in gates if g["exit"] != 0]
    print("failed gates:", failed)
    print("status after clean:", not status_after)
    return 1 if failed or status_after else 0


if __name__ == "__main__":
    sys.exit(main())
