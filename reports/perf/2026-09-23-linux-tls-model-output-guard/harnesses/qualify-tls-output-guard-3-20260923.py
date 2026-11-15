#!/usr/bin/env python3
"""Qualifying run for the third L02-P9 repair (Linux AArch64, 2026-09-23).

Runs the touched test targets and the repository gates on a clean checkout,
then the direct probes behind the repair, and writes every log and probe
record under RUN/records:

- the third review's response-file reproductions on the repaired binary: a
  typed value that begins with `@` (`--rpath`, `--soname`, `-o`, an input
  path, `-L`, `-l`) refused by name before anything runs, with no output
  written anywhere and any pre-existing file byte-identical;
- the positive twin: an output and input spelled `./@...` link and run (42);
- the documented unexamined routes (an object named in a `-Wl` group and as
  `-l:<file>`): each links and its user exits 236, pinned as the boundary.

Nothing here edits the checkout; the tree must be clean before and after.
RUN/inputs/*.tmbc are the modules retained in
reports/perf/2026-09-23-linux-tls-model-output-guard/records/inputs.

Usage: qualify-tls-output-guard-3-20260923.py WORKTREE RUN
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
RAN = re.compile(r"^(Ran \d+ tests.*|OK.*|FAILED.*)$", re.M)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(WORKTREE), *args], check=True, capture_output=True, text=True
    ).stdout.strip()


def run(name: str, argv: list[str], *, cwd: Path = WORKTREE, timeout: int = 1500) -> dict:
    """Run one gate command, keep its complete output as records/logs/NAME.log."""
    completed = subprocess.run(argv, cwd=cwd, env=ENV, capture_output=True, text=True, timeout=timeout)
    text = f"$ {' '.join(argv)}\n(cwd {cwd})\n--- stdout ---\n{completed.stdout}--- stderr ---\n{completed.stderr}--- exit {completed.returncode} ---\n"
    (LOGS / f"{name}.log").write_text(text)
    both = completed.stdout + completed.stderr
    record = {
        "name": name,
        "argv": argv,
        "exit": completed.returncode,
        "test_results": RESULT.findall(both) or RAN.findall(both),
    }
    print(f"{name}: exit {completed.returncode} {record['test_results']}", flush=True)
    return record


def probe(name: str, argv: list[str], cwd: Path, timeout: int = 120, env=None) -> dict:
    """Run one direct probe, keep command, exit, stdout and stderr in records/direct/NAME.txt."""
    try:
        completed = subprocess.run(argv, cwd=cwd, env=env or ENV, capture_output=True, text=True, timeout=timeout)
        exit_code, stdout, stderr = completed.returncode, completed.stdout, completed.stderr
    except subprocess.TimeoutExpired:
        exit_code, stdout, stderr = "timeout", "", ""

    def shown(text: str) -> str:
        return text.replace(str(DIRECT), "$DIRECT").replace(str(RUN), "$RUN")

    (DIRECT / f"{name}.txt").write_text(
        f"$ {' '.join(shown(a) for a in argv)}\n--- stdout ---\n{shown(stdout)}--- stderr ---\n{shown(stderr)}--- exit {exit_code} ---\n"
    )
    print(f"probe {name}: exit {exit_code}", flush=True)
    return {"name": name, "argv": [shown(a) for a in argv], "exit": exit_code}


def state(name: str, directory: Path, files: list[str]) -> dict:
    """Record the directory listing (hidden entries included) and the SHA-256 of FILES."""
    listing = sorted(p.name for p in directory.iterdir())
    hashes = {f: (sha256(directory / f) if (directory / f).is_file() else None) for f in files}
    (DIRECT / f"{name}.txt").write_text(json.dumps({"listing": listing, "sha256": hashes}, indent=2) + "\n")
    return {"name": name, "listing": listing, "sha256": hashes}


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


def main() -> int:
    for directory in (LOGS, DIRECT):
        directory.mkdir(parents=True, exist_ok=True)
    head = git("rev-parse", "HEAD")
    status_before = git("status", "--porcelain", "--untracked-files=all")
    if status_before:
        print("checkout is dirty; refusing to qualify", file=sys.stderr)
        return 1
    lld_env = dict(ENV, PATH=os.pathsep.join([str(HOME / ".local/bin"), PATH]))

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
        tool("ld.lld", ["ld.lld", "--version"], env=lld_env),
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
        run("native_test_host_matrix", ["python3", "-B", "scripts/native_test_host_matrix.py", "--check"]),
        run("check_documentation_write", ["python3", "-B", "scripts/check_documentation.py", "--write"]),
        run("check_documentation", ["python3", "-B", "scripts/check_documentation.py", "--check"]),
        run("diagnostics_inventory", ["python3", "-B", "scripts/generate_diagnostics_inventory.py", "--check"]),
    ]
    status_after_write = git("status", "--porcelain", "--untracked-files=all")

    trust_cg = WORKTREE / "target/debug/trust-cg"
    tc = str(trust_cg)
    cg = DIRECT / "cg"
    cg.mkdir(exist_ok=True)
    for name in ("tls_lib", "tls_prog", "tls_user", "tls_reader_thread"):
        shutil.copy(INPUTS / f"{name}.tmbc", cg / f"{name}.tmbc")
    # A local-exec object, as the review compiled it, for the unexamined
    # routes. div.tmbc gives a positional non-TLS input so the -Wl/-l: object
    # is the only local-exec one.
    probe("cg-compile-le", [tc, "-c", "-o", "le.o", "tls_lib.tmbc"], cg)
    # The response files the review used, and a pre-existing output.
    (cg / "resp").write_text("/x --shared -o libevil.so\n")
    (cg / "resp2").write_text("libq.so.1 le.o\n")
    (cg / "resp3").write_text("libredir.so -shared\n")
    shutil.copy("/bin/true", cg / "preexist")
    shutil.copy(cg / "tls_prog.tmbc", cg / "@inp")
    probes: list[dict] = []
    kept = ["preexist", "resp", "resp2", "resp3", "le.o", "@inp"]
    states: list[dict] = [state("state-0-before", cg, kept)]

    # --- D1: forwarded values that begin with @ ------------------------------
    for label, args in (
        ("rpath", ["--rpath", "@resp", "-o", "preexist", "tls_lib.tmbc"]),
        ("soname", ["--shared", "--relocation-model", "pic", "--soname", "@resp2", "-o", "libtcgq.so", "tls_lib.tmbc"]),
        ("output", ["-o", "@resp3", "tls_prog.tmbc"]),
        ("input", ["-o", "prog", "@inp"]),
        ("libpath", ["-L", "@resp", "-o", "prog", "tls_prog.tmbc"]),
        ("libname", ["-l", "@resp", "-o", "prog", "tls_prog.tmbc"]),
    ):
        probes.append(probe(f"cli-response-file-{label}", [tc, *args], cg))
    states.append(state("state-1-after-response-files", cg, kept))
    # Positive twin: ./@ spellings link and run.
    shutil.copy(cg / "tls_prog.tmbc", cg / "@src")
    probes += [
        probe("cli-dot-at", [tc, "-o", "./@out", "./@src"], cg),
        probe("run-dot-at", ["./@out"], cg),
    ]

    # --- D2: the documented unexamined routes --------------------------------
    rpath = str(cg)
    for label, route in (("wl", ["-Wl,le.o"]), ("lcolon", ["-L", ".", "-l", ":le.o"])):
        lib = f"libtcg{label}.so"
        probes.append(probe(
            f"cli-route-{label}",
            [tc, "--shared", "--relocation-model", "pic", "-o", lib, *route, "tls_reader_thread.tmbc"],
            cg,
        ))
        user = f"user_{label}"
        probes += [
            probe(f"readelf-h-{lib}", ["readelf", "-h", lib], cg),
            probe(f"cli-user-{label}", [tc, "-o", user, "-L", ".", "-l", f"tcg{label}", "--rpath", rpath, "tls_user.tmbc"], cg),
            probe(f"run-{user}", [f"./{user}"], cg),
        ]
    states.append(state("state-2-end", cg, kept))

    status_after = git("status", "--porcelain", "--untracked-files=all")
    results = {
        "schema": "trust-cg.l02-p9-tls-output-guard-repair-3.v1",
        "source": {
            "head": head,
            "tree": git("rev-parse", "HEAD^{tree}"),
            "status_before": status_before,
            "status_after_documentation_write": status_after_write,
            "status_after": status_after,
        },
        "host": host,
        "tools": tools,
        "trust_cg_binary_sha256": sha256(trust_cg),
        "inputs": {p.name: sha256(p) for p in sorted(INPUTS.glob("*.tmbc"))},
        "gates": gates,
        "probes": probes,
        "states": states,
    }
    (RECORDS / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    failed = [g["name"] for g in gates if g["exit"] != 0]
    print("failed gates:", failed)
    print("status after clean:", not status_after)
    return 1 if failed or status_after or status_after_write else 0


if __name__ == "__main__":
    sys.exit(main())
