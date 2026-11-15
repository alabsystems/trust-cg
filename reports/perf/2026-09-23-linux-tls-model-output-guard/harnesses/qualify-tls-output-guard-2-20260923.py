#!/usr/bin/env python3
"""Qualifying run for the second L02-P9 repair (Linux AArch64, 2026-09-23).

Runs the touched test targets and the repository gates on a clean checkout,
then the direct probes behind the repair, and writes every log and probe
record under RUN/records:

- how the host GNU ld 2.42 (and LLD 22.1.6) reads every spelling of a
  driver-owned option (RUN/ld-option-reading-20260923.py);
- the second review's two reproductions on the repaired binary: an output
  redirection (`-Wl,-shar,--outp=libtcgb.so`, `-Wl,--outp=`, `-Wl,-o<p>`)
  against an existing and a fresh `-o` path, and `-Wl,--version` against an
  existing `-o` file;
- the read-back through a `cc` shim that always adds `-shared`, against an
  existing `-o` file;
- the positive twins: the staged executable link (fresh and replacing a
  file) runs 42, the pic library links `-shared` and its user runs 42, and
  the pic `-Wl,--version` link keeps its unchecked behaviour.

Nothing here edits the checkout; the tree must be clean before and after.
RUN/inputs/*.tmbc are the modules retained in
reports/perf/2026-09-23-linux-tls-model-output-guard/records/inputs.

Usage: qualify-tls-output-guard-2-20260923.py WORKTREE RUN
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

    # --- How the host linkers read each spelling -----------------------------
    reading = run(
        "ld_option_reading",
        ["python3", "-B", str(RUN / "ld-option-reading-20260923.py"), str(DIRECT / "ld")],
        cwd=RUN,
    )

    # --- The second review's reproductions on the repaired binary -------------
    trust_cg = WORKTREE / "target/debug/trust-cg"
    tc = str(trust_cg)
    cg = DIRECT / "cg"
    cg.mkdir(exist_ok=True)
    for name in ("tls_lib", "tls_prog", "tls_user"):
        shutil.copy(INPUTS / f"{name}.tmbc", cg / f"{name}.tmbc")
    shutil.copy("/bin/true", cg / "preexist")
    probes: list[dict] = []
    states: list[dict] = [state("state-0-before", cg, ["preexist"])]
    # 1. Output redirection, against an existing and a fresh -o path.
    for label, group in (
        ("shar-outp", "-shar,--outp=libtcgb.so"),
        ("outp", "--outp=libtcgb.so"),
        ("o-joined", "-olibtcgb.so"),
        ("outp-1dash", "-outp=libtcgb.so"),
    ):
        for target in ("preexist", "fresh"):
            probes.append(probe(f"cli-redirect-{label}-{target}", [tc, f"-Wl,{group}", "-o", target, "tls_lib.tmbc"], cg))
    states.append(state("state-1-after-redirects", cg, ["preexist"]))
    # 2. A link that writes nothing, against an existing -o file.
    (cg / "keep2.txt").write_text("precious\n")
    states.append(state("state-2-before-version", cg, ["preexist", "keep2.txt"]))
    probes.append(probe("cli-version-keep2", [tc, "-Wl,--version", "-o", "keep2.txt", "tls_prog.tmbc"], cg))
    states.append(state("state-3-after-version", cg, ["preexist", "keep2.txt"]))
    # Twin: the pic model has no local-exec input; the link keeps its old
    # unchecked behaviour (exit 0, file untouched).
    probes.append(probe("cli-version-keep2-pic", [tc, "-Wl,--version", "--relocation-model", "pic", "-o", "keep2.txt", "tls_prog.tmbc"], cg))
    states.append(state("state-4-after-version-pic", cg, ["preexist", "keep2.txt"]))
    # 3. The read-back through a cc that always links -shared.
    shim = RUN / "shim"
    shim.mkdir(exist_ok=True)
    host_cc = shutil.which("cc", path=PATH)
    (shim / "cc").write_text(f"#!/bin/sh\nexec '{host_cc}' -shared \"$@\"\n")
    (shim / "cc").chmod(0o755)
    shim_env = dict(ENV, PATH=os.pathsep.join([str(shim), PATH]))
    (cg / "libtcgshim.so").write_text("precious\n")
    states.append(state("state-5-before-shim", cg, ["preexist", "keep2.txt", "libtcgshim.so"]))
    probes.append(probe("cli-shim-shared-static", [tc, "-o", "libtcgshim.so", "tls_lib.tmbc"], cg, env=shim_env))
    states.append(state("state-6-after-shim", cg, ["preexist", "keep2.txt", "libtcgshim.so"]))
    # Positive twins.
    probes += [
        probe("cli-shim-shared-pic", [tc, "--relocation-model", "pic", "-o", "libtcgshim.so", "tls_lib.tmbc"], cg, env=shim_env),
        probe("readelf-h-libtcgshim.so", ["readelf", "-h", "libtcgshim.so"], cg),
        probe("cli-user-against-shim-library", [tc, "-o", "user_shim", "-L", ".", "-l", "tcgshim", "--rpath", str(cg), "tls_user.tmbc"], cg),
        probe("run-user_shim", ["./user_shim"], cg),
        probe("cli-pic-shared", [tc, "-shared", "--relocation-model", "pic", "-o", "libtcgtls.so", "tls_lib.tmbc"], cg),
        probe("cli-user-against-pic-library", [tc, "-o", "user_pic", "-L", ".", "-l", "tcgtls", "--rpath", str(cg), "tls_user.tmbc"], cg),
        probe("run-user_pic", ["./user_pic"], cg),
        probe("cli-executable-fresh", [tc, "-o", "prog", "tls_prog.tmbc"], cg),
        probe("readelf-h-prog", ["readelf", "-h", "prog"], cg),
        probe("run-prog", ["./prog"], cg),
        probe("cli-executable-replaces-keep2", [tc, "-o", "keep2.txt", "tls_prog.tmbc"], cg),
        probe("run-keep2", ["./keep2.txt"], cg),
    ]
    states.append(state("state-7-end", cg, ["preexist", "keep2.txt", "libtcgshim.so"]))

    status_after = git("status", "--porcelain", "--untracked-files=all")
    results = {
        "schema": "trust-cg.l02-p9-tls-output-guard-repair-2.v1",
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
        "ld_option_reading": reading,
        "probes": probes,
        "states": states,
    }
    (RECORDS / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    failed = [g["name"] for g in gates if g["exit"] != 0] + ([] if reading["exit"] == 0 else ["ld_option_reading"])
    print("failed gates:", failed)
    print("status after clean:", not status_after)
    return 1 if failed or status_after or status_after_write else 0


if __name__ == "__main__":
    sys.exit(main())
