#!/usr/bin/env python3
"""Qualifying run for the L02-P9 repair: the output-kind TLS guard (Linux AArch64, 2026-09-23).

Runs the touched test targets and the repository gates on a clean checkout,
then the direct probes behind the repair, and writes every log and probe
record under RUN/records:

- the review's bypass through the driver (`-Wl,--shared`, `-Wl,--Bshareable`)
  and GNU ld's abbreviations (`-Wl,--shar`, `-Wl,-shar`, `-Wl,--Bshare`,
  `-Wl,-Bshar`) on the static-model thread-local module;
- the positive twins (the pic library through `-Wl,--shar`, and executables
  under the pie default, --no-pie and --static);
- the same abbreviation used outside the driver, which is not checked;
- executable-side local-exec references to a thread-local a shared library
  defines, under GNU ld and lld (gcc objects), whose complete stderr the unit
  tests pin.

Nothing here edits the checkout; the tree must be clean before and after.
RUN/inputs/*.tmbc are the modules retained in
reports/perf/2026-09-23-linux-tls-model-link-controls/records/inputs.

Usage: qualify-tls-output-guard-20260923.py WORKTREE RUN
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
    shown = [a.replace(str(DIRECT), "$DIRECT") for a in argv]
    stdout_shown = stdout.replace(str(DIRECT), "$DIRECT")
    stderr_shown = stderr.replace(str(DIRECT), "$DIRECT")
    (DIRECT / f"{name}.txt").write_text(
        f"$ {' '.join(shown)}\n--- stdout ---\n{stdout_shown}--- stderr ---\n{stderr_shown}--- exit {exit_code} ---\n"
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
        run("check_documentation", ["python3", "-B", "scripts/check_documentation.py", "--check"]),
        run("diagnostics_inventory", ["python3", "-B", "scripts/generate_diagnostics_inventory.py", "--check"]),
    ]

    # --- Direct probes through the trust-cg CLI -------------------------------
    trust_cg = WORKTREE / "target/debug/trust-cg"
    tc = str(trust_cg)
    cg = DIRECT / "cg"
    cg.mkdir(exist_ok=True)
    for name in ("tls_lib", "tls_prog", "tls_user"):
        shutil.copy(INPUTS / f"{name}.tmbc", cg / f"{name}.tmbc")
    probes = [
        probe("cg-compile-tls_lib", [tc, "-c", "-o", "tls_lib.o", "tls_lib.tmbc"], cg),
        probe("cg-readelf-rW-tls_lib.o", ["readelf", "-rW", "tls_lib.o"], cg),
    ]
    # The review's bypass and the other full spellings: refused as driver-owned.
    for label, spelling in (
        ("wl-shared-2dash", "--shared"),
        ("wl-bshareable-2dash", "--Bshareable"),
        ("wl-shared-1dash", "-shared"),
        ("wl-bshareable-1dash", "-Bshareable"),
    ):
        probes.append(probe(f"cli-{label}", [tc, f"-Wl,{spelling}", "-o", f"lib_{label}.so", "tls_lib.tmbc"], cg))
    # GNU ld abbreviations: the linker writes a shared object, which the driver
    # reads back, removes and refuses.
    for label, spelling in (
        ("wl-shar-2dash", "--shar"),
        ("wl-shar-1dash", "-shar"),
        ("wl-bshare-2dash", "--Bshare"),
        ("wl-bshar-1dash", "-Bshar"),
    ):
        probes.append(probe(f"cli-{label}", [tc, f"-Wl,{spelling}", "-o", f"lib_{label}.so", "tls_lib.tmbc"], cg))
    probes.append(probe("cli-refused-outputs-absent", ["ls", "-1", "."], cg))
    # Positive twin: the pic library through the same abbreviation, used by an
    # executable with its own thread-local.
    probes += [
        probe("cli-pic-wl-shar", [tc, "-Wl,--shar", "--relocation-model", "pic", "-o", "libtcgtls.so", "tls_lib.tmbc"], cg),
        probe("pic-readelf-h-libtcgtls.so", ["readelf", "-h", "libtcgtls.so"], cg),
        probe("pic-readelf-rW-libtcgtls.so", ["readelf", "-rW", "libtcgtls.so"], cg),
        probe("cli-user-against-pic-library", [tc, "-o", "user_pic", "-L", ".", "-l", "tcgtls", "--rpath", str(cg), "tls_user.tmbc"], cg),
        probe("run-user_pic", ["./user_pic"], cg),
    ]
    # Positive twins: local-exec executables under each output kind.
    for label, flags in (("pie", []), ("no_pie", ["--no-pie"]), ("static", ["--static"])):
        probes += [
            probe(f"cli-executable-{label}", [tc, *flags, "-o", f"prog_{label}", "tls_prog.tmbc"], cg),
            probe(f"readelf-h-prog_{label}", ["readelf", "-h", f"prog_{label}"], cg),
            probe(f"readelf-d-prog_{label}", ["readelf", "-d", f"prog_{label}"], cg),
            probe(f"run-prog_{label}", [f"./prog_{label}"], cg),
        ]
    # The same abbreviation outside the driver is not checked (boundary).
    probes += [
        probe("outside-cc-wl-shar", ["cc", "-Wl,--shar", "tls_lib.o", "-o", "libtcgoutside.so"], cg),
        probe("outside-readelf-h-libtcgoutside.so", ["readelf", "-h", "libtcgoutside.so"], cg),
        probe("outside-objdump-d-libtcgoutside.so", ["objdump", "-d", "--disassemble=tcg_cli_tls_bump", "libtcgoutside.so"], cg),
        probe("outside-cli-user", [tc, "-o", "user_outside", "-L", ".", "-l", "tcgoutside", "--rpath", str(cg), "tls_user.tmbc"], cg),
        probe("run-user_outside", ["./user_outside"], cg),
    ]

    # --- Executable-side local-exec against a shared library (gcc objects) ----
    gcc = DIRECT / "gcc"
    gcc.mkdir(exist_ok=True)
    sources = {
        "def.c": "__thread int ext_tls = 40;\n__thread int ext_bss;\n",
        "exe.c": "extern __thread int ext_tls;\nint main(void){ return ext_tls + 2; }\n",
        "exe3.c": "extern __thread int ext_tls;\n__thread int own_tls = 1;\nint main(void){ return ext_tls + own_tls; }\n",
        "exe4.c": "extern __thread int ext_bss;\n__thread int own_tls = 1;\nint main(void){ return ext_bss + own_tls; }\n",
    }
    for name, text in sources.items():
        (gcc / name).write_text(text)
    gcc_probes = [
        probe("gcc-libdef", ["gcc", "-O1", "-fPIC", "-shared", "def.c", "-o", "libdef.so"], gcc),
        probe("gcc-libdef-so1-link", ["ln", "-sf", "libdef.so", "libdef.so.1"], gcc),
        *[
            probe(f"gcc-compile-{stem}", ["gcc", "-O1", "-ftls-model=local-exec", "-c", f"{stem}.c", "-o", f"{stem}.o"], gcc)
            for stem in ("exe", "exe3", "exe4")
        ],
        probe("gnu-exe-no-tls-segment", ["gcc", "exe.o", "-L.", "-ldef", "-o", "e"], gcc),
        probe("gnu-exe3-tdata", ["gcc", "exe3.o", "-L.", "-ldef", "-o", "e"], gcc),
        probe("gnu-exe4-tbss", ["gcc", "exe4.o", "-L.", "-ldef", "-o", "e"], gcc),
        probe("gnu-exe3-versioned-soname", ["gcc", "exe3.o", "./libdef.so.1", "-o", "e"], gcc),
        probe("lld-exe3-tdata", ["gcc", "-fuse-ld=lld", "exe3.o", "-L.", "-ldef", "-o", "e"], gcc, env=lld_env),
        probe("lld-exe4-tbss", ["gcc", "-fuse-ld=lld", "exe4.o", "-L.", "-ldef", "-o", "e"], gcc, env=lld_env),
    ]

    status_after = git("status", "--porcelain", "--untracked-files=all")
    results = {
        "schema": "trust-cg.l02-p9-tls-output-guard.v1",
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
