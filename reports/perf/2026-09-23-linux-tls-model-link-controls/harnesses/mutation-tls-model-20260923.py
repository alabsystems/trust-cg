#!/usr/bin/env python3
"""Mutation leg for the L02-P9 TLS-model controls (run after the clean run).

Disables the link driver's local-exec refusal in run_link, runs the two
native controls that depend on it, and restores the file. The controls must
fail with the refusal gone: the CLI's static-model -shared link then succeeds
through GNU ld, and run_link reaches the linker. The checkout must be clean
before and after.

Usage: mutation-tls-model-20260923.py WORKTREE RUN
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

WORKTREE = Path(sys.argv[1]).resolve()
RUN = Path(sys.argv[2]).resolve()
OUT = RUN / "records" / "mutation"
HOME = Path.home()
ENV = dict(
    os.environ,
    PATH=os.pathsep.join(
        [
            str(HOME / ".local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin"),
            str(HOME / ".cargo/bin"),
            os.environ["PATH"],
        ]
    ),
)
TARGET = WORKTREE / "crates/trust-cg-codegen/src/link_driver.rs"
GUARD = "    if !refused_inputs.is_empty() {\n        return Err(LinkError::InputRefused(refused_inputs));\n    }\n"
RESULT = re.compile(r"^test result: .*$", re.M)


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(WORKTREE), *args], check=True, capture_output=True, text=True
    ).stdout


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    if git("status", "--porcelain", "--untracked-files=all").strip():
        print("checkout is dirty; refusing to mutate", file=sys.stderr)
        return 1
    original = TARGET.read_text()
    if original.count(GUARD) != 1:
        print("guard not found exactly once", file=sys.stderr)
        return 1
    TARGET.write_text(original.replace(GUARD, "    let _ = refused_inputs;\n"))
    (OUT / "disable-guard.patch").write_text(git("diff"))
    records = []
    try:
        for name, argv in (
            ("cli_link_options_linux_tls", ["cargo", "test", "-p", "trust-cg-cli", "--test", "link_options", "--locked", "--offline", "-j", "8", "--", "linux_tls"]),
            ("e2e_tlsie_shared_control", ["cargo", "test", "-p", "trust-cg-codegen", "--test", "e2e_aarch64_elf_tlsie", "--locked", "--offline", "-j", "8", "--", "local_exec_tls_in_a_shared_link"]),
        ):
            completed = subprocess.run(argv, cwd=WORKTREE, env=ENV, capture_output=True, text=True, timeout=1500)
            text = completed.stdout + completed.stderr
            (OUT / f"{name}.log").write_text(f"$ {' '.join(argv)}\n{text}--- exit {completed.returncode} ---\n")
            records.append({"name": name, "exit": completed.returncode, "test_results": RESULT.findall(text)})
            print(name, completed.returncode, RESULT.findall(text), flush=True)
    finally:
        TARGET.write_text(original)
    clean = not git("status", "--porcelain", "--untracked-files=all").strip()
    (OUT / "results.json").write_text(json.dumps({"mutation": "run_link refusal removed", "legs": records, "restored_clean": clean}, indent=2) + "\n")
    failing = all(record["exit"] != 0 for record in records)
    print("every leg failed under the mutation:", failing, "restored clean:", clean)
    return 0 if failing and clean else 1


if __name__ == "__main__":
    sys.exit(main())
