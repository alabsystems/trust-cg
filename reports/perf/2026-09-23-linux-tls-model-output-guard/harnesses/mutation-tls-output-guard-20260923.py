#!/usr/bin/env python3
"""Mutation legs for the L02-P9 repair (run after the clean qualifying run).

Three mutations of crates/trust-cg-codegen/src/link_driver.rs, each applied,
exercised and reverted in turn:

- output-check: run_link no longer refuses a local-exec input's non-executable
  output. The CLI abbreviation control, the e2e steered-shared-object control
  and the unit test with a scripted driver must fail.
- driver-owned: `--shared` and `--Bshareable` are dropped from the driver-owned
  -Wl spellings. The CLI spelling control and the parse_wl_group unit test must
  fail.
- both: the two together restore the reviewed behavior. The mutated trust-cg
  binary is built and the review's reproduction is replayed: `-Wl,--shared`
  links the static-model thread-local module into a library, and an executable
  with its own thread-local linked against it exits 236 instead of 42.

The file is restored after every leg, trust-cg is rebuilt from the clean
source at the end, and the checkout must be clean before and after.

Usage: mutation-tls-output-guard-20260923.py WORKTREE RUN
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

WORKTREE = Path(sys.argv[1]).resolve()
RUN = Path(sys.argv[2]).resolve()
OUT = RUN / "records" / "mutation"
INPUTS = RUN / "inputs"
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
OUTPUT_CHECK = "        if !refused_output.is_empty() {\n"
OUTPUT_CHECK_MUTATED = "        if false && !refused_output.is_empty() {\n"
# Anchored at the preceding newline so the indented test-table rows do not match.
OWNED = '\n    ("--shared", "--shared"),\n', '\n    ("--Bshareable", "--shared"),\n'
RESULT = re.compile(r"^test result: .*$", re.M)
COMMON = ["--locked", "--offline", "-j", "8"]


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(WORKTREE), *args], check=True, capture_output=True, text=True
    ).stdout


def mutate(source: str, legs: set[str]) -> str:
    if "output-check" in legs:
        assert source.count(OUTPUT_CHECK) == 1
        source = source.replace(OUTPUT_CHECK, OUTPUT_CHECK_MUTATED)
    if "driver-owned" in legs:
        for line in OWNED:
            assert source.count(line) == 1
            source = source.replace(line, "\n")
    return source


def cargo(name: str, argv: list[str], records: list[dict]) -> None:
    completed = subprocess.run(argv, cwd=WORKTREE, env=ENV, capture_output=True, text=True, timeout=1500)
    text = completed.stdout + completed.stderr
    (OUT / f"{name}.log").write_text(f"$ {' '.join(argv)}\n{text}--- exit {completed.returncode} ---\n")
    records.append({"name": name, "exit": completed.returncode, "test_results": RESULT.findall(text)})
    print(name, completed.returncode, RESULT.findall(text), flush=True)


def probe(name: str, argv: list[str], cwd: Path, records: list[dict]) -> None:
    completed = subprocess.run(argv, cwd=cwd, env=ENV, capture_output=True, text=True, timeout=300)
    shown = [a.replace(str(cwd), "$REPRO") for a in argv]
    (OUT / f"{name}.txt").write_text(
        f"$ {' '.join(shown)}\n--- stdout ---\n{completed.stdout.replace(str(cwd), '$REPRO')}"
        f"--- stderr ---\n{completed.stderr.replace(str(cwd), '$REPRO')}--- exit {completed.returncode} ---\n"
    )
    records.append({"name": name, "argv": shown, "exit": completed.returncode})
    print(name, completed.returncode, flush=True)


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    if git("status", "--porcelain", "--untracked-files=all").strip():
        print("checkout is dirty; refusing to mutate", file=sys.stderr)
        return 1
    original = TARGET.read_text()
    legs: dict[str, list[dict]] = {}
    try:
        for leg, mutations, tests in (
            (
                "output-check",
                {"output-check"},
                [
                    ("cli_linux_tls", ["cargo", "test", "-p", "trust-cg-cli", "--test", "link_options", *COMMON, "--", "linux_tls::wl_shared_spellings"]),
                    ("e2e_steered", ["cargo", "test", "-p", "trust-cg-codegen", "--test", "e2e_aarch64_elf_tlsie", *COMMON, "--", "local_exec_tls_in_a_linker_steered"]),
                    ("unit_scripted_driver", ["cargo", "test", "-p", "trust-cg-codegen", "--lib", *COMMON, "--", "local_exec_tls_in_a_shared_output_is_refused_after_the_link"]),
                ],
            ),
            (
                "driver-owned",
                {"driver-owned"},
                [
                    ("cli_linux_tls", ["cargo", "test", "-p", "trust-cg-cli", "--test", "link_options", *COMMON, "--", "linux_tls::wl_shared_spellings"]),
                    ("unit_wl_groups", ["cargo", "test", "-p", "trust-cg-codegen", "--lib", *COMMON, "--", "wl_groups_refuse_driver_owned_and_malformed_arguments"]),
                ],
            ),
            ("both", {"output-check", "driver-owned"}, []),
        ):
            TARGET.write_text(mutate(original, mutations))
            (OUT / f"{leg}.patch").write_text(git("diff"))
            records: list[dict] = []
            for name, argv in tests:
                cargo(f"{leg}-{name}", argv, records)
            if leg == "both":
                cargo(f"{leg}-build_cli", ["cargo", "build", "-p", "trust-cg-cli", *COMMON], records)
                repro = RUN / "mutation-repro"
                if repro.exists():
                    shutil.rmtree(repro)
                repro.mkdir()
                for name in ("tls_lib", "tls_user"):
                    shutil.copy(INPUTS / f"{name}.tmbc", repro / f"{name}.tmbc")
                tc = str(WORKTREE / "target/debug/trust-cg")
                probe(f"{leg}-cli-wl-shared", [tc, "-Wl,--shared", "-o", "libtcgb.so", "tls_lib.tmbc"], repro, records)
                probe(f"{leg}-readelf-h-libtcgb.so", ["readelf", "-h", "libtcgb.so"], repro, records)
                probe(f"{leg}-objdump-d-libtcgb.so", ["objdump", "-d", "--disassemble=tcg_cli_tls_bump", "libtcgb.so"], repro, records)
                probe(f"{leg}-cli-user", [tc, "-o", "userB", "-L", ".", "-l", "tcgb", "--rpath", str(repro), "tls_user.tmbc"], repro, records)
                probe(f"{leg}-run-userB", ["./userB"], repro, records)
            legs[leg] = records
            TARGET.write_text(original)
    finally:
        TARGET.write_text(original)
    rebuild: list[dict] = []
    cargo("restored-build_cli", ["cargo", "build", "-p", "trust-cg-cli", *COMMON], rebuild)
    clean = not git("status", "--porcelain", "--untracked-files=all").strip()
    tests_failed = all(
        record["exit"] != 0
        for leg in ("output-check", "driver-owned")
        for record in legs.get(leg, [])
    )
    both = {record["name"]: record["exit"] for record in legs.get("both", [])}
    reproduced = both.get("both-cli-wl-shared") == 0 and both.get("both-run-userB") == 236
    (OUT / "results.json").write_text(
        json.dumps(
            {
                "legs": legs,
                "restored_build": rebuild,
                "every_test_leg_failed": tests_failed,
                "both_reproduces_236": reproduced,
                "restored_clean": clean,
            },
            indent=2,
        )
        + "\n"
    )
    print("every test leg failed:", tests_failed, "both reproduces 236:", reproduced, "restored clean:", clean)
    return 0 if tests_failed and reproduced and clean and rebuild[0]["exit"] == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
