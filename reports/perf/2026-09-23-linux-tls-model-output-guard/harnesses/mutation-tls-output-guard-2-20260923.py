#!/usr/bin/env python3
"""Mutation legs for the second L02-P9 repair (run after the clean qualifying run).

Three mutations of crates/trust-cg-codegen/src/link_driver.rs, each applied,
exercised and reverted in turn:

- gnu-model: parse_wl_group stops applying the GNU ld reading of driver-owned
  options (only the exact spellings stay refused). The parser unit test, the
  CLI redirection and --shared-spelling controls and the e2e steered control
  must fail. The mutated trust-cg replays the second review's first
  reproduction: `-Wl,-shar,--outp=libtcgb.so -o preexist` makes GNU ld write
  a local-exec library at libtcgb.so, and a user linked against it exits 236.
- unstaged: the checked link writes, reads and refuses the requested output
  path itself instead of the driver's staging path (the reviewed shape). The
  CLI --version and cc-shim controls, the scripted-driver unit test and the
  e2e steered control must fail. The mutated trust-cg replays `-Wl,--version
  -o keep2.txt` (a false tls-model-mismatch naming keep2.txt) and the cc-shim
  link over an existing file (the file is overwritten by the refused
  library).
- output-check: the staged image is installed without the local-exec check.
  The CLI cc-shim control, the scripted-driver unit test and the e2e steered
  control must fail. The mutated trust-cg links the local-exec library
  through the shim, and a user linked against it exits 236.

The file is restored after every leg, trust-cg is rebuilt from the clean
source at the end and compared with the qualifying binary, and the checkout
must be clean before and after.

Usage: mutation-tls-output-guard-2-20260923.py WORKTREE RUN
"""

from __future__ import annotations

import hashlib
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
PATH = os.pathsep.join(
    [
        str(HOME / ".local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin"),
        str(HOME / ".cargo/bin"),
        os.environ["PATH"],
    ]
)
ENV = dict(os.environ, PATH=PATH)
TARGET = WORKTREE / "crates/trust-cg-codegen/src/link_driver.rs"
MUTATIONS = {
    "gnu-model": (
        "        if !darwin && let Some((_, why)) = gnu_ld_driver_owned(piece) {\n",
        "        if false && !darwin && let Some((_, why)) = gnu_ld_driver_owned(piece) {\n",
    ),
    "unstaged": (
        "    let image = stage.image.clone();\n",
        # The stage is still created and removed; only the path changes.
        "    let image = request.output.clone();\n    let _ = stage;\n",
    ),
    "output-check": (
        "    let refused = local_exec_tls_output_refusals_for(request, uses, &image);\n    if !refused.is_empty() {\n",
        "    let refused = local_exec_tls_output_refusals_for(request, uses, &image);\n    if false && !refused.is_empty() {\n",
    ),
}
RESULT = re.compile(r"^test result: .*$", re.M)
COMMON = ["--locked", "--offline", "-j", "8"]
CLI = ["cargo", "test", "-p", "trust-cg-cli", "--test", "link_options", *COMMON, "--"]
UNIT = ["cargo", "test", "-p", "trust-cg-codegen", "--lib", *COMMON, "--"]
E2E = ["cargo", "test", "-p", "trust-cg-codegen", "--test", "e2e_aarch64_elf_tlsie", *COMMON, "--"]
TESTS = {
    "gnu-model": [
        ("unit_wl_groups", UNIT + ["wl_groups_refuse_driver_owned_and_malformed_arguments"]),
        ("cli_redirection", CLI + ["linux_tls::wl_output_redirection_is_refused_by_name"]),
        ("cli_shared_spellings", CLI + ["linux_tls::wl_shared_spellings_cannot_make_a_local_exec_library"]),
        ("e2e_steered", E2E + ["local_exec_tls_in_a_linker_steered"]),
    ],
    "unstaged": [
        ("cli_no_output", CLI + ["linux_tls::a_link_that_writes_no_output_leaves_the_output_file_alone"]),
        ("cli_shim", CLI + ["linux_tls::a_shared_object_the_driver_writes_for_an_executable_is_refused"]),
        ("unit_scripted_driver", UNIT + ["local_exec_tls_in_a_shared_output_is_refused_after_the_link"]),
        ("e2e_steered", E2E + ["local_exec_tls_in_a_linker_steered"]),
    ],
    "output-check": [
        ("cli_shim", CLI + ["linux_tls::a_shared_object_the_driver_writes_for_an_executable_is_refused"]),
        ("unit_scripted_driver", UNIT + ["local_exec_tls_in_a_shared_output_is_refused_after_the_link"]),
        ("e2e_steered", E2E + ["local_exec_tls_in_a_linker_steered"]),
    ],
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(WORKTREE), *args], check=True, capture_output=True, text=True
    ).stdout


def cargo(name: str, argv: list[str], records: list[dict]) -> None:
    completed = subprocess.run(argv, cwd=WORKTREE, env=ENV, capture_output=True, text=True, timeout=1500)
    text = completed.stdout + completed.stderr
    (OUT / f"{name}.log").write_text(f"$ {' '.join(argv)}\n{text}--- exit {completed.returncode} ---\n")
    records.append({"name": name, "exit": completed.returncode, "test_results": RESULT.findall(text)})
    print(name, completed.returncode, RESULT.findall(text), flush=True)


def probe(name: str, argv: list[str], cwd: Path, records: list[dict], env=None) -> None:
    completed = subprocess.run(argv, cwd=cwd, env=env or ENV, capture_output=True, text=True, timeout=300)

    def shown(text: str) -> str:
        return text.replace(str(cwd), "$REPRO").replace(str(RUN), "$RUN")

    (OUT / f"{name}.txt").write_text(
        f"$ {' '.join(shown(a) for a in argv)}\n--- stdout ---\n{shown(completed.stdout)}"
        f"--- stderr ---\n{shown(completed.stderr)}--- exit {completed.returncode} ---\n"
    )
    records.append({"name": name, "argv": [shown(a) for a in argv], "exit": completed.returncode})
    print(name, completed.returncode, flush=True)


def state(name: str, directory: Path, files: list[str], records: list[dict]) -> None:
    listing = sorted(p.name for p in directory.iterdir())
    hashes = {f: (sha256(directory / f) if (directory / f).is_file() else None) for f in files}
    (OUT / f"{name}.txt").write_text(json.dumps({"listing": listing, "sha256": hashes}, indent=2) + "\n")
    records.append({"name": name, "listing": listing, "sha256": hashes})


def repro_dir(leg: str) -> Path:
    repro = RUN / f"mutation-repro-{leg}"
    if repro.exists():
        shutil.rmtree(repro)
    repro.mkdir()
    for name in ("tls_lib", "tls_prog", "tls_user"):
        shutil.copy(INPUTS / f"{name}.tmbc", repro / f"{name}.tmbc")
    return repro


def shim_env() -> dict:
    shim = RUN / "mutation-shim"
    shim.mkdir(exist_ok=True)
    host_cc = shutil.which("cc", path=PATH)
    (shim / "cc").write_text(f"#!/bin/sh\nexec '{host_cc}' -shared \"$@\"\n")
    (shim / "cc").chmod(0o755)
    return dict(ENV, PATH=os.pathsep.join([str(shim), PATH]))


def replay(leg: str, records: list[dict]) -> None:
    tc = str(WORKTREE / "target/debug/trust-cg")
    repro = repro_dir(leg)
    if leg == "gnu-model":
        shutil.copy("/bin/true", repro / "preexist")
        state(f"{leg}-state-before", repro, ["preexist"], records)
        probe(f"{leg}-cli-shar-outp", [tc, "-Wl,-shar,--outp=libtcgb.so", "-o", "preexist", "tls_lib.tmbc"], repro, records)
        state(f"{leg}-state-after", repro, ["preexist", "libtcgb.so"], records)
        probe(f"{leg}-readelf-h-libtcgb.so", ["readelf", "-h", "libtcgb.so"], repro, records)
        probe(f"{leg}-objdump-d-libtcgb.so", ["objdump", "-d", "--disassemble=tcg_cli_tls_bump", "libtcgb.so"], repro, records)
        probe(f"{leg}-cli-user", [tc, "-o", "userB", "-L", ".", "-l", "tcgb", "--rpath", str(repro), "tls_user.tmbc"], repro, records)
        probe(f"{leg}-run-userB", ["./userB"], repro, records)
    elif leg == "unstaged":
        (repro / "keep2.txt").write_text("precious\n")
        (repro / "libtcgshim.so").write_text("precious\n")
        state(f"{leg}-state-before", repro, ["keep2.txt", "libtcgshim.so"], records)
        probe(f"{leg}-cli-version-keep2", [tc, "-Wl,--version", "-o", "keep2.txt", "tls_prog.tmbc"], repro, records)
        probe(f"{leg}-cli-shim-shared-static", [tc, "-o", "libtcgshim.so", "tls_lib.tmbc"], repro, records, env=shim_env())
        state(f"{leg}-state-after", repro, ["keep2.txt", "libtcgshim.so"], records)
        probe(f"{leg}-readelf-h-libtcgshim.so", ["readelf", "-h", "libtcgshim.so"], repro, records)
    else:
        probe(f"{leg}-cli-shim-shared-static", [tc, "-o", "libtcgshim.so", "tls_lib.tmbc"], repro, records, env=shim_env())
        probe(f"{leg}-readelf-h-libtcgshim.so", ["readelf", "-h", "libtcgshim.so"], repro, records)
        probe(f"{leg}-objdump-d-libtcgshim.so", ["objdump", "-d", "--disassemble=tcg_cli_tls_bump", "libtcgshim.so"], repro, records)
        probe(f"{leg}-cli-user", [tc, "-o", "userS", "-L", ".", "-l", "tcgshim", "--rpath", str(repro), "tls_user.tmbc"], repro, records)
        probe(f"{leg}-run-userS", ["./userS"], repro, records)


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    if git("status", "--porcelain", "--untracked-files=all").strip():
        print("checkout is dirty; refusing to mutate", file=sys.stderr)
        return 1
    qualifying = json.loads((RUN / "records" / "results.json").read_text())["trust_cg_binary_sha256"]
    original = TARGET.read_text()
    legs: dict[str, list[dict]] = {}
    try:
        for leg, (anchor, mutated) in MUTATIONS.items():
            assert original.count(anchor) == 1, leg
            TARGET.write_text(original.replace(anchor, mutated))
            (OUT / f"{leg}.patch").write_text(git("diff"))
            records: list[dict] = []
            for name, argv in TESTS[leg]:
                cargo(f"{leg}-{name}", argv, records)
            cargo(f"{leg}-build_cli", ["cargo", "build", "-p", "trust-cg-cli", *COMMON], records)
            if records[-1]["exit"] == 0:
                replay(leg, records)
            legs[leg] = records
            TARGET.write_text(original)
    finally:
        TARGET.write_text(original)
    rebuild: list[dict] = []
    cargo("restored-build_cli", ["cargo", "build", "-p", "trust-cg-cli", *COMMON], rebuild)
    restored_sha = sha256(WORKTREE / "target/debug/trust-cg")
    clean = not git("status", "--porcelain", "--untracked-files=all").strip()
    # A leg counts only when the mutant compiled and its test ran and
    # failed: exit 101 from a compile error is not a failing control.
    tests_failed = all(
        record["exit"] != 0
        and any(line.startswith("test result: FAILED.") for line in record["test_results"])
        for leg, tests in TESTS.items()
        for record in legs.get(leg, [])
        if record["name"] in {f"{leg}-{name}" for name, _ in tests}
    ) and all(
        any(record["name"] == f"{leg}-build_cli" and record["exit"] == 0 for record in legs.get(leg, []))
        for leg in TESTS
    )
    exits = {record["name"]: record.get("exit") for records in legs.values() for record in records}
    replays = {
        "gnu_model_writes_local_exec_library_236": exits.get("gnu-model-run-userB") == 236,
        "unstaged_overwrites_existing_file": next(
            (r["sha256"]["libtcgshim.so"] for r in legs.get("unstaged", []) if r["name"] == "unstaged-state-after"),
            None,
        )
        != next(
            (r["sha256"]["libtcgshim.so"] for r in legs.get("unstaged", []) if r["name"] == "unstaged-state-before"),
            None,
        ),
        "output_check_installs_local_exec_library_236": exits.get("output-check-cli-shim-shared-static") == 0
        and exits.get("output-check-run-userS") == 236,
    }
    (OUT / "results.json").write_text(
        json.dumps(
            {
                "legs": legs,
                "restored_build": rebuild,
                "restored_binary_sha256": restored_sha,
                "qualifying_binary_sha256": qualifying,
                "restored_binary_matches_qualifying": restored_sha == qualifying,
                "every_test_leg_failed": tests_failed,
                "replays": replays,
                "restored_clean": clean,
            },
            indent=2,
        )
        + "\n"
    )
    print("every test leg failed:", tests_failed, "replays:", replays, "restored clean:", clean,
          "binary matches:", restored_sha == qualifying)
    ok = tests_failed and all(replays.values()) and clean and rebuild[0]["exit"] == 0
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
