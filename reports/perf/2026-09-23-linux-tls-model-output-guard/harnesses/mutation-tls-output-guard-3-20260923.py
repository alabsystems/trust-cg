#!/usr/bin/env python3
"""Mutation leg for the third L02-P9 repair (run after the clean qualifying run).

One mutation of crates/trust-cg-codegen/src/link_driver.rs: LinkRequest no
longer refuses forwarded values that begin with `@`. The unit test and the
CLI response-file control must fail. The mutated trust-cg replays the review's
reproduction: `--rpath @resp -o preexist tls_lib.tmbc` with `resp` holding a
shared-object redirection makes GNU ld write a local-exec library at the
redirected path, and a user linked against it exits 236, while `preexist`
keeps its bytes.

The file is restored after the leg, trust-cg is rebuilt from the clean source
and compared with the qualifying binary, and the checkout must be clean before
and after.

Usage: mutation-tls-output-guard-3-20260923.py WORKTREE RUN
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
ANCHOR = "        refusals.extend(self.response_file_refusals());\n"
MUTATED = "        let _ = self.response_file_refusals();\n"
RESULT = re.compile(r"^test result: .*$", re.M)
COMMON = ["--locked", "--offline", "-j", "8"]
CLI = ["cargo", "test", "-p", "trust-cg-cli", "--test", "link_options", *COMMON, "--"]
UNIT = ["cargo", "test", "-p", "trust-cg-codegen", "--lib", *COMMON, "--"]
TESTS = [
    ("unit_response_file", UNIT + ["forwarded_values_beginning_with_at_are_refused_as_response_files"]),
    ("cli_response_file", CLI + ["linux_tls::response_files_in_forwarded_values_are_refused_by_name"]),
]


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


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    if git("status", "--porcelain", "--untracked-files=all").strip():
        print("checkout is dirty; refusing to mutate", file=sys.stderr)
        return 1
    qualifying = json.loads((RUN / "records" / "results.json").read_text())["trust_cg_binary_sha256"]
    original = TARGET.read_text()
    records: list[dict] = []
    try:
        assert original.count(ANCHOR) == 1
        TARGET.write_text(original.replace(ANCHOR, MUTATED))
        (OUT / "response-file.patch").write_text(git("diff"))
        for name, argv in TESTS:
            cargo(f"response-file-{name}", argv, records)
        cargo("response-file-build_cli", ["cargo", "build", "-p", "trust-cg-cli", *COMMON], records)
        if records[-1]["exit"] == 0:
            tc = str(WORKTREE / "target/debug/trust-cg")
            repro = RUN / "mutation-repro"
            if repro.exists():
                shutil.rmtree(repro)
            repro.mkdir()
            for name in ("tls_lib", "tls_user"):
                shutil.copy(INPUTS / f"{name}.tmbc", repro / f"{name}.tmbc")
            (repro / "resp").write_text("/x --shared -o libevil.so\n")
            shutil.copy("/bin/true", repro / "preexist")
            state("response-file-state-before", repro, ["preexist", "resp"], records)
            probe("response-file-cli-rpath", [tc, "--rpath", "@resp", "-o", "preexist", "tls_lib.tmbc"], repro, records)
            state("response-file-state-after", repro, ["preexist", "resp"], records)
            probe("response-file-readelf-h-libevil.so", ["readelf", "-h", "libevil.so"], repro, records)
            probe("response-file-objdump-d-libevil.so", ["objdump", "-d", "--disassemble=tcg_cli_tls_bump", "libevil.so"], repro, records)
            probe("response-file-cli-user", [tc, "-o", "userE", "-L", ".", "-l", "evil", "--rpath", str(repro), "tls_user.tmbc"], repro, records)
            probe("response-file-run-userE", ["./userE"], repro, records)
    finally:
        TARGET.write_text(original)
    rebuild: list[dict] = []
    cargo("restored-build_cli", ["cargo", "build", "-p", "trust-cg-cli", *COMMON], rebuild)
    restored_sha = sha256(WORKTREE / "target/debug/trust-cg")
    clean = not git("status", "--porcelain", "--untracked-files=all").strip()
    tests_failed = all(
        record["exit"] != 0 and any(l.startswith("test result: FAILED.") for l in record["test_results"])
        for record in records
        if record["name"] in {f"response-file-{name}" for name, _ in TESTS}
    )
    built = any(r["name"] == "response-file-build_cli" and r["exit"] == 0 for r in records)
    exits = {r["name"]: r.get("exit") for r in records}
    before = next((r["sha256"]["preexist"] for r in records if r["name"] == "response-file-state-before"), None)
    after = next((r["sha256"]["preexist"] for r in records if r["name"] == "response-file-state-after"), None)
    replay = {
        "preexist_untouched": before is not None and before == after,
        "user_exits_236": exits.get("response-file-run-userE") == 236,
    }
    (OUT / "results.json").write_text(
        json.dumps(
            {
                "records": records,
                "restored_build": rebuild,
                "restored_binary_sha256": restored_sha,
                "qualifying_binary_sha256": qualifying,
                "restored_binary_matches_qualifying": restored_sha == qualifying,
                "test_leg_failed": tests_failed and built,
                "replay": replay,
                "restored_clean": clean,
            },
            indent=2,
        )
        + "\n"
    )
    print("test leg failed:", tests_failed and built, "replay:", replay, "restored clean:", clean,
          "binary matches:", restored_sha == qualifying)
    ok = tests_failed and built and all(replay.values()) and clean and rebuild[0]["exit"] == 0
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
