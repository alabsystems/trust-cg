#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Build reports/perf/2026-09-23-linux-linked-image-binding from one runner output.

Copies the complete runner output directory into records/, gzip-encoding every
file except the proof sidecars (*.cert, proofs/**/*.json) with mtime 0 so the
stored bytes are reproducible. Objects become NAME.o.gz because the repository
ignores *.o. Adds the launch record, logs, the independent readelf/llvm-objdump
cross-check, the runner source and its helpers, and writes inventory.json with
decoded and stored hashes. README.md is written by hand and not listed.

    archive_linked_image_binding.py RUN_DIR SCRATCH ARCHIVE_DIR REPO_ROOT
"""

from __future__ import annotations

import gzip
import hashlib
import json
import shutil
import sys
from pathlib import Path

EXPECTED_SOURCE = "f2a53aadff1b95c8e0e03bf6a63c71cae69f5f11"
BUILD_SOURCE = "450e714b0daecc495f45612393b0dacbb9e9c6d9"
CLI_SHA256 = "b25e467aa61e359f17e77af9613c48e14f26c7610a020a4a1bd8816808d82bfc"
RUNNER_SOURCES = ("check_aarch64_aot_arithmetic.py", "check_linux_aarch64.py", "release_gate_summary.py",
                  "run_with_timeout.py", "dependency_identity.py")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def keep_raw(relative: Path) -> bool:
    return relative.suffix == ".cert" or (relative.suffix == ".json" and "proofs" in relative.parts)


def store(destination: Path, data: bytes, encode: bool, entries: list, root: Path) -> None:
    destination.parent.mkdir(parents=True, exist_ok=True)
    if encode:
        destination = destination.with_name(destination.name + ".gz")
        stored = gzip.compress(data, compresslevel=9, mtime=0)
        destination.write_bytes(stored)
        entries.append({"path": destination.relative_to(root).as_posix(), "sha256": sha(data), "bytes": len(data),
                        "stored_sha256": sha(stored), "stored_bytes": len(stored)})
    else:
        destination.write_bytes(data)
        entries.append({"path": destination.relative_to(root).as_posix(), "sha256": sha(data), "bytes": len(data)})


def main(argv) -> int:
    run, scratch, archive, repo = (Path(arg) for arg in argv[1:5])
    report = json.loads((run / "report.json").read_text())
    assert report["status"] == "pass" and report["schema"] == "trust-cg-aarch64-aot-arithmetic-v2", report["status"]
    assert report["provenance"]["dirty"] is False and report["provenance"]["source_sha"] == EXPECTED_SOURCE
    assert report["final_source"]["source_fingerprint"] == report["provenance"]["source_fingerprint"]
    assert report["tools"]["trust_cg"]["sha256"] == CLI_SHA256
    assert not archive.exists(), archive
    archive.mkdir(parents=True)
    entries: list = []
    for path in sorted(run.rglob("*")):
        if path.is_symlink():
            raise SystemExit(f"runner output holds a symlink: {path}")
        if not path.is_file():
            continue
        relative = path.relative_to(run)
        store(archive / "records" / relative, path.read_bytes(), not keep_raw(relative), entries, archive)
    launch = {
        "command": [
            "python3", "-B", "scripts/check_aarch64_aot_arithmetic.py", "--trust-cg",
            f"{repo}/target/release/trust-cg", "--require-clean", "--max-rss-gib", "16", "--out", str(run),
        ],
        "cwd": f"{repo} (clean git worktree at {EXPECTED_SOURCE})",
        "environment_overrides": {
            "AY_SOLVER_PATH": "/home/ayates/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/store/ay/current/bin/ay",
            "TCG_EXTERNAL_CLEAN_CHECKER":
                "/home/ayates/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/store/clean/current/bin/clean",
            "PATH_prefix": "/home/ayates/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin:/home/ayates/.cargo/bin",
        },
        "unset": ["RUSTFLAGS", "CARGO_TARGET_DIR"],
        "started_utc": report["started_utc"], "finished_utc": report["finished_utc"],
        "cli_build": {
            "worktree": str(repo),
            "full_build": {
                "head": BUILD_SOURCE, "command": ["cargo", "build", "--release", "--locked", "--offline", "-j", "12",
                                                  "-p", "trust-cg-cli"],
                "log": "records/release-cli-build.log.gz",
                "note": "cold target directory; started before any file of the increment was edited",
            },
            "rebuild_at_run_source": {
                "head": EXPECTED_SOURCE, "status_porcelain_lines": 0,
                "command": ["cargo", "build", "--release", "--locked", "--offline", "-j", "12", "-p", "trust-cg-cli"],
                "log": "records/release-cli-rebuild.log.gz",
                "result": "no-op: the increment changes tests, scripts and documents, no input of the binary",
            },
            "toolchain": "rustc 1.97.1 (8bab26f4f 2026-07-14) via rustup proxies",
            "binary_sha256": CLI_SHA256, "version": "trust-cg 0.6.0",
        },
        "cross_check": {
            "command": ["python3", "-B", "harnesses/crosscheck_linked_images.py", str(run),
                        "records/readelf-crosscheck.json"],
            "output": "records/readelf-crosscheck.json.gz",
            "note": "DEBUGINFOD_URLS is removed from each tool's environment so llvm-objdump makes no network lookup",
        },
        "companion_logs": {
            "records/cli-emit-proofs-flag-test.log.gz": (
                "cargo test --locked --offline -j 8 -p trust-cg-cli --test emit_proofs_flag -- --nocapture "
                "--test-threads=1 (same PATH prefix; no AY/Clean override)"),
            "records/runner-unit-tests.log.gz": "python3 -B -m unittest -v scripts/tests/test_aarch64_aot_arithmetic.py",
            "records/runner-stdout.log.gz": "the runner's own stdout/stderr",
        },
        "concurrent_load": "other agents' Cargo builds on the same host; not controlled",
    }
    store(archive / "records" / "launch.json", (json.dumps(launch, indent=2) + "\n").encode(), False, entries, archive)
    for source, name in (("release-build-1.log", "release-cli-build.log"),
                         ("release-cli-build-2.log", "release-cli-rebuild.log"),
                         ("runner-stdout.log", "runner-stdout.log"),
                         ("readelf-crosscheck.json", "readelf-crosscheck.json"),
                         ("cli-emit-proofs-flag-test.log", "cli-emit-proofs-flag-test.log"),
                         ("runner-unit-tests.log", "runner-unit-tests.log")):
        store(archive / "records" / name, (scratch / source).read_bytes(), True, entries, archive)
    for name in RUNNER_SOURCES:
        store(archive / "runner-source" / name, (repo / "scripts" / name).read_bytes(), True, entries, archive)
    for name in ("crosscheck_linked_images.py", "archive_linked_image_binding.py"):
        store(archive / "harnesses" / name, (scratch / name).read_bytes(), False, entries, archive)
    entries.sort(key=lambda entry: entry["path"])
    (archive / "inventory.json").write_text(json.dumps({"artifacts": entries}, indent=2) + "\n")
    stored = sum(entry.get("stored_bytes", entry["bytes"]) for entry in entries)
    print(f"archived {len(entries)} files, {stored} stored bytes, into {archive}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
