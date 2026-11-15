#!/usr/bin/env python3
"""Re-run the construct inventory after the L05-P3 disposition correction.

Usage: rerun-inventory-correction-20260923.py REPO OUT

REPO must be a clean checkout. The script records its HEAD, tree and
porcelain status before and after, then runs the construct-inventory gate and
the ARC-op target with the same pinned PATH as the qualifying harness (ambient
TCG_* and TRUST_CG_* variables removed). It writes one capture.json and log
per command, plus a summary of the committed inventory JSON's counts, its
three ARC rows and its no_native_execution list, into OUT (created fresh).
It asserts nothing about the result; the summary records what was observed.
"""

from __future__ import annotations

import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

PACKAGE = ".local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin"
ENV_KEYS = ("PATH", "ARC_OPS_LINUX_RETAIN_DIR", "CARGO_TARGET_DIR", "RUST_MIN_STACK")
ARC = ("Retain", "Release", "IsUnique")


def now() -> str:
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], check=True, capture_output=True,
                          text=True).stdout


def run(name: str, argv: list[str], repo: Path, env: dict, logs: Path) -> dict:
    started = now()
    proc = subprocess.run(argv, cwd=repo, env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, timeout=1800)
    log = logs / f"{name}.log"
    log.write_bytes(proc.stdout)
    capture = {
        "name": name, "argv": argv, "cwd": str(repo),
        "environment": {key: env.get(key) for key in ENV_KEYS},
        "started": started, "finished": now(), "returncode": proc.returncode,
        "log": log.name, "log_sha256": hashlib.sha256(proc.stdout).hexdigest(),
        "log_bytes": len(proc.stdout),
    }
    (logs / f"{name}.capture.json").write_text(json.dumps(capture, indent=2) + "\n")
    return capture


def main() -> int:
    repo, out = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    out.mkdir(parents=True, exist_ok=False)
    logs = out / "commands"
    logs.mkdir()
    source = {"head": git(repo, "rev-parse", "HEAD").strip(),
              "tree": git(repo, "rev-parse", "HEAD^{tree}").strip(),
              "status_before": git(repo, "status", "--porcelain", "--untracked-files=all")}
    home = Path.home()
    env = dict(os.environ)
    env["PATH"] = os.pathsep.join([str(home / PACKAGE), str(home / ".cargo/bin"),
                                   env.get("PATH", "")])
    for key in list(env):
        if key.startswith(("TCG_", "TRUST_CG_")) or key in ENV_KEYS[1:]:
            del env[key]
    cargo = ["cargo", "test", "--locked", "--offline", "-j", "8"]
    captures = [
        run("construct_inventory", cargo + ["-p", "trust-cg-lower", "--test",
            "trust_ir_construct_inventory", "--", "--test-threads=1"], repo, env, logs),
        run("arc_ops_linux", cargo + ["-p", "trust-cg-codegen", "--test",
            "e2e_aarch64_arc_ops_linux", "--", "--test-threads=1"], repo, env, logs),
    ]
    source["status_after"] = git(repo, "status", "--porcelain", "--untracked-files=all")
    (out / "source.json").write_text(json.dumps(source, indent=2) + "\n")
    inventory = json.loads((repo / "reports/fixtures/trust-ir-construct-inventory.json").read_text())
    rows = {row["construct"]: row for row in inventory["rows"] if row["family"] == "Inst"}
    summary = {
        "source": source["head"],
        "commands": {c["name"]: {
            "returncode": c["returncode"],
            "test_results": [line for line in (logs / c["log"]).read_text().splitlines()
                             if line.startswith("test result:")]} for c in captures},
        "inventory_executed_definition": inventory["dispositions"]["executed"],
        "inventory_counts": inventory["counts"],
        "inventory_inst_counts": inventory["families"]["Inst"],
        "no_native_execution_len": len(inventory["no_native_execution"]),
        "arc_rows": {name: {key: rows[name][key] for key in
                            ("disposition", "evidence_file", "evidence_test", "note")}
                     for name in ARC},
        "arc_in_no_native_execution": [f"Inst::{name}" in inventory["no_native_execution"]
                                       for name in ARC],
    }
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
