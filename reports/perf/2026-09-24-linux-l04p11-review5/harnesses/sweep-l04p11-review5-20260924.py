#!/usr/bin/env python3
"""Integration sweep after the fifth review repair: every [[test]] target of
the crates that encode AArch64 code, looking for any compile that relied on the
encoder reading a non-immediate as 0 or on the refused ALU shapes.

Usage: sweep6.py <out-dir>
"""
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path("$HOME/trust-cg/.claude/worktrees/agent-a132798c1f3a4825a")
OUT = Path(sys.argv[1])
OUT.mkdir(parents=True, exist_ok=True)
PKG = "/home/ayates/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin"
ENV = {k: v for k, v in os.environ.items() if not k.startswith(("TCG_", "TRUST_CG_"))}
ENV.update(
    CARGO_TARGET_DIR="/home/ayates/trust-cg-wt/target-l04p11",
    CARGO_PROFILE_DEV_DEBUG="0", CARGO_PROFILE_TEST_DEBUG="0",
    PATH=f"{PKG}:/home/ayates/.cargo/bin:/home/ayates/.local/bin:/usr/local/sbin:/usr/local/bin:"
         "/usr/sbin:/usr/bin:/sbin:/bin",
)
SIGNATURES = [
    "expected an immediate, got",
    "is not credited: the encoder encodes only",
    "with a register third operand",
    "has no immediate shift amount",
]


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True, check=True).stdout.strip()


def now():
    return datetime.now(timezone.utc).isoformat()


record = {"head": git("rev-parse", "HEAD"), "status_before": git("status", "--porcelain", "--untracked-files=all"),
          "started_utc": now(), "crates": {}}
for crate, timeout in [("trust-cg-codegen", 14400), ("trust-cg-cli", 3600), ("trust-cg-llvm-import", 3600),
                       ("trust-cg-test", 3600), ("trust-cg-jit-matrix", 3600)]:
    build = subprocess.run(["cargo", "test", "--locked", "--offline", "-j", "16", "-p", crate, "--test", "*",
                            "--no-run"], cwd=ROOT, env=ENV, capture_output=True, text=True)
    (OUT / f"{crate}.build.log").write_text(build.stdout + build.stderr)
    try:
        run = subprocess.run(["cargo", "test", "--locked", "--offline", "-j", "16", "--no-fail-fast", "-p", crate,
                              "--test", "*", "--", "--test-threads=4"], cwd=ROOT, env=ENV, capture_output=True,
                             text=True, timeout=timeout)
        text, rc = run.stdout + run.stderr, run.returncode
    except subprocess.TimeoutExpired as expired:
        text = (expired.stdout or b"").decode(errors="replace") + (expired.stderr or b"").decode(errors="replace")
        rc = "timeout"
    (OUT / f"{crate}.test.log").write_text(text)
    results = re.findall(r"test result: (\w+)\. (\d+) passed; (\d+) failed", text)
    failed = sorted(set(re.findall(r"^test (\S+) \.\.\. FAILED$", text, re.M)))
    hits = {s: text.count(s) for s in SIGNATURES if s in text}
    record["crates"][crate] = {
        "build_returncode": build.returncode, "test_returncode": rc,
        "passed": sum(int(p) for _, p, _ in results), "failed": sum(int(f) for _, _, f in results),
        "targets": len(results), "failed_tests": failed, "new_refusal_signatures": hits,
    }
    print(crate, record["crates"][crate]["passed"], record["crates"][crate]["failed"], len(failed), hits, flush=True)
record["finished_utc"] = now()
record["status_after"] = git("status", "--porcelain", "--untracked-files=all")
(OUT / "sweep.json").write_text(json.dumps(record, indent=2) + "\n")
print("DONE")
