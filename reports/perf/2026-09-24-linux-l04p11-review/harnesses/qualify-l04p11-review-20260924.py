#!/usr/bin/env python3
"""L04-P11 review round: qualifying run on Linux AArch64 (2026-09-24).

Runs, from a clean checkout, the tests the review round changes and three
mutation controls, and stages logs under <out-dir>/records:

  1. `trust-cg-verify --lib` subsets (decoded-value proofs, function verifier,
     coverage gate, proof database), the five trust-cg-verify gate targets,
     `trust-cg-codegen --lib`, the CLI binary and `emit_proofs_flag` tests,
     the two native L04-P11 targets and `scripts/check_fmt.sh`;
  2. `trust-cg-verify --lib -- --skip ay_bridge` (the whole library minus the
     solver-batch lane, which the first-round record ran in full);
  3. mutation controls, each replacing one exact source span, running the
     named tests (which must FAIL) and restoring the file, with a clean-tree
     check after each:
       r1  the typed zero-source copy `MOVXrr Xd, ZR` loses its form;
       r2  SubsRI goes back to the never-selected exclusion;
       r3  AddTprelHi12/Lo12 go back to the exclusion.

Cargo runs with `--locked --offline -j 16`, PATH led by the pinned AY/Clean
package directory, CARGO_TARGET_DIR outside the repository and ambient
`TCG_*`/`TRUST_CG_*` variables removed.

Usage: qualify-l04p11-review-20260924.py <out-dir>
"""

from __future__ import annotations

import gzip
import hashlib
import json
import os
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(os.environ.get("L04P11_SOURCE_ROOT", "$HOME/trust-cg/.claude/worktrees/agent-a132798c1f3a4825a"))
OUT = Path(sys.argv[1]).resolve()
PACKAGE_BIN = "/home/ayates/.local/lib/trust-cg/09aa977c-ayba60326b-cleand35d6f23/bin"
TARGET_DIR = "/home/ayates/trust-cg-wt/target-l04p11"
RECORDS = OUT / "records"
COMMANDS = RECORDS / "commands"

ENV = {k: v for k, v in os.environ.items() if not k.startswith(("TCG_", "TRUST_CG_"))}
ENV.update(
    CARGO_TARGET_DIR=TARGET_DIR, CARGO_PROFILE_DEV_DEBUG="0", CARGO_PROFILE_TEST_DEBUG="0",
    PATH=f"{PACKAGE_BIN}:/home/ayates/.cargo/bin:/home/ayates/.local/bin:"
    "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
)


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True, check=True).stdout.strip()


def cargo(*args: str) -> list[str]:
    return ["cargo", "test", "--locked", "--offline", "-j", "16", *args]


def run(name: str, argv: list[str], expect: str = "pass") -> int:
    started = now()
    result = subprocess.run(argv, cwd=ROOT, env=ENV, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    data = result.stdout
    text = data.decode("utf-8", errors="replace")
    COMMANDS.mkdir(parents=True, exist_ok=True)
    (COMMANDS / f"{name}.log.gz").write_bytes(gzip.compress(data, mtime=0))
    summary = [line.strip() for line in text.splitlines()
               if line.strip().startswith(("test result:", "switch matrix on ", "indirect calls on ", "check_fmt:"))]
    failed = sorted(line for line in text.splitlines() if line.startswith("test ") and line.endswith("... FAILED"))
    outcome = "pass" if result.returncode == 0 else "fail"
    (COMMANDS / f"{name}.capture.json").write_text(json.dumps({
        "name": name, "argv": argv, "cwd": "<repository root>",
        "environment": {k: ENV[k] for k in ("PATH", "CARGO_TARGET_DIR")},
        "started_utc": started, "finished_utc": now(), "returncode": result.returncode,
        "log": f"{name}.log.gz", "log_sha256": hashlib.sha256(data).hexdigest(),
        "summary": summary, "failed_tests": failed, "expected": expect, "outcome": outcome,
        "as_expected": outcome == expect,
    }, indent=2) + "\n")
    print(f"{name}: rc={result.returncode} expected={expect} {summary[-2:]} {failed[:4]}", flush=True)
    return result.returncode


MUTATIONS = [
    ("r1-typed-zero-source-copy-form-dropped", "crates/trust-cg-verify/src/aarch64_value_decode_proofs.rs",
     "                (64, GprName::Num(_), GprName::Zr) => Some(A64ValueForm::MovXrrFromZr),\n", "",
     [("verify_lib", cargo("-p", "trust-cg-verify", "--lib", "--", "register_copies_bind",
                           "every_decoded_value_opcode", "every_captured_word"))]),
    ("r2-subsri-back-to-never-selected", "crates/trust-cg-verify/src/coverage_gate.rs",
     "        O::SubsRI => EmittableNeedsProof,\n",
     "        O::SubsRI => FailClosedAllowlisted { reason: \"never selected\" },\n",
     [("coverage_gate_tests", cargo("-p", "trust-cg-verify", "--test", "coverage_gate_tests", "--",
                                    "aarch64_emittable_coverage_is_honest_under_strict",
                                    "aarch64_widening_muls_have_their_own_obligations"))]),
    ("r3-tprel-back-to-exclusion", "crates/trust-cg-verify/src/coverage_gate.rs",
     "        O::AddTprelHi12 | O::AddTprelLo12 => EmittableNeedsProof,\n",
     "        O::AddTprelHi12 | O::AddTprelLo12 => FailClosedAllowlisted { reason: \"excluded\" },\n",
     [("coverage_gate_tests", cargo("-p", "trust-cg-verify", "--test", "coverage_gate_tests", "--",
                                    "aarch64_emittable_coverage_is_honest_under_strict"))]),
]


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    RECORDS.mkdir(parents=True, exist_ok=True)
    before = {"head": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}"),
              "status_porcelain": git("status", "--porcelain", "--untracked-files=all")}
    if before["status_porcelain"]:
        print("source is dirty; refusing", file=sys.stderr)
        return 2
    run("verify_lib_subsets", cargo("-p", "trust-cg-verify", "--lib", "--", "aarch64_value_decode",
                                    "function_verifier::tests", "coverage_gate", "proof_database"))
    run("verify_gate_targets", cargo("-p", "trust-cg-verify", "--no-fail-fast", "--test", "coverage_gate_tests",
                                     "--test", "aarch64_value_decode_gate", "--test", "proof_gate_strict",
                                     "--test", "soundness_manifest", "--test", "meta_theorems"))
    run("codegen_lib", cargo("-p", "trust-cg-codegen", "--lib"))
    run("cli", cargo("-p", "trust-cg-cli", "--no-fail-fast", "--bins", "--test", "emit_proofs_flag"))
    run("native_switch_indirect", cargo("-p", "trust-cg-codegen", "--test", "e2e_aarch64_switch", "--test",
                                        "e2e_aarch64_indirect_call", "--", "--show-output", "--test-threads=1"))
    run("check_fmt", ["scripts/check_fmt.sh"])
    run("verify_lib_without_ay_bridge", cargo("-p", "trust-cg-verify", "--lib", "--", "--skip", "ay_bridge"),
        expect="fail")
    results = []
    for name, rel, old, new, commands in MUTATIONS:
        path = ROOT / rel
        original = path.read_text()
        if original.count(old) != 1:
            raise SystemExit(f"{name}: anchor matches {original.count(old)} times")
        path.write_text(original.replace(old, new))
        rows = []
        try:
            for label, argv in commands:
                rc = run(f"{name}--{label}", argv, expect="fail")
                rows.append({"label": label, "returncode": rc, "caught": rc != 0})
        finally:
            path.write_text(original)
        if git("status", "--porcelain", "--untracked-files=all"):
            raise SystemExit(f"{name}: source not restored")
        results.append({"name": name, "file": rel, "old": old, "new": new, "runs": rows})
    (RECORDS / "mutations.json").write_text(json.dumps(results, indent=2) + "\n")
    after = {"head": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}"),
             "status_porcelain": git("status", "--porcelain", "--untracked-files=all")}
    (RECORDS / "source.json").write_text(json.dumps({"before": before, "after": after}, indent=2) + "\n")
    return 0 if before == after else 3


if __name__ == "__main__":
    sys.exit(main())
