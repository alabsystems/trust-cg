#!/usr/bin/env python3
"""L04-P11 fourth review repair: qualifying run on Linux AArch64 (2026-09-24).

Runs, from a clean checkout, the tests the fourth review repair changes and
four semantic mutation controls, and stages logs under <out-dir>/records:

  1. `trust-cg-verify --lib` subsets (the function verifier, decoded-value
     proofs, coverage gate), the five trust-cg-verify gate targets (the ENC-5
     disclosure test among them), `trust-cg-codegen --lib`, the proof-grade
     codegen targets `jit_fail_closed_proof_policy`,
     `jit_source_bound_arithmetic` and `aarch64_raw_dataflow_boundary`, and
     `scripts/check_fmt.sh`;
  2. mutation controls, each replacing one exact source span behind
     `std::hint::black_box`, running the named tests (which must FAIL) and
     restoring the file, with a clean-tree check after each:
       u1  the register-ALU extra-operand refusal is guarded off;
       u2  ENC-5's ADD/SUB register arm stops decoding the three-register
           shape (the reviewer's Plant C);
       u3  a MOVZ instruction with no operands falls back to the opcode-wide
           query (MOVZWi/MOVZXi become opcode-wide);
       u4  one ENC-5 arm exit's reason text changes.

Cargo runs with `--locked --offline -j 16`, PATH led by the pinned AY/Clean
package directory, CARGO_TARGET_DIR outside the repository and ambient
`TCG_*`/`TRUST_CG_*` variables removed.

Usage: qualify-l04p11-review4-20260924.py <out-dir>
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
    ("u1-register-alu-refusal-guarded-off", "crates/trust-cg-verify/src/function_verifier.rs",
     "    ) && inst.operands.len() > 3)\n",
     "    ) && inst.operands.len() > 3 && std::hint::black_box(false))\n",
     [("verify_lib", cargo("-p", "trust-cg-verify", "--lib", "--", "register_alu_with_an_extra_operand_is_refused")),
      ("coverage_gate_tests", cargo("-p", "trust-cg-verify", "--test", "coverage_gate_tests", "--",
                                    "credited_aarch64_rows_without_an_enc5_arm_are_pinned_and_disclosed"))]),
    ("u2-enc5-add-sub-arm-stops-decoding", "crates/trust-cg-codegen/src/aarch64/decode_check.rs",
     "            Op::AddRR | Op::SubRR => {\n                if intent.operands.len() > 3 {\n",
     "            Op::AddRR | Op::SubRR => {\n                if intent.operands.len() > std::hint::black_box(2) {\n",
     [("coverage_gate_tests", cargo("-p", "trust-cg-verify", "--test", "coverage_gate_tests", "--",
                                    "credited_aarch64_rows_without_an_enc5_arm_are_pinned_and_disclosed"))]),
    ("u3-movz-without-operands-opcode-wide", "crates/trust-cg-verify/src/function_verifier.rs",
     "        if !(min_operands..=max_operands).contains(&inst.operands.len()) {\n            return None;\n",
     "        if !(min_operands..=max_operands).contains(&inst.operands.len()) {\n"
     "            return std::hint::black_box(Self::opcode_to_proof_query(inst.opcode));\n",
     [("coverage_gate_tests", cargo("-p", "trust-cg-verify", "--test", "coverage_gate_tests", "--",
                                    "credited_aarch64_rows_without_an_enc5_arm_are_pinned_and_disclosed"))]),
    ("u4-enc5-arm-exit-reason-changed", "crates/trust-cg-codegen/src/aarch64/decode_check.rs",
     "                        \"a64-slice3: shifted add/sub variant not yet decoded\",\n",
     "                        \"a64-slice3: shifted add/sub variant not decoded\",\n",
     [("coverage_gate_tests", cargo("-p", "trust-cg-verify", "--test", "coverage_gate_tests", "--",
                                    "credited_aarch64_rows_without_an_enc5_arm_are_pinned_and_disclosed"))]),
]


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)
    RECORDS.mkdir(parents=True, exist_ok=True)
    before = {"head": git("rev-parse", "HEAD"), "tree": git("rev-parse", "HEAD^{tree}"),
              "status_porcelain": git("status", "--porcelain", "--untracked-files=all")}
    if before["status_porcelain"]:
        print("source is dirty; refusing", file=sys.stderr)
        return 2
    run("verify_lib_subsets", cargo("-p", "trust-cg-verify", "--lib", "--", "function_verifier::tests",
                                    "function_verifier::walk_query", "aarch64_value_decode", "coverage_gate"))
    run("verify_gate_targets", cargo("-p", "trust-cg-verify", "--no-fail-fast", "--test", "coverage_gate_tests",
                                     "--test", "aarch64_value_decode_gate", "--test", "proof_gate_strict",
                                     "--test", "soundness_manifest", "--test", "meta_theorems"))
    run("codegen_lib", cargo("-p", "trust-cg-codegen", "--lib"))
    run("codegen_proof_grade_targets", cargo("-p", "trust-cg-codegen", "--no-fail-fast",
                                             "--test", "jit_fail_closed_proof_policy",
                                             "--test", "jit_source_bound_arithmetic",
                                             "--test", "aarch64_raw_dataflow_boundary"))
    run("check_fmt", ["scripts/check_fmt.sh"])
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
