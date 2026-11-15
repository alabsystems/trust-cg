#!/usr/bin/env python3
"""L04-P11 third review repair: qualifying run on Linux AArch64 (2026-09-24).

Runs, from a clean checkout, the tests the third review repair changes, the
earlier rounds' mutation controls whose source spans still exist and seven
new semantic ones, and stages logs under <out-dir>/records:

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
       r3  AddTprelHi12/Lo12 go back to the exclusion;
       s1  an ORR (vector) of two different registers is accepted as a copy;
       s2  ENC-5 accepts any SIMD logical word for a bound 16B bitwise shape;
       s3  the gate's ORR (vector) row stops requiring the lanewise obligation;
       s6  the function verifier credits AddTprelHi12 again;
       s7  the TPREL rows lose their deferred reason;
       t1  NEON AND is credited opcode-wide again (its 8B shape included);
       t2  the three-register bitwise shapes stop requiring Q registers;
       t3  ENC-5 accepts an 8B NOT word for the 16B NOT;
       t4  ENC-5 loses its arm for NEON AND;
       t5  virtual registers are numbered without regard to physical operands;
       t6  ENC-5 reads AND's word as BIC;
       t7  the ENC-5 inventory probe counts every opcode as decoded.
     (s4 and s5 of the second round mutated spans this round replaced; t1 and
     t2 take their place.) The mutants guard their change with
     `std::hint::black_box` or change a pattern, so each compiles under
     `-D warnings` and fails only by its semantics.

Cargo runs with `--locked --offline -j 16`, PATH led by the pinned AY/Clean
package directory, CARGO_TARGET_DIR outside the repository and ambient
`TCG_*`/`TRUST_CG_*` variables removed.

Usage: qualify-l04p11-review3-20260924.py <out-dir>
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
    ("s1-orr-vector-two-sources-accepted-as-copy", "crates/trust-cg-verify/src/aarch64_value_decode_proofs.rs",
     "            if n != m {\n                return Err(out_of_model(\n"
     "                    \"ORR (vector) of two different registers is a bitwise OR, not a copy\",\n",
     "            if n != m && std::hint::black_box(false) {\n                return Err(out_of_model(\n"
     "                    \"ORR (vector) of two different registers is a bitwise OR, not a copy\",\n",
     [("verify_lib", cargo("-p", "trust-cg-verify", "--lib", "--", "orr_vector_binds",
                           "tprel_adds_and_malformed_neon_orr_are_refused")),
      ("value_decode_gate", cargo("-p", "trust-cg-verify", "--test", "aarch64_value_decode_gate", "--",
                                  "per_compile_decode_check_runs_the_value_obligation"))]),
    ("s2-enc5-orr-16b-field-check-accepts-any-logical-word",
     "crates/trust-cg-verify/src/aarch64_value_decode_proofs.rs",
     "        Ok(decoded) if decoded == want => Ok(()),\n",
     "        Ok(decoded) if decoded == want || std::hint::black_box(true) => Ok(()),\n",
     [("verify_lib", cargo("-p", "trust-cg-verify", "--lib", "--", "orr_vector_binds",
                           "neon_bitwise_binds_only_the_16b_shape")),
      ("value_decode_gate", cargo("-p", "trust-cg-verify", "--test", "aarch64_value_decode_gate", "--",
                                  "per_compile_decode_check_runs_the_value_obligation"))]),
    ("s3-gate-orr-row-without-lanewise-obligation", "crates/trust-cg-verify/src/coverage_gate.rs",
     "                    if opcode == AArch64Opcode::NeonOrrV && row.finding.is_none() {\n",
     "                    if opcode == AArch64Opcode::NeonOrrV && row.finding.is_none() && std::hint::black_box(false) {\n",
     [("verify_lib", cargo("-p", "trust-cg-verify", "--lib", "--", "neon_orr_and_tprel_row_tests")),
      ("coverage_gate_tests", cargo("-p", "trust-cg-verify", "--test", "coverage_gate_tests", "--",
                                    "aarch64_decoded_value_rows_are_credited_by_every_form"))]),
    ("s6-verifier-credits-tprel-hi12", "crates/trust-cg-verify/src/function_verifier.rs",
     "            AddTprelHi12 | AddTprelLo12 => None,\n",
     "            AddTprelHi12 => std::hint::black_box(Some((\"add(lsl#12) == tp\", ProofCategory::MachOEmission))),\n"
     "            AddTprelLo12 => None,\n",
     [("verify_lib", cargo("-p", "trust-cg-verify", "--lib", "--", "tprel_adds_and_malformed_neon_orr_are_refused",
                           "neon_orr_and_tprel_row_tests")),
      ("coverage_gate_tests", cargo("-p", "trust-cg-verify", "--test", "coverage_gate_tests", "--",
                                    "aarch64_emittable_coverage_is_honest_under_strict"))]),
    ("s7-tprel-rows-lose-deferred-reason", "crates/trust-cg-verify/src/coverage_gate.rs",
     "        O::AddTprelHi12 | O::AddTprelLo12 => Some(\n",
     "        O::AddTprelHi12 | O::AddTprelLo12 if std::hint::black_box(true) => None,\n"
     "        O::AddTprelHi12 | O::AddTprelLo12 => Some(\n",
     [("verify_lib", cargo("-p", "trust-cg-verify", "--lib", "--", "neon_orr_and_tprel_row_tests")),
      ("coverage_gate_tests", cargo("-p", "trust-cg-verify", "--test", "coverage_gate_tests", "--",
                                    "aarch64_emittable_coverage_is_honest_under_strict"))]),
    ("t1-neon-and-opcode-wide-credit-restored", "crates/trust-cg-verify/src/function_verifier.rs",
     "            NeonAndV | NeonOrrV | NeonEorV | NeonBicV | NeonNotV => None,\n",
     "            NeonAndV => std::hint::black_box(Some((\"andv.16b lanewise-intent\", ProofCategory::NeonLowering))),\n"
     "            NeonOrrV | NeonEorV | NeonBicV | NeonNotV => None,\n",
     [("verify_lib", cargo("-p", "trust-cg-verify", "--lib", "--", "neon_bitwise_8b_shapes_are_refused_like_orr"))]),
    ("t2-bitwise-shapes-without-q-registers", "crates/trust-cg-verify/src/aarch64_value_decode_proofs.rs",
     "            Operand::Fpr { bits: 128, num: d },\n"
     "            Operand::Fpr { bits: 128, num: n },\n"
     "            Operand::Fpr { bits: 128, num: m },\n",
     "            Operand::Fpr { num: d, .. },\n"
     "            Operand::Fpr { num: n, .. },\n"
     "            Operand::Fpr { num: m, .. },\n",
     [("verify_lib", cargo("-p", "trust-cg-verify", "--lib", "--", "neon_bitwise_binds_only_the_16b_shape",
                           "neon_bitwise_8b_shapes_are_refused_like_orr", "tprel_adds_and_malformed_neon_orr"))]),
    ("t3-enc5-not-accepts-8b", "crates/trust-cg-verify/src/aarch64_value_decode_proofs.rs",
     "        return Some(if (q, rn, rd) == (1, u32::from(n), u32::from(d)) {\n",
     "        return Some(if (q | std::hint::black_box(1), rn, rd) == (1, u32::from(n), u32::from(d)) {\n",
     [("verify_lib", cargo("-p", "trust-cg-verify", "--lib", "--", "neon_bitwise_binds_only_the_16b_shape")),
      ("value_decode_gate", cargo("-p", "trust-cg-verify", "--test", "aarch64_value_decode_gate", "--",
                                  "per_compile_decode_check_runs_the_value_obligation"))]),
    ("t4-enc5-loses-the-and-arm", "crates/trust-cg-codegen/src/aarch64/decode_check.rs",
     "            Op::NeonOrrV | Op::NeonAndV | Op::NeonEorV | Op::NeonBicV | Op::NeonNotV => {\n",
     "            Op::NeonOrrV | Op::NeonEorV | Op::NeonBicV | Op::NeonNotV => {\n",
     [("value_decode_gate", cargo("-p", "trust-cg-verify", "--test", "aarch64_value_decode_gate", "--",
                                  "per_compile_decode_check_runs_the_value_obligation")),
      ("coverage_gate_tests", cargo("-p", "trust-cg-verify", "--test", "coverage_gate_tests", "--",
                                    "credited_aarch64_rows_without_an_enc5_arm_are_pinned_and_disclosed"))]),
    ("t5-virtual-registers-numbered-over-physical", "crates/trust-cg-verify/src/aarch64_value_decode_proofs.rs",
     "            MachOperand::PReg(p) => Some((\n",
     "            MachOperand::PReg(p) if std::hint::black_box(false) => Some((\n",
     [("verify_lib", cargo("-p", "trust-cg-verify", "--lib", "--", "virtual_registers_never_alias_physical_operands",
                           "tprel_adds_and_malformed_neon_orr_are_refused"))]),
    ("t6-enc5-reads-and-as-bic", "crates/trust-cg-verify/src/aarch64_value_decode_proofs.rs",
     "        AArch64Opcode::NeonAndV => (0, 0b00),\n",
     "        AArch64Opcode::NeonAndV => (0, std::hint::black_box(0b01)),\n",
     [("verify_lib", cargo("-p", "trust-cg-verify", "--lib", "--", "neon_bitwise_binds_only_the_16b_shape")),
      ("value_decode_gate", cargo("-p", "trust-cg-verify", "--test", "aarch64_value_decode_gate", "--",
                                  "per_compile_decode_check_runs_the_value_obligation"))]),
    ("t7-inventory-probe-counts-everything-decoded", "crates/trust-cg-verify/tests/coverage_gate_tests.rs",
     "                Ok(DecodeCheckOutcome::Allowlisted(reason)) if reason == A64_UNDECODED_FAMILY\n",
     "                Ok(DecodeCheckOutcome::Allowlisted(reason)) if reason == A64_UNDECODED_FAMILY && std::hint::black_box(false)\n",
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
    run("verify_lib_subsets", cargo("-p", "trust-cg-verify", "--lib", "--", "aarch64_value_decode",
                                    "function_verifier::tests", "function_verifier::walk_query",
                                    "coverage_gate", "proof_database", "neon_lowering_proofs::tests"))
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
