#!/usr/bin/env python3
"""Run the captured 51-instruction writer through canonical ByteV1 replay.

This opt-in gate uses the real pinned Clean vocabulary. It is not native ABI
qualification or compiler publication authority. Run with the pinned root Rust
toolchain on PATH; output must be outside the checkout to retain source identity.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

from check_linux_aarch64 import dependency_identity, dependency_recorder, run_target, source_provenance

ROOT = Path(__file__).resolve().parents[1]
TESTS = {
    "writer_replays_complete_captured_module",
    "symbolic::writer_replays_all_canonical_input_words",
    "symbolic::caller::writer_replays_arbitrary_caller_memory",
    "writer_rejects_changed_fetched_stores",
    "writer_rejects_false_terminal_world",
    "writer_rejects_invalid_caller_memory",
    "writer_retained_proof_binds_inputs_and_decodes_exactly",
}
REJECTIONS = {
    **{f"store-{index}-value": "kernel audit" for index in range(5)},
    "store-2-address": "kernel audit",
    **{f"terminal-{case}": "kernel audit" for case in (
        "WrongWord", "EraseLastStore", "UnwrittenByte", "Host", "Cursor",
        "DropHistory", "ActiveOwner", "OwnerCounter")},
    **{case: "kernel audit" for case in (
        "inactive-owner", "retired-output", "short-output", "overlapping-output",
        "reused-different-word", "reused-different-address")},
    "trailing-proof-byte": "decode",
    "truncated-proof": "decode",
    "wrapping-output": "reconstruct",
    **{case: "kernel audit" for case in (
        "symbolic-reused-address", "symbolic-changed-store",
        "symbolic-wrong-word-bound", "symbolic-unwritten-byte")},
    **{case: "kernel audit" for case in (
        "caller-WrongAddressBound", "caller-WrongWordBound", "caller-WrongAccess",
        "caller-Host", "caller-UnwrittenByte", "caller-changed-store", "caller-changed-offset",
        "caller-retired-instance", "caller-short-instance")},
}
FIXTURE = "crates/trust-cg-verify/tests/fixtures/output_memory_writer-layout-O1.trust-ir.json"
FIXTURE_SHA256 = "ba3659953f16521ba6fdf241d3fd2414c1330b5bd88f01cc368cd4dfd35d346c"



def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    if output == ROOT or ROOT in output.parents:
        parser.error("--output must be outside the source checkout")
    output.mkdir(parents=True, exist_ok=False)
    cargo, git = shutil.which("cargo"), shutil.which("git")
    report = {"schema": "trust-cg-core-byte-writer-v1", "passed": False,
              "scope": "Captured 51-instruction IR invocation, including arbitrary caller memory/address under actual entry, range and access premises; concrete applications and universal canonical words/initial bytes; no Rust adequacy, native ABI or publication authority"}
    try:
        if not cargo or not git:
            raise RuntimeError("cargo and git are required")
        fixture = (ROOT / FIXTURE).read_bytes()
        digest = hashlib.sha256(fixture).hexdigest()
        if digest != FIXTURE_SHA256:
            raise RuntimeError("writer fixture differs from the retained frontend capture")
        report["fixture"] = {"path": FIXTURE, "sha256": digest, "bytes": len(fixture),
                             "capture_commit": "e976052fd4b1fb7984bca44da218e25392aa47de"}
        report["source"] = source_provenance(git)
        report["dependency_identity"] = dependency_identity(git)
        problems = dependency_recorder().offline_problems(report["dependency_identity"])
        if problems:
            raise RuntimeError("; ".join(problems))
        report["toolchain"] = subprocess.check_output(
            [cargo, "--version", "--verbose"], cwd=ROOT, text=True, timeout=20)
        stripped = [name for name in os.environ if name.startswith(("TCG_", "TRUST_CG_", "AY_"))
                    or name in ("RUSTFLAGS", "RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
                                "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_TARGET")]
        for name in stripped:
            os.environ.pop(name, None)
        proof_dir = output / "proofs"
        proof_dir.mkdir()
        os.environ["TCG_CORE_BYTE_WRITER_EXPORT"] = str(proof_dir)
        command = [cargo, "test", "--locked", "--offline", "--color", "never", "-j", "2",
                   "-p", "trust-cg-verify", "--features", "core-byte-replay", "--test", "core_byte_writer", "--", "--nocapture", "--test-threads=1"]
        report["execution"] = run_target(command, output / "replay.log", 1800,
                                         root=ROOT, grace_seconds=0, max_rss_gib=16)
        log = (output / "replay.log").read_text()
        observed = re.findall(r"^test (\S+) \.\.\. ok$", log, re.M)
        if len(observed) != len(TESTS) or set(observed) != TESTS:
            raise RuntimeError("required canonical replay tests missing, duplicated or not successful")
        if report["execution"]["status"] != "pass":
            raise RuntimeError("bounded test invocation failed")
        proofs = sorted(proof_dir.glob("*.dag"))
        if {path.name for path in proofs} != {"writer-80.dag", "writer-88.dag", "symbolic-writer-80.dag", "symbolic-writer-88.dag", "caller-writer.dag", "caller-80.dag", "caller-18446744073709551576.dag"}:
            raise RuntimeError("expected seven retained whole-writer proof terms")
        rejections = [json.loads(path.read_text()) for path in sorted(proof_dir.glob("reject-*.json"))]
        observed_rejections = {row["label"]: row["stage"] for row in rejections}
        if len(rejections) != len(REJECTIONS) or observed_rejections != REJECTIONS:
            raise RuntimeError("required semantic/input/serialization rejection records missing")
        report["rejections"] = rejections
        report["acceptances"] = [json.loads((proof_dir / f"{prefix}-{address}.json").read_text())
                                  for prefix in ("writer", "symbolic-writer") for address in (80, 88)]
        report["acceptances"].extend(json.loads((proof_dir / f"{name}.json").read_text())
                                     for name in ("caller-writer", "caller-80", "caller-18446744073709551576"))
        report["proofs"] = [{"path": str(path.relative_to(output)), "bytes": path.stat().st_size,
                            "sha256": hashlib.sha256(path.read_bytes()).hexdigest()} for path in proofs]
        report["final_source"] = source_provenance(git)
        report["final_dependency_identity"] = dependency_identity(git)
        problems = dependency_recorder().identity_changes(
            report["dependency_identity"], report["final_dependency_identity"])
        if problems:
            raise RuntimeError("; ".join(problems))
        if report["source"]["source_fingerprint"] != report["final_source"]["source_fingerprint"]:
            raise RuntimeError("source changed during replay")
        report["passed"] = True
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        report["error"] = str(error)
    finally:
        (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"passed": report["passed"], "report": str(output / "report.json"),
                      "error": report.get("error")}))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
