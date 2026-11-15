#!/usr/bin/env python3
"""Run CG's canonical ByteV1 caller-store replay and semantic mutation controls.

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
    "core_byte_store_replays_all_initial_bytes_and_canonical_word_boundaries",
    "core_byte_store_rejects_forged_fetched_execution_and_complete_terminal_world",
    "core_byte_store_rejects_false_caller_memory_admission_and_access",
    "core_byte_store_retained_proof_binds_inputs_and_decodes_exactly",
    "core_byte_store_replays_last_addressable_byte_and_rejects_wrapping_allocations",
    "core_byte_store_refuses_unsupported_original_modules_and_unbounded_rows",
}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    if output == ROOT or ROOT in output.parents:
        parser.error("--output must be outside the source checkout")
    output.mkdir(parents=True, exist_ok=False)
    # The installed Trust package (scripts/trust_toolchain.py); no stock cargo.
    # Its tests run through scripts/trust_cargo.sh, which keeps the TCG_*
    # export variable below out of trustc's environment (it refuses to run
    # under one) and hands it to the test binary.
    trust_cargo, git = ROOT / "scripts" / "trust_cargo.sh", shutil.which("git")
    try:
        targo = subprocess.check_output(
            [sys.executable, "-B", str(ROOT / "scripts" / "trust_toolchain.py"), "--print", "targo"],
            text=True, timeout=120).strip()
    except (OSError, subprocess.SubprocessError):
        targo = None
    report = {"schema": "trust-cg-core-byte-store-v1", "passed": False,
              "scope": "Store/Return kernel replay for explicit caller rows/address/word, all initial byte maps; no native ABI or publication authority"}
    try:
        if not targo or not git:
            raise RuntimeError("the installed Trust package (targo) and git are required")
        report["source"] = source_provenance(git)
        report["dependency_identity"] = dependency_identity(git)
        problems = dependency_recorder().offline_problems(report["dependency_identity"])
        if problems:
            raise RuntimeError("; ".join(problems))
        report["toolchain"] = subprocess.check_output(
            [targo, "--unverified", "--version", "--verbose"], cwd=ROOT, text=True, timeout=20)
        stripped = [name for name in os.environ if name.startswith(("TCG_", "TRUST_CG_", "AY_"))
                    or name in ("RUSTFLAGS", "RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
                                "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_TARGET")]
        for name in stripped:
            os.environ.pop(name, None)
        proof_dir = output / "proofs"
        proof_dir.mkdir()
        os.environ["TCG_CORE_BYTE_REPLAY_EXPORT"] = str(proof_dir)
        command = [str(trust_cargo), "test", "--locked", "--offline", "--color", "never", "-j", "2",
                   "-p", "trust-cg-verify", "--features", "core-byte-replay", "--test", "core_byte_store", "--", "--nocapture", "--test-threads=1"]
        report["execution"] = run_target(command, output / "replay.log", 1800,
                                         root=ROOT, grace_seconds=0, max_rss_gib=16)
        log = (output / "replay.log").read_text()
        observed = re.findall(r"^test (\S+) \.\.\. ok$", log, re.M)
        if len(observed) != len(TESTS) or set(observed) != TESTS:
            raise RuntimeError("required canonical replay tests missing, duplicated or not successful")
        if report["execution"]["status"] != "pass":
            raise RuntimeError("bounded test invocation failed")
        proofs = sorted(proof_dir.glob("*.dag"))
        if len(proofs) != 10:
            raise RuntimeError("expected ten retained word/address proof terms")
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
