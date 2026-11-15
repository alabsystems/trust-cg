#!/usr/bin/env python3
"""Exercise genuine native compiler custody through the bridge probe helper.

This is unverified metadata-compilation evidence, not bridge/native proof
qualification. Use the regular explicit Trust toolchain selection and gate.
"""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "scripts/tests/fixtures/bridge_probe_custody"
CASES = ("genuine", "missing-gnu", "mismatched-gnu", "malformed-handoff")
SOURCES = (
    Path(__file__).resolve(),
    ROOT / "crates/rustc-codegen-trust-cg/build_support/probe.rs",
    FIXTURE / "Cargo.toml", FIXTURE / "Cargo.lock", FIXTURE / "build.rs",
    FIXTURE / "src/lib.rs",
)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--artifacts", type=Path)
    args = parser.parse_args()
    base = args.artifacts or ROOT / "target/bridge-probe-custody-records"
    base.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix="run-", dir=base)).resolve()
    before = {str(p.relative_to(ROOT)): sha(p) for p in SOURCES}
    command = ["build-slot", "--", "scripts/trust_cargo.sh", "check",
               "--locked", "--offline", "--manifest-path", str(FIXTURE / "Cargo.toml")]
    records = []
    okay = True
    for case in CASES:
        case_dir = directory / case
        case_dir.mkdir()
        environment = dict(os.environ, BRIDGE_PROBE_CUSTODY_CASE=case,
                           BRIDGE_PROBE_CUSTODY_RECORD=str(case_dir))
        start = time.monotonic()
        with (case_dir / "cargo.log").open("wb") as output:
            result = subprocess.run(command, cwd=ROOT, env=environment,
                                    stdout=output, stderr=subprocess.STDOUT)
        log = (case_dir / "cargo.log").read_bytes()
        (case_dir / "cargo.log.gz").write_bytes(gzip.compress(log, mtime=0))
        (case_dir / "cargo.log").unlink()
        receipt = {"case": case, "command": command,
                   "exit_code": result.returncode,
                   "elapsed_seconds": time.monotonic() - start,
                   "log_sha256": hashlib.sha256(log).hexdigest()}
        try:
            actual = json.loads((case_dir / "result.json").read_bytes())
            require(result.returncode == 0, "Cargo did not complete the fixture")
            require(actual["case"] == case, "wrong case record")
            require(actual["parent_native_handoff"] is True and actual["parent_gnu_auth"] is True,
                    "genuine parent transport was not observed")
            require(actual["version_status"] == (0 if case == "genuine" else 75),
                    "wrong compiler exit status")
            require(actual["ordinary_metadata_compile"] == (case == "genuine"),
                    "wrong metadata compilation outcome")
            if case == "genuine":
                require((case_dir / "version.stderr").read_bytes() == b"", "query emitted stderr")
                require((case_dir / "probe_native_custody_consumer.rmeta").stat().st_size > 0,
                        "no fresh metadata retained")
                require(b"genuine-version-and-metadata" in log, "positive marker missing")
            else:
                error = (case_dir / "version.stderr").read_bytes()
                require(b"inherited compiler resource custody unavailable" in error,
                        "not a custody refusal")
                reason = {"missing-gnu": b"native/scoped compiler custody has no inherited GNU scheduler",
                          "mismatched-gnu": b"jobserver handoff does not bind the advertised pool",
                          "malformed-handoff": b"unsupported jobserver handoff advertisement"}[case]
                require(reason in error, "wrong custody refusal reason")
                require(("refused=" + case).encode() in log, "refusal marker missing")
            receipt["passed"] = True
        except (OSError, ValueError, KeyError, AssertionError) as error:
            receipt["passed"] = False
            receipt["failure"] = str(error)
            okay = False
        (case_dir / "command.json").write_text(json.dumps(receipt, indent=2) + "\n")
        records.append(receipt)
    unchanged = before == {str(p.relative_to(ROOT)): sha(p) for p in SOURCES}
    summary = {"source_sha256": before, "source_bookend": unchanged,
               "cases": records, "passed": okay and unchanged,
               "scope": "explicitly unverified ordinary metadata compilation; no native execution"}
    (directory / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"BRIDGE_PROBE_CUSTODY cases={len(records)} passed={sum(r['passed'] for r in records)} "
          f"bookend={unchanged} artifacts={directory}")
    return 0 if summary["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
