#!/usr/bin/env python3
"""Focused kernel/value-proof checks. Run through build-slot; no compiler attestation."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / "formal/lean"
SOURCES = [
    "Trust/Cert/BitManip.lean", "Trust/Cert/BitManip/ByteCore.lean",
    "Trust/Cert/BitManip/Folds.lean", "scripts/BitManipAudit.lean",
    "scripts/BitManipChecks.lean", "lean-toolchain", "lakefile.lean",
]


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def hashes():
    return {name: hashlib.sha256((FORMAL / name).read_bytes()).hexdigest() for name in SOURCES}


def campaign(out):
    before = hashes()
    records = []
    def run(label, arguments, expected_failure=False):
        start = time.monotonic()
        process = subprocess.Popen(
            arguments, cwd=FORMAL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        try:
            output, _ = process.communicate(timeout=180)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                output, _ = process.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                output, _ = process.communicate()
            (out / (label + ".log")).write_bytes(output)
            raise SystemExit(f"{label} exceeded its bound; no proof credit")
        (out / (label + ".log")).write_bytes(output)
        text = output.decode(errors="replace")
        records.append(dict(label=label, command=arguments, exit_code=process.returncode,
                            wall_s=time.monotonic() - start, expected_failure=expected_failure))
        (out / "steps.json").write_text(json.dumps(records, indent=2) + "\n")
        if expected_failure:
            require(process.returncode == 1 and "decide" in text and "false" in text,
                    f"{label} did not reject its false proposition: {text}")
        else:
            require(process.returncode == 0 and "warning:" not in text,
                    f"{label} failed: {text}")
        print(f"SWAR-PROOF-STEP {label} exit={process.returncode} expected_failure={expected_failure}", flush=True)
        return text
    version = run("version", ["lake", "env", "lean", "-V"]).strip()
    pin = (FORMAL / "lean-toolchain").read_text().strip().rsplit(":v", 1)[-1]
    require(version == pin, f"Lean version {version!r} differs from pin {pin!r}")
    run("build", ["lake", "build", "Trust.Cert.BitManip"])
    for label, name in (("byte-source", SOURCES[1]), ("fold-source", SOURCES[2]), ("value-source", SOURCES[0])):
        run(label, ["lake", "env", "lean", "-DwarningAsError=true", name])
    audit = run("audit", ["lake", "env", "lean", "-DwarningAsError=true", SOURCES[3]])
    match = re.search(r"BITMANIP-AUDIT declarations=([1-9][0-9]*) sorryAx=0 project_axioms=0 native_axioms=0 widths=32,64", audit)
    require(match is not None, "strict axiom audit marker missing")
    checks = run("checks", ["lake", "env", "lean", "-DwarningAsError=true", SOURCES[4]])
    require("BITMANIP-CHECKS bindings=2 boundaries=7 mutations=5 invalid_byte_counts=2" in checks,
            "definition/hostile control census missing")
    negative = {
        "wrong-mask32": "example : Internal.fold32 (Internal.byteCore (2 : BitVec 32) 0x55555554 0x33333333 0x0f0f0f0f) = (2 : BitVec 32).cpop := by decide",
        "wrong-count64": "example : popcnt64Swar 0xffffffffffffffff = 0 := by decide",
    }
    for label, goal in negative.items():
        path = out / (label.replace("-", "_") + ".lean")
        path.write_text("import Trust.Cert.BitManip\nopen Trust.Cert.BitManip\n" + goal + "\n")
        run(label, ["lake", "env", "lean", "-DwarningAsError=true", str(path)], expected_failure=True)
    require(hashes() == before, "proof inputs changed during campaign")
    result = dict(status="passed", lean_version=version, inputs=before, audited_declarations=int(match[1]),
                  bindings=2, boundaries=7, mutations=5, invalid_byte_counts=2,
                  expected_false_proof_refusals=2, steps=records, qualification="value-only; NOT ATTESTED")
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print("SWAR-VALUE-PROOFS " + json.dumps({k: v for k, v in result.items() if k not in ("inputs", "steps")}), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path)
    args = parser.parse_args()
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        require(not any(args.out_dir.iterdir()), "output directory must be empty")
        campaign(args.out_dir.resolve())
    else:
        parent = Path(tempfile.gettempdir()) / ".ubd"
        parent.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="swar-value-", dir=parent) as temporary:
            campaign(Path(temporary))


if __name__ == "__main__":
    main()
