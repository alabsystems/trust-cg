#!/usr/bin/env python3
"""Focused immediate-load model and production-byte checks; NOT ATTESTED."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
INPUTS = [
    "formal/lean/Trust/Model/Encoder.lean",
    "formal/lean/Trust/Model/EncoderStep.lean",
    "formal/lean/Trust/Model/MovabsGolden.lean",
    "formal/lean/scripts/MovabsChecks.lean",
    "formal/lean/Trust/Model/RegisterBits.lean",
    "crates/trust-cg-codegen/tests/lean_encode_golden_binding.rs",
    "formal/lean/lean-toolchain",
    "formal/lean/Trust/Model/EncoderGolden.lean",
    "crates/trust-cg-codegen/src/x86_64/encode.rs",
    "Cargo.toml", "Cargo.lock", "scripts/check_movabs_model.py",
]


def hashes():
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in INPUTS}


def campaign(out):
    before = hashes()
    commands = [
        ("build", ROOT / "formal/lean", ["lake", "build", "Trust.Model.MovabsGolden", "Trust.Model.EncoderGolden",
            "Trust.Model.EncoderStep", "Trust.MetaTheorem.Vacuity"]),
    ]
    for name in INPUTS[:4]:
        commands.append((Path(name).stem, ROOT / "formal/lean",
            ["lake", "env", "lean", "-DwarningAsError=true", str(Path(name).relative_to("formal/lean"))]))
    commands.append(("backend", ROOT, ["targo", "--unverified", "test", "-p",
        "trust-cg-codegen", "--test", "lean_encode_golden_binding"]))
    steps = []
    for label, cwd, command in commands:
        with (out / (label + ".log")).open("wb") as log:
            child = subprocess.Popen(command, cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                                     start_new_session=True)
            try:
                code = child.wait(timeout=600)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGTERM)
                try:
                    child.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGKILL)
                    child.wait()
                raise SystemExit(f"{label} timed out; no check credit")
        steps.append(dict(label=label, command=command, exit_code=code))
        (out / "steps.json").write_text(json.dumps(steps, indent=2) + "\n")
        if code:
            raise SystemExit(f"{label} failed; see {out / (label + '.log')}")
        print(f"MOVABS-STEP {label} passed", flush=True)
    marker = "MOVABS-CHECKS axioms=foundational-only declarations=8 golden_vectors=96 truncated=16 nonwide=16 resident_execution=1"
    if marker not in (out / "MovabsChecks.log").read_text() or before != hashes():
        raise SystemExit("missing audit marker or inputs changed")
    result = dict(status="passed", inputs=before, steps=steps,
                  qualification="model, shared prefix and enumerated byte binding; NOT ATTESTED")
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print("MOVABS-MODEL passed; NOT ATTESTED", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path)
    args = parser.parse_args()
    if args.out_dir:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        if any(args.out_dir.iterdir()):
            raise SystemExit("output directory must be empty")
        campaign(args.out_dir.resolve())
    else:
        with tempfile.TemporaryDirectory(prefix="trust-cg-movabs-") as temporary:
            campaign(Path(temporary))


if __name__ == "__main__":
    main()
