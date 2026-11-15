#!/usr/bin/env python3
"""Focused Trust/Clean source integration and shift model checks; NOT ATTESTED."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bump_trust_ir_pin import resource_fds

ROOT = Path(__file__).resolve().parents[1]
INPUTS = ['formal/lean/Trust/Model/RegisterBits.lean', 'formal/lean/Trust/Model/Encoder.lean', 'formal/lean/Trust/Model/EncoderStep.lean', 'formal/lean/Trust/Model.lean', 'formal/lean/Trust/Model/ShrGolden.lean', 'formal/lean/scripts/ShrChecks.lean', 'crates/trust-cg-codegen/src/x86_64/encode.rs', 'crates/trust-cg-codegen/tests/lean_encode_golden_binding.rs', 'crates/trust-cg-ir/src/lib.rs', 'crates/trust-cg-regalloc/src/lib.rs', 'proofs/abi_clobber_spec.lean', 'proofs/sentinel_decide_spec.lean', 'Cargo.toml', 'Cargo.lock', 'formal/lean/lean-toolchain', 'scripts/check_trust_clean_units.py']


def hashes():
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in INPUTS}


def campaign(out):
    before = hashes()
    commands = [
        ("build", ROOT / "formal/lean", ["lake", "build", "Trust.Model.MovabsGolden", "Trust.Model.EncoderGolden",
            "Trust.Model.ShrGolden", "Trust.Model.EncoderStep", "Trust.MetaTheorem.Vacuity"]),
    ]
    for name in INPUTS[:6]:
        commands.append((Path(name).stem, ROOT / "formal/lean",
            ["lake", "env", "lean", "-DwarningAsError=true", str(Path(name).relative_to("formal/lean"))]))
    commands.append(("backend", ROOT, ["targo", "--unverified", "test", "-p",
        "trust-cg-codegen", "--test", "lean_encode_golden_binding"]))
    steps = []
    for label, cwd, command in commands:
        with (out / (label + ".log")).open("wb") as log:
            child = subprocess.Popen(command, cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                                     start_new_session=True, pass_fds=resource_fds(os.environ))
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
        print(f"TRUST-CLEAN-STEP {label} passed", flush=True)
    marker = "SHR-CHECKS axioms=foundational-only declarations=9 prefixes=16 backend_cases=4096 resident_choices=2 decoder_refusals=9"
    if marker not in (out / "ShrChecks.log").read_text() or before != hashes():
        raise SystemExit("missing audit marker or inputs changed")
    source = ROOT / INPUTS[0]
    wrapper = out / "positive.rs"
    wrapper.write_text('#[path = ' + json.dumps(str(source)) + ']\nclean mod bits;\n'
        'const MASKED: u8 = trust_cg_x86_low3(255);\n'
        'fn main() { assert_eq!(MASKED,7); for r in 0u8..=255 {'
        'assert_eq!(trust_cg_x86_low3(r),r & 7); } println!("CLEAN-BITS calls=256 ctfe=1"); }\n')
    mutant = out / "mutant.lean"
    mutant.write_text(source.read_text().replace('reg &&& 7', 'reg &&& 6', 1))
    negative = out / "negative.rs"
    negative.write_text('#[path = ' + json.dumps(str(mutant)) + ']\nclean mod bits;\nfn main() {}\n')
    for label, wrapper_path, expected in [('native-positive', wrapper, 0), ('native-negative', negative, 1)]:
        command = ['trustc', '-Ztrust-verify=off', '--edition=2024', str(wrapper_path),
                   '-o', str(out / label)]
        child = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                 start_new_session=True, pass_fds=resource_fds(os.environ))
        try:
            output, _ = child.communicate(timeout=120)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid, signal.SIGKILL)
            child.communicate()
            raise SystemExit(label + ' timeout; no credit')
        (out / (label + '.log')).write_bytes(output)
        if child.returncode != expected:
            raise SystemExit(label + ' unexpected exit: ' + str(child.returncode))
        if expected:
            text = output.decode(errors='replace')
            if 'trust_cg_x86_low3_body' not in text or 'Type mismatch' not in text or 'error:' not in text:
                raise SystemExit('negative did not refuse the false body equation')
        else:
            if b'Clean island kernel-checked: 2 declaration' not in output:
                raise SystemExit('missing native proof census')
            runtime = subprocess.check_output([str(out / label)], timeout=30)
            (out / 'native-runtime.log').write_bytes(runtime)
            if b'CLEAN-BITS calls=256 ctfe=1' not in runtime:
                raise SystemExit('missing runtime/CTFE controls')
        steps.append(dict(label=label, command=command, exit_code=child.returncode))
    if before != hashes():
        raise SystemExit('inputs changed during native controls')
    result = dict(status="passed", inputs=before, steps=steps,
                  qualification="partial Clean source port, shift model and byte binding; NOT ATTESTED")
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print("TRUST-CLEAN-UNITS passed; NOT ATTESTED", flush=True)


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
        with tempfile.TemporaryDirectory(prefix="trust-cg-clean-units-") as temporary:
            campaign(Path(temporary))


if __name__ == "__main__":
    main()
