#!/usr/bin/env python3
"""Focused Trust/Clean source integration and shift model checks; NOT ATTESTED."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bump_trust_ir_pin import resource_fds

ROOT = Path(__file__).resolve().parents[1]
INPUTS = ['formal/lean/Trust/Model/RegisterBits.lean', 'formal/lean/Trust/Model/Encoder.lean', 'formal/lean/Trust/Model/EncoderStep.lean', 'formal/lean/Trust/Model.lean', 'formal/lean/Trust/Model/ShrGolden.lean', 'formal/lean/scripts/ShrChecks.lean', 'crates/trust-cg-codegen/src/x86_64/encode.rs', 'crates/trust-cg-codegen/src/x86_64/encode_register_bits_tests.rs', 'crates/trust-cg-codegen/tests/lean_encode_golden_binding.rs', 'crates/trust-cg-ir/src/lib.rs', 'crates/trust-cg-regalloc/src/lib.rs', 'proofs/abi_clobber_spec.lean', 'proofs/sentinel_decide_spec.lean', 'Cargo.toml', 'Cargo.lock', 'formal/lean/lean-toolchain', 'scripts/check_trust_clean_units.py']


def hashes():
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in INPUTS}


REGISTER_CONTROLS = (
    'shared_register_bits_cover_every_u8_carrier',
    'shared_register_bits_preserve_all_sib_and_modrm_bytes',
    'shared_extended_flag_covers_every_carrier_and_actual_rex_registers',
    'shared_rex_byte_preserves_every_flag_combination',
)


def require_register_controls(text):
    """An exit-zero filtered Cargo invocation must actually run every caller test."""
    summaries = re.findall(
        r'^test result: (\w+)\. (\d+) passed; (\d+) failed; (\d+) ignored; '
        r'\d+ measured; (\d+) filtered out;', text, re.M)
    if len(summaries) != 1 or summaries[0][:4] != ('ok', '4', '0', '0'):
        raise SystemExit('actual register controls need exactly four passes, no failures/ignores')
    for name in REGISTER_CONTROLS:
        path = 'x86_64::encode::register_bits_tests::' + name
        if not re.search(r'^test ' + re.escape(path) + r' \.\.\. ok$', text, re.M):
            raise SystemExit('missing actual register control: ' + name)
    return dict(required=list(REGISTER_CONTROLS), filtered_out=int(summaries[0][4]))


REGISTER_DECLARATIONS = {
    'trust_cg_x86_low3', 'trust_cg_x86_low3_body',
    'trust_cg_x86_is_extended', 'trust_cg_x86_is_extended_body',
    'trust_cg_x86_rex_byte', 'trust_cg_x86_rex_byte_body',
}


def register_source_accepted(text, code, artifact_exists):
    """Require the complete original unit, with no duplicated or substituted name."""
    rows = re.findall(
        r'Clean island kernel-checked: (\d+) declaration\(s\) registered \(([^\n]*)\)',
        text)
    if code != 0 or not artifact_exists or len(rows) != 1 or rows[0][0] != '6':
        return False
    names = [name.strip() for name in rows[0][1].split(',')]
    return len(names) == 6 and set(names) == REGISTER_DECLARATIONS


def register_body_refused(text, code, artifact_exists, theorem):
    """Bind one exact theorem and its type mismatch to a primary error message."""
    if code != 101 or artifact_exists or theorem not in REGISTER_DECLARATIONS:
        return False
    name = re.escape(theorem)
    header = (
        r'error(?:\[[^\]\n]+\])?: (?:error: )?(?:'
        r'`' + name + r'` did not elaborate: |'
        r'Clean island declaration `' + name
        + r'` (?:failed to elaborate|failed the reference kernel recheck): )')
    for diagnostic in re.split(
            r'(?m)(?=^(?:error|warning|note|help)(?:\[[^\]\n]+\])?:)', text):
        # Exclude locations, rendered source and diagnostic notes/help. A quoted
        # theorem or mismatch in those fields is not this error's reason.
        primary = re.split(
            r'(?m)^\s*(?:-->|\d+\s*\||\||=\s*(?:note|help|warning):)',
            diagnostic, maxsplit=1)[0]
        match = re.match(header, primary)
        if match is None:
            continue
        reason = primary[match.end():]
        if re.search(r'(?i)timeout|timed out|out of memory|resource limit|panicked|internal compiler error', reason):
            continue
        if re.search(r'\bType mismatch(?:\b|:)', reason):
            return True
    return False


def campaign(out):
    before = hashes()
    commands = [
        ("build", ROOT / "formal/lean", ["lake", "build", "Trust.Model.MovabsGolden", "Trust.Model.EncoderGolden",
            "Trust.Model.ShrGolden", "Trust.Model.EncoderStep", "Trust.MetaTheorem.Vacuity"]),
    ]
    for name in INPUTS[:6]:
        commands.append((Path(name).stem, ROOT / "formal/lean",
            ["lake", "env", "lean", "-DwarningAsError=true", str(Path(name).relative_to("formal/lean"))]))
    commands.append(("backend", ROOT, [str(ROOT / "scripts/trust_cargo.sh"), "test", "-p",
        "trust-cg-codegen", "--test", "lean_encode_golden_binding"]))
    commands.append(("actual-register-controls", ROOT,
        [str(ROOT / "scripts/trust_cargo.sh"), "test", "--locked", "-p",
         "trust-cg-codegen", "--lib", "x86_64::encode::register_bits_tests::",
         "--", "--test-threads=1"]))
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
        if label == 'actual-register-controls':
            controls = require_register_controls((out / (label + '.log')).read_text())
            steps[-1]['population'] = controls
            (out / "steps.json").write_text(json.dumps(steps, indent=2) + "\n")
        print(f"TRUST-CLEAN-STEP {label} passed", flush=True)
    marker = "SHR-CHECKS axioms=foundational-only declarations=9 prefixes=16 backend_cases=4096 resident_choices=2 decoder_refusals=9"
    if marker not in (out / "ShrChecks.log").read_text() or before != hashes():
        raise SystemExit("missing audit marker or inputs changed")
    source = ROOT / INPUTS[0]
    wrapper = out / "positive.rs"
    wrapper.write_text('#[path = ' + json.dumps(str(source)) + ']\nclean mod bits;\n'
        'const MASKED: u8 = trust_cg_x86_low3(255);\n'
        'const EXTENDED: bool = trust_cg_x86_is_extended(255) == 1;\n'
        'const REX: u8 = trust_cg_x86_rex_byte(1, 0, 1, 0);\n'
        'fn main() { assert_eq!(MASKED,7); assert!(EXTENDED); assert_eq!(REX,74); '
        'for r in 0u8..=255 { '
        'assert_eq!(trust_cg_x86_low3(r),r % 8); '
        'assert_eq!(trust_cg_x86_is_extended(r) == 1,u16::from(r)/8 != 0); } '
        'for flags in 0u8..16 { '
        'assert_eq!(trust_cg_x86_rex_byte(flags/8, (flags/4)%2, '
        '(flags/2)%2, flags%2),64+flags); } '
        'println!("CLEAN-BITS low3=256 extended=256 rex=16 ctfe=3"); }\n')
    cases = [('native-positive', wrapper, None)]
    for label, original, changed, theorem in [
        ('low3', 'reg &&& 7', 'reg &&& 6', 'trust_cg_x86_low3_body'),
        ('extended', 'reg < 8', 'reg < 9', 'trust_cg_x86_is_extended_body'),
        ('rex-byte', '0x40', '0x41', 'trust_cg_x86_rex_byte_body'),
    ]:
        text = source.read_text()
        if text.count(original) != 2:
            raise SystemExit(label + ' mutation must find the definition and unchanged theorem')
        mutant = out / (label + '-mutant.lean')
        mutant.write_text(text.replace(original, changed, 1))
        negative = out / (label + '-negative.rs')
        negative.write_text('#[path = ' + json.dumps(str(mutant)) + ']\nclean mod bits;\nfn main() {}\n')
        cases.append(('native-negative-' + label, negative, theorem))
    for label, wrapper_path, theorem in cases:
        expected = 101 if theorem else 0
        package_name = 'trust-cg-clean-' + label
        package = out / (label + '-package')
        package.mkdir()
        manifest = package / 'Cargo.toml'
        manifest.write_text(
            '[package]\nname = ' + json.dumps(package_name)
            + '\nversion = "0.0.0"\nedition = "2024"\n\n'
            + '[[bin]]\nname = ' + json.dumps(package_name)
            + '\npath = ' + json.dumps('../' + wrapper_path.name)
            + '\n\n[workspace]\n')
        target = package / 'target'
        artifact = target / 'debug' / (package_name + ('.exe' if os.name == 'nt' else ''))
        command = ['targo', '--unverified', 'rustc', '--offline',
                   '--manifest-path', str(manifest), '--target-dir', str(target),
                   '--bin', package_name]
        child = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                 start_new_session=True, pass_fds=resource_fds(os.environ))
        try:
            output, _ = child.communicate(timeout=120)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid, signal.SIGKILL)
            child.communicate()
            raise SystemExit(label + ' timeout; no credit')
        (out / (label + '.log')).write_bytes(output)
        steps.append(dict(label=label, command=command, exit_code=child.returncode,
                          expected_exit=expected, required_rejection=theorem))
        (out / "steps.json").write_text(json.dumps(steps, indent=2) + "\n")
        if child.returncode != expected:
            raise SystemExit(label + ' unexpected exit: ' + str(child.returncode))
        if expected:
            text = output.decode(errors='replace')
            if not register_body_refused(text, child.returncode, artifact.exists(), theorem):
                raise SystemExit('negative did not refuse the false body equation')
            if artifact.exists():
                raise SystemExit('false body produced a callable artifact')
        else:
            if not register_source_accepted(output.decode(errors='replace'), child.returncode,
                                            artifact.exists()):
                raise SystemExit('missing native proof census')
            runtime = subprocess.check_output([str(artifact)], timeout=30)
            (out / 'native-runtime.log').write_bytes(runtime)
            if b'CLEAN-BITS low3=256 extended=256 rex=16 ctfe=3' not in runtime:
                raise SystemExit('missing runtime/CTFE controls')
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
