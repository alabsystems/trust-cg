#!/usr/bin/env python3
"""Qualify actual Trust-emitted ABI classifiers; no whole-program proof claim."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
INPUTS = [
    "proofs/abi_clobber_spec.lean",
    "crates/trust-cg-regalloc/src/call_clobber.rs",
    "crates/trust-cg-regalloc/src/lib.rs",
    "crates/trust-cg-regalloc/tests/abi_clobber_weld.rs",
    "scripts/check_abi_clean_port.py",
]


def hashes():
    return {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in INPUTS}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, required=True)
    parser.add_argument("--expect-commit", required=True)
    parser.add_argument("--trust-source", type=Path, required=True,
                        help="matching clean Trust source for its maintained native custody owner")
    parser.add_argument("--out-dir", type=Path, required=True)
    args = parser.parse_args()
    if not args.compiler.is_absolute():
        parser.error("--compiler must name the actual compiler by absolute path")
    if len(args.expect_commit) != 40 or any(
            c not in "0123456789abcdef" for c in args.expect_commit):
        parser.error("--expect-commit must be a full source commit")
    out = args.out_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    if any(out.iterdir()):
        parser.error("output directory must be empty; preserve earlier evidence")
    before = hashes()
    steps = []
    trust_source = args.trust_source.resolve(strict=True)
    actual_source = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=trust_source, text=True).strip()
    if actual_source != args.expect_commit:
        raise SystemExit("custody source does not match the expected compiler commit")
    helper_paths = ["scripts/lib/native_serial.py", "scripts/lib/landing_targo.py"]
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--", *helper_paths],
                   cwd=trust_source, check=True)
    sys.path.insert(0, str(trust_source / "scripts/lib"))
    import native_serial
    env = dict(os.environ)
    executor = native_serial.managed_serial_executor(env)
    custody_inputs = {name: hashlib.sha256((trust_source / name).read_bytes()).hexdigest()
                     for name in helper_paths}

    def run(label, command, expected=0, marker=None):
        actual = [str(executor), "--", *map(str, command)]
        result = native_serial.run_custodied_command(
            actual, env=env, cwd=ROOT, timeout=120)
        code = result.returncode
        with (out / (label + ".log")).open("x") as log:
            log.write(result.stdout)
            log.write(result.stderr)
        text = (out / (label + ".log")).read_text(errors="replace")
        steps.append(dict(label=label, command=actual, exit=code))
        (out / "steps.json").write_text(json.dumps(steps, indent=2) + "\n")
        if code != expected or (marker is not None and marker not in text):
            raise SystemExit(f"{label} failed qualification; see {out / (label + '.log')}")
        return text

    identity = run("compiler-version", [args.compiler, "-vV"])
    if "\ntrust: " not in identity or (
            f"\ncommit-hash: {args.expect_commit}\n" not in identity):
        raise SystemExit("compiler is not the expected branded Trust source build")
    sysroot = run("compiler-sysroot", [args.compiler, "--print", "sysroot"]).strip()
    if not Path(sysroot).is_absolute() or not Path(sysroot).is_dir():
        raise SystemExit("compiler did not supply its actual sysroot")
    proof = ROOT / INPUTS[0]
    native = out / "native.rs"
    native.write_text("#[path = " + json.dumps(str(proof)) + "]\nclean mod abi;\n" + """
const G: u8 = trust_cg_aarch64_gpr_callee(29);
const F: u8 = trust_cg_aarch64_fpr_callee(8);
fn main() {
    assert_eq!((G, F), (1, 1));
    for reg in 0u8..=255 {
        assert_eq!(trust_cg_aarch64_gpr_callee(reg), u8::from((19..30).contains(&reg)));
        assert_eq!(trust_cg_aarch64_fpr_callee(reg), u8::from((8..16).contains(&reg)));
    }
    println!("ABI-CLEAN native=512 ctfe=2");
}
""")
    common = [args.compiler, "--sysroot", sysroot, "--edition=2024", "-Ztrust-verify=off"]
    for level in [0, 2]:
        binary = out / f"native-o{level}"
        run(f"compile-o{level}", common + [f"-Copt-level={level}", native, "-o", binary],
            marker="Clean island kernel-checked: 54 declaration")
        run(f"runtime-o{level}", [binary], marker="ABI-CLEAN native=512 ctfe=2")
    source = proof.read_text()
    for name, original, changed in [
            ("gpr", "reg < 30", "reg < 29"),
            ("fpr", "reg < 16", "reg < 15")]:
        if source.count(original) != 1:
            raise SystemExit(f"{name} mutant does not identify exactly one source boundary")
        mutant = out / f"{name}-mutant.lean"
        mutant.write_text(source.replace(original, changed, 1))
        wrapper = out / f"{name}-mutant.rs"
        wrapper.write_text("#[path = " + json.dumps(str(mutant)) +
                           "]\nclean mod abi;\nfn main() {}\n")
        diagnostic = run(f"{name}-mutant", common + ["--emit=metadata", wrapper,
                         "-o", out / f"{name}-mutant.rmeta"], expected=1,
                         marker=f"`{name}_native_callee_agrees` did not elaborate")
        if "type mismatch" not in diagnostic.lower():
            raise SystemExit(f"{name} mutant failed without the required semantic mismatch")
    if before != hashes():
        raise SystemExit("qualification inputs changed during the campaign")
    if custody_inputs != {name: hashlib.sha256((trust_source / name).read_bytes()).hexdigest()
                          for name in helper_paths}:
        raise SystemExit("maintained custody inputs changed during the campaign")
    (out / "result.json").write_text(json.dumps(dict(
        inputs=before, compiler_commit=args.expect_commit, sysroot=sysroot, steps=steps,
        custody_source=str(trust_source), custody_inputs=custody_inputs,
        native_owner=str(executor),
        scope="actual classifier code, CTFE and semantic mutation refusal; allocator checks separate",
        qualification="Rust verification off; NOT ATTESTED"), indent=2) + "\n")
    print("ABI-CLEAN native O0/O2, CTFE and boundary refusals passed; NOT ATTESTED")


if __name__ == "__main__":
    main()
