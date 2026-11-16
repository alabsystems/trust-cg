#!/usr/bin/env python3
"""Actual Trust refusal of the complete original trust-debt fixture; no proof grade."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bump_trust_ir_pin import resource_fds

ROOT = Path(__file__).resolve().parents[1]
ORIGINAL = ROOT / "reports/fixtures/ProofIndexedRewriteTrustDebt.lean"
FIXTURE = ROOT / "scripts/fixtures/required_proof_trust_debt.rs"
THEOREM = "ProofIndexedRewriteTrustDebt.step_unsound_trust_debt"
DECLARATIONS = {
    "ProofIndexedRewriteTrustDebt.BV",
    "ProofIndexedRewriteTrustDebt.bvEq",
    "ProofIndexedRewriteTrustDebt.RewriteStep",
    THEOREM,
}
SCOPE = (
    "Complete unchanged original explicit-sorry fixture through actual Trust, paired "
    "with the same complete source changing only the theorem RHS to lhs and sorry to rfl. "
    "Explicitly unverified Rust lane; no valid proof of the original statement, "
    "owning-crate, implementation refinement, native-byte or whole-port claim."
)


def digest(path):
    value = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            value.update(chunk)
    return value.hexdigest()


def positive_accepted(text, code, artifact_exists):
    rows = re.findall(
        r"Clean island kernel-checked: (\d+) declaration\(s\) registered \(([^\n]*)\)",
        text,
    )
    if code != 0 or not artifact_exists or len(rows) != 1 or rows[0][0] != "4":
        return False
    names = [name.strip() for name in rows[0][1].split(",")]
    return len(names) == 4 and set(names) == DECLARATIONS


def debt_refusal(text, code, artifact_exists):
    """Bind the exact theorem to its semantic refusal in one error diagnostic."""
    if code != 101 or artifact_exists:
        return None
    # rustc may wrap Clean's own `error:` header. Source/help echoes and other
    # diagnostics cannot supply the theorem or phase for this error record.
    diagnostics = re.split(
        r"(?m)(?=^(?:error|warning|note|help)(?:\[[^\]\n]+\])?:)", text
    )
    error_prefix = r"error(?:\[[^\]\n]+\])?: (?:error: )?"
    publish_prefix = (
        error_prefix
        + r"(?:Clean island batch has no source-local recovery boundary: error: )?"
    )
    theorem = re.escape(THEOREM)
    for diagnostic in diagnostics:
        if (
            re.match(publish_prefix + r"the publish audit refused this batch; nothing was registered(?:\r?\n|$)", diagnostic)
            and re.search(
                r"(?m)^[ \t]*-[ \t]+`" + theorem
                + r"` reaches the incomplete-proof marker `sorryAx`\.",
                diagnostic,
            )
            and "the Clean island was rejected during resolver checking" in diagnostic
        ):
            return "publish-audit-sorryAx"
        if re.match(
            error_prefix + r"Clean island declaration `" + theorem
            + r"` uses explicit `sorry`; strict islands reject all trust debt(?:\r?\n|$)",
            diagnostic,
        ):
            return "strict-island-explicit-sorry"
    return None


def compile_case(compiler, targo, wrapper, out, label, log_path, crate_name, timeout):
    package = out / (label + "-package")
    package.mkdir()
    manifest = package / "Cargo.toml"
    manifest.write_text(
        "[package]\nname = " + json.dumps(crate_name)
        + "\nversion = \"0.0.0\"\nedition = \"2024\"\n\n"
        + "[[bin]]\nname = " + json.dumps(crate_name)
        + "\npath = " + json.dumps(str(wrapper.resolve()), ensure_ascii=False)
        + "\n\n[workspace]\n"
    )
    target = package / "target"
    artifact = target / "debug" / (crate_name + (".exe" if os.name == "nt" else ""))
    argv = [
        str(targo), "--unverified", "rustc", "--offline",
        "--manifest-path", str(manifest), "--target-dir", str(target),
        "--config", "build.rustc=" + json.dumps(str(compiler)),
        "--config", 'build.rustc-wrapper=""',
        "--config", 'build.rustc-workspace-wrapper=""',
        "--bin", crate_name,
    ]
    environment = dict(os.environ)
    for name in (
        "RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
        "CARGO_BUILD_RUSTC", "CARGO_BUILD_RUSTC_WRAPPER",
        "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "CARGO_TARGET_DIR",
        "CARGO_BUILD_TARGET_DIR", "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS",
        "CARGO_BUILD_RUSTFLAGS",
    ):
        environment.pop(name, None)
    environment["RUSTC"] = str(compiler)
    child = subprocess.Popen(
        argv, cwd=ROOT, env=environment, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, start_new_session=True,
        pass_fds=resource_fds(environment),
    )
    timed_out = False
    try:
        output, _ = child.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(child.pid, signal.SIGKILL)
        output, _ = child.communicate()
    log_path.write_bytes(output)
    return argv, child.returncode, output.decode(errors="replace"), timed_out, artifact


def campaign(compiler, targo, out, timeout):
    out.mkdir(parents=True, exist_ok=True)
    if any(out.iterdir()):
        raise SystemExit("output directory must be empty")
    source = ORIGINAL.read_text()
    needle = "bvEq s.lhs s.rhs := by\n  sorry"
    replacement = "bvEq s.lhs s.lhs := by\n  rfl"
    if source.count(needle) != 1:
        raise SystemExit("original statement/proof population changed; review the control")
    positive_source = out / "reflexive_baseline.lean"
    positive_source.write_text(source.replace(needle, replacement))
    assert positive_source.read_text().replace(replacement, needle) == source
    original_path = '"../../reports/fixtures/ProofIndexedRewriteTrustDebt.lean"'
    fixture = FIXTURE.read_text()
    if fixture.count(original_path) != 1:
        raise SystemExit("required original-source include changed")
    positive_wrapper = out / "reflexive_baseline.rs"
    positive_wrapper.write_text(
        fixture.replace(original_path, json.dumps(str(positive_source), ensure_ascii=False))
    )
    paths = [
        ORIGINAL, FIXTURE, Path(__file__).resolve(),
        ROOT / "scripts/bump_trust_ir_pin.py", ROOT / "scripts/rust_guard_transcript.py",
        compiler, targo, positive_source, positive_wrapper,
    ]
    before = {str(path): digest(path) for path in paths}
    (out / "inputs.before.json").write_text(json.dumps(before, indent=2) + "\n")
    rows = []
    for label, wrapper, accept in [
        ("positive", positive_wrapper, True), ("original-negative", FIXTURE, False),
    ]:
        argv, code, text, timed_out, artifact = compile_case(
            compiler, targo, wrapper, out, label, out / (label + ".log"),
            "proof_debt_" + label.replace("-", "_"), timeout,
        )
        reason = None if accept else debt_refusal(text, code, artifact.exists())
        passed = not timed_out and (
            positive_accepted(text, code, artifact.exists()) if accept else reason is not None
        )
        rows.append(dict(
            label=label, argv=argv, exit_code=code, expected_accept=accept,
            artifact_exists=artifact.exists(), timed_out=timed_out,
            refusal_kind=reason, passed=passed,
        ))
        (out / "commands.json").write_text(json.dumps(rows, indent=2) + "\n")
        if not passed:
            break
    unchanged = all(digest(path) == value for path, value in before.items())
    result = dict(
        scope=SCOPE, compiler=str(compiler), compiler_resolved=str(compiler.resolve()),
        driver=str(targo), driver_resolved=str(targo.resolve()),
        original_sha256=before[str(ORIGINAL)], rows=rows, inputs_unchanged=unchanged,
        success=len(rows) == 2 and all(row["passed"] for row in rows) and unchanged,
    )
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result), flush=True)
    return 0 if result["success"] else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--compiler", default="trustc")
    parser.add_argument("--targo", default="targo")
    parser.add_argument("--timeout", type=float, default=120)
    args = parser.parse_args()
    compiler = shutil.which(args.compiler)
    if compiler is None:
        raise SystemExit("selected Trust compiler is unavailable")
    targo = shutil.which(args.targo)
    if targo is None:
        raise SystemExit("selected Targo driver is unavailable")
    if args.timeout <= 0:
        raise SystemExit("timeout must be positive")
    return campaign(
        Path(os.path.abspath(compiler)), Path(os.path.abspath(targo)),
        args.out_dir.resolve(), args.timeout,
    )


if __name__ == "__main__":
    raise SystemExit(main())
