#!/usr/bin/env python3
"""Qualify an exact compiler cohort and publish a durable, leased development record.

Run through normal build-slot admission in an isolated clean checkout. The
maintained pin owner and certificate gate remain the authorities. This driver
publishes only to a feature/qualification branch, never main or attest refs.
Logs and JSON stay in a new private directory outside the checkout. A red check
may publish a FAILED narrative, but never its candidate pin changes. The IR
revision must already be published: unpublished certificate-rule candidates use
the pin owner's separate qualification-only staging mode before this driver.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
from datetime import datetime, timezone

import bump_trust_ir_pin as pin
import private_cache
from rust_guard_transcript import validate_exact_rust_test_transcript

POINTER_TESTS = (
    "fsym_trust_ir::tests::pointer_comparison_checks_each_operand_before_its_result_is_used",
    "fsym_trust_ir::tests::pointer_comparison_known_addresses_and_integer_comparisons_remain_clean",
    "fsym_trust_ir::tests::pointer_comparisons_check_both_operand_addresses",
    "fsym_trust_ir::tests::pointer_comparisons_on_tracked_objects_are_unmodeled_and_prune_nothing",
)
# Reviewed libtest inventory for this source epoch, not inferred from output.
# The merged roster adds 18 declarations and removes 2 from that epoch;
# the native 080ac158 inventory lists all 6,357, including these four controls.
POINTER_INVENTORY = 6357
CERTIFICATE_CELLS = {f"{shape} {op}" for shape in ("V16I8", "V8I16", "V4I32", "V2I64")
                     for op in ("Ne", "Sge", "Slt", "Sle", "Ugt", "Uge", "Ult", "Ule")}
SHA = re.compile(r"[0-9a-f]{64}\Z")


class Refusal(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise Refusal(message)


def validate_ref(ref):
    require(isinstance(ref, str) and re.fullmatch(
        r"refs/heads/(?:feat|qualification)/[A-Za-z0-9][A-Za-z0-9._/-]*", ref)
        and ".." not in ref and "//" not in ref and not ref.endswith(("/", ".", ".lock")),
        "publication requires a non-main feature or qualification ref")
    return ref


def validate_report(report, root_revision, ay_revision, ir_version):
    require(isinstance(report, dict), "certificate report is not an object")
    require(report.get("schema") == "trust-cg.x86-icmp-certificates.v2", "unknown certificate schema")
    require(type(report.get("exit")) is int and report["exit"] == 0,
            "certificate gate did not pass")
    require(report.get("findings") == [] and report.get("missing") == [],
            "certificate findings or missing inputs")
    require(report.get("queries") == {"source": "regenerated"}, "queries were not regenerated")
    require(report.get("trust_ir_rev") == root_revision and report.get("ay_rev") == ay_revision,
            "certificate source identities differ from the requested cohort")
    build = report.get("trust_ir_build")
    require(isinstance(build, str)
            and build.startswith(f"{ir_version}+g{root_revision[:12]}."),
            "compiled TrustIR build does not name the requested version and revision")
    for key, count in (("certificate_cells", 32), ("instruction_model_cells", 8), ("fail_closed_cells", 0)):
        require(type(report.get(key)) is int and report[key] == count,
                f"reviewed reader inventory changed: {key}")
    cells = report.get("cells")
    require(isinstance(cells, list) and len(cells) == 32 and all(isinstance(c, dict) for c in cells),
            "certificate cells are incomplete")
    require({c.get("cell") for c in cells} == CERTIFICATE_CELLS, "certificate cell roster changed")
    for cell in cells:
        require(type(cell.get("clean_exit")) is int and cell["clean_exit"] == 0,
                "a cell lacks successful Clean replay")
        require(type(cell.get("proof_bytes")) is int and cell["proof_bytes"] > 0,
                "a cell has no proof")
        require(all(isinstance(cell.get(k), str) and SHA.fullmatch(cell[k])
                    for k in ("proof_sha256", "query_sha256")), "a cell lacks proof/query hashes")
        certificate = cell.get("ay_certificate")
        require(isinstance(certificate, dict) and all(certificate.get(k) == v for k, v in {
            "trust_free": "yes", "foreign_assumes": "no", "unproved_steps": "0",
            "unsat_admission": "strict-proof"}.items()), "a cell lacks strict AY evidence")
    rule = report.get("rule")
    require(isinstance(rule, dict), "certificate rule missing")
    for tool in ("ay", "clean"):
        actual, expected = report.get(tool), rule.get(tool)
        require(isinstance(actual, dict) and isinstance(expected, dict)
                and actual.get("rev") == expected.get("rev")
                and isinstance(actual.get("sha256"), str) and SHA.fullmatch(actual["sha256"]),
                f"{tool} identity does not bind the compiled rule")
    require(report["ay"]["rev"] == ay_revision, "wrong AY tool revision")
    return report


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


def changed(root):
    # Reject renames/copies and exotic names instead of ambiguously parsing them.
    raw = subprocess.check_output(["git", "-C", str(root), "status", "--porcelain=v1",
                                   "--untracked-files=all", "-z"])
    result = set()
    for entry in raw.split(b"\0"):
        if not entry:
            continue
        require(len(entry) > 3 and entry[2:3] == b" " and not any(c in entry[:2] for c in b"RC"),
                "ambiguous Git status entry")
        result.add(entry[3:].decode("utf-8", errors="strict"))
    return result


def check_tree(root, source, receipt=None):
    require(git(root, "rev-parse", "HEAD") == source, "source HEAD changed during qualification")
    require(not git(root, "diff", "--cached", "--name-only"), "Git index changed during qualification")
    allowed = set(pin.OWNED) | ({receipt} if receipt else set())
    require(changed(root) <= allowed, "unreviewed source or untracked files changed")


def run_stage(root, output, name, argv):
    path = output / (name + ".log")
    with os.fdopen(private_cache.create_private_file(path), "wb") as log:
        child = subprocess.Popen(argv, cwd=root, stdout=log, stderr=subprocess.STDOUT,
                                 start_new_session=True)
        try:
            code = child.wait()
        except BaseException:
            try:
                os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
            raise
    require(code == 0, f"{name} exited {code}; private transcript retained")
    return path


def receipt_text(args, passed, phase, logs, report):
    text = ("# Compiler cohort qualification\n\n"
            f"Outcome: **{'PASS' if passed else 'FAILED'}**. Last phase: {phase}.\n\n"
            f"CG input: `{args.source_head}`. TrustIR: `{args.root_revision}` "
            f"(`{args.selected_ir_version}`). Clean packages: `{args.selected_clean_version}`. "
            f"AY: `{args.ay_revision}`.\n\n"
            "This is explicit unverified Rust compilation, named test execution and\n"
            "the canonical external-certificate gate. It is not a compiler, source/native,\n"
            "provider, DDC, release or full-toolchain soundness attestation.\n\n")
    if passed:
        text += ("All eight maintained pin guards passed. Four reviewed pointer controls\n"
                 "executed individually; the complete reader inventory accounts for\n"
                 "32 certificate cells and eight instruction-model cells, with regenerated\n"
                 "queries, no missing inputs and no findings.\n\n")
        for tool in ("ay", "clean"):
            value = report[tool]
            text += f"{tool}: source `{value['rev']}`, observed binary SHA256 `{value['sha256']}`.\n\n"
    else:
        text += "Candidate pin changes are excluded from this failure-record commit.\n\n"
    text += "Payloads stay outside Git under the durable-evidence policy.\n\n| Private artifact | SHA256 |\n|---|---|\n"
    for path in logs:
        text += f"| {path.name} | `{hashlib.sha256(path.read_bytes()).hexdigest()}` |\n"
    return text


def publish(root, output, args, relative, passed):
    validate_ref(args.publication_ref)
    check_tree(root, args.source_head, relative)
    paths = [relative, *(pin.OWNED if passed else ())]
    subprocess.run(["git", "-C", str(root), "add", "--", *paths], check=True)
    staged = set(git(root, "diff", "--cached", "--name-only").splitlines())
    require(relative in staged and staged <= set(paths), "publication index contains unrelated work")
    subprocess.run(["git", "-C", str(root), "commit", "-m",
                    "Record compiler cohort qualification" if passed else
                    "Record failed compiler cohort qualification"], check=True)
    after = git(root, "rev-parse", "HEAD")
    require(git(root, "rev-parse", "HEAD^") == args.source_head, "qualification commit has a different parent")
    committed = set(git(root, "diff", "--name-only", args.source_head, after).splitlines())
    require(relative in committed and committed <= set(paths), "commit contains unrelated work")
    request = output / "publication.json"
    private_cache.write_private_file(request, json.dumps([{
        "ref": args.publication_ref, "before": args.source_head, "after": after}]))
    subprocess.run(["agh", "repo", "push", "alabsystems/trust-cg", str(root),
                    "--input", str(request)], check=True)
    return after


def parse_args(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root_revision")
    parser.add_argument("--ay-revision", required=True)
    parser.add_argument("--ir-version", choices=[pin.IR_VERSION_MIGRATION[1]])
    parser.add_argument("--clean-version", choices=[pin.CLEAN_VERSION_MIGRATION[1]])
    parser.add_argument("--source-head", required=True)
    parser.add_argument("--publication-ref", required=True)
    parser.add_argument("--targo", required=True)
    parser.add_argument("--ay-source", type=Path, required=True)
    parser.add_argument("--clean-source", type=Path, required=True)
    parser.add_argument("--evidence-dir", type=Path, required=True)
    return parser.parse_args(argv)


def pin_owner_command(args):
    command = [sys.executable, "scripts/bump_trust_ir_pin.py", args.root_revision,
               "--ay-revision", args.ay_revision, "--targo", args.targo]
    if args.ir_version is not None:
        command.extend(("--ir-version", args.ir_version))
    if args.clean_version is not None:
        command.extend(("--clean-version", args.clean_version))
    return command


def main(argv=None):
    args = parse_args(argv)
    root = Path(__file__).resolve().parents[1]
    for value in (args.root_revision, args.ay_revision, args.source_head):
        pin.exact_sha(value)
    validate_ref(args.publication_ref)
    args.targo = str(pin.selected_targo(args.targo))
    os.environ["TRUST_TARGO"] = args.targo
    require(git(root, "rev-parse", "HEAD") == args.source_head and not changed(root),
            "qualification needs the exact clean committed source")
    initial_state = pin.current(root, pin.snapshot(root))
    args.selected_ir_version = pin.selected_ir_version(initial_state, args.ir_version)
    args.selected_clean_version = pin.selected_clean_version(initial_state, args.clean_version)
    output = args.evidence_dir
    require(output.is_absolute() and not output.exists(), "evidence directory must be new and absolute")
    require(not output.resolve().is_relative_to(root), "evidence payloads must stay outside the checkout")
    common = Path(git(root, "rev-parse", "--path-format=absolute", "--git-common-dir"))
    require(not output.resolve().is_relative_to(common), "evidence must stay outside the Git database")
    private_cache.create_private_dir_all(output)
    output = Path(private_cache.require_private(output))
    phase, passed, report = "pin-owner", False, None
    try:
        run_stage(root, output, phase, pin_owner_command(args))
        for number, name in enumerate(POINTER_TESTS):
            phase = f"pointer-{number}"
            log = run_stage(root, output, phase, ["scripts/trust_cargo.sh", "test", "--locked",
                            "-p", "trust-cg-verify", "--lib", name, "--", "--exact", "--test-threads=1"])
            validate_exact_rust_test_transcript(log.read_text(), name, POINTER_INVENTORY)
        phase = "certificates"
        path = output / "certificates.json"
        run_stage(root, output, phase, [sys.executable, "scripts/check_x86_icmp_certificates.py",
                  "--ay-source", str(args.ay_source), "--clean-source", str(args.clean_source),
                  "--keep-work", str(output / "work"), "--json-out", str(path)])
        report = validate_report(json.loads(path.read_text()), args.root_revision, args.ay_revision,
                                 args.selected_ir_version)
        state = pin.current(root, pin.snapshot(root))
        require(state.ir == args.root_revision and state.ay == args.ay_revision
                and set(state.ir_packages.values()) == {args.selected_ir_version}
                and set(state.clean_packages.values()) == {args.selected_clean_version},
                "final pin state differs")
        passed = True
    except (Refusal, ValueError, OSError, pin.Refusal) as error:
        print(f"Qualification FAILED at {phase}: {error}", file=sys.stderr)
    check_tree(root, args.source_head)
    stamp = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    relative = f"reports/{stamp}-cohort-{args.source_head[:12]}/README.md"
    destination = root / relative
    require(not destination.exists(), "qualification narrative already exists")
    for parent in destination.parents:
        if parent == root:
            break
        require(not parent.is_symlink(), "symlink in qualification narrative path")
    destination.parent.mkdir(parents=True)
    logs = sorted(output.glob("*.log")) + sorted(output.glob("*.json"))
    destination.write_text(receipt_text(args, passed, phase, logs, report))
    after = publish(root, output, args, relative, passed)
    print(f"Published {'PASS' if passed else 'FAILED'} qualification at {after}")
    return 0 if passed else 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (Refusal, pin.Refusal, OSError, subprocess.CalledProcessError) as error:
        raise SystemExit(f"Qualification publication refused: {error}")
