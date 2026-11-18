"""Fail-closed qualification and publication controls; no native tools/network."""
import copy
from contextlib import redirect_stderr
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from types import SimpleNamespace
from unittest.mock import patch

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
spec = importlib.util.spec_from_file_location("cohort_qualification", SCRIPTS / "qualify_compiler_cohort.py")
q = importlib.util.module_from_spec(spec)
spec.loader.exec_module(q)
SOURCE, ROOT, AY, CLEAN = (c * 40 for c in "abcd")
RECEIPT = "reports/2026-11-07-cohort-input/README.md"
IR_CURRENT, IR_TARGET = q.pin.IR_VERSION_MIGRATION
CLEAN_CURRENT, CLEAN_TARGET = q.pin.CLEAN_VERSION_MIGRATION


def report(ir_version=IR_TARGET):
    cells = []
    for shape in ("V16I8", "V8I16", "V4I32", "V2I64"):
        for op in ("Ne", "Sge", "Slt", "Sle", "Ugt", "Uge", "Ult", "Ule"):
            cells.append({"cell": f"{shape} {op}", "clean_exit": 0, "proof_bytes": 10,
                          "proof_sha256": "e" * 64, "query_sha256": "f" * 64,
                          "ay_certificate": {"trust_free": "yes", "foreign_assumes": "no",
                                             "unproved_steps": "0", "unsat_admission": "strict-proof"}})
    return {"schema": "trust-cg.x86-icmp-certificates.v2", "exit": 0,
            "findings": [], "missing": [], "queries": {"source": "regenerated"},
            "trust_ir_rev": ROOT, "trust_ir_build": f"{ir_version}+g{ROOT[:12]}.local", "ay_rev": AY,
            "certificate_cells": 32, "instruction_model_cells": 8, "fail_closed_cells": 0,
            "cells": cells, "rule": {"ay": {"rev": AY}, "clean": {"rev": CLEAN}},
            "ay": {"rev": AY, "sha256": "e" * 64, "certifying_bytes": True},
            "clean": {"rev": CLEAN, "sha256": "f" * 64, "certifying_bytes": False}}


class ReportTests(unittest.TestCase):
    def test_complete_source_bound_report_accepts_observed_clean_build(self):
        # Historical byte-list membership is informative, not a source substitution.
        q.validate_report(report(), ROOT, AY, IR_TARGET)

    def test_incomplete_or_unbound_reports_refuse(self):
        mutations = [
            lambda r: r.update(exit=False),
            lambda r: r.update(exit=1),
            lambda r: r.update(findings=[{"code": "proof-hole"}]),
            lambda r: r.update(missing=[{"code": "tool"}]),
            lambda r: r.update(queries={"source": "supplied"}),
            lambda r: r.update(trust_ir_rev=SOURCE),
            lambda r: r.update(trust_ir_build=f"{IR_TARGET}+gwrong.local"),
            lambda r: r.update(trust_ir_build=f"{IR_CURRENT}+g{ROOT[:12]}.local"),
            lambda r: r.update(ay_rev=SOURCE),
            lambda r: r.update(schema="future"),
            lambda r: r.update(certificate_cells=True),
            lambda r: r.update(instruction_model_cells=0),
            lambda r: r.update(fail_closed_cells=1),
            lambda r: r.update(cells=[]),
            lambda r: r["cells"].__setitem__(0, copy.deepcopy(r["cells"][1])),
            lambda r: r["cells"][0].update(clean_exit=False),
            lambda r: r["cells"][0].update(clean_exit=1),
            lambda r: r["cells"][0].update(proof_bytes=0),
            lambda r: r["cells"][0].update(query_sha256="bad"),
            lambda r: r["cells"][0]["ay_certificate"].update(foreign_assumes="yes"),
            lambda r: r["cells"][0]["ay_certificate"].update(unproved_steps="1"),
            lambda r: r["cells"][0]["ay_certificate"].update(unsat_admission="unchecked"),
            lambda r: r["ay"].update(rev=SOURCE),
            lambda r: r["clean"].update(rev=SOURCE),
        ]
        for mutate in mutations:
            with self.subTest(mutate=mutate):
                value = report()
                mutate(value)
                with self.assertRaises(q.Refusal):
                    q.validate_report(value, ROOT, AY, IR_TARGET)

    def test_main_attest_and_unsafe_refs_refuse(self):
        for ref in ("refs/heads/main", "refs/attest/x", "refs/tags/x", "refs/heads/feat/a/../main",
                    "refs/heads/feat/a.lock", "refs/heads/feat/a//b", "refs/heads/feat/a b"):
            with self.subTest(ref=ref), self.assertRaises(q.Refusal):
                q.validate_ref(ref)
        self.assertEqual(q.validate_ref("refs/heads/feat/cohort"), "refs/heads/feat/cohort")

    def test_receipt_names_selected_versions_and_all_eight_guards(self):
        args = SimpleNamespace(source_head=SOURCE, root_revision=ROOT, ay_revision=AY,
                               selected_ir_version=IR_TARGET,
                               selected_clean_version=CLEAN_TARGET)
        text = q.receipt_text(args, True, "certificates", [], report())
        self.assertIn(f"TrustIR: `{ROOT}` (`{IR_TARGET}`)", text)
        self.assertIn(f"Clean packages: `{CLEAN_TARGET}`", text)
        self.assertIn("All eight maintained pin guards passed", text)


class VersionSelectionTests(unittest.TestCase):
    @staticmethod
    def arguments():
        return [ROOT, "--ay-revision", AY, "--source-head", SOURCE,
                "--publication-ref", "refs/heads/qualification/cohort",
                "--targo", "/selected/targo", "--ay-source", "/source/ay",
                "--clean-source", "/source/clean", "--evidence-dir", "/evidence"]

    def test_reviewed_versions_reach_the_canonical_pin_owner(self):
        selections = [(IR_TARGET, CLEAN_TARGET), (IR_TARGET, "0.9.3"),
                      (IR_TARGET, "0.9.4"), ("0.16.0", "0.9.4")]
        for ir_version, clean_version in selections:
            with self.subTest(ir_version=ir_version, clean_version=clean_version):
                args = q.parse_args([*self.arguments(), "--ir-version", ir_version,
                                     "--clean-version", clean_version])
                self.assertEqual(q.pin_owner_command(args), [
                    sys.executable, "scripts/bump_trust_ir_pin.py", ROOT,
                    "--ay-revision", AY, "--targo", "/selected/targo",
                    "--ir-version", ir_version, "--clean-version", clean_version])

    def test_unsupported_versions_refuse_at_the_cli_boundary(self):
        for option, version in (("--ir-version", "0.17.0"),
                                ("--clean-version", "0.9.5")):
            with self.subTest(option=option), redirect_stderr(io.StringIO()), \
                    self.assertRaises(SystemExit) as refused:
                q.parse_args([*self.arguments(), option, version])
            self.assertEqual(refused.exception.code, 2)


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="cohort-publication-")
        self.addCleanup(self.temporary.cleanup)
        self.output = Path(self.temporary.name)
        self.root = self.output / "repo"
        self.args = SimpleNamespace(source_head=SOURCE, publication_ref="refs/heads/feat/cohort")
        self.head, self.staged, self.committed, self.calls = SOURCE, set(), set(), []
        self.dirty = set(q.pin.OWNED) | {RECEIPT}
        self.fail_push = False

    def git(self, root, *args):
        if args == ("rev-parse", "HEAD"):
            return self.head
        if args == ("rev-parse", "HEAD^"):
            return SOURCE
        if args == ("diff", "--cached", "--name-only"):
            return "\n".join(sorted(self.staged))
        if args == ("diff", "--name-only", SOURCE, "e" * 40):
            return "\n".join(sorted(self.committed))
        raise AssertionError(args)

    def mock_run(self, argv, **kwargs):
        self.calls.append(argv)
        if argv[0] == "git" and argv[3] == "add":
            self.staged = set(argv[5:])
        elif argv[0] == "git" and argv[3] == "commit":
            self.head, self.committed = "e" * 40, set(self.staged)
            self.staged.clear()
        elif argv[:3] == ["agh", "repo", "push"]:
            update = json.loads((self.output / "publication.json").read_text())
            self.assertEqual(update, [{"ref": self.args.publication_ref, "before": SOURCE, "after": self.head}])
            if self.fail_push:
                raise subprocess.CalledProcessError(1, argv)
        else:
            raise AssertionError(argv)
        return subprocess.CompletedProcess(argv, 0)

    def invoke(self, passed):
        with patch.object(q, "git", self.git), patch.object(q, "changed", lambda root: self.dirty), \
                patch.object(q.subprocess, "run", self.mock_run):
            return q.publish(self.root, self.output, self.args, RECEIPT, passed)

    def test_success_commits_only_owned_pins_and_narrative_with_exact_lease(self):
        self.invoke(True)
        self.assertEqual(self.committed, set(q.pin.OWNED) | {RECEIPT})
        self.assertEqual(len([c for c in self.calls if c[0] == "agh"]), 1)

    def test_failure_record_never_commits_candidate_pins(self):
        self.invoke(False)
        self.assertEqual(self.committed, {RECEIPT})

    def test_unreviewed_or_staged_source_never_publishes(self):
        for dirty, staged in (({"crates/changed.rs"}, set()), (self.dirty, {"Cargo.toml"})):
            self.dirty, self.staged = dirty, staged
            with self.assertRaises(q.Refusal):
                self.invoke(True)
            self.assertFalse(self.calls)

    def test_head_drift_never_publishes(self):
        self.head = "f" * 40
        with self.assertRaises(q.Refusal):
            self.invoke(True)
        self.assertFalse(self.calls)

    def test_refused_lease_is_not_forced_or_retried(self):
        self.fail_push = True
        with self.assertRaises(subprocess.CalledProcessError):
            self.invoke(True)
        self.assertEqual(len([c for c in self.calls if c[0] == "agh"]), 1)


if __name__ == "__main__":
    unittest.main()
