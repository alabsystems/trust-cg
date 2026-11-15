#!/usr/bin/env python3
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Copyright 2026 Andrew Yates | License: Apache-2.0
"""Controls for the Linux AArch64 cross-backend ABI runner.

The verdict tests build reports in memory; the orchestration tests drive the
real runner with a stand-in `trustc` that writes Python programs. Neither
compiles Rust, loads a backend or produces ABI evidence: they pin what the
runner accepts, not what trust-cg does.
"""

from __future__ import annotations

import copy
import contextlib
import io
import types
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/check_linux_aarch64_xback.py"
SPEC = importlib.util.spec_from_file_location("linux_aarch64_xback", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)
SHA = hashlib.sha256(b"backend").hexdigest()

# Independent of the runner's tables: shrinking a production pin must not
# shrink these controls with it.
SUITE_CASES = {"abi-xback": 40, "abi-families": 346, "regclass-xback": 9, "sret-xback": 1}
FAMILY_CASES = {
    "integer": 20, "float": 6, "hfa": 23, "hva": 15, "composite": 13, "i128": 6, "sret": 10,
    "byref": 8, "bool": 6, "varargs": 20, "callback": 8, "exhaustion": 12, "spill": 6,
    "overalign": 95, "packed": 16, "union": 16, "enum": 14, "niche": 12, "random": 40,
}


def families_module():
    sys.path.insert(0, str(GATE.FAMILIES.parent))
    try:
        return importlib.import_module("families")
    finally:
        sys.path.pop(0)


def case_names() -> dict[str, list[tuple[str, str]]]:
    """(case, family) per suite: the generators' real case names."""
    return {
        "abi-xback": [(f"seed{seed}", "random-scalar") for seed in range(1, 41)],
        "abi-families": [(case.name, case.family) for case in families_module().cases()],
        "regclass-xback": [(shape, "regclass-xback") for shape in GATE.REGCLASS_SHAPES],
        "sret-xback": [("argty", "sret-xback")],
    }


def synthetic_report(backend_sha256: str = SHA, compiler_path: str = "/fixture/trustc",
                     declines: dict | None = None) -> dict:
    """A complete report in which every cell matched, except `declines`.

    `declines` maps (suite, case, side) -> {"tags", "opt_levels"}; it defaults
    to the runner's committed EXPECTED_DECLINES so the report passes as is.
    """
    declines = GATE.EXPECTED_DECLINES if declines is None else declines
    cells = []
    for suite, names in case_names().items():
        for case, family in names:
            for opt in GATE.OPT_LEVELS:
                for caller, callee in GATE.CELLS:
                    row = {"suite": suite, "unit": "u", "case": case, "family": family, "abi": "C",
                           "sides": "both", "opt": opt, "caller": caller, "callee": callee, "mode": "group",
                           "outcome": "oracle-ok" if (caller, callee) == ("llvm", "llvm") else "match"}
                    for side, backend in (("callee", callee), ("caller", caller)):
                        expected = declines.get((suite, case, side))
                        if backend == "tcg" and expected is not None and opt in expected["opt_levels"]:
                            row["outcome"] = "decline"
                            row["decline"] = {"side": side, "tags": GATE.expected_cell_tags(expected, opt),
                                              "message": "fixture refusal", "functions": []}
                            break
                    cells.append(row)
    return {
        "schema": GATE.SCHEMA, "status": "pass", "selection": None, "errors": [],
        "opt_levels": list(GATE.OPT_LEVELS), "knobs": list(GATE.TCG_KNOBS),
        "base_flags": list(GATE.BASE_FLAGS), "backend": {"sha256": backend_sha256},
        "compiler": {"path": compiler_path}, "cells": cells,
    }


class CompileClassificationTests(unittest.TestCase):
    @staticmethod
    def diagnostic(message: str, level: str = "error") -> str:
        return json.dumps({"$message_type": "diagnostic", "message": message, "level": level,
                           "code": None, "children": []})

    def test_tagged_refusal_is_a_decline_with_its_tags_and_functions(self):
        message = ("[TCG-MIR-UNSUPPORTED] rustc_codegen_trust_cg: cannot compile required function:\n"
                   "  - _RNvCs1_6caller4case: [TCG-ARG-ABI] by-value argument 0 refused")
        stderr = "\n".join([self.diagnostic(message), self.diagnostic("aborting due to 1 previous error")])
        verdict = GATE.classify_compile(1, stderr)
        self.assertEqual(verdict["kind"], "decline")
        self.assertEqual(verdict["tags"], ["[TCG-ARG-ABI]", "[TCG-MIR-UNSUPPORTED]"])
        self.assertTrue(verdict["message"].startswith("[TCG-ARG-ABI] by-value argument 0"))
        self.assertEqual(verdict["functions"], ["_RNvCs1_6caller4case"])

    def test_every_other_failure_is_a_build_failure(self):
        tagged = self.diagnostic("[TCG-ARG-ABI] refused")
        cases = {
            "untagged error": (1, "\n".join([tagged, self.diagnostic("mismatched types")])),
            "compiler panic": (101, tagged + "\nthread 'rustc' panicked at src/lib.rs:1:1"),
            "panic text at exit 1": (1, tagged + "\ninternal compiler error: unexpected"),
            "timeout": (124, tagged),
            "signal": (139, tagged),
            "no error diagnostic": (1, self.diagnostic("only a note", "note")),
            "footer disagrees": (1, "\n".join([tagged, self.diagnostic("aborting due to 2 previous errors")])),
            "malformed json": (1, "{not json"),
        }
        for name, (status, stderr) in cases.items():
            with self.subTest(name):
                self.assertEqual(GATE.classify_compile(status, stderr)["kind"], "build-failure")

    def test_success_is_built(self):
        self.assertEqual(GATE.classify_compile(0, "")["kind"], "built")


class CompareTests(unittest.TestCase):
    CASE = {"name": "c", "expected": "c ret=0000000000000001", "expected_exit": 0}

    def execution(self, stdout="c ret=0000000000000001\n", returncode=0, status="exited", signal=None):
        return {"status": status, "returncode": returncode, "stdout": stdout, "signal": signal}

    def test_oracle_must_print_the_generator_value_and_exit_as_the_fixture_says(self):
        self.assertEqual(GATE.compare(self.CASE, ("llvm", "llvm"), self.execution(), None)["outcome"], "oracle-ok")
        for execution in (self.execution(stdout="c ret=0000000000000002\n"), self.execution(returncode=1),
                          self.execution(status="signal", returncode=-11, signal="SIGSEGV")):
            self.assertEqual(GATE.compare(self.CASE, ("llvm", "llvm"), execution, None)["outcome"],
                             "oracle-failure")

    def test_cross_cells_compare_bytes_and_status_with_the_oracle(self):
        oracle = self.execution()
        self.assertEqual(GATE.compare(self.CASE, ("tcg", "llvm"), self.execution(), oracle)["outcome"], "match")
        self.assertEqual(GATE.compare(self.CASE, ("tcg", "llvm"), self.execution(stdout="x\n"), oracle)["outcome"],
                         "mismatch")
        self.assertEqual(GATE.compare(self.CASE, ("llvm", "tcg"), self.execution(returncode=3), oracle)["outcome"],
                         "mismatch")
        crash = self.execution(status="signal", returncode=-7, signal="SIGBUS")
        self.assertEqual(GATE.compare(self.CASE, ("tcg", "tcg"), crash, oracle)["outcome"], "crash")
        self.assertEqual(GATE.compare(self.CASE, ("tcg", "tcg"), self.execution(status="timeout"), oracle)["outcome"],
                         "crash")
        self.assertEqual(GATE.compare(self.CASE, ("tcg", "llvm"), self.execution(), None)["outcome"], "no-oracle")


class VerdictTests(unittest.TestCase):
    def test_complete_report_passes(self):
        self.assertEqual(GATE.verdict_errors(synthetic_report(), SHA), [])

    def test_pins_match_the_independent_inventory(self):
        self.assertEqual(GATE.SUITE_MIN_CASES, SUITE_CASES)
        self.assertEqual(GATE.FAMILY_MIN_CASES, FAMILY_CASES)
        self.assertEqual(sum(FAMILY_CASES.values()), SUITE_CASES["abi-families"])

    def mutate(self, mutation) -> list[str]:
        report = synthetic_report()
        mutation(report)
        return GATE.verdict_errors(report, SHA)

    def first_cross(self, report, suite="abi-families"):
        return next(row for row in report["cells"]
                    if row["suite"] == suite and row["outcome"] == "match")

    def test_wrong_value_crash_build_failure_and_oracle_failure_each_fail(self):
        def mismatch(report):
            row = self.first_cross(report)
            row.update(outcome="mismatch", reason="exit 1 vs 0")

        def crash(report):
            self.first_cross(report).update(outcome="crash", reason="SIGSEGV")

        def build_failure(report):
            self.first_cross(report).update(outcome="build-failure", failure={"side": "caller"})

        def oracle(report):
            row = next(row for row in report["cells"] if row["outcome"] == "oracle-ok")
            row.update(outcome="oracle-failure", reason="oracle exit 3")

        def no_oracle(report):
            self.first_cross(report).update(outcome="no-oracle")

        for mutation, text in ((mismatch, "WRONG VALUE"), (crash, "CRASH"), (build_failure, "build failure"),
                               (oracle, "oracle-failure"), (no_oracle, "no-oracle")):
            with self.subTest(text):
                errors = self.mutate(mutation)
                self.assertTrue(any(text in error for error in errors), errors)

    def test_outcomes_must_belong_to_their_cell(self):
        def oracle_as_match(report):
            next(row for row in report["cells"] if row["outcome"] == "oracle-ok")["outcome"] = "match"

        def cross_as_oracle(report):
            self.first_cross(report)["outcome"] = "oracle-ok"

        def llvm_decline(report):
            row = next(row for row in report["cells"] if row["outcome"] == "oracle-ok")
            row.update(outcome="decline", decline={"side": "callee", "tags": ["[TCG-ARG-ABI]"], "message": "",
                                                   "functions": []})

        for mutation, text in ((oracle_as_match, "wrong cell"), (cross_as_oracle, "wrong cell"),
                               (llvm_decline, "did not compile")):
            with self.subTest(text=text, mutation=mutation.__name__):
                errors = self.mutate(mutation)
                self.assertTrue(any(text in error for error in errors), errors)

    def test_missing_or_duplicated_cells_fail(self):
        errors = self.mutate(lambda report: report["cells"].pop())
        self.assertTrue(any("missing cell" in error for error in errors), errors)
        errors = self.mutate(lambda report: report["cells"].append(copy.deepcopy(report["cells"][0])))
        self.assertTrue(any("recorded 2 times" in error for error in errors), errors)

    def test_declines_must_equal_the_committed_table(self):
        key = ("abi-families", "int_widths_c", "callee")
        table = {key: {"tags": ["[TCG-ARG-ABI]"], "opt_levels": [0, 1, 2, 3], "reason": "fixture"}}
        report = synthetic_report(declines=table)
        floors = dict.fromkeys(GATE.SUITE_MIN_CROSS_MATCHES, 0)
        with mock.patch.object(GATE, "SUITE_MIN_CROSS_MATCHES", floors):
            with mock.patch.object(GATE, "EXPECTED_DECLINES", {}):
                errors = GATE.verdict_errors(report, SHA)
            self.assertTrue(any("unlisted decline" in error for error in errors), errors)
            with mock.patch.object(GATE, "EXPECTED_DECLINES", table):
                self.assertEqual(GATE.verdict_errors(report, SHA), [])
                errors = GATE.verdict_errors(synthetic_report(declines={}), SHA)
            self.assertTrue(any("stale expected decline" in error for error in errors), errors)
            changed = {key: {**table[key], "opt_levels": [0]}}
            with mock.patch.object(GATE, "EXPECTED_DECLINES", table):
                errors = GATE.verdict_errors(synthetic_report(declines=changed), SHA)
            self.assertTrue(any("changed" in error for error in errors), errors)
            retagged = {key: {**table[key], "tags": ["[TCG-RET-ABI]"]}}
            with mock.patch.object(GATE, "EXPECTED_DECLINES", table):
                errors = GATE.verdict_errors(synthetic_report(declines=retagged), SHA)
            self.assertTrue(any("changed" in error for error in errors), errors)

    def test_committed_declines_name_real_cases_sides_and_tags(self):
        names = {(suite, case) for suite, cases in case_names().items() for case, _ in cases}
        for (suite, case, side), row in GATE.EXPECTED_DECLINES.items():
            with self.subTest(case=case, side=side):
                self.assertIn((suite, case), names)
                self.assertIn(side, ("callee", "caller"))
                self.assertTrue(row["tags"] and all(tag.startswith("[TCG-") for tag in row["tags"]))
                self.assertTrue(set(row["opt_levels"]) <= set(GATE.OPT_LEVELS) and row["opt_levels"])
                self.assertTrue(row["reason"].strip())
                if "level_tags" in row:
                    self.assertEqual(sorted(row["level_tags"]), sorted(row["opt_levels"]))
                    self.assertEqual(sorted({tag for tags in row["level_tags"].values() for tag in tags}),
                                     sorted(row["tags"]))
                    for tags in row["level_tags"].values():
                        self.assertTrue(tags and all(tag.startswith("[TCG-") for tag in tags))

    def test_level_tags_bind_each_level(self):
        key = ("abi-families", "va_f64_c", "callee")
        row = GATE.EXPECTED_DECLINES[key]
        self.assertIn("level_tags", row)
        report = synthetic_report()
        self.assertEqual(GATE.verdict_errors(report, SHA), [])
        # The O0 cell carrying the O2 set is a change, even though the union of
        # the row's tags still holds every tag.
        cell = next(cell for cell in report["cells"] if cell["case"] == "va_f64_c" and cell["opt"] == 0
                    and cell["outcome"] == "decline")
        cell["decline"]["tags"] = GATE.expected_cell_tags(row, 2)
        errors = GATE.verdict_errors(report, SHA)
        self.assertTrue(any("decline tags changed at O0" in error for error in errors), errors)

    def test_shrunken_inventory_fails_even_when_everything_left_matches(self):
        def drop_family_case(report):
            report["cells"] = [row for row in report["cells"] if row["case"] != "hva_ret_v2_c"]

        errors = self.mutate(drop_family_case)
        self.assertTrue(any("family hva" in error for error in errors), errors)
        self.assertTrue(any("suite abi-families ran 345" in error for error in errors), errors)

        def drop_suite(report):
            report["cells"] = [row for row in report["cells"] if row["suite"] != "sret-xback"]

        errors = self.mutate(drop_suite)
        self.assertTrue(any("suite sret-xback did not run" in error for error in errors), errors)

    def test_executed_cross_floor_cannot_be_met_by_declines(self):
        key = ("regclass-xback", "fret", "callee")
        table = {key: {"tags": ["[TCG-RET-ABI]"], "opt_levels": [0, 1, 2, 3], "reason": "fixture"}}
        floors = {**GATE.SUITE_MIN_CROSS_MATCHES, "regclass-xback": 9 * 4 * 3}
        with mock.patch.object(GATE, "EXPECTED_DECLINES", table), \
                mock.patch.object(GATE, "SUITE_MIN_CROSS_MATCHES", floors):
            errors = GATE.verdict_errors(synthetic_report(declines=table), SHA)
        self.assertTrue(any("suite regclass-xback matched 100 executed cross cells" in error for error in errors),
                        errors)

    def test_levels_flags_backend_and_subset_are_bound(self):
        mutations = {
            "O0-O3": lambda report: report.update(opt_levels=[0, 1, 2]),
            "pinned compile flags": lambda report: report.update(knobs=["-Ztrust-ir-cg-args=no-proof-certs"]),
            "qualified backend hash": lambda report: report["backend"].update(sha256="0" * 64),
            "subset run": lambda report: report.update(selection={"suites": ["abi-xback"]}),
            "schema": lambda report: report.update(schema="other"),
        }
        for text, mutation in mutations.items():
            with self.subTest(text):
                errors = self.mutate(mutation)
                self.assertTrue(any(text in error for error in errors), errors)

    def test_decline_rows_list_every_level_and_cell(self):
        key = ("abi-xback", "seed3", "caller")
        table = {key: {"tags": ["[TCG-ARG-ABI]"], "opt_levels": [1, 3], "reason": "fixture"}}
        rows = GATE.decline_rows(GATE.cell_records(synthetic_report(declines=table)))
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["opt_levels"], [1, 3])
        # caller-side declines take the tcg x llvm and tcg x tcg cells at each level
        self.assertEqual(rows[0]["cells"], 4)

    def test_decline_rows_union_the_tags_of_every_level(self):
        key = ("abi-xback", "seed3", "caller")
        table = {key: {"tags": ["[TCG-ARG-ABI]"], "opt_levels": [0, 1, 2, 3], "reason": "fixture"}}
        report = synthetic_report(declines=table)
        late = [row for row in report["cells"] if row["outcome"] == "decline" and row["opt"] == 3]
        for row in late:
            row["decline"]["tags"] = ["[TCG-RET-ABI]"]
        rows = GATE.decline_rows(GATE.cell_records(report))
        self.assertEqual(rows[0]["tags"], ["[TCG-ARG-ABI]", "[TCG-RET-ABI]"])

    def test_a_tag_that_changes_at_one_level_fails(self):
        key = ("abi-families", "int_widths_c", "callee")
        table = {key: {"tags": ["[TCG-ARG-ABI]", "[TCG-MIR-UNSUPPORTED]"], "opt_levels": [0, 1, 2, 3],
                       "reason": "fixture"}}
        report = synthetic_report(declines=table)
        # One declined cell at O2 loses its specific tag: the union over the
        # row is unchanged, the cell is not.
        row = next(row for row in report["cells"] if row["outcome"] == "decline" and row["opt"] == 2)
        row["decline"]["tags"] = ["[TCG-MIR-UNSUPPORTED]"]
        floors = dict.fromkeys(GATE.SUITE_MIN_CROSS_MATCHES, 0)
        with mock.patch.object(GATE, "EXPECTED_DECLINES", table), \
                mock.patch.object(GATE, "SUITE_MIN_CROSS_MATCHES", floors):
            errors = GATE.verdict_errors(report, SHA)
        self.assertTrue(any("decline tags changed at O2" in error for error in errors), errors)


class GroupAttemptTests(unittest.TestCase):
    """A superseded whole-group attempt still executed cells; each is judged."""

    REFUSED, OTHER = "int_widths_c", "int_ret_i8_c"
    TAGS = ["[TCG-ARG-ABI]", "[TCG-MIR-UNSUPPORTED]"]

    def report(self, other_tags: list[str] | None = None) -> tuple[dict, dict]:
        """The unit's matrix rows (per-case) and its superseded group attempt.

        With `other_tags`, the second case's per-case callee also refuses, with
        those tags, and the group attempt's refusal carries both cases' tags,
        as a group compile refusing two functions does.
        """
        table = {("abi-families", self.REFUSED, "callee"): {"tags": self.TAGS, "opt_levels": [0, 1, 2, 3],
                                                             "reason": "fixture"}}
        group_tags = list(self.TAGS)
        if other_tags is not None:
            table[("abi-families", self.OTHER, "callee")] = {"tags": other_tags, "opt_levels": [0, 1, 2, 3],
                                                             "reason": "fixture"}
            group_tags = sorted(set(self.TAGS) | set(other_tags))
        report = synthetic_report(declines=table)
        for row in report["cells"]:
            if row["case"] in (self.REFUSED, self.OTHER):
                row.update(unit="integer_c", mode="per-case")
        attempts = []
        for case in (self.REFUSED, self.OTHER):
            for opt in GATE.OPT_LEVELS:
                for caller, callee in GATE.CELLS:
                    row = {"suite": "abi-families", "unit": "integer_c", "case": case, "family": "integer",
                           "abi": "C", "sides": "both", "opt": opt, "caller": caller, "callee": callee,
                           "mode": "group", "superseded": True}
                    if callee == "tcg":
                        row.update(outcome="decline", decline={"side": "callee", "tags": list(group_tags),
                                                               "message": "fixture", "functions": []})
                    else:
                        row.update(outcome="oracle-ok" if caller == "llvm" else "match",
                                   execution={"status": "exited", "returncode": 0, "stdout": "x\n"})
                    attempts.append({"group_attempt": row})
        report["cells"].extend(attempts)
        return report, table

    def errors(self, mutation=None, other_tags=None, matrix_mutation=None) -> list[str]:
        report, table = self.report(other_tags)
        if mutation is not None:
            mutation(GATE.group_attempt_records(report))
        if matrix_mutation is not None:
            matrix_mutation(GATE.cell_records(report))
        floors = dict.fromkeys(GATE.SUITE_MIN_CROSS_MATCHES, 0)
        with mock.patch.object(GATE, "EXPECTED_DECLINES", table), \
                mock.patch.object(GATE, "SUITE_MIN_CROSS_MATCHES", floors):
            return GATE.verdict_errors(report, SHA)

    def executed(self, rows, case=None):
        return next(row for row in rows if row["outcome"] == "match" and (case is None or row["case"] == case))

    def test_a_reproduced_group_refusal_and_matching_attempt_cells_pass(self):
        self.assertEqual(self.errors(), [])

    def test_every_executed_attempt_cell_is_judged(self):
        def mismatch(rows):
            self.executed(rows, self.OTHER).update(outcome="mismatch", reason="exit 0 vs oracle 0")

        def crash(rows):
            self.executed(rows).update(outcome="crash", reason="SIGSEGV")

        def oracle(rows):
            next(row for row in rows if row["outcome"] == "oracle-ok").update(outcome="oracle-failure",
                                                                              reason="oracle exit 3")

        def build_failure(rows):
            self.executed(rows).update(outcome="build-failure", failure={"side": "caller"})

        for mutation, text in ((mismatch, "WRONG VALUE abi-families/int_ret_i8_c"), (crash, "CRASH"),
                               (oracle, "oracle-failure"), (build_failure, "build failure")):
            with self.subTest(text):
                errors = self.errors(mutation)
                self.assertTrue(any(text in error and "superseded group attempt" in error for error in errors),
                                errors)

    def test_a_group_refusal_must_be_reproduced_per_case(self):
        def retag(rows):
            for row in rows:
                if row["outcome"] == "decline":
                    row["decline"]["tags"] = ["[TCG-RET-ABI]"]

        def other_side(rows):
            for row in rows:
                if row["outcome"] == "decline" and row["caller"] == "tcg":
                    row["decline"]["side"] = "caller"

        for mutation in (retag, other_side):
            with self.subTest(mutation.__name__):
                errors = self.errors(mutation)
                self.assertTrue(any("not reproduced by any per-case rebuild" in error for error in errors), errors)

    def test_an_attempt_needs_its_per_case_rebuild(self):
        def orphan(rows):
            for row in rows:
                row["unit"] = "elsewhere"

        errors = self.errors(orphan)
        self.assertTrue(any("group attempt without a per-case rebuild" in error for error in errors), errors)

    def test_group_mode_matrix_rows_are_not_a_rebuild(self):
        # The unit's matrix rows exist at every level, but as group rows: no
        # per-case rebuild ran, so the attempt has none.
        def group_rows(rows):
            for row in rows:
                if row.get("unit") == "integer_c":
                    row["mode"] = "group"

        errors = self.errors(matrix_mutation=group_rows)
        self.assertTrue(any("group attempt without a per-case rebuild" in error for error in errors), errors)

    def test_a_group_refusal_is_reproduced_by_the_union_of_its_cases(self):
        # The group compile refused two functions, each case's own rebuild one
        # of them: the group's tags are the union of the per-case tags, which
        # no single per-case refusal carries.
        other = ["[TCG-MIR-UNSUPPORTED]", "[TCG-RET-ABI]"]
        self.assertEqual(self.errors(other_tags=other), [])

        def drop_other(rows):
            for row in rows:
                if row["case"] == self.OTHER and row["outcome"] == "decline":
                    row.update(outcome="oracle-ok" if row["caller"] == "llvm" else "match")
                    row.pop("decline")

        errors = self.errors(other_tags=other, matrix_mutation=drop_other)
        self.assertTrue(any("not reproduced by any per-case rebuild" in error for error in errors), errors)


class GeneratorTests(unittest.TestCase):
    def test_families_inventory_meets_the_runner_pins(self):
        listing = json.loads(subprocess.run(
            [sys.executable, str(GATE.FAMILIES), "--list"], capture_output=True, text=True, check=True,
        ).stdout)
        sys.path.insert(0, str(GATE.FAMILIES.parent))
        try:
            families = importlib.import_module("families")
        finally:
            sys.path.pop(0)
        counts = {}
        for case in families.cases():
            counts[case.family] = counts.get(case.family, 0) + 1
        self.assertEqual(sum(len(group["cases"]) for group in listing), GATE.SUITE_MIN_CASES["abi-families"])
        for family, minimum in GATE.FAMILY_MIN_CASES.items():
            self.assertGreaterEqual(counts.get(family, 0), minimum, family)

    def test_group_expected_values_are_deterministic(self):
        with tempfile.TemporaryDirectory() as directory:
            for attempt in ("a", "b"):
                subprocess.run([sys.executable, str(GATE.GEN), "--emit-group", str(Path(directory) / attempt),
                                "1", "40"], check=True)
            first = (Path(directory) / "a" / "expected.json").read_text()
            self.assertEqual(first, (Path(directory) / "b" / "expected.json").read_text())
            cases = json.loads(first)["cases"]
            self.assertEqual([case["name"] for case in cases], [f"seed{seed}" for seed in range(1, 41)])
            self.assertEqual([case["argc"] for case in cases], list(range(2, 42)))


FAKE_TRUSTC = r'''
import json, os, re, sys
from pathlib import Path
args = sys.argv[1:]
if args == ["-vV"]:
    print("rustc 1.99.0-dev (fixture)\nbinary: trustc\ncommit-hash: " + "a" * 40 +
          "\ncommit-date: 2026-01-01\nhost: aarch64-unknown-linux-gnu\nrelease: 1.99.0-dev")
    raise SystemExit(0)
if args == ["--print", "sysroot"]:
    print("/fixture/sysroot")
    raise SystemExit(0)
scenario = os.environ["XBACK_FIXTURE_SCENARIO"]
backend = "tcg" if any(a.startswith("-Zcodegen-backend=") for a in args) else "llvm"
kind = args[args.index("--crate-type") + 1]
source = Path(args[-1])
expected_path = source.parent / "expected.json"
cases = json.loads(expected_path.read_text())["cases"] if expected_path.exists() else []
names = [case["name"] for case in cases]
def refuse(message):
    print(json.dumps({"$message_type": "diagnostic", "level": "error", "message": message,
                      "code": None, "children": []}), file=sys.stderr)
    print(json.dumps({"$message_type": "diagnostic", "level": "error",
                      "message": "aborting due to 1 previous error", "code": None, "children": []}),
          file=sys.stderr)
    raise SystemExit(1)
# Like the real backend on Linux, a trust-cg compile without the certificate
# and solver knobs is refused at proof promotion.
knobs = ["-Ztrust-ir-cg-args=no-proof-certs", "-Ztrust-ir-cg-args=refine-solver=0"]
if backend == "tcg" and any(knob not in args for knob in knobs):
    refuse("[TCG-MIR-UNSUPPORTED] cannot compile:\n  - f: [TCG-PROOF-465] fixture proof promotion refusal")
if backend == "tcg" and kind == "rlib" and scenario in ("decline", "group-wrong") and "bool_regs_c" in names:
    refuse("[TCG-MIR-UNSUPPORTED] cannot compile:\n  - bool_regs_c: [TCG-ARG-ABI] fixture refusal")
if backend == "tcg" and kind == "bin" and scenario == "caller-decline" and "bool_regs_c" in names:
    refuse("[TCG-MIR-UNSUPPORTED] cannot compile:\n  - main: [TCG-ARG-ABI] fixture caller refusal")
if backend == "tcg" and kind == "bin" and scenario == "untagged":
    refuse("mismatched types")
if kind == "rlib":
    out = Path(args[args.index("--out-dir") + 1])
    name = re.search(r'#!\[crate_name = "([a-z_]+)"\]', source.read_text())[1]
    (out / f"lib{name}.rlib").write_text(backend)
    raise SystemExit(0)
library = Path(args[args.index("-L") + 1])
callee = next(library.glob("lib*.rlib")).read_text()
output = Path(args[args.index("-o") + 1])
lines = {case["argc"]: case["expected"] for case in cases}
wrong = scenario == "mismatch" and "tcg" in (backend, callee)
# group-wrong: the trust-cg caller is wrong only when built from a whole group.
wrong = wrong or (scenario == "group-wrong" and backend == "tcg" and len(cases) > 1)
crash = scenario == "crash" and backend == "tcg"
program = (
    f"#!{sys.executable}\nimport os, signal, sys\nlines = {lines!r}\n"
    "argc = len(sys.argv)\n"
    f"if {crash!r} and argc == 3: os.kill(os.getpid(), signal.SIGSEGV)\n"
    "line = lines.get(argc)\n"
    "if line is None: raise SystemExit(42 if not lines else 3)\n"
    f"if {wrong!r} and argc == 2: line = line[:-1] + ('0' if line[-1] != '0' else '1')\n"
    "sys.stdout.write(line + '\\n')\n"
)
output.write_text(program)
output.chmod(0o755)
'''


class OrchestrationTests(unittest.TestCase):
    def scratch(self) -> Path:
        holder = tempfile.TemporaryDirectory(prefix="xback-orchestration-")
        self.addCleanup(holder.cleanup)
        return Path(holder.name)

    def run_gate(self, scenario: str, groups: str = "bool_c") -> tuple[int, dict]:
        directory = self.scratch()
        trustc = directory / "trustc"
        trustc.write_text(f"#!{sys.executable}\n{FAKE_TRUSTC}")
        trustc.chmod(0o755)
        backend = directory / "backend.so"
        backend.write_bytes(b"backend")
        out = directory / "report"
        environment = {**os.environ, "XBACK_FIXTURE_SCENARIO": scenario}
        # This is an in-process unit model, not Linux ABI qualification.
        # Replace only the runner's sys binding: mutating global sys.platform
        # would also change Python's own subprocess and filesystem behavior.
        with mock.patch.dict(os.environ, environment, clear=True), \
                contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            model_sys = types.SimpleNamespace(**{**vars(sys), "platform": "linux"})
            with mock.patch.object(GATE, "sys", model_sys):
                code = GATE.main(
                    ["--backend", str(backend), "--backend-sha256", SHA,
                     "--trustc", str(trustc), "--out", str(out), "--jobs", "2",
                     "--suites", "abi-families", "--groups", groups,
                     "--opt-levels", "0,2", "--run-timeout", "20"])
        return code, json.loads((out / "report.json").read_text())

    def test_linux_compiler_label_does_not_admit_a_darwin_host(self):
        model_sys = types.SimpleNamespace(**{**vars(sys), "platform": "darwin"})
        identity = subprocess.CompletedProcess(
            ["trustc", "-vV"], 0,
            "trustc 1.0\nhost: aarch64-unknown-linux-gnu\ncommit-hash: fixture\n", "")
        with mock.patch.object(GATE, "sys", model_sys), \
                mock.patch.object(GATE.subprocess, "run", return_value=identity) as run:
            with self.assertRaisesRegex(GATE.GateError, "on darwin"):
                GATE.compiler_identity(Path("trustc"), {})
        self.assertEqual(run.call_count, 1)

    def test_matching_subset_is_never_a_pass(self):
        code, report = self.run_gate("pass")
        self.assertEqual(code, 0, report["errors"])
        self.assertEqual(report["status"], "subset-ok")
        self.assertEqual(report["summary"]["abi-families"]["cases"], 3)
        self.assertEqual(report["summary"]["abi-families"]["cross_matches"], 3 * 2 * 3)
        self.assertNotEqual(report["status"], "pass")
        self.assertTrue(any("subset" in error for error in GATE.verdict_errors(report, SHA)))

    def test_wrong_value_and_crash_are_named(self):
        code, report = self.run_gate("mismatch")
        self.assertEqual(code, 1)
        self.assertTrue(any(error.startswith("WRONG VALUE abi-families/bool_regs_c") for error in report["errors"]),
                        report["errors"])
        code, report = self.run_gate("crash")
        self.assertEqual(code, 1)
        self.assertTrue(any(error.startswith("CRASH abi-families/bool_stack_c") and "SIGSEGV" in error
                            for error in report["errors"]), report["errors"])

    def test_one_refused_function_does_not_hide_the_rest_of_its_group(self):
        code, report = self.run_gate("decline")
        self.assertEqual(code, 1)
        live = GATE.cell_records(report)
        modes = {row["mode"] for row in live}
        self.assertEqual(modes, {"per-case"})
        declined = {(row["case"], row["caller"], row["callee"], row["opt"])
                    for row in live if row["outcome"] == "decline"}
        self.assertEqual(declined, {("bool_regs_c", caller, "tcg", opt)
                                    for caller in ("llvm", "tcg") for opt in (0, 2)})
        others = [row for row in live if row["case"] != "bool_regs_c"]
        self.assertTrue(others and all(row["outcome"] in ("match", "oracle-ok") for row in others))
        self.assertEqual([row["case"] for row in report["declines"]], ["bool_regs_c"])
        self.assertTrue(any("unlisted decline abi-families/bool_regs_c callee" in error
                            for error in report["errors"]), report["errors"])

    def test_a_refused_trust_cg_caller_is_rebuilt_one_case_per_crate_pair(self):
        # Every callee builds; the trust-cg CALLER of the whole group refuses
        # one case. Only a per-case rebuild shows the other cases' tcg x llvm
        # and tcg x tcg cells, and pins the refusal on its own case.
        code, report = self.run_gate("caller-decline")
        self.assertEqual(code, 1)
        live = GATE.cell_records(report)
        self.assertEqual({row["mode"] for row in live}, {"per-case"})
        declined = {(row["case"], row["caller"], row["callee"], row["opt"])
                    for row in live if row["outcome"] == "decline"}
        self.assertEqual(declined, {("bool_regs_c", "tcg", callee, opt)
                                    for callee in ("llvm", "tcg") for opt in (0, 2)})
        others = [row for row in live if row["case"] != "bool_regs_c"]
        self.assertTrue(others and all(row["outcome"] in ("match", "oracle-ok") for row in others))
        self.assertTrue(any("unlisted decline abi-families/bool_regs_c caller" in error
                            for error in report["errors"]), report["errors"])

    def test_a_wrong_value_in_a_superseded_group_attempt_fails(self):
        # The callee group refuses one case; the trust-cg caller of the WHOLE
        # group is wrong, every per-case caller right. The group attempt's
        # executed tcg x llvm cells are the only witnesses.
        code, report = self.run_gate("group-wrong")
        self.assertEqual(code, 1)
        live = GATE.cell_records(report)
        self.assertFalse([row for row in live if row["outcome"] == "mismatch"])
        self.assertTrue(any(error.startswith("WRONG VALUE abi-families/bool_regs_c") and
                            "superseded group attempt bool_c" in error for error in report["errors"]),
                        report["errors"])
        self.assertGreater(report["group_attempt_summary"]["executed"], 0)

    def test_trust_cg_halves_carry_the_certificate_knobs(self):
        # The stand-in compiler refuses a trust-cg compile without both knobs,
        # as the real backend does at proof promotion; a matching run proves
        # the runner passed them, not only that the report lists them.
        code, report = self.run_gate("pass")
        self.assertEqual(code, 0, report["errors"])
        self.assertEqual(report["declines"], [])
        self.assertEqual(report["knobs"], list(GATE.TCG_KNOBS))

    def test_untagged_compile_failure_is_a_build_failure_not_a_decline(self):
        code, report = self.run_gate("untagged")
        self.assertEqual(code, 1)
        self.assertEqual(report["declines"], [])
        self.assertTrue(any(error.startswith("build failure") for error in report["errors"]), report["errors"])

    def test_backend_hash_is_checked_before_any_compile(self):
        directory = self.scratch()
        backend = directory / "backend.so"
        backend.write_bytes(b"other bytes")
        trustc = directory / "trustc"
        trustc.write_text(f"#!{sys.executable}\n{FAKE_TRUSTC}")
        trustc.chmod(0o755)
        with mock.patch.dict(os.environ, {"XBACK_FIXTURE_SCENARIO": "pass"}), \
                contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(io.StringIO()):
            model_sys = types.SimpleNamespace(**{**vars(sys), "platform": "linux"})
            with mock.patch.object(GATE, "sys", model_sys):
                code = GATE.main(
                    ["--backend", str(backend), "--backend-sha256", SHA,
                     "--trustc", str(trustc), "--out", str(directory / "report")])
        self.assertEqual(code, 1)
        report = json.loads((directory / "report" / "report.json").read_text())
        self.assertIn("backend SHA-256 differs from --backend-sha256", report["errors"])
        self.assertNotIn("cells", report)


if __name__ == "__main__":
    unittest.main()
