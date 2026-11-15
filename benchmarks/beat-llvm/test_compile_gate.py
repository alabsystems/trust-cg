#!/usr/bin/env python3
"""Corpus admission controls for the compile-completeness gate.

Author: Andrew Yates. Copyright 2026 Andrew Yates. License: Apache-2.0.
"""

import contextlib
import importlib.util
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
SPEC = importlib.util.spec_from_file_location("beat_llvm_compile_gate", HERE / "compile_gate.py")
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)


class CorpusAdmissionTests(unittest.TestCase):
    def invoke(self, root, *arguments):
        driver = {"compiler": "stand-in-trustc", "compiler_flags": [], "host": "test-host"}
        stdout, stderr = io.StringIO(), io.StringIO()
        with (mock.patch.object(gate, "HERE", root),
              mock.patch.object(sys, "argv", ["compile_gate.py", "--dylib", str(root / "backend"), *arguments]),
              mock.patch.object(gate, "stale_backend_source", return_value=None),
              mock.patch.object(gate.TRUST_TOOLCHAIN, "resolve", return_value=driver),
              mock.patch.object(gate.TRUST_TOOLCHAIN, "summary", return_value="stand-in"),
              mock.patch.object(gate.subprocess, "run") as compile_run,
              contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr)):
            compile_run.return_value.returncode = 0
            compile_run.return_value.stderr = ""
            result = gate.main()
            self.commands = [call.args[0] for call in compile_run.call_args_list]
        return result, stdout.getvalue(), stderr.getvalue(), compile_run.call_count

    def test_invalid_corpus_never_compiles_or_passes(self):
        cases = [
            ("empty", {"programs": {}}, []),
            ("unlisted source", {"programs": {}}, ["hidden"]),
            ("missing source", {"programs": {"missing": {}}}, []),
            ("extra source", {"programs": {"listed": {}}}, ["listed", "hidden"]),
            ("program list", {"programs": ["listed"]}, ["listed"]),
            ("missing programs", {}, []),
            ("document list", [], []),
            ("malformed JSON", "{", []),
            ("excessively nested JSON", '{"programs":' + '[' * 2000 + '0' + ']' * 2000 + '}', []),
            ("duplicate program", '{"programs":{"listed":{},"listed":{}}}', ["listed"]),
            ("duplicate program map", '{"programs":{},"programs":{"listed":{}}}', ["listed"]),
            ("duplicate metadata", '{"programs":{"listed":{"expected_exit":0,"expected_exit":7}}}', ["listed"]),
            ("null metadata", {"programs": {"listed": None}}, ["listed"]),
            ("list metadata", {"programs": {"listed": []}}, ["listed"]),
            ("boolean metadata", {"programs": {"listed": True}}, ["listed"]),
        ]
        for label, manifest, sources in cases:
            with self.subTest(label=label), tempfile.TemporaryDirectory() as td:
                root = Path(td)
                (root / "progs").mkdir()
                (root / "backend").touch()
                (root / "progs" / "manifest.json").write_text(
                    manifest if isinstance(manifest, str) else json.dumps(manifest))
                for name in sources:
                    (root / "progs" / (name + ".rs")).write_text("fn main() {}")
                result, stdout, stderr, calls = self.invoke(root)
                self.assertEqual(result, 2)
                self.assertEqual(calls, 0)
                self.assertNotIn("compile-gate: 0/0", stdout)
                self.assertIn("corpus", stderr)

    def test_source_directory_cannot_satisfy_manifest_row(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "progs" / "listed.rs").mkdir(parents=True)
            (root / "backend").touch()
            (root / "progs" / "manifest.json").write_text(json.dumps({"programs": {"listed": {}}}))
            result, stdout, stderr, calls = self.invoke(root)
        self.assertEqual(result, 2)
        self.assertEqual(calls, 0)
        self.assertIn("drift", stderr)

    def test_unreadable_manifest_is_a_tooling_error(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "backend").touch()
            result, stdout, stderr, calls = self.invoke(root)
        self.assertEqual(result, 2)
        self.assertEqual(calls, 0)
        self.assertIn("unreadable", stderr)

    def test_valid_corpus_compiles_every_optimization_level(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "progs").mkdir()
            (root / "backend").touch()
            (root / "progs" / "manifest.json").write_text(json.dumps({"programs": {"listed": {}}}))
            (root / "progs" / "listed.rs").write_text("fn main() {}")
            result, stdout, stderr, calls = self.invoke(root)
        self.assertEqual(result, 0)
        self.assertEqual(calls, 3)
        self.assertIn("compile-gate: 3/3", stdout)
        self.assertEqual(stderr, "")
        self.assertTrue(all("--target" not in command for command in self.commands))
        self.assertEqual([next(a for a in c if a.startswith("-Copt-level="))
                          for c in self.commands], ["-Copt-level=0", "-Copt-level=2", "-Copt-level=3"])

    def test_explicit_cross_target_keeps_every_optimization_level(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "progs").mkdir()
            (root / "backend").touch()
            (root / "progs" / "manifest.json").write_text(json.dumps({"programs": {"listed": {}}}))
            (root / "progs" / "listed.rs").write_text("fn main() {}")
            result, stdout, stderr, calls = self.invoke(root, "--target", "cross-host")
        self.assertEqual((result, calls), (0, 3))
        self.assertIn("compile-gate: 3/3", stdout)
        self.assertEqual(stderr, "")
        for command in self.commands:
            self.assertEqual(command.count("--target"), 1)
            self.assertEqual(command[command.index("--target") + 1], "cross-host")


if __name__ == "__main__":
    unittest.main()
