from __future__ import annotations

import contextlib
import importlib.util
import io
from pathlib import Path
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "native_test_host_matrix.py"
SPEC = importlib.util.spec_from_file_location("native_test_host_matrix", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MATRIX = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MATRIX)

MACOS = MATRIX.HOSTS["macos"]
LINUX = MATRIX.HOSTS["linux"]


class CfgEvaluationTests(unittest.TestCase):
    def test_nested_predicates_evaluate_per_host(self):
        both = 'all(target_arch = "aarch64", any(target_os = "macos", all(target_os = "linux", target_env = "gnu")))'
        self.assertTrue(MATRIX.evaluate(both, MACOS))
        self.assertTrue(MATRIX.evaluate(both, LINUX))
        linux = 'all(target_arch = "aarch64", target_os = "linux", target_env = "gnu", feature = "verify")'
        self.assertFalse(MATRIX.evaluate(linux, MACOS))
        self.assertTrue(MATRIX.evaluate(linux, LINUX))
        self.assertTrue(MATRIX.evaluate('not(target_os = "macos")', LINUX))
        self.assertTrue(MATRIX.evaluate("unix", MACOS))

    def test_unknown_keys_and_malformed_predicates_fail_closed(self):
        for predicate in ('target_feature = "lse"', "miri", "not(unix, unix)", 'all(target_os = "macos"'):
            with self.subTest(predicate=predicate), self.assertRaises(MATRIX.CfgError):
                MATRIX.evaluate(predicate, MACOS)

    def test_comment_stripping_keeps_string_contents(self):
        text = 'let s = "a//b"; // cfg!(target_os = "macos")\n/* cfg!(unix) */ x'
        stripped = MATRIX.strip_comments(text)
        self.assertIn('"a//b"', stripped)
        self.assertNotIn("cfg!", stripped)


class ClassificationTests(unittest.TestCase):
    def classify(self, source: str, name: str = "e2e_aarch64_fixture.rs"):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / name
            path.write_text(source, encoding="utf-8")
            return MATRIX.classify(path)

    def test_macos_guard_is_macos_only(self):
        row = self.classify(
            'fn can() -> bool { cfg!(all(target_os = "macos", target_arch = "aarch64")) }\n'
            'fn run() { std::process::Command::new("cc"); }\n'
        )
        self.assertEqual(row["native"], {"macos": True, "linux": False})
        self.assertEqual(row["basis"], "target_os guards")

    def test_shared_harness_is_both_hosts(self):
        row = self.classify(
            '#[path = "common/native_host.rs"]\nmod native_host;\n'
            'const T: &str = "aarch64-apple-darwin";\nfn run() { Command::new("cc"); }\n'
        )
        self.assertEqual(row["native"], {"macos": True, "linux": True})
        self.assertEqual(row["basis"], "shared native harness")

    def test_file_cfg_excludes_a_host(self):
        row = self.classify(
            '#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]\n'
            'fn run() { Command::new("cc"); }\n'
        )
        self.assertEqual(row["native"], {"macos": False, "linux": True})
        self.assertTrue(row["basis"].startswith("file cfg excludes macos"))

    def test_host_selected_object_format_is_both_hosts(self):
        row = self.classify(
            'fn triple() -> &str { if cfg!(target_os = "macos") { "aarch64-apple-darwin" }'
            ' else { "aarch64-unknown-linux-gnu" } }\nfn run() { Command::new("cc"); }\n'
        )
        self.assertEqual(row["native"], {"macos": True, "linux": True})

    def test_non_native_and_non_aarch64_files_are_excluded(self):
        self.assertIsNone(self.classify("fn encode() {} // aarch64 words only\n"))
        self.assertIsNone(self.classify('fn run() { Command::new("cc"); } // aarch64\n', "e2e_x86_64_fixture.rs"))


class LiveTreeTests(unittest.TestCase):
    def test_print_mode_writes_the_table_to_stdout_only(self):
        for args in ([], ["--print"]):
            with self.subTest(args=args):
                stdout = io.StringIO()
                with contextlib.redirect_stdout(stdout):
                    self.assertEqual(MATRIX.main(args), 0)
                self.assertTrue(stdout.getvalue().startswith("# AArch64 native test host matrix\n"))
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            self.assertEqual(MATRIX.main(["--check"]), 0)
        self.assertEqual(stdout.getvalue(), "")

    def test_static_only_files_are_not_native_and_stay_current(self):
        results, errors = MATRIX.rows()
        self.assertEqual(errors, [])
        by_name = {row["name"]: row for row in results}
        for name in MATRIX.STATIC_ONLY:
            self.assertTrue(MATRIX.STATIC_ONLY[name])
            # Still matched by the heuristic, or the entry would be stale.
            self.assertIsNotNone(MATRIX.classify(MATRIX.TESTS / name), name)
            if name in by_name:
                self.assertIsNone(by_name[name]["native"], name)
        original = dict(MATRIX.STATIC_ONLY)
        try:
            MATRIX.STATIC_ONLY["aarch64_encoding.rs"] = "no native marker"
            _, errors = MATRIX.rows()
            self.assertIn("stale static-only entry for aarch64_encoding.rs: no native marker matches", errors)
        finally:
            MATRIX.STATIC_ONLY.clear()
            MATRIX.STATIC_ONLY.update(original)

    def test_every_linux_floor_native_target_is_linux_capable(self):
        results, errors = MATRIX.rows()
        self.assertEqual(errors, [])
        for row in results:
            if row["floor"] and row["native"] is not None:
                self.assertTrue(row["native"]["linux"], row["name"])


if __name__ == "__main__":
    unittest.main()
