"""check_documentation.py's mode dispatch: every gate runs, and none needs a metadata tool."""

from __future__ import annotations

from contextlib import redirect_stderr, redirect_stdout
import importlib.util
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch


ROOT = Path(__file__).resolve().parents[2]


class DocumentationCheckModeTests(unittest.TestCase):
    def setUp(self):
        # Load without inserting into sys.modules, like the other document
        # tests: a second importer must not see this patched instance.
        spec = importlib.util.spec_from_file_location(
            "documentation_modes_under_test", ROOT / "scripts/check_documentation.py"
        )
        assert spec is not None and spec.loader is not None
        self.checker = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.checker)

    def main(self, *args):
        stdout, stderr = io.StringIO(), io.StringIO()
        with patch.object(self.checker.sys, "argv", ["check_documentation.py", *args]):
            with redirect_stdout(stdout), redirect_stderr(stderr):
                status = self.checker.main()
        return status, stdout.getvalue(), stderr.getvalue()

    def test_check_preserves_every_existing_document_gate(self):
        gates = ["check_links", "acceptance_document_errors", "diagnostics_census_errors"]
        for args in [("--check",), ()]:
            with self.subTest(args=args):
                replacements = {name: Mock(return_value=[]) for name in gates}
                with patch.multiple(self.checker, **replacements):
                    status, _, stderr = self.main(*args)
                self.assertEqual((status, stderr), (0, ""))
                for gate in replacements.values():
                    gate.assert_called_once_with()

    def test_links_mode_runs_only_links_and_structure(self):
        gates = ["check_links", "acceptance_document_errors", "diagnostics_census_errors"]
        replacements = {name: Mock(return_value=[]) for name in gates}
        with patch.multiple(self.checker, **replacements):
            status, _, stderr = self.main("--links")
        self.assertEqual((status, stderr), (0, ""))
        replacements["check_links"].assert_called_once_with()
        replacements["acceptance_document_errors"].assert_called_once_with()
        replacements["diagnostics_census_errors"].assert_not_called()

    def test_no_mode_needs_a_metadata_tool(self):
        gates = ["check_links", "acceptance_document_errors", "diagnostics_census_errors"]
        for args in [("--links",), ("--check",)]:
            with self.subTest(args=args):
                replacements = {name: Mock(return_value=[]) for name in gates}
                with patch("subprocess.run") as run, patch.multiple(self.checker, **replacements):
                    status, _, stderr = self.main(*args)
                self.assertEqual((status, stderr), (0, ""))
                run.assert_not_called()

    def test_gate_errors_fail_the_check(self):
        gates = ["check_links", "acceptance_document_errors", "diagnostics_census_errors"]
        replacements = {name: Mock(return_value=[]) for name in gates}
        replacements["diagnostics_census_errors"] = Mock(return_value=["census drift"])
        with patch.multiple(self.checker, **replacements):
            status, _, stderr = self.main("--check")
        self.assertEqual(status, 1)
        self.assertIn("census drift", stderr)

    def test_broken_link_in_a_development_document_fails_the_gate(self):
        # The one negative control for check_links: a maintained development
        # document with a dangling relative link is reported by file and line.
        plan_name = "docs/darwin-aarch64-completion.md"
        self.assertIn(plan_name, self.checker.DEVELOPMENT_DOCS)
        with tempfile.TemporaryDirectory(prefix="trust-cg-docs-") as temporary:
            root = Path(temporary)
            for name in self.checker.PUBLIC_DOCS:
                (root / name).write_text("# placeholder\n", encoding="utf-8")
            plan = root / plan_name
            plan.parent.mkdir(parents=True)
            plan.write_text(
                "# Plan\n\n[ledger](present.md) and [gone](no-such-ledger.md)\n",
                encoding="utf-8",
            )
            (plan.parent / "present.md").write_text("# present\n", encoding="utf-8")
            self.checker.ROOT = root
            errors = self.checker.check_links()
        self.assertEqual(errors, [f"{plan_name}:3: missing no-such-ledger.md"])


if __name__ == "__main__":
    unittest.main()
