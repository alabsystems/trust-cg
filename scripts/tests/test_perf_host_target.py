"""Performance entry points take their target from the host, never a fixed triple.

Ledger X-DARWIN-P8 recorded that the beat-llvm harness defaulted to
`x86_64-apple-darwin` and that the compile-time canary and determinism sentinel
hardcoded it, so on this Apple silicon host every lane cross-compiled for x86
against a backend built for the host. The harness and both scripts now take the
resolved Trust compiler's host triple (their behaviour is covered by
`benchmarks/beat-llvm/test_run_provenance.py` and
`test_benchmark_prerequisites.py`). This module keeps every performance entry
point from regaining a fixed default triple or a fixed backend suffix, and
covers `benchmarks/compile-scaling/run.py`, whose default backend was a Linux
`.so` path.

It is a regression lint over source text plus the compile-scaling backend
selection; it measures nothing.
"""

import contextlib
import importlib.util
import io
import os
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
# Every entry point whose lanes compile the benchmark corpus or a scaling
# ladder. A new one belongs here.
ENTRY_POINTS = (
    "benchmarks/beat-llvm/run.py",
    "benchmarks/beat-llvm/scale_gate.py",
    "benchmarks/beat-llvm/compile_gate.py",
    "benchmarks/compile-scaling/run.py",
    "benchmarks/real-corpus/run.py",
    "scripts/compile_time_canary.sh",
    "scripts/compile_determinism_sentinel.sh",
)
TRIPLE = r"(?:x86_64|aarch64|arm64)-(?:apple-darwin|unknown-linux-gnu)"
# A triple bound as a default: a TARGET assignment (shell or Python), an
# argparse default, or a literal `--target <triple>` compile argument.
FIXED_TARGET = re.compile(
    rf"""(?x)
    ^\s*TARGET\s*=\s*["']?{TRIPLE}
    | ^\s*TARGET="\$\{{TARGET:-{TRIPLE}
    | default\s*=\s*["']{TRIPLE}
    | ["']--target["']\s*,\s*["']{TRIPLE}
    | --target\s+{TRIPLE}
    """,
    re.MULTILINE,
)
# A backend path with a fixed platform suffix instead of scripts/bridge_backend.py.
FIXED_BACKEND = re.compile(r"librustc_codegen_trust_cg\.(?:so|dylib)")


def load(relative, name):
    spec = importlib.util.spec_from_file_location(name, ROOT / relative)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class NoFixedTargetTests(unittest.TestCase):
    def test_entry_points_carry_no_fixed_default_triple(self):
        for relative in ENTRY_POINTS:
            with self.subTest(entry_point=relative):
                text = (ROOT / relative).read_text(encoding="utf-8")
                self.assertEqual(FIXED_TARGET.findall(text), [])

    def test_entry_points_carry_no_fixed_backend_suffix(self):
        for relative in ENTRY_POINTS:
            with self.subTest(entry_point=relative):
                text = (ROOT / relative).read_text(encoding="utf-8")
                self.assertEqual(FIXED_BACKEND.findall(text), [])

    def test_the_lint_recognises_the_retired_spellings(self):
        # Each spelling the entry points used before the host default.
        for spelling in ('TARGET = "x86_64-apple-darwin"\n',
                         'TARGET="x86_64-apple-darwin"\n',
                         'TARGET="${TARGET:-x86_64-apple-darwin}"\n',
                         'ap.add_argument("--target", default="x86_64-apple-darwin")\n',
                         '    "--target", "x86_64-apple-darwin",\n',
                         '  "$RUSTC" --crate-type bin --target aarch64-apple-darwin \\\n'):
            with self.subTest(spelling=spelling):
                self.assertTrue(FIXED_TARGET.search(spelling))
        for spelling in ('TARGET=""\n', 'ap.add_argument("--target", default=None)\n',
                         '"--target", self.args.target,\n', '--target "$TARGET"\n'):
            with self.subTest(spelling=spelling):
                self.assertIsNone(FIXED_TARGET.search(spelling))


class CompileScalingBackendTests(unittest.TestCase):
    def setUp(self):
        self.scaling = load("benchmarks/compile-scaling/run.py", "trust_cg_compile_scaling")
        self.temporary = tempfile.TemporaryDirectory(prefix="trust-cg-compile-scaling-")
        self.addCleanup(self.temporary.cleanup)
        self.repo = Path(self.temporary.name)

    def test_default_backend_has_this_hosts_suffix(self):
        suffix = ".dylib" if sys.platform == "darwin" else ".so"
        missing = self.scaling.default_dylib(self.repo)
        self.assertEqual(missing.name, "librustc_codegen_trust_cg" + suffix)
        older = self.repo / "crates/rustc-codegen-trust-cg/target/release" / missing.name
        newer = self.repo / "crates/rustc-codegen-trust-cg/target-bridge/release" / missing.name
        for path, when in ((older, 2_000_000_000), (newer, 1_000_000_000)):
            path.parent.mkdir(parents=True)
            path.touch()
            os.utime(path, (when, when))
        # The newest build wins, wherever it was written.
        self.assertEqual(self.scaling.default_dylib(self.repo), older)

    def test_a_stale_backend_is_refused_before_any_compile(self):
        backend = self.repo / "librustc_codegen_trust_cg.dylib"
        backend.touch()
        os.utime(backend, (1, 1))  # older than every build input of the checkout
        stdout = io.StringIO()
        with mock.patch.object(sys, "argv", ["run.py", "--dylib", str(backend)]), \
                mock.patch.object(self.scaling, "resolve_driver") as driver, \
                contextlib.redirect_stdout(stdout):
            self.assertEqual(self.scaling.main(), 2)
        self.assertIn("is STALE", stdout.getvalue())
        driver.assert_not_called()


if __name__ == "__main__":
    unittest.main()
