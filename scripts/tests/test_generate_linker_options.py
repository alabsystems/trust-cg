"""The link driver's measured linker option table must match the installed
linkers: `scripts/generate_linker_options.py --check` (recorded versions and
`--help` hashes) and `--check --sweep` (a new native measurement of every
spelling) pass on a host with GNU ld, gold and LLD, and fail with a
"regenerate" message when the table drifts. Skipped without the three
linkers."""

from __future__ import annotations

import importlib.util
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
GENERATOR = ROOT / "scripts/generate_linker_options.py"
TABLE = Path("crates/trust-cg-codegen/src/link_driver/linker_options.rs")


def load_generator():
    spec = importlib.util.spec_from_file_location("generate_linker_options", GENERATOR)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run(generator: Path, *arguments: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, "-B", str(generator), *arguments],
        capture_output=True,
        text=True,
        timeout=600,
        env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
    )


@unittest.skipUnless(
    load_generator().linkers() is not None,
    "ld.bfd, ld.gold and ld.lld are not all installed",
)
class LinkerOptionTableTests(unittest.TestCase):
    def test_the_checked_in_table_matches_the_installed_linkers(self):
        generator = load_generator()
        versions, hashes = generator.recorded((ROOT / TABLE).read_text(encoding="utf-8"))
        self.assertEqual(sorted(versions), ["GNU_LD", "GOLD", "LLD"])
        self.assertEqual(sorted(hashes), ["GNU_LD", "GOLD", "LLD"])
        fast = run(GENERATOR, "--check")
        self.assertEqual(fast.returncode, 0, fast.stdout + fast.stderr)
        swept = run(GENERATOR, "--check", "--sweep")
        self.assertEqual(swept.returncode, 0, swept.stdout + swept.stderr)
        self.assertIn("matches a new measurement", swept.stdout)

    def test_a_drifted_table_fails_with_regenerate(self):
        original = (ROOT / TABLE).read_text(encoding="utf-8")
        gnu_ld = original.index("pub(super) const GNU_LD")
        flipped = original.index("Read::NotNext", gnu_ld)
        entry_drift = original[:flipped] + "Read::Next" + original[flipped + len("Read::NotNext"):]
        version_drift = original.replace('"LLD 22.', '"LLD 21.', 1)
        self.assertNotEqual(version_drift, original)
        for name, text, arguments in [
            ("entry", entry_drift, ("--check", "--sweep")),
            ("version", version_drift, ("--check",)),
        ]:
            with self.subTest(name), tempfile.TemporaryDirectory(prefix="tcg-options-") as temporary:
                repository = Path(temporary)
                (repository / "scripts").mkdir()
                shutil.copy2(GENERATOR, repository / "scripts" / GENERATOR.name)
                (repository / TABLE).parent.mkdir(parents=True)
                (repository / TABLE).write_text(text, encoding="utf-8")
                result = run(repository / "scripts" / GENERATOR.name, *arguments)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("regenerate", result.stdout)


if __name__ == "__main__":
    unittest.main()
