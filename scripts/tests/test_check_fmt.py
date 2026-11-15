"""The formatting gate runs the Trust package's targo from the repo root."""

from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]


class FormatGateTests(unittest.TestCase):
    def test_runs_the_trust_formatter_from_the_repository_and_propagates_failure(self):
        with tempfile.TemporaryDirectory(prefix="trust-cg-fmt-") as temporary:
            base = Path(temporary).resolve()
            repo = base / "repository"
            scripts = repo / "scripts"
            scripts.mkdir(parents=True)
            shutil.copy2(ROOT / "scripts/check_fmt.sh", scripts / "check_fmt.sh")
            package = base / "package" / "bin"
            package.mkdir(parents=True)
            targo = package / "targo"
            targo.write_text(
                '#!/bin/sh\n'
                '[ "$(pwd -P)" = "$FMT_TEST_REPO" ] || exit 87\n'
                'case "$*" in\n'
                '  "fmt --all -- --check") exit "$FMT_TEST_RC" ;;\n'
                '  *) exit 86 ;;\n'
                'esac\n', encoding="utf-8",
            )
            targo.chmod(0o755)
            fake_bin = base / "bin"
            fake_bin.mkdir()
            for command in ("cargo", "rustc", "rustup", "rustfmt"):
                ambient = fake_bin / command
                ambient.write_text('#!/bin/sh\necho "ambient tool used" >&2\nexit 88\n', encoding="utf-8")
                ambient.chmod(0o755)
            for formatter_rc, expected_rc in ((0, 0), (1, 1), (42, 2)):
                env = dict(os.environ, PATH=f"{fake_bin}:{os.environ['PATH']}", TRUST_TARGO=str(targo),
                           FMT_TEST_REPO=str(repo), FMT_TEST_RC=str(formatter_rc))
                result = subprocess.run(
                    ["bash", str(scripts / "check_fmt.sh")], cwd=base, env=env,
                    capture_output=True, text=True, check=False,
                )
                with self.subTest(formatter_rc=formatter_rc):
                    self.assertEqual(result.returncode, expected_rc, result.stdout + result.stderr)
                    self.assertNotIn("ambient tool used", result.stdout + result.stderr)

    def test_a_missing_or_relative_trust_targo_is_tooling_not_a_clean_tree(self):
        with tempfile.TemporaryDirectory(prefix="trust-cg-fmt-") as temporary:
            base = Path(temporary)
            scripts = base / "repository" / "scripts"
            scripts.mkdir(parents=True)
            shutil.copy2(ROOT / "scripts/check_fmt.sh", scripts / "check_fmt.sh")
            for value in ("targo", str(base / "absent" / "targo")):
                env = dict(os.environ, TRUST_TARGO=value)
                result = subprocess.run(["bash", str(scripts / "check_fmt.sh")], env=env,
                                        capture_output=True, text=True, check=False)
                with self.subTest(value=value):
                    self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                    self.assertIn("TOOLING", result.stderr)


if __name__ == "__main__":
    unittest.main()
