"""Tracked paths must stay distinct on a case-insensitive filesystem.

The fixture commits are built with git plumbing (hash-object/update-index), so
a colliding pair can be committed even on the case-insensitive filesystem that
the collision is about. The last case checks this checkout itself, which puts
the gate inside the release gate's python-unit-tests lane.
"""

from __future__ import annotations

import importlib.util
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("check_path_case_collisions", ROOT / "scripts/check_path_case_collisions.py")
assert SPEC is not None and SPEC.loader is not None
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)

# The pair ff4c27eca committed and 74a753fdd renamed.
DIRECT = "reports/perf/2026-09-23-linux-got-addressing-kinds/records/repair/direct"
SECTIONS = f"{DIRECT}/prior-readelf-S-lld-shared.txt.gz"
SYMBOLS = f"{DIRECT}/prior-readelf-s-lld-shared.txt.gz"
Z40 = "0" * 40


def git_env(base: Path) -> dict[str, str]:
    config = base / "gitconfig"
    config.write_text("[user]\n\tname = fixture\n\temail = fixture@example.invalid\n[commit]\n\tgpgSign = false\n")
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env.update(GIT_CONFIG_GLOBAL=str(config), GIT_CONFIG_NOSYSTEM="1")
    return env


def git(repo: Path, env: dict[str, str], *args: str, stdin: bytes | None = None) -> str:
    completed = subprocess.run(["git", "-C", str(repo), *args], env=env, input=stdin, capture_output=True, check=True)
    return completed.stdout.decode().strip()


def commit_paths(repo: Path, env: dict[str, str], contents: dict[str, bytes]) -> str:
    """Commit exactly these paths through the index only (no worktree files)."""
    git(repo, env, "read-tree", "--empty")
    for path, data in contents.items():
        blob = git(repo, env, "hash-object", "-w", "--stdin", stdin=data)
        git(repo, env, "update-index", "--add", "--cacheinfo", f"100644,{blob},{path}")
    tree = git(repo, env, "write-tree")
    commit = git(repo, env, "commit-tree", tree, "-m", "fixture")
    git(repo, env, "update-ref", "HEAD", commit)
    return commit


class FoldTests(unittest.TestCase):
    def test_the_archived_readelf_pair_collides(self):
        self.assertEqual(CHECK.collisions([SECTIONS, SYMBOLS]), [[SECTIONS, SYMBOLS]])

    def test_the_renamed_pair_does_not_collide(self):
        renamed = [f"{DIRECT}/prior-readelf-sections-lld-shared.txt.gz", f"{DIRECT}/prior-readelf-symbols-lld-shared.txt.gz"]
        self.assertEqual(CHECK.collisions(renamed), [])

    def test_a_directory_collision_is_reported_once_at_the_directory(self):
        self.assertEqual(CHECK.collisions(["Docs/a.md", "docs/b.md", "docs/c/d.md"]), [["Docs", "docs"]])

    def test_a_file_colliding_with_a_directory_is_reported(self):
        self.assertEqual(CHECK.collisions(["notes", "NOTES/a.md"]), [["NOTES", "notes"]])

    def test_unicode_normalization_forms_collide(self):
        composed, decomposed = "café.md", "café.md"
        self.assertEqual(CHECK.collisions([composed, decomposed]), [sorted([composed, decomposed])])

    def test_case_folding_is_full_not_ascii_only(self):
        self.assertEqual(CHECK.collisions(["straße", "STRASSE"]), [["STRASSE", "straße"]])

    def test_distinct_paths_pass(self):
        self.assertEqual(CHECK.collisions(["a/b", "a/c", "ab", "a-b"]), [])


class CommandAndHookTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="trust-cg-case-")
        self.base = Path(self.temporary.name)
        self.repo = self.base / "repo"
        self.repo.mkdir()
        self.env = git_env(self.base)
        git(self.repo, self.env, "init", "-q", "-b", "main")

    def tearDown(self):
        self.temporary.cleanup()

    def run_check(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            ["python3", "-B", str(ROOT / "scripts/check_path_case_collisions.py"), "--root", str(self.repo), *args],
            env=self.env, capture_output=True, text=True, check=False,
        )

    def test_command_fails_on_a_committed_collision_and_names_both_paths(self):
        commit = commit_paths(self.repo, self.env, {SECTIONS: b"sections\n", SYMBOLS: b"symbols\n"})
        for args in ((), ("--rev", commit)):
            with self.subTest(args=args):
                result = self.run_check(*args)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn(SECTIONS, result.stderr)
                self.assertIn(SYMBOLS, result.stderr)

    def test_command_passes_on_distinct_paths(self):
        commit = commit_paths(self.repo, self.env, {"a/b.txt": b"b\n", "a/c.txt": b"c\n"})
        result = self.run_check("--rev", commit)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_command_reports_an_unreadable_revision_as_a_tooling_error(self):
        commit_paths(self.repo, self.env, {"a": b"a\n"})
        self.assertEqual(self.run_check("--rev", "no-such-revision").returncode, 2)

    def push_through_hook(self, commit: str) -> subprocess.CompletedProcess:
        """Run the real hooks/pre-push as git would for a push of COMMIT to main."""
        hooks = self.repo / "hooks"
        scripts = self.repo / "scripts"
        hooks.mkdir(exist_ok=True)
        scripts.mkdir(exist_ok=True)
        shutil.copy2(ROOT / "hooks/pre-push", hooks / "pre-push")
        shutil.copy2(ROOT / "scripts/check_path_case_collisions.py", scripts / "check_path_case_collisions.py")
        return subprocess.run(
            ["bash", str(hooks / "pre-push"), "origin", "fixture://remote"],
            cwd=self.repo, env=self.env, capture_output=True, text=True, check=False,
            input=f"refs/heads/main {commit} refs/heads/main {Z40}\n",
        )

    def test_pre_push_blocks_a_colliding_commit_before_the_clean_tree_check(self):
        commit = commit_paths(self.repo, self.env, {SECTIONS: b"sections\n", SYMBOLS: b"symbols\n"})
        result = self.push_through_hook(commit)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("case-colliding tracked paths", result.stderr)
        self.assertIn(SYMBOLS, result.stderr)
        self.assertNotIn("worktree is dirty", result.stderr)

    def test_pre_push_lets_a_distinct_commit_reach_the_next_check(self):
        commit = commit_paths(self.repo, self.env, {"a/b.txt": b"b\n"})
        result = self.push_through_hook(commit)
        # The fixture has no worktree files, so the next check (clean tree) stops it.
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertNotIn("case-colliding tracked paths", result.stderr)
        self.assertIn("worktree is dirty", result.stderr)


class CheckoutTests(unittest.TestCase):
    def test_this_checkout_has_no_case_colliding_tracked_paths(self):
        if not (ROOT / ".git").exists():
            self.skipTest("not a git checkout (anonymous source export)")
        groups = CHECK.collisions(CHECK.tracked_paths(ROOT))
        self.assertEqual(groups, [], "tracked paths that are one file on a case-insensitive filesystem")


if __name__ == "__main__":
    unittest.main()
