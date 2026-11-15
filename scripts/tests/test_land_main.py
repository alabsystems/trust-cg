"""scripts/land_main.sh: the serialized landing train, against a bare local remote.

The fixture repository commits the PRODUCTION hooks/pre-push, train and
tracked-path collision check (the hook runs it on every main push and blocks
when it is missing), plus a stub gate (its --attest writes a record ref for
HEAD, or fails, or first moves the remote main as a concurrent lander would)
and a stub attestation tool (verify answers 0 when a record exists for the
commit, else 3; deferred-classes defers x86_64-native when LAND_DEFER_X86=1;
host is never native x86-64). The train's push therefore also runs through the
real hook, which uses the shared transport's local-bare fixture route.
"""

from __future__ import annotations

import os
from pathlib import Path
import shutil
import shlex
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]

SOURCE_CHECK = r'''import os, pathlib, subprocess, sys
head = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
with open(os.environ["LAND_LOG"], "a") as log:
    log.write("source-check " + head + "\n")
marker = os.environ.get("LAND_SOURCE_MOVE_ONCE")
if marker and not pathlib.Path(marker).exists():
    pathlib.Path(marker).touch()
    subprocess.run(["git", "-C", os.environ["LAND_OTHER"], "push", "-q",
                    "--no-verify", "origin", "HEAD:refs/heads/main"], check=True)
if os.environ.get("LAND_SOURCE_DIRTY"):
    pathlib.Path("README").write_text("changed during qualification\n")
sys.exit(int(os.environ.get("LAND_SOURCE_FAIL", "0")))
'''

GATE = r'''#!/usr/bin/env bash
set -eu
echo "gate $* $(git rev-parse HEAD)" >>"$LAND_LOG"
if [ -n "${LAND_MOVE_REMOTE_ONCE:-}" ] && [ ! -e "$LAND_MOVE_REMOTE_ONCE" ]; then
  : >"$LAND_MOVE_REMOTE_ONCE"
  git -C "$LAND_OTHER" push -q --no-verify origin HEAD:refs/heads/main
fi
[ "${LAND_GATE_FAIL:-0}" = 0 ] || exit 1
head="$(git rev-parse HEAD)"
tree="$(git mktree </dev/null)"
git update-ref "refs/attest/soundness/$head/fixture-host" "$(git commit-tree "$tree" -p "$head" -m record)"
'''

# The hook's two pre-flight gates (scripts/check_fmt.sh, scripts/check_tippy.sh).
# A missing one BLOCKS a push to main since 98e806d6f, so the fixture commits a
# stub of each that logs its call and passes; scripts/test_pre_push_hook.sh
# covers their red and missing cases.
PREFLIGHT = r'''#!/usr/bin/env bash
echo "preflight $(basename "$0" .sh)" >>"$LAND_LOG"
if [ "${LAND_PREFLIGHT_FAIL:-}" = "$(basename "$0" .sh)" ]; then
  exit 1
fi
'''

TOOL = r'''import os, subprocess, sys
with open(os.environ["LAND_LOG"], "a") as log:
    log.write("tool " + " ".join(sys.argv[1:]) + "\n")
command = sys.argv[1]
if command == "deferred-classes":
    print('{"x86_64-native": "fixture"}' if os.environ.get("LAND_DEFER_X86") == "1" else "{}")
    sys.exit(0)
if command == "host":
    sys.exit(1)
if command == "landing-exception":
    sys.exit(0)
commit = sys.argv[2]
top = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True).stdout.strip()
sha = subprocess.run(["git", "-C", top, "rev-parse", commit], capture_output=True, text=True).stdout.strip()
if command == "fetch":
    sys.exit(0)
if command in ("verify", "verify-anchored"):
    refs = subprocess.run(["git", "-C", top, "for-each-ref", f"refs/attest/soundness/{sha}/"],
                          capture_output=True, text=True).stdout.strip()
    sys.exit(0 if refs else 3)
if command == "push":
    remote = sys.argv[sys.argv.index("--remote") + 1]
    spec = f"refs/attest/soundness/{sha}/*:refs/attest/soundness/{sha}/*"
    sys.exit(subprocess.call(["git", "-C", top, "push", "-q", remote, spec]))
sys.exit(2)
'''


class LandingTrainTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="land-main-")
        self.addCleanup(self.temporary.cleanup)
        base = Path(self.temporary.name)
        self.log = base / "calls.log"
        config = base / "gitconfig"
        config.write_text("[user]\n\tname = Train\n\temail = train@example.invalid\n[commit]\n\tgpgSign = false\n"
                          "[init]\n\tdefaultBranch = main\n")
        self.env = dict(os.environ, GIT_CONFIG_GLOBAL=str(config), GIT_CONFIG_NOSYSTEM="1", LAND_LOG=str(self.log))
        for key in list(self.env):
            if key.startswith("GIT_") and key not in ("GIT_CONFIG_GLOBAL", "GIT_CONFIG_NOSYSTEM"):
                del self.env[key]
        self.remote = base / "remote.git"
        self.repo = base / "repo"
        self.other = base / "other"
        self.git(base, "init", "-q", "--bare", str(self.remote))
        self.git(base, "init", "-q", str(self.repo))
        (self.repo / "scripts").mkdir()
        (self.repo / "hooks").mkdir()
        shutil.copy2(ROOT / "hooks/pre-push", self.repo / "hooks/pre-push")
        shutil.copy2(ROOT / "scripts/land_main.sh", self.repo / "scripts/land_main.sh")
        shutil.copy2(ROOT / "scripts/github_transport.py", self.repo / "scripts/github_transport.py")
        shutil.copy2(ROOT / "scripts/check_path_case_collisions.py",
                     self.repo / "scripts/check_path_case_collisions.py")
        (self.repo / "scripts/soundness_check.sh").write_text(GATE)
        (self.repo / "scripts/soundness_check.sh").chmod(0o755)
        (self.repo / "scripts/soundness_attestation.py").write_text(TOOL)
        (self.repo / "scripts/focused_source.py").write_text(SOURCE_CHECK)
        for preflight in ("check_fmt", "check_tippy"):
            (self.repo / f"scripts/{preflight}.sh").write_text(PREFLIGHT)
            (self.repo / f"scripts/{preflight}.sh").chmod(0o755)
        (self.repo / "README").write_text("base\n")
        self.git(self.repo, "add", "-A")
        self.git(self.repo, "commit", "-qm", "base")
        self.git(self.repo, "config", "core.hooksPath", "hooks")
        self.git(self.repo, "remote", "add", "origin", str(self.remote))
        self.git(self.repo, "push", "-q", "--no-verify", "origin", "HEAD:refs/heads/main")
        self.base = self.git(self.repo, "rev-parse", "HEAD")
        for lane in ("lane-a", "lane-b"):
            self.git(self.repo, "checkout", "-q", "-b", lane, self.base)
            (self.repo / f"{lane}.txt").write_text(lane + "\n")
            self.git(self.repo, "add", "-A")
            self.git(self.repo, "commit", "-qm", lane)
        self.git(self.repo, "checkout", "-q", "--detach", self.base)
        # A second clone that lands concurrently.
        self.git(base, "clone", "-q", str(self.remote), str(self.other))
        (self.other / "concurrent.txt").write_text("concurrent\n")
        self.git(self.other, "add", "-A")
        self.git(self.other, "commit", "-qm", "concurrent landing")

    def git(self, where: Path, *args: str) -> str:
        return subprocess.run(["git", "-C", str(where), *args], check=True, capture_output=True, text=True,
                              env=self.env).stdout.strip()

    def train(self, *args: str, **extra: str) -> subprocess.CompletedProcess:
        self.log.write_text("")
        return subprocess.run(["bash", str(self.repo / "scripts/land_main.sh"), *args], cwd=self.repo,
                              env=dict(self.env, **extra), capture_output=True, text=True, timeout=120)

    def remote_main(self) -> str:
        return self.git(self.remote, "rev-parse", "refs/heads/main")

    def gate_calls(self) -> list[str]:
        return [line for line in self.log.read_text().splitlines() if line.startswith("gate")]

    def remote_records(self, commit: str) -> str:
        return self.git(self.remote, "for-each-ref", f"refs/attest/soundness/{commit}/")

    def test_two_lanes_land_as_one_attested_batch(self):
        result = self.train("lane-a", "lane-b")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        landed = self.remote_main()
        self.assertEqual(len(self.gate_calls()), 1)
        self.assertIn(landed, self.gate_calls()[0])
        files = self.git(self.remote, "ls-tree", "--name-only", landed).split()
        self.assertIn("lane-a.txt", files)
        self.assertIn("lane-b.txt", files)
        self.assertNotEqual(self.remote_records(landed), "")
        # The train gave the landing verdict against the base and its push took
        # the hook's fast path. Without a deferral the run is the full scope.
        self.assertRegex(self.log.read_text(), rf"tool verify {landed} --repo \S+ --landing --anchor {self.base}")
        self.assertRegex(self.gate_calls()[0], r"^gate --attest [0-9a-f]{40}$")
        self.assertIn("is attested", result.stdout + result.stderr)
        # The push that landed ran the hook's format and lint pre-flights.
        self.assertIn("preflight check_fmt", self.log.read_text().splitlines())
        self.assertIn("preflight check_tippy", self.log.read_text().splitlines())

    def test_train_requires_explicit_hook_even_when_local_hooks_are_disabled(self):
        # Agh intentionally never runs hooks: the train's explicit invocation
        # must retain this gate independently of source core.hooksPath.
        self.git(self.repo, "checkout", "-q", "lane-a")
        self.git(self.repo, "rm", "hooks/pre-push")
        self.git(self.repo, "commit", "-qm", "missing mandatory hook")
        self.git(self.repo, "config", "core.hooksPath", os.devnull)
        result = self.train("lane-a")
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("mandatory hooks/pre-push", result.stdout + result.stderr)
        self.assertEqual(self.remote_main(), self.base)

    def test_a_concurrent_landing_is_re_merged_and_re_attested(self):
        marker = Path(self.temporary.name, "moved")
        result = self.train("lane-a", LAND_MOVE_REMOTE_ONCE=str(marker), LAND_OTHER=str(self.other))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        landed = self.remote_main()
        calls = self.gate_calls()
        self.assertEqual(len(calls), 2, calls)
        self.assertNotIn(landed, calls[0])  # the first candidate never landed
        self.assertIn(landed, calls[1])
        files = self.git(self.remote, "ls-tree", "--name-only", landed).split()
        self.assertIn("concurrent.txt", files)
        self.assertIn("lane-a.txt", files)
        self.assertNotEqual(self.remote_records(landed), "")

    def test_a_base_that_defers_x86_runs_the_portable_scope(self):
        # The base's verifier defers the x86-64-native class and this host has
        # no x86-64 executor: the train runs the portable scope.
        result = self.train("lane-a", LAND_DEFER_X86="1")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertRegex(self.gate_calls()[0], r"^gate --attest --scope portable [0-9a-f]{40}$")
        # An executor keeps the full scope even under a deferral.
        self.git(self.remote, "update-ref", "refs/heads/main", self.base)
        result = self.train("lane-a", LAND_DEFER_X86="1", SOUNDNESS_X86_HOST="fixture-x86")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertRegex(self.gate_calls()[0], r"^gate --attest [0-9a-f]{40}$")

    def test_a_gate_failure_pushes_nothing(self):
        result = self.train("lane-a", LAND_GATE_FAIL="1")
        self.assertEqual(result.returncode, 1)
        self.assertIn("nothing was pushed", result.stderr)
        self.assertEqual(self.remote_main(), self.base)
        self.assertEqual(self.git(self.remote, "for-each-ref", "refs/attest/"), "")

    def test_early_hook_preflights_precede_attestation_and_final_push_keeps_them(self):
        result = self.train("lane-a")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        lines = self.log.read_text().splitlines()
        gate_index = next(i for i, line in enumerate(lines) if line.startswith("gate "))
        for check in ("check_fmt", "check_tippy"):
            self.assertLess(lines.index(f"preflight {check}"), gate_index)
            self.assertEqual(lines.count(f"preflight {check}"), 2)
        self.assertNotEqual(self.remote_records(self.remote_main()), "")

    def test_early_hook_preflight_format_failure_never_attests(self):
        result = self.train("lane-a", LAND_PREFLIGHT_FAIL="check_fmt")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertEqual(self.gate_calls(), [])
        self.assertEqual(self.remote_main(), self.base)
        self.assertEqual(self.git(self.repo, "for-each-ref", "refs/attest/"), "")

    def test_early_hook_preflight_lint_failure_never_attests(self):
        result = self.train("lane-a", LAND_PREFLIGHT_FAIL="check_tippy")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertEqual(self.gate_calls(), [])
        self.assertEqual(self.remote_main(), self.base)
        self.assertEqual(self.git(self.repo, "for-each-ref", "refs/attest/"), "")

    def test_early_hook_preflight_missing_command_never_attests(self):
        for check in ("check_fmt", "check_tippy"):
            with self.subTest(check=check):
                lane = f"missing-{check}"
                self.git(self.repo, "checkout", "-q", "-b", lane, self.base)
                self.git(self.repo, "rm", "-q", f"scripts/{check}.sh")
                self.git(self.repo, "commit", "-qm", f"missing {check}")
                self.git(self.repo, "checkout", "-q", "--detach", self.base)
                result = self.train(lane)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertEqual(self.gate_calls(), [])
                self.assertEqual(self.remote_main(), self.base)
                self.assertEqual(self.git(self.repo, "for-each-ref", "refs/attest/"), "")

    def test_a_conflicting_lane_stops_the_train(self):
        self.git(self.repo, "checkout", "-q", "-b", "lane-c", self.base)
        (self.repo / "lane-a.txt").write_text("conflict\n")
        self.git(self.repo, "add", "-A")
        self.git(self.repo, "commit", "-qm", "lane-c")
        self.git(self.repo, "checkout", "-q", "--detach", self.base)
        result = self.train("lane-a", "lane-c")
        self.assertEqual(result.returncode, 1)
        self.assertIn("lane lane-c does not merge", result.stderr)
        self.assertEqual(self.gate_calls(), [])
        self.assertEqual(self.remote_main(), self.base)

    def test_a_held_lease_refuses_a_second_train(self):
        common = Path(self.git(self.repo, "rev-parse", "--absolute-git-dir"))
        lease = common / "land-main.lease"
        lease.mkdir()
        (lease / "pid").write_text(f"{os.getpid()}\n")
        result = self.train("lane-a")
        self.assertEqual(result.returncode, 1)
        self.assertIn("holds the lease", result.stderr)
        # A lease whose owner is gone is reclaimed.
        (lease / "pid").write_text("999999\n")
        result = self.train("lane-a")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("reclaiming a stale lease", result.stdout)

    def test_no_push_attests_without_landing(self):
        result = self.train("--no-push", "lane-a")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.remote_main(), self.base)
        self.assertEqual(len(self.gate_calls()), 1)
        self.assertIn("--no-push: not landing it", result.stdout)

    def test_a_base_without_a_verifier_stops_the_train(self):
        # The bootstrap: the base predates the verifier. The candidate would
        # carry one, but a candidate never judges itself.
        self.git(self.repo, "rm", "-q", "scripts/soundness_attestation.py")
        self.git(self.repo, "commit", "-qm", "no verifier on main yet")
        self.git(self.repo, "push", "-q", "--no-verify", "origin", "HEAD:refs/heads/main")
        bare = self.git(self.repo, "rev-parse", "HEAD")
        self.git(self.repo, "checkout", "-q", "-b", "lane-v", bare)
        (self.repo / "scripts/soundness_attestation.py").write_text(TOOL)
        self.git(self.repo, "add", "-A")
        self.git(self.repo, "commit", "-qm", "the verifier arrives")
        self.git(self.repo, "checkout", "-q", "--detach", bare)
        result = self.train("lane-v")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("UNANCHORED", result.stdout)
        self.assertEqual(self.gate_calls(), [])
        self.assertEqual(self.remote_main(), bare)
        self.assertNotIn("tool verify", self.log.read_text())

    def test_a_lane_that_weakens_its_own_verifier_is_judged_by_the_base(self):
        # The lane's gate writes no record and its own verifier approves
        # everything; the verifier committed at the base judges it and refuses.
        self.git(self.repo, "checkout", "-q", "-b", "lane-w", self.base)
        (self.repo / "scripts/soundness_check.sh").write_text("#!/usr/bin/env bash\necho \"gate $*\" >>\"$LAND_LOG\"\n")
        (self.repo / "scripts/soundness_attestation.py").write_text(
            'import os, sys\nwith open(os.environ["LAND_LOG"], "a") as log:\n'
            '    log.write("weak-tool " + " ".join(sys.argv[1:]) + "\\n")\nsys.exit(0)\n')
        self.git(self.repo, "add", "-A")
        self.git(self.repo, "commit", "-qm", "weaken the gate and the verifier")
        self.git(self.repo, "checkout", "-q", "--detach", self.base)
        result = self.train("lane-w")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("does not verify against its base", result.stderr)
        self.assertIn(f"anchored: the verifier committed at {self.base} judges", result.stdout)
        self.assertRegex(self.log.read_text(), rf"(?m)^tool verify \S+ --repo \S+ --landing --anchor {self.base}$")
        self.assertNotIn("weak-tool", self.log.read_text())
        self.assertEqual(self.remote_main(), self.base)
        self.assertEqual(self.git(self.remote, "for-each-ref", "refs/attest/"), "")

    def test_arguments_are_checked(self):
        for args in ((), ("--attempts", "0", "lane-a"), ("no-such-lane",)):
            with self.subTest(args=args):
                result = self.train(*args)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(self.gate_calls(), [])

    def source_train(self, *args, **env):
        return self.train("--source-only", "--source-check",
                          shlex.join([sys.executable, "scripts/focused_source.py"]), *args, **env)

    def test_source_only_lands_focused_checks_without_attestation_or_workspace_sweeps(self):
        self.git(self.remote, "update-ref", f"refs/attest/soundness/{self.base}/historic", self.base)
        records = self.git(self.remote, "for-each-ref", "refs/attest/")
        result = self.source_train("lane-a", "lane-b")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        landed = self.remote_main()
        self.assertNotEqual(landed, self.base)
        self.assertEqual(self.git(self.remote, "for-each-ref", "refs/attest/"), records)
        self.assertEqual(self.gate_calls(), [])
        self.assertEqual(self.log.read_text().splitlines(), [f"source-check {landed}"])
        self.assertIn("NOT ATTESTED", result.stdout)

    @unittest.skipUnless(os.name == "posix", "POSIX descriptor inheritance")
    def test_source_only_preserves_inherited_pipe_and_normal_exec_boundaries(self):
        import fcntl

        self.git(self.repo, "checkout", "-q", "lane-a")
        control = r'''import errno, os, pathlib, sys
fd = int(os.environ["LAND_DATA_FD"])
assert os.get_inheritable(fd)
assert os.read(fd, 64) == b"original pipe data"
try:
    os.fstat(int(os.environ["LAND_PRIVATE_FD"]))
except OSError as error:
    assert error.errno == errno.EBADF
else:
    raise AssertionError("private CLOEXEC descriptor leaked")
assert sys.argv[1:] == ["two words", 'quote"', "trailing\\"]
assert pathlib.Path.cwd().name == "land-main-worktree"
print("REAL_PIPE_ARGV_CWD_ENV_OK")
'''
        (self.repo / "scripts/focused_source.py").write_text(control)
        self.git(self.repo, "add", "scripts/focused_source.py")
        self.git(self.repo, "commit", "-qm", "fixture pipe control")
        reader, writer = os.pipe()
        self.addCleanup(os.close, reader)
        os.set_inheritable(reader, True)
        try:
            os.write(writer, b"original pipe data")
        finally:
            os.close(writer)
        with tempfile.TemporaryFile() as private:
            private_fd = fcntl.fcntl(private.fileno(), fcntl.F_DUPFD_CLOEXEC, 64)
            try:
                command = shlex.join([sys.executable, "scripts/focused_source.py",
                                      "two words", 'quote"', "trailing\\"])
                result = subprocess.run(
                    ["bash", str(self.repo / "scripts/land_main.sh"), "--source-only",
                     "--source-check", command, "lane-a"], cwd=self.repo,
                    env=dict(self.env, LAND_DATA_FD=str(reader),
                             LAND_PRIVATE_FD=str(private_fd)), close_fds=False,
                    capture_output=True, text=True, timeout=60)
            finally:
                os.close(private_fd)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("REAL_PIPE_ARGV_CWD_ENV_OK", result.stdout)
        self.assertNotEqual(self.remote_main(), self.base)
        self.assertEqual(self.git(self.remote, "for-each-ref", "refs/attest/"), "")

    def test_source_only_failure_pushes_nothing_and_mints_no_record(self):
        result = self.source_train("lane-a", LAND_SOURCE_FAIL="19")
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.remote_main(), self.base)
        self.assertEqual(self.gate_calls(), [])
        self.assertEqual(self.git(self.repo, "for-each-ref", "refs/attest/"), "")

    def test_source_only_remerges_advancing_main_and_reruns_only_focused_checks(self):
        marker = str(Path(self.temporary.name) / "source-moved")
        result = self.source_train("lane-a", LAND_SOURCE_MOVE_ONCE=marker, LAND_OTHER=str(self.other))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        landed = self.remote_main()
        lines = self.log.read_text().splitlines()
        self.assertEqual(len(lines), 2, lines)
        self.assertTrue(all(line.startswith("source-check ") for line in lines))
        self.assertEqual(lines[-1], f"source-check {landed}")
        self.assertNotEqual(lines[0], lines[-1])
        self.assertIn("concurrent.txt", self.git(self.remote, "ls-tree", "--name-only", landed))
        self.assertEqual(self.remote_records(landed), "")

    def test_source_only_rejects_candidate_mutation_during_qualification(self):
        result = self.source_train("lane-a", LAND_SOURCE_DIRTY="1")
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("candidate changed", result.stderr)
        self.assertEqual(self.remote_main(), self.base)

    def test_source_only_dry_run_checks_without_publishing_or_attesting(self):
        result = self.source_train("--no-push", "lane-a")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.remote_main(), self.base)
        self.assertEqual(len(self.log.read_text().splitlines()), 1)
        self.assertEqual(self.gate_calls(), [])
        self.assertEqual(self.git(self.repo, "for-each-ref", "refs/attest/"), "")

    def test_source_only_requires_explicit_nonempty_checks_and_separate_mode(self):
        for args in (("--source-only", "lane-a"),
                     ("--source-check", "true", "lane-a"),
                     ("--source-only", "--source-check", " ", "lane-a")):
            with self.subTest(args=args):
                result = self.train(*args)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(self.remote_main(), self.base)
                self.assertEqual(self.gate_calls(), [])


    def resume_candidate(self):
        worktree = Path(self.temporary.name) / "resume-worktree"
        self.git(self.repo, "worktree", "add", "-q", "--detach", str(worktree), self.base)
        self.git(worktree, "merge", "--no-ff", "--no-edit", "lane-a")
        return worktree, self.git(worktree, "rev-parse", "HEAD")

    def resume_train(self, worktree, candidate, *lanes, **env):
        return self.source_train("--resume-source-candidate", candidate,
                                 "--worktree", str(worktree), *(lanes or ("lane-a",)), **env)

    def preflight_failure_env(self, *, unavailable_readback=False):
        """Fail only the actual local transport's push dry-run, never a check."""
        directory = Path(self.temporary.name) / "transport-bin"
        directory.mkdir()
        marker = directory / "preflight-failed"
        helper = directory / "git_failure.py"
        helper.write_text(
            "import os, pathlib, sys\n"
            f"marker = pathlib.Path({str(marker)!r})\n"
            "args = sys.argv[1:]\n"
            "if 'push' in args and '--dry-run' in args:\n"
            "    marker.touch()\n"
            "    sys.stderr.write('fatal: did not receive expected object 5d3010\\n')\n"
            "    sys.exit(128)\n"
            f"if {unavailable_readback!r} and marker.exists() and 'for-each-ref' in args and {str(self.remote.resolve())!r} in args:\n"
            "    sys.stderr.write('fixture remote readback unavailable\\n')\n"
            "    sys.exit(128)\n"
            f"os.execv({shutil.which('git')!r}, [{shutil.which('git')!r}, *args])\n")
        wrapper = directory / "git"
        wrapper.write_text("#!/bin/sh\nexec " + shlex.join([sys.executable, "-I", "-B", str(helper)]) + ' "$@"\n')
        wrapper.chmod(0o755)
        return {"PATH": str(directory) + os.pathsep + self.env["PATH"]}

    def test_source_resume_preflight_failure_reports_unchanged_main_and_retains_reason(self):
        worktree, candidate = self.resume_candidate()
        result = self.resume_train(worktree, candidate, **self.preflight_failure_env())
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("preflight refused (exit 128; write not invoked)", result.stderr)
        self.assertIn(f"readback confirms origin/main unchanged at {self.base}", result.stderr)
        self.assertNotIn("main moved during source resume", result.stderr)
        self.assertEqual(self.remote_main(), self.base)
        self.assertEqual(self.git(worktree, "rev-parse", "HEAD"), candidate)
        self.assertEqual(self.log.read_text().splitlines(), [f"source-check {candidate}"])
        receipts = list((self.repo / ".git/github-transport-receipts").glob("*/dry-run.stderr"))
        self.assertEqual(len(receipts), 1)
        self.assertIn(str(receipts[0].parent), result.stderr)
        self.assertIn("did not receive expected object 5d3010", receipts[0].read_text())
        self.assertFalse((receipts[0].parent / "write.stdout").exists())
        self.assertEqual(self.remote_records(candidate), "")

    def test_source_resume_failed_readback_does_not_invent_ref_movement(self):
        worktree, candidate = self.resume_candidate()
        result = self.resume_train(worktree, candidate, **self.preflight_failure_env(unavailable_readback=True))
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("preflight refused (exit 128; write not invoked)", result.stderr)
        self.assertIn("readback unavailable, ref state unknown", result.stderr)
        self.assertNotIn("main moved during source resume", result.stderr)
        self.assertNotIn("readback confirms", result.stderr)
        self.assertEqual(self.remote_main(), self.base)
        self.assertEqual(self.git(worktree, "rev-parse", "HEAD"), candidate)
        self.assertEqual(self.log.read_text().splitlines(), [f"source-check {candidate}"])
        receipts = list((self.repo / ".git/github-transport-receipts").glob("*/dry-run.stderr"))
        self.assertEqual(len(receipts), 1)
        self.assertIn(str(receipts[0].parent), result.stderr)
        self.assertIn("did not receive expected object 5d3010", receipts[0].read_text())
        self.assertFalse((receipts[0].parent / "write.stdout").exists())
        self.assertEqual(self.remote_records(candidate), "")

    def test_source_resume_publishes_existing_exact_candidate_without_recreating_it(self):
        worktree, candidate = self.resume_candidate()
        head_file = Path(self.git(worktree, "rev-parse", "--path-format=absolute", "--git-path", "HEAD"))
        before = (head_file.stat().st_ino, head_file.stat().st_mtime_ns, head_file.read_bytes())
        result = self.resume_train(worktree, candidate)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.remote_main(), candidate)
        self.assertEqual(self.git(worktree, "rev-parse", "HEAD"), candidate)
        self.assertEqual((head_file.stat().st_ino, head_file.stat().st_mtime_ns, head_file.read_bytes()), before)
        self.assertEqual(self.log.read_text().splitlines(), [f"source-check {candidate}"])
        self.assertEqual(self.remote_records(candidate), "")
        self.assertIn("no checkout or recreation", result.stdout)
        self.assertIn("NOT ATTESTED", result.stdout)

    def test_source_resume_requires_source_scope_explicit_existing_worktree_and_raw_sha(self):
        worktree, candidate = self.resume_candidate()
        absent = Path(self.temporary.name) / "not-created"
        for args in (("--source-only", "--source-check", "true", "--resume-source-candidate", candidate, "lane-a"),
                     ("--resume-source-candidate", candidate, "--worktree", str(worktree), "lane-a"),
                     ("--source-only", "--source-check", "true", "--resume-source-candidate", "HEAD", "--worktree", str(worktree), "lane-a"),
                     ("--source-only", "--source-check", "true", "--resume-source-candidate", candidate, "--worktree", str(absent), "lane-a")):
            with self.subTest(args=args):
                result = self.train(*args)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(self.remote_main(), self.base)
                self.assertEqual(self.git(worktree, "rev-parse", "HEAD"), candidate)
                self.assertFalse(absent.exists())
                self.assertEqual(self.gate_calls(), [])

    def test_source_resume_refuses_wrong_head_without_checkout(self):
        worktree, candidate = self.resume_candidate()
        result = self.resume_train(worktree, self.git(self.repo, "rev-parse", "lane-a"))
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("HEAD differs", result.stderr)
        self.assertEqual(self.remote_main(), self.base)
        self.assertEqual(self.git(worktree, "rev-parse", "HEAD"), candidate)
        self.assertEqual(self.log.read_text(), "")

    def test_source_resume_refuses_dirty_existing_candidate(self):
        worktree, candidate = self.resume_candidate()
        (worktree / "README").write_text("owned dirty input\n")
        result = self.resume_train(worktree, candidate)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("dirty", result.stderr)
        self.assertEqual(self.remote_main(), self.base)
        self.assertEqual((worktree / "README").read_text(), "owned dirty input\n")
        self.assertEqual(self.git(worktree, "rev-parse", "HEAD"), candidate)

    def test_source_resume_refuses_main_outside_candidate_ancestry(self):
        worktree, candidate = self.resume_candidate()
        self.git(self.other, "push", "-q", "--no-verify", "origin", "HEAD:refs/heads/main")
        advanced = self.remote_main()
        result = self.resume_train(worktree, candidate)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("main advanced beyond", result.stderr)
        self.assertEqual(self.remote_main(), advanced)
        self.assertEqual(self.git(worktree, "rev-parse", "HEAD"), candidate)
        self.assertEqual(self.log.read_text(), "")

    def test_source_resume_refuses_lane_not_already_in_candidate(self):
        worktree, candidate = self.resume_candidate()
        result = self.resume_train(worktree, candidate, "lane-a", "lane-b")
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("lane lane-b is not an ancestor", result.stderr)
        self.assertEqual(self.remote_main(), self.base)
        self.assertEqual(self.git(worktree, "rev-parse", "HEAD"), candidate)
        self.assertEqual(self.log.read_text(), "")

    def test_source_resume_retains_focused_failure_and_mutation_refusals(self):
        for setting, value in (("LAND_SOURCE_FAIL", "19"), ("LAND_SOURCE_DIRTY", "1")):
            with self.subTest(setting=setting):
                worktree, candidate = self.resume_candidate()
                result = self.resume_train(worktree, candidate, **{setting: value})
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(self.remote_main(), self.base)
                self.assertEqual(self.git(worktree, "rev-parse", "HEAD"), candidate)
                self.assertEqual(self.remote_records(candidate), "")
                self.git(worktree, "checkout", "--", "README")
                self.git(self.repo, "worktree", "remove", str(worktree))

    def test_source_resume_stops_when_main_moves_during_checks(self):
        worktree, candidate = self.resume_candidate()
        marker = str(Path(self.temporary.name) / "resume-main-moved")
        result = self.resume_train(worktree, candidate, LAND_SOURCE_MOVE_ONCE=marker, LAND_OTHER=str(self.other))
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("main moved during source resume", result.stderr)
        self.assertIn(f"base {self.base}, observed {self.git(self.other, 'rev-parse', 'HEAD')}", result.stderr)
        self.assertNotIn("readback confirms", result.stderr)
        self.assertNotIn("ref state unknown", result.stderr)
        self.assertEqual(self.remote_main(), self.git(self.other, "rev-parse", "HEAD"))
        self.assertEqual(self.git(worktree, "rev-parse", "HEAD"), candidate)
        self.assertEqual(self.log.read_text().splitlines(), [f"source-check {candidate}"])
        self.assertEqual(self.remote_records(candidate), "")

    def test_source_resume_still_checks_when_candidate_is_already_main(self):
        worktree, candidate = self.resume_candidate()
        self.git(worktree, "push", "-q", "--no-verify", "origin", "HEAD:refs/heads/main")
        result = self.resume_train(worktree, candidate)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.remote_main(), candidate)
        self.assertEqual(self.log.read_text().splitlines(), [f"source-check {candidate}"])
        self.assertEqual(self.remote_records(candidate), "")

    def test_source_resume_retains_train_lease(self):
        worktree, candidate = self.resume_candidate()
        lease = self.repo / ".git/land-main.lease"
        lease.mkdir()
        (lease / "pid").write_text(f"{os.getpid()}\n")
        result = self.resume_train(worktree, candidate)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("holds the lease", result.stderr)
        self.assertEqual(self.remote_main(), self.base)
        self.assertEqual(self.log.read_text(), "")
        self.assertEqual(self.git(worktree, "rev-parse", "HEAD"), candidate)


if __name__ == "__main__":
    unittest.main()
