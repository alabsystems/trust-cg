"""scripts/soundness_remote.sh against a fake x86-64 host behind a fake ssh.

The fake host (scripts/tests/soundness_fixture.py) runs the PRODUCTION remote
script in a local "remote home"; only the x86-64 gate it would run there is
replaced by a writer of a native-host record. Nothing reaches a network.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import soundness_fixture as fixture  # noqa: E402

REMOTE = "scripts/soundness_remote.sh"
# A non-ASCII remote directory name (bash quotes it as $'...' under LC_ALL=C).
NON_ASCII = "caf" + chr(0xE9)
INCOMING = ".cache/trust-cg/soundness-remote/incoming"


def mode(path: Path) -> int:
    return stat.S_IMODE(path.lstat().st_mode)


def remote_prelude(cg: Path) -> str:
    """What remote() sends ahead of REMOTE_SCRIPT: the private-cache rule's
    source and the incoming directory, quoted by bash's own printf %q."""
    return subprocess.run(["bash", "-c", 'printf "private_cache_py=%q\\nincoming=%q\\n" "$(cat "$1")" "$2"', "_",
                           str(cg / "scripts" / "private_cache.py"), INCOMING],
                          capture_output=True, text=True, check=True).stdout


class RemoteExecutorTests(unittest.TestCase):
    def setUp(self):
        self.directory = fixture.FixtureDirectory("soundness-remote-")
        self.addCleanup(self.directory.cleanup)
        self.world = fixture.Constellation(Path(self.directory.name))
        self.out = Path(self.directory.name, "out")

    def remote(self, phase: str, umask: int = -1, **extra: str) -> subprocess.CompletedProcess:
        args = ["bash", str(self.world.cg / REMOTE), phase, "--repo", str(self.world.cg), "--host", "fixture-x86"]
        if phase == "run":
            args += ["--commit", self.world.head(), "--out", str(self.out)]
        self.world.log.write_text("")
        return subprocess.run(args, env=self.world.env(**extra), capture_output=True, text=True, timeout=300,
                              umask=umask)

    def records(self) -> str:
        return fixture.git(self.world.cg, "for-each-ref", "--format=%(refname) %(objectname)", "refs/attest/")

    def test_probe_names_every_missing_requirement(self):
        result = self.remote("probe")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("REMOTE-OK Linux x86_64", result.stdout)
        result = self.remote("probe", FIXTURE_REMOTE_NO_CREDENTIALS="1")
        self.assertNotEqual(result.returncode, 0)
        for repo in ("trust-ir", "clean", "ay"):
            self.assertIn(f"cannot-read-https://github.com/{fixture.ORG}/{repo}.git", result.stdout)
        # Without the fake x86-64 uname the host is this machine: not x86-64.
        env_path = self.world.env()["FIXTURE_REMOTE_PATH"].split(":", 1)[1]
        result = self.remote("probe", FIXTURE_REMOTE_PATH=env_path)
        if os.uname().machine not in ("x86_64", "amd64"):
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("machine=", result.stdout)

    def test_unreachable_host_fails_and_imports_nothing(self):
        result = self.remote("run", FIXTURE_SSH_UNREACHABLE="1")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unreachable or unqualified", result.stderr)
        self.assertEqual((self.out / "status").read_text().strip(), "1")
        self.assertEqual(self.records(), "")

    def test_run_imports_a_checked_native_record_and_reuses_it(self):
        result = self.remote("run")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        oid = (self.out / "record_oid").read_text().strip()
        triple = (self.out / "triple").read_text().strip()
        self.assertEqual(triple, "x86_64-unknown-linux-gnu")
        # Staged, not published: only the gate's own atomic record write
        # creates refs/attest/soundness/<C>/<triple>.
        self.assertEqual(self.records(), "")
        self.assertEqual(fixture.git(self.world.cg, "for-each-ref", "--format=%(refname) %(objectname)",
                                     "refs/soundness/"),
                         f"refs/soundness/import/{self.world.head()}/{triple} {oid}")
        # A second dispatch of the same commit reuses the record (same commit only).
        result = self.remote("run")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("reusing the x86-64 record", result.stdout)
        self.assertFalse(any(line.startswith("ssh") for line in self.world.workloads()))

    def test_later_dispatches_send_an_incremental_bundle(self):
        self.assertEqual(self.remote("run").returncode, 0)
        (self.world.cg / "CHANGE").write_text("next\n")
        self.world.commit_all("next commit")
        result = self.remote("run")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        verify = subprocess.run(["git", "-C", str(self.world.cg), "bundle", "list-heads", str(self.out / "candidate.bundle")],
                                capture_output=True, text=True)
        self.assertIn("refs/soundness/dispatch/", verify.stdout)
        header = (self.out / "candidate.bundle").read_bytes().split(b"\n\n", 1)[0].decode()
        self.assertRegex(header, r"(?m)^-[0-9a-f]{40}")  # prerequisites: not the whole history

    def test_failed_remote_legs_fail_the_dispatch(self):
        result = self.remote("run", FIXTURE_X86_GATE_FAIL="1")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("did not pass", result.stdout + result.stderr)
        self.assertEqual(self.records(), "")

    def test_emulated_host_record_is_refused_locally(self):
        # The remote's own writer already refuses it...
        result = self.remote("run", FIXTURE_X86_EMULATED="1")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("not native x86-64", result.stdout)
        self.assertEqual(self.records(), "")
        # ...and a host that skips that check is refused by the importer.
        result = self.remote("run", FIXTURE_X86_EMULATED="1", FIXTURE_X86_BYPASS_WRITE="1")
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("failed its local checks", result.stderr)
        self.assertIn("QEMU/TCG", result.stdout)
        self.assertEqual(self.records(), "")

    def test_remote_refuses_a_dirty_clone_and_a_wrong_tree(self):
        self.assertEqual(self.remote("run").returncode, 0)
        remote_clone = Path(self.directory.name, "remote-home/.cache/trust-cg/soundness-remote/trust-cg")
        script = (self.world.cg / REMOTE).read_text()
        body = re.search(r"\nREMOTE_SCRIPT='\n(.*?)\n'\n", script, re.S).group(1)
        commit = self.world.head()
        bundle = Path(self.directory.name, "remote-home/.cache/trust-cg/soundness-remote/incoming", f"{commit}.bundle")
        env = self.world.env()
        env.update(HOME=str(Path(self.directory.name, "remote-home")),
                   PATH=env["FIXTURE_REMOTE_PATH"])

        def remote_run(tree: str) -> subprocess.CompletedProcess:
            return subprocess.run(["/bin/bash", "-s", "--", "run", "", commit, tree, str(bundle)],
                                  input=remote_prelude(self.world.cg) + body, env=env, capture_output=True,
                                  text=True, timeout=120)

        result = remote_run("0" * 40)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("REMOTE-FAIL: tree mismatch", result.stdout)
        (remote_clone / "stray").write_text("dirty\n")
        result = remote_run(fixture.git(self.world.cg, "rev-parse", "HEAD^{tree}"))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("is dirty", result.stdout)

    def test_remote_cache_directories_are_private_under_umask_0002(self):
        """X-HOST-P13: on an executor whose login umask is 0002, a `mkdir -p`
        made ~/.cache and ~/.cache/trust-cg 0775, and AY's identity rule then
        refused AY there. Every directory the remote side creates under the
        cache is 0700 (scripts/private_cache.py); the clone, the x86-64 legs
        (here the fixture's gate, which writes Python caches and the record's
        git objects in the clone) and the bundles all write under umask 077;
        and an existing directory is never changed. The fake ssh joins its
        arguments as OpenSSH does, so an unset SOUNDNESS_X86_REMOTE_DIR
        reaches the remote as an empty argument and the default clone
        directory is used."""
        home = Path(self.directory.name, "remote-home")
        cache = home / ".cache"
        result = self.remote("probe", umask=0o002)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        clone = cache / "trust-cg" / "soundness-remote" / "trust-cg"
        incoming = home / INCOMING
        for created in (cache, cache / "trust-cg", cache / "trust-cg" / "soundness-remote", clone, incoming):
            self.assertEqual(mode(created), 0o700, created)
        self.assertFalse((home / "trust").exists(), "an empty remote-dir argument was dropped")

        result = self.remote("run", umask=0o002)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        commit = self.world.head()
        for bundle in (incoming / f"{commit}.bundle", incoming / f"record-{commit}.bundle"):
            self.assertEqual(mode(bundle), 0o600, bundle)
        self.assertEqual(mode(clone / ".git"), 0o700)
        written = [path for path in clone.rglob("*") if not path.is_symlink()]
        self.assertTrue([path for path in written if "__pycache__" in path.parts], "the legs wrote Python caches")
        self.assertTrue(list((clone / ".git" / "refs" / "attest").rglob("*")), "the legs wrote the record")
        self.assertEqual([f"{mode(path):04o} {path.relative_to(clone)}" for path in written if mode(path) & 0o077], [])

        # A remote whose ~/.cache/trust-cg an earlier run left 0775: never
        # changed (AY's refusal names it and the remedy); what is created
        # below it is still 0700.
        fresh = fixture.FixtureDirectory("soundness-remote-open-")
        self.addCleanup(fresh.cleanup)
        open_home = Path(fresh.name, "home")
        (open_home / ".cache" / "trust-cg").mkdir(parents=True)
        os.chmod(open_home / ".cache" / "trust-cg", 0o775)
        result = self.remote("probe", umask=0o002, FIXTURE_REMOTE_HOME=str(open_home))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(mode(open_home / ".cache" / "trust-cg"), 0o775)
        self.assertEqual(mode(open_home / ".cache" / "trust-cg" / "soundness-remote"), 0o700)
        self.assertEqual(mode(open_home / INCOMING), 0o700)

    def test_a_tilde_remote_dir_is_the_remote_home(self):
        """The phase arguments reach the remote quoted, so its shell no longer
        expands a "~" in SOUNDNESS_X86_REMOTE_DIR; the remote script reads a
        leading "~/" as its HOME itself (as the unquoted argument was read
        before), and a path with a space arrives whole."""
        home = Path(self.directory.name, "remote-home")
        result = self.remote("probe", umask=0o002, SOUNDNESS_X86_REMOTE_DIR="~/tcg x86")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(mode(home / "tcg x86"), 0o700)
        self.assertFalse((home / "~").exists(), "no literal ~ directory")
        result = self.remote("run", umask=0o002, SOUNDNESS_X86_REMOTE_DIR="~/tcg x86")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue((home / "tcg x86" / ".git").is_dir())
        self.assertFalse((home / "~").exists())
        self.assertFalse((home / ".cache" / "trust-cg" / "soundness-remote" / "trust-cg").exists())
        # A path relative to the remote HOME, as before.
        result = self.remote("probe", SOUNDNESS_X86_REMOTE_DIR="relative/clone")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue((home / "relative" / "clone").is_dir())

    def test_a_remote_dir_reached_through_a_symlink_is_entered_by_its_physical_path(self):
        """X-HOST-P13 third closure audit: a name that runs through a symlink
        can be re-pointed between its use and a later one. The remote enters
        the clone ONCE with `cd -P`, so the tree it checks, the legs it runs
        and the remote gate's own TRUST_CG_DIR (derived from the shell's
        `pwd`, which the fake gate records as `pwd`) all name the physical
        directory, never the symlink SOUNDNESS_X86_REMOTE_DIR ran through."""
        home = Path(os.path.realpath(self.directory.name), "remote-home")
        physical = home / "physical"
        physical.mkdir(mode=0o700)
        os.chmod(physical, 0o700)
        (home / "via-link").symlink_to(physical)
        result = self.remote("run", umask=0o002, SOUNDNESS_X86_REMOTE_DIR="~/via-link/clone")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        prefix = "fixture-x86-bytecode "
        witnesses = [json.loads(line[len(prefix):]) for line in self.world.workloads() if line.startswith(prefix)]
        self.assertEqual(len(witnesses), 1, self.world.workloads())
        self.assertEqual(witnesses[0]["pwd"], str(physical / "clone"))
        self.assertEqual(witnesses[0]["repo"], str(physical / "clone"))
        self.assertTrue((physical / "clone" / ".git").is_dir())

    def test_a_remote_dir_a_posix_login_shell_would_split_is_refused_by_name(self):
        """X-HOST-P13 second audit: bash's %q quotes a control character (and
        a non-ASCII byte under LC_ALL=C) as $'...', which dash reads literally,
        and escapes a quote inside it as \\', which dash does not honor, so
        SOUNDNESS_X86_REMOTE_DIR="d<TAB>'; touch INJECTED #" ran `touch
        INJECTED` on a remote whose login shell is dash. Every value with a
        character outside the safe set is refused by name before anything is
        sent; the control line shows the injection the refusal prevents."""
        value = "d\t'; touch INJECTED #"
        dash = shutil.which("dash")
        if dash is not None:
            # The control: the line the script used to send, read by dash.
            line = subprocess.run(["bash", "-c", 'printf " %q" run "$1" c0ffee', "_", value], capture_output=True,
                                  text=True, check=True).stdout
            control = Path(self.directory.name, "dash-control")
            control.mkdir()
            subprocess.run([dash, "-c", f"printf '[%s]' {line}"], cwd=control, capture_output=True, text=True)
            self.assertTrue((control / "INJECTED").exists(), "the control: dash runs the tail of a %q $'...' word")
        for bad in (value, NON_ASCII, "line\nbreak", "a$(id)", "a`id`", "a;b", "a'b", 'a"b', "a*b", "a\\b"):
            for phase in ("probe", "run"):
                with self.subTest(value=bad, phase=phase):
                    result = self.remote(phase, SOUNDNESS_X86_REMOTE_DIR=bad,
                                         LC_ALL="C" if bad == NON_ASCII else "C.utf8")
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertIn("soundness_remote: SOUNDNESS_X86_REMOTE_DIR holds a character outside", result.stderr)
                    self.assertEqual([line for line in self.world.workloads() if line.startswith("ssh ")], [],
                                     "nothing was sent to the remote")
                    self.assertEqual([path for path in Path(self.directory.name).rglob("INJECTED")
                                      if "dash-control" not in path.parts], [])
        # The characters an ordinary path needs still pass, as before.
        result = self.remote("probe", SOUNDNESS_X86_REMOTE_DIR="~/x86_64-runner/clone.v2,a+b@c:d=e")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
