"""scripts/host_boundary.py: the host trust boundary of an attested run (LD-73).

The user's own toolchain installs, git and its configuration and the
candidate checkout are the host's trust boundary; an --attest run must still
fail closed there, refusing (FAIL with the path and remedy, no attestation)
when any tool it executes or configuration it reads is writable by another
user: world-writable, group-writable by a group with a member other than
this user (/etc/group members and every account's primary group; the
SOUNDNESS_EXTRA_* files add entries), owned by another account, or writable
through a POSIX ACL. A group-writable path in a group with no other member
is not writable by another user. The X-HOST-P13 sixth closure audit's
reproducers: a substituted lake in a group-writable ~/.elan/bin and a
substituted rustup in a group-writable ~/.cargo/bin each turned into an
attested pass or ran as the gate's user. The rule's unit cases use files
in /etc's format and synthetic metadata; the gate cases run the production
soundness_check.sh in the fixture constellation with its primary group made
shared through those files. Test rung, not proof.

Ruling LD-75 (the round-3 verifier's four findings against fa2d651e8): an
alternate object store a judged git directory borrows from is judged as a
tree (and GIT_OBJECT_DIRECTORY / GIT_ALTERNATE_OBJECT_DIRECTORIES refuse); a
directory's default ACL is judged and the rest of an --attest run runs under
umask 077; a directory above a checkout, cache or Cargo home in which another
user can create the `.cargo` Cargo reads refuses, sticky or not; the extra
account files never make a group private. LD-75's repair (the round-4
verifier's findings): a location variable set to a value that is not an
absolute path refuses by name, and an ancestor refused for its default ACL is
reported as that.

Ruling OD-XHOST-GATE-CWD-20261025 (the sixth closure audit's F1-F3): an
attested run starts nothing in its caller's working directory, which the
check does not judge (it works in / until the check passes, then in the
candidate), and every inline python3 of the gate scripts runs with -I. Its
repair round 2 (two verifiers): the gate finds its own directory without
CDPATH and checks it holds the script bash runs, refuses a relative or empty
PATH entry before the scrub, starts every python3 (scripts too) with -I, held
statically by GatePythonIsolationTests with every `cd` CDPATH-proof, and the
check judges each directory a user-site .pth file names and refuses the code
a python3 run without -I would execute from there at startup. Its repair
round 3 (the second verification's two older fail-opens): the gate pins one
python3 by its canonical path before its prelude changes PATH and starts
every python3 by it, the check judges exactly that file (--python3) and
refuses one that is not the interpreter running it, and a bare python3 after
a gate script's pin point fails GatePythonIsolationTests; an --attest run
that bash does not read as a script from the candidate's
scripts/soundness_check.sh file (stdin, -c, sourced, another file) refuses
before any program; and a user-site .pth holding a character str.splitlines
breaks a line at besides \\n and \\r refuses. Its repair round 4 (the third
verification: round 3 judged the pinned interpreter alone while the legs
start python3 by name on the prelude's PATH): the check refuses the run
unless the first python3 on that PATH is the pinned file with the same
pyvenv.cfg around its name (a wrapper in $HOME/.elan/bin, a virtual
environment's python3 first on PATH and a pyvenv.cfg another user could
create each refuse, and the fixture's fakes find python3 by name again), a
pin that is a `#!` script or, on Linux, not the file /proc/self/exe names
refuses, and the scripts an --attest run starts before the check are named
by the gate's own directory, never by a caller's TRUST_CG_DIR.
"""

from __future__ import annotations

import contextlib
import grp
import importlib.util
import io
import json
import os
from pathlib import Path
import pwd
import re
import shlex
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(Path(__file__).resolve().parent))
import soundness_fixture as fixture  # noqa: E402


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


HB = load("host_boundary", ROOT / "scripts" / "host_boundary.py")
GID = os.getegid()
EUID = os.geteuid()
GROUP = grp.getgrgid(GID).gr_name
ME = pwd.getpwuid(EUID).pw_name
HAS_SETFACL = unittest.skipUnless(shutil.which("setfacl"), "no setfacl")
HOST_GROUP_SHARED = HB.Accounts(EUID).others(GID)
NEEDS_PRIVATE_GROUP = unittest.skipIf(
    bool(HOST_GROUP_SHARED), f"this host's group {GROUP} has another member: {HOST_GROUP_SHARED}")


def mode(path: Path) -> int:
    return stat.S_IMODE(os.lstat(path).st_mode)


def fake_stat(mode_bits: int, uid: int = EUID, gid: int = GID, kind: int = stat.S_IFREG) -> os.stat_result:
    return os.stat_result((kind | mode_bits, 1, 1, 1, uid, gid, 0, 0, 0, 0))


def verdict(boundary, path: str, metadata: os.stat_result) -> str:
    """The rule's reason another user can write `path`, or `(accepted)`."""
    return boundary.problem(path, metadata) or "(accepted)"


class DarwinCOracleBoundaryTests(unittest.TestCase):
    def test_judges_selected_compiler_install_and_sdk(self):
        boundary = mock.Mock()
        boundary.refusals = []
        boundary.resolve.side_effect = lambda path, place: path
        answers = [subprocess.CompletedProcess([], 0, b"/Developer/Toolchain/usr/bin/clang\n", b""),
                   subprocess.CompletedProcess([], 0, b"/Developer/SDKs/MacOSX.sdk\n", b"")]
        with mock.patch.object(HB.subprocess, "run", side_effect=answers) as run, \
             mock.patch.object(HB, "_install_root", return_value="/Developer/Toolchain/usr"):
            HB.judge_darwin_c_oracle(boundary)
        self.assertEqual(run.call_args_list[0].args[0],
                         ["/usr/bin/xcrun", "--sdk", "macosx", "--find", "clang"])
        self.assertEqual(run.call_args_list[1].args[0],
                         ["/usr/bin/xcrun", "--sdk", "macosx", "--show-sdk-path"])
        boundary.judge_tree.assert_any_call("/Developer/Toolchain/usr", "the Darwin C compiler install root")
        boundary.judge_tree.assert_any_call("/Developer/SDKs/MacOSX.sdk", "the Darwin C oracle SDK")

    def test_refused_xcrun_never_executes(self):
        boundary = mock.Mock()
        boundary.refusals = ["xcrun writable by another user"]
        boundary.resolve.return_value = None
        with mock.patch.object(HB.subprocess, "run") as run:
            HB.judge_darwin_c_oracle(boundary)
        run.assert_not_called()

    def test_malformed_discovery_refuses_before_judging_selected_tools(self):
        boundary = mock.Mock()
        boundary.refusals = []
        boundary.resolve.side_effect = lambda path, place: path
        with mock.patch.object(HB.subprocess, "run", return_value=
                               subprocess.CompletedProcess([], 0, b"clang\n", b"")):
            HB.judge_darwin_c_oracle(boundary)
        boundary.refuse.assert_called_once()
        boundary.judge_tree.assert_not_called()


class RuleTests(unittest.TestCase):
    def setUp(self):
        # Canonical, as the check reports every path (macOS's /var is a link).
        self.base = Path(os.path.realpath(tempfile.mkdtemp(prefix="host-boundary-")))
        os.chmod(self.base, 0o700)
        self.addCleanup(shutil.rmtree, self.base, True)

    def accounts(self, group: str = "", passwd: str = "") -> HB.Accounts:
        files = {}
        for name, text in (("group", group), ("passwd", passwd)):
            if text:
                path = self.base / f"extra-{name}"
                path.write_text(text)
                files[name] = str(path)
        return HB.Accounts(EUID, files.get("group"), files.get("passwd"))

    def existing(self, name: str) -> Path:
        """A file of this user's, for a verdict on synthetic metadata (an
        ACL is read from the path itself)."""
        path = self.base / name
        path.write_text("")
        return path

    def shared_member(self) -> HB.Accounts:
        return self.accounts(group=f"{GROUP}:x:{GID}:cogroup\n",
                             passwd="cogroup:x:4242:4242::/nonexistent:/usr/sbin/nologin\n")

    def loose_tree(self) -> Path:
        tree = self.base / "tree"
        (tree / "bin").mkdir(parents=True)
        (tree / "bin" / "tool").write_text("#!/bin/sh\n")
        for path, bits in ((tree, 0o775), (tree / "bin", 0o775), (tree / "bin" / "tool", 0o775)):
            os.chmod(path, bits)
        return tree

    @NEEDS_PRIVATE_GROUP
    def test_a_group_with_no_other_member_is_not_another_writer(self):
        tree = self.loose_tree()
        boundary = HB.Boundary(self.accounts())
        boundary.judge_tree(str(tree), "test tree")
        boundary.judge_search_path(str(tree / "bin"))
        self.assertEqual(boundary.refusals, [])
        self.assertGreaterEqual(boundary.entries, 3)

    def test_a_listed_member_makes_the_group_shared(self):
        tree = self.loose_tree()
        boundary = HB.Boundary(self.shared_member())
        boundary.judge_tree(str(tree), "test tree")
        self.assertEqual(len(boundary.refusals), 1, boundary.refusals)
        self.assertIn(f"{tree} (test tree): group-writable (mode 0775) by group {GROUP} (gid {GID}), which has "
                      "another member: member cogroup", boundary.refusals[0])

    def test_an_account_whose_primary_group_it_is_makes_the_group_shared(self):
        accounts = self.accounts(passwd=f"cogroup:x:4242:{GID}::/nonexistent:/usr/sbin/nologin\n")
        self.assertIn("cogroup (uid 4242) has it as primary group", accounts.others(GID))
        boundary = HB.Boundary(accounts)
        self.assertRegex(verdict(boundary,str(self.existing("f")), fake_stat(0o664)), r"has it as primary group")

    def test_a_member_with_no_account_and_a_group_with_no_entry_count_as_other_members(self):
        accounts = self.accounts(group=f"{GROUP}:x:{GID}:ghost\n")
        self.assertIn("member ghost has no account", accounts.others(GID))
        unknown = 4242420
        self.assertIn(f"no group entry names gid {unknown}, so its members are unknown",
                      accounts.others(unknown))
        boundary = HB.Boundary(accounts)
        self.assertRegex(verdict(boundary,str(self.existing("f")), fake_stat(0o664, gid=unknown)),
                         r"no group entry names gid")

    def test_extra_files_only_add(self):
        """An extra account file can map a name to this user's uid, but a
        name the host maps elsewhere stays another member."""
        accounts = self.accounts(group=f"{GROUP}:x:{GID}:root\n", passwd=f"root:x:{EUID}:0::/:/bin/sh\n")
        self.assertEqual(accounts._uids_of("root") >= {0, EUID}, True)
        self.assertNotIn("member root", accounts.others(GID), "root and this user are not other users")
        other = self.accounts(group=f"{GROUP}:x:{GID}:daemon\n", passwd=f"daemon:x:{EUID}:1::/:/bin/sh\n")
        self.assertIn("member daemon", other.others(GID), "the host maps daemon to another uid")

    def test_world_writable_and_foreign_owners(self):
        boundary = HB.Boundary(self.accounts())
        self.assertRegex(verdict(boundary,str(self.existing("f")), fake_stat(0o666)),
                         r"writable by every user \(mode 0666\)")
        self.assertRegex(verdict(boundary,str(self.base / "f"), fake_stat(0o644, uid=4242)),
                         r"owned by uid 4242 .*another user")
        # A system account's file in a root-owned directory (a package's
        # setuid helper) is accepted and listed; in a user directory it is not.
        self.assertIsNone(boundary.problem("/usr/bin/fixture-helper", fake_stat(0o4750, uid=127)))
        self.assertIn("/usr/bin/fixture-helper (uid 127)", boundary.system_owned)
        self.assertRegex(verdict(boundary,str(self.base / "helper"), fake_stat(0o755, uid=127)),
                         r"owned by uid 127")
        self.assertRegex(verdict(boundary,"/usr/bin/fixture-nobody", fake_stat(0o755, uid=HB.NOBODY_UID)),
                         r"owned by uid 65534")
        login = boundary.uid_min + 50000
        self.assertRegex(verdict(boundary,"/usr/bin/fixture-login", fake_stat(0o755, uid=login)),
                         f"owned by uid {login} .*another user")

    def test_a_sticky_directory_protects_a_lookup_never_a_listing(self):
        shared = self.base / "sticky"
        shared.mkdir()
        os.chmod(shared, 0o1777)
        (shared / "tool").write_text("#!/bin/sh\n")
        os.chmod(shared / "tool", 0o755)
        boundary = HB.Boundary(self.accounts())
        self.assertEqual(boundary.resolve(str(shared / "tool"), "tool"), str(shared / "tool"))
        self.assertEqual(boundary.refusals, [])
        boundary.judge_search_path(str(shared))
        self.assertEqual(len(boundary.refusals), 1, boundary.refusals)
        self.assertIn("writable by every user (mode 1777)", boundary.refusals[0])
        missing = HB.Boundary(self.accounts())
        self.assertIsNone(missing.resolve(str(shared / "absent"), "absent"))
        self.assertRegex(missing.refusals[0], r"a missing name could be created in it")

    def test_a_temporary_directory_may_be_shared_only_with_the_sticky_bit(self):
        scratch = self.base / "scratch"
        scratch.mkdir()
        os.chmod(scratch, 0o777)
        boundary = HB.Boundary(self.accounts())
        boundary.judge_scratch_directory(str(scratch), "TMPDIR")
        self.assertEqual(len(boundary.refusals), 1, boundary.refusals)
        self.assertIn(f"{scratch} (TMPDIR): writable by every user (mode 0777)", boundary.refusals[0])
        os.chmod(scratch, 0o1777)
        os.symlink(str(scratch), str(self.base / "tmp-link"))
        for path in (scratch, self.base / "tmp-link"):
            sticky = HB.Boundary(self.accounts())
            sticky.judge_scratch_directory(str(path), "TMPDIR")
            self.assertEqual(sticky.refusals, [], path)

    def test_every_command_of_a_private_path_directory_is_judged(self):
        bin_dir = self.base / "bin"
        bin_dir.mkdir()
        os.chmod(bin_dir, 0o755)
        for name, bits in (("good", 0o755), ("loose", 0o757)):
            (bin_dir / name).write_text("#!/bin/sh\n")
            os.chmod(bin_dir / name, bits)
        boundary = HB.Boundary(self.accounts())
        boundary.judge_search_path(f"{bin_dir}:relative/bin:")
        self.assertEqual(len(boundary.refusals), 3, boundary.refusals)
        self.assertIn(f"{bin_dir / 'loose'} (PATH entry", boundary.refusals[0])
        self.assertIn("relative/bin (PATH entry 'relative/bin'): a relative PATH entry", boundary.refusals[1])
        self.assertIn("(empty) (PATH entry ''): a relative PATH entry", boundary.refusals[2])

    def test_a_link_is_judged_hop_by_hop_and_its_directory_as_a_tree(self):
        outside = self.base / "outside"
        (outside / "lib").mkdir(parents=True)
        (outside / "lib" / "core.olean").write_text("olean\n")
        os.chmod(outside / "lib" / "core.olean", 0o666)
        hop = self.base / "hop"
        hop.mkdir()
        os.chmod(hop, 0o777)
        os.symlink(str(outside), str(hop / "toolchain"))
        home = self.base / "elan"
        (home / "toolchains").mkdir(parents=True)
        os.symlink(str(hop / "toolchain"), str(home / "toolchains" / "pinned"))
        boundary = HB.Boundary(self.accounts())
        boundary.judge_tree(str(home), "ELAN_HOME")
        self.assertEqual(len(boundary.refusals), 1, boundary.refusals)
        self.assertIn(f"{hop} (ELAN_HOME): writable by every user (mode 0777) (a name looked up in it)",
                      boundary.refusals[0])
        os.chmod(hop, 0o755)
        again = HB.Boundary(self.accounts())
        again.judge_tree(str(home), "ELAN_HOME")
        self.assertEqual(len(again.refusals), 1, again.refusals)
        self.assertIn(f"{outside / 'lib' / 'core.olean'} (ELAN_HOME): writable by every user", again.refusals[0])

    def test_a_nested_entry_of_a_tree_is_judged(self):
        tree = self.base / "cargo"
        (tree / "registry" / "src" / "crate").mkdir(parents=True)
        (tree / "registry" / "src" / "crate" / "build.rs").write_text("fn main() {}\n")
        os.chmod(tree / "registry" / "src" / "crate" / "build.rs", 0o646)
        boundary = HB.Boundary(self.accounts())
        boundary.judge_tree(str(tree), "CARGO_HOME")
        self.assertEqual(len(boundary.refusals), 1, boundary.refusals)
        self.assertIn("build.rs (CARGO_HOME): writable by every user (mode 0646)", boundary.refusals[0])

    @unittest.skipUnless(shutil.which("setfacl"), "no setfacl")
    def test_an_acl_that_lets_another_user_write_is_refused(self):
        target = self.base / "config"
        target.write_text("[core]\n")
        os.chmod(target, 0o644)
        result = subprocess.run(["setfacl", "-m", "u:4242:rw", str(target)], capture_output=True, text=True)
        if result.returncode != 0:
            self.skipTest(f"setfacl failed: {result.stderr}")
        boundary = HB.Boundary(self.accounts())
        self.assertRegex(verdict(boundary,str(target), os.lstat(target)),
                         r"writable through its ACL \(mode 0664\): its ACL lets uid 4242 write it")
        # Read access only: the recomputed mask has no write bit either.
        subprocess.run(["setfacl", "-m", "u:4242:r", "-m", "g::r", str(target)], check=True)
        self.assertEqual(mode(target), 0o644)
        self.assertIsNone(boundary.problem(str(target), os.lstat(target)))

    def test_the_command_line_prints_each_refusal_and_the_remedy(self):
        tree = self.loose_tree()
        os.chmod(tree / "bin" / "tool", 0o777)
        env = {"HOME": str(self.base), "PATH": "/usr/bin:/bin", "LANG": "C"}
        result = subprocess.run([sys.executable, "-I", str(ROOT / "scripts" / "host_boundary.py"),
                                 "--search-path", str(tree / "bin"), "--candidate", str(self.base / "absent")],
                                capture_output=True, text=True, env=env)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn(f"host_boundary: REFUSED {tree / 'bin' / 'tool'} (PATH entry", result.stdout)
        last = result.stdout.strip().splitlines()[-1]
        self.assertTrue(last.startswith("host_boundary: FAIL: "), last)
        self.assertIn("`chmod go-w <path>`", last)

    # -- LD-75 ---------------------------------------------------------
    def cli(self, candidate: Path, *arguments: str, **env: str) -> subprocess.CompletedProcess:
        """The command line, with a private HOME and TMPDIR and an empty
        PATH directory (so no git runs)."""
        home, tmp, bin_dir = self.base / "cli-home", self.base / "cli-tmp", self.base / "cli-bin"
        for directory in (home, tmp, bin_dir):
            directory.mkdir(exist_ok=True)
            os.chmod(directory, 0o700)
        run_env = {"HOME": str(home), "TMPDIR": str(tmp), "PATH": "/usr/bin:/bin", "LANG": "C"}
        run_env.update(env)
        return subprocess.run([sys.executable, "-I", "-B", str(ROOT / "scripts" / "host_boundary.py"),
                               "--search-path", str(bin_dir), "--candidate", str(candidate), *arguments],
                              capture_output=True, text=True, env=run_env)

    @staticmethod
    def refused(result: subprocess.CompletedProcess) -> list[str]:
        prefix = "host_boundary: REFUSED "
        return [line[len(prefix):] for line in result.stdout.splitlines() if line.startswith(prefix)]

    @staticmethod
    def git(*args: str, cwd: Path | None = None) -> str:
        env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull, GIT_AUTHOR_NAME="fixture",
                   GIT_AUTHOR_EMAIL="fixture@example.invalid", GIT_COMMITTER_NAME="fixture",
                   GIT_COMMITTER_EMAIL="fixture@example.invalid")
        return subprocess.run(["git", *args], cwd=cwd, env=env, check=True, capture_output=True,
                              text=True).stdout.strip()

    def committed_repository(self, name: str) -> Path:
        repo = self.base / name
        repo.mkdir()
        self.git("init", "-q", "-b", "main", str(repo))
        (repo / "kernel.rs").write_text("pub const CHECK_PROOFS: bool = true;\n")
        self.git("-C", str(repo), "add", "-A")
        self.git("-C", str(repo), "commit", "-q", "-m", "fixture")
        return repo

    def test_an_alternate_object_store_is_judged_as_a_tree(self):
        """The round-3 verifier's alt_probe, in small: a source repository
        cloned with --shared from a mirror whose object store every user can
        write. Its own git directory passed; the mirror's objects, which git
        reads the source's objects from, now refuse."""
        upstream = self.committed_repository("upstream")
        mirror = self.base / "mirror.git"
        self.git("clone", "-q", "--bare", str(upstream), str(mirror))
        for current, _directories, files in os.walk(mirror / "objects"):
            os.chmod(current, 0o777)
            for name in files:
                os.chmod(os.path.join(current, name), 0o666)
        source = self.base / "clean"
        self.git("clone", "-q", "--shared", str(mirror), str(source))
        candidate = self.committed_repository("candidate")
        result = self.cli(candidate, "--git-repo", str(source))
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        objects = os.path.realpath(mirror / "objects")
        self.assertIn(f"{objects} (the git directory of {source}: an alternate object store): writable by every "
                      "user (mode 0777)", self.refused(result))
        for current, _directories, files in os.walk(mirror / "objects"):
            os.chmod(current, 0o755)
            for name in files:
                os.chmod(os.path.join(current, name), 0o444)
        private = self.cli(candidate, "--git-repo", str(source))
        self.assertEqual([line for line in self.refused(private) if "alternate" in line], [])
        self.assertIn(f"host_boundary: judged alternate object store {objects}", private.stdout)

    def test_an_alternates_chain_is_followed_and_what_cannot_be_judged_refuses(self):
        def repository(name: str, alternates: bytes | None = None, http: bool = False) -> Path:
            info = self.base / name / ".git" / "objects" / "info"
            info.mkdir(parents=True)
            (self.base / name / ".git" / "HEAD").write_text("ref: refs/heads/main\n")
            if alternates is not None:
                (info / "alternates").write_bytes(alternates)
            if http:
                (info / "http-alternates").write_text("https://example.invalid/objects\n")
            return self.base / name
        deep = self.base / "deep" / "objects"
        (deep / "pack").mkdir(parents=True)
        (deep / "pack" / "pack-1.pack").write_text("")
        os.chmod(deep / "pack" / "pack-1.pack", 0o666)
        middle = self.base / "middle" / "objects"
        (middle / "info").mkdir(parents=True)
        (middle / "info" / "alternates").write_text(f"# a comment, then a blank line\n\n{deep}\n")
        # Relative to the borrowing objects directory, as git resolves it.
        chained = repository("chained", b"../../../middle/objects\n")
        quoted = repository("quoted", b'"' + str(middle).encode() + b'"\n')
        missing = repository("missing", str(self.base / "absent" / "objects").encode() + b"\n")
        http = repository("http", http=True)
        unreadable = repository("unreadable", str(middle).encode() + b"\n")
        os.chmod(self.base / "unreadable" / ".git" / "objects" / "info" / "alternates", 0o000)
        candidate = self.committed_repository("candidate")
        arguments = [argument for repo in (chained, quoted, missing, http, unreadable)
                     for argument in ("--git-repo", str(repo))]
        lines = self.refused(self.cli(candidate, *arguments))
        place = "(the git directory of {}"
        self.assertIn(f"{deep / 'pack' / 'pack-1.pack'} ({place.format(chained)[1:]}: an alternate object store): "
                      "writable by every user (mode 0666)", lines)
        quoted_file = quoted / ".git" / "objects" / "info" / "alternates"
        self.assertIn(f"{quoted_file} {place.format(quoted)}): has a C-quoted line, which this check does not "
                      "parse", lines)
        self.assertTrue(any(line.startswith(f"{self.base / 'absent' / 'objects'} {place.format(missing)}): is "
                                            "named in ") for line in lines), lines)
        http_file = http / ".git" / "objects" / "info" / "http-alternates"
        self.assertIn(f"{http_file} {place.format(http)}): names alternate object stores by URL, which this check "
                      "cannot judge", lines)
        unreadable_file = unreadable / ".git" / "objects" / "info" / "alternates"
        self.assertTrue(any(line.startswith(f"{unreadable_file} {place.format(unreadable)}): cannot be read")
                            for line in lines), lines)

    def test_a_git_object_store_variable_refuses(self):
        candidate = self.committed_repository("candidate")
        for name in ("GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_OBJECT_DIRECTORY"):
            with self.subTest(name):
                result = self.cli(candidate, **{name: str(self.base / "elsewhere")})
                self.assertEqual(result.returncode, 1, result.stdout[-2000:])
                self.assertTrue(any(line.startswith(f"${name} (the environment): is set") for line in
                                    self.refused(result)), result.stdout[-2000:])

    @HAS_SETFACL
    def test_a_default_acl_that_opens_new_entries_is_refused(self):
        """The round-3 verifier's later_entries_probe B: a default ACL is
        what an entry created in the directory later gets, whatever the
        umask."""
        directory = self.base / "shared-later"
        directory.mkdir()
        os.chmod(directory, 0o755)
        result = subprocess.run(["setfacl", "-d", "-m", "u:4242:rwx", str(directory)], capture_output=True, text=True)
        if result.returncode != 0:
            self.skipTest(f"setfacl failed: {result.stderr}")
        boundary = HB.Boundary(self.accounts())
        self.assertEqual(verdict(boundary, str(directory), os.lstat(directory)),
                         "its default ACL lets uid 4242 write what is created in it")
        # Under a default mask without write, the named user cannot write.
        subprocess.run(["setfacl", "-d", "-m", "m::rx", str(directory)], check=True)
        self.assertIsNone(boundary.problem(str(directory), os.lstat(directory)))
        # The mask never holds the other class (-n: the mask stays r-x).
        subprocess.run(["setfacl", "-n", "-d", "-m", "o::rwx", str(directory)], check=True)
        self.assertEqual(verdict(boundary, str(directory), os.lstat(directory)),
                         "its default ACL lets every user write what is created in it")
        # A named group with another member.
        subprocess.run(["setfacl", "-d", "-b", str(directory)], check=True)
        subprocess.run(["setfacl", "-k", str(directory)], check=True)
        subprocess.run(["setfacl", "-d", "-m", f"g:{GID}:rwx", str(directory)], check=True)
        self.assertRegex(verdict(HB.Boundary(self.shared_member()), str(directory), os.lstat(directory)),
                         r"its default ACL lets group .* write what is created in it, and member cogroup")
        # The probe: a default ACL on the candidate checkout's root.
        candidate = self.committed_repository("candidate")
        subprocess.run(["setfacl", "-d", "-m", "u:4242:rwx", str(candidate)], check=True)
        self.assertIn(f"{candidate} (the candidate checkout): its default ACL lets uid 4242 write what is created "
                      "in it", self.refused(self.cli(candidate)))

    def test_a_directory_others_can_create_a_cargo_in_refuses_what_lies_below(self):
        """The round-3 verifier's later_entries_probe A: a checkout below a
        sticky, world-writable directory. Another user can create its
        `.cargo` after the check, and Cargo would read that configuration."""
        sticky = self.base / "sticky"
        sticky.mkdir()
        os.chmod(sticky, 0o1777)
        candidate = self.committed_repository("sticky/candidate")
        expected = (f"{sticky} (Cargo's configuration search above the candidate checkout): writable by every "
                    f"user (mode 1777), so another user can create {sticky / '.cargo'} there")
        result = self.cli(candidate)
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        self.assertTrue(any(line.startswith(expected) for line in self.refused(result)), result.stdout[-3000:])
        # The cache and a directory the gate runs Cargo in, above a private checkout.
        private = self.committed_repository("private-candidate")
        cache = sticky / "cache"
        cache.mkdir(mode=0o700)
        os.chmod(cache, 0o700)
        lines = self.refused(self.cli(private, XDG_CACHE_HOME=str(cache)))
        self.assertTrue(any(line.startswith(f"{sticky} (Cargo's configuration search above the user cache's "
                                            "trust-cg directory): writable by every user") for line in lines), lines)
        lines = self.refused(self.cli(private, "--cargo-root", str(sticky / "deps")))
        self.assertTrue(any(line.startswith(f"{sticky} (Cargo's configuration search above a directory the gate "
                                            "runs Cargo in): writable by every user") for line in lines), lines)
        # A .cargo of this user's already in the sticky directory: judged as
        # a tree, and nobody else can create one there.
        (sticky / ".cargo").mkdir()
        os.chmod(sticky / ".cargo", 0o755)
        boundary = HB.Boundary(self.accounts())
        boundary.judge_cargo_ancestry(str(candidate), "test")
        self.assertEqual([line for line in boundary.refusals if line.startswith(f"{sticky} (")], [])
        self.assertIn(str(sticky / ".cargo"), boundary.trees)
        (sticky / ".cargo" / "config.toml").write_text("")
        os.chmod(sticky / ".cargo" / "config.toml", 0o666)
        held = HB.Boundary(self.accounts())
        held.judge_cargo_ancestry(str(candidate), "test")
        self.assertTrue(any(line.startswith(f"{sticky / '.cargo' / 'config.toml'} (") for line in held.refusals),
                        held.refusals)
        # Without the sticky bit another user could rename that .cargo away.
        os.chmod(sticky / ".cargo" / "config.toml", 0o644)
        os.chmod(sticky, 0o777)
        open_directory = HB.Boundary(self.accounts())
        open_directory.judge_cargo_ancestry(str(candidate), "test")
        self.assertTrue(any(line.startswith(f"{sticky} (test): writable by every user (mode 0777)")
                            for line in open_directory.refusals), open_directory.refusals)

    # -- LD-75 repair (the round-4 verifier's findings) ------------------
    def test_a_location_variable_that_is_not_absolute_refuses_naming_it(self):
        """The round-4 verifier's test_v4_relative_roots, in small: Cargo,
        rustup, elan, gate_env.sh and private_cache.py resolve a relative
        CARGO_HOME, CARGO_TARGET_DIR, RUSTUP_HOME, ELAN_HOME,
        SOUNDNESS_DEPS_DIR or ATPKG_BIN against their working directory, and
        the check skipped every root that was not absolute, so `../shared` at
        a 0777 directory passed where the absolute form refused. Each is now
        refused by name with the remedy (an empty value too), and a
        --cargo-root or tree root that is not absolute refuses on its own."""
        candidate = self.committed_repository("candidate")
        shared = self.base / "shared"
        shared.mkdir()
        os.chmod(shared, 0o777)
        variables = ("CARGO_HOME", "CARGO_TARGET_DIR", "RUSTUP_HOME", "ELAN_HOME", "SOUNDNESS_DEPS_DIR", "ATPKG_BIN")
        for name in variables:
            for value in ("../shared", "shared", ""):
                with self.subTest(name=name, value=value):
                    result = self.cli(candidate, **{name: value})
                    self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                    self.assertIn(f"${name} (the environment): is {value!r}, not an absolute path, so what it names "
                                  "depends on the working directory of each program that reads it, and this check "
                                  "cannot judge it; remedy: unset it or set it to an absolute path (LD-75)",
                                  self.refused(result))
            with self.subTest(name=name, value="absolute"):
                lines = self.refused(self.cli(candidate, **{name: str(self.base / "elsewhere" / "bin")}))
                self.assertEqual([line for line in lines if line.startswith(f"${name} ")], [])
        lines = self.refused(self.cli(candidate, "--cargo-root", "private"))
        self.assertIn("private (Cargo's configuration search above a directory the gate runs Cargo in): is not an "
                      "absolute path, so Cargo's configuration search above it depends on the working directory "
                      "(LD-75)", lines)
        # An empty HOME left every default tree below it relative (`.cargo`),
        # and those were skipped unjudged.
        lines = self.refused(self.cli(candidate, HOME=""))
        self.assertIn(".cargo (CARGO_HOME): is not an absolute path, so it depends on the working directory", lines)
        self.assertEqual(getattr(HB, "LOCATION_VARIABLES", None), variables)

    @HAS_SETFACL
    def test_an_ancestor_refused_for_its_default_acl_is_reported_as_that(self):
        """LD-75's own residual: an ancestor of a Cargo root refused only for
        its default ACL was reported as one in which another user "can create
        .cargo", which that user cannot. It is now reported as what it is.
        A sticky one holding this user's .cargo stays refused for its default
        ACL (the look-up of that .cargo in it refuses it first)."""
        ancestor = self.base / "acl-ancestor"
        below = ancestor / "below"
        below.mkdir(parents=True)
        os.chmod(ancestor, 0o755)
        result = subprocess.run(["setfacl", "-d", "-m", "u:4242:rwx", str(ancestor)], capture_output=True, text=True)
        if result.returncode != 0:
            self.skipTest(f"setfacl failed: {result.stderr}")
        def at_ancestor(boundary):
            # Only the refusal of `ancestor` (the base's own ancestors may
            # refuse too, as /tmp does).
            return [line for line in boundary.refusals if line.startswith(f"{ancestor} (")]

        opened = ("its default ACL lets uid 4242 write what is created in it, so an entry created in it is open to "
                  "another user whatever the umask (LD-75)")
        boundary = HB.Boundary(self.accounts())
        boundary.judge_cargo_ancestry(str(below), "test")
        self.assertEqual(at_ancestor(boundary), [f"{ancestor} (test): {opened}"])
        # Writable by every user as well: both reasons, the .cargo one first.
        os.chmod(ancestor, 0o777)
        both = HB.Boundary(self.accounts())
        both.judge_cargo_ancestry(str(below), "test")
        self.assertEqual(at_ancestor(both), [f"{ancestor} (test): writable by every user (mode 0777), so another user "
                                             f"can create {ancestor / '.cargo'} there, whose configuration Cargo "
                                             f"reads in every directory below it; and {opened}"])
        # Sticky, holding this user's .cargo: the .cargo is judged as a tree,
        # and looking it up in the directory refuses the default ACL.
        (ancestor / ".cargo").mkdir()
        os.chmod(ancestor / ".cargo", 0o755)
        subprocess.run(["setfacl", "-k", str(ancestor / ".cargo")], check=True)
        os.chmod(ancestor, 0o1777)
        held = HB.Boundary(self.accounts())
        held.judge_cargo_ancestry(str(below), "test")
        self.assertIn(str(ancestor / ".cargo"), held.trees)
        self.assertEqual(len(at_ancestor(held)), 1, held.refusals)
        self.assertIn("its default ACL lets uid 4242 write what is created in it", at_ancestor(held)[0])

    def test_a_repository_where_git_sets_its_own_modes_is_refused(self):
        """core.sharedRepository makes git set the modes of what it writes in
        the repository (the attestation's objects and refs) itself, past the
        umask 077 the rest of an --attest run relies on: only `umask` and a
        false value pass."""
        repo = self.committed_repository("shared-repository")
        config = repo / ".git" / "config"
        plain = config.read_text()
        cases = (("group", True), ("0666", True), ("all", True), ("umask", False), ("false", False), (None, True))
        for value, refused in cases:
            with self.subTest(value=value):
                config.write_text(plain + ("[core]\n\tsharedRepository\n" if value is None
                                           else f"[core]\n\tsharedRepository = {value}\n"))
                with mock.patch.dict(os.environ, {"GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}):
                    boundary = HB.Boundary(self.accounts())
                    HB.judge_git(boundary, "/usr/bin:/bin", [str(repo)])
                found = [line for line in boundary.refusals if line.startswith(f"{repo} core.sharedRepository (")]
                self.assertEqual(bool(found), refused, boundary.refusals)

    def test_a_git_program_named_by_a_relative_path_is_refused(self):
        """The residual verifier's git_relative_program_probe: git runs a
        configured program named by a relative path with a slash from its
        working directory, which no rule judges, so `./tools/ssh` in a 0777
        `tools/` ran unjudged. Such a name refuses; an absolute path is
        resolved as before and a bare name is found on the judged PATH."""
        repo = self.committed_repository("relative-program")
        # In the global configuration, where these word rules decide (a
        # repository's own configuration refuses every program key by the
        # allowlist; OD-XHOST-GIT-PROGRAM-KEYS-20261024).
        config = self.base / "global.gitconfig"
        plain = ""
        cases = (("core.fsmonitor", "./tools/ssh", True), ("core.sshCommand", "tools/ssh -v", True),
                 ("core.pager", "less", False), ("core.editor", "/usr/bin/true", False))
        for key, value, refused in cases:
            with self.subTest(key=key, value=value):
                section, name = key.split(".")
                config.write_text(plain + f"[{section}]\n\t{name} = {value}\n")
                with mock.patch.dict(os.environ, {"GIT_CONFIG_GLOBAL": str(config), "GIT_CONFIG_NOSYSTEM": "1"}):
                    boundary = HB.Boundary(self.accounts())
                    HB.judge_git(boundary, "/usr/bin:/bin", [str(repo)])
                found = [line for line in boundary.refusals if line.startswith(f"{repo} {key.lower()} (")]
                self.assertEqual(bool(found), refused, boundary.refusals)
                if refused:
                    self.assertIn("by a relative path, which git runs from its working directory", found[0])

    def test_an_empty_tmpdir_is_refused_by_name(self):
        """The residual verifier's finding: an empty TMPDIR was judged as
        /tmp, but Rust's std::env::temp_dir() returns the empty path, so a
        program's temporary files land in its unjudged working directory."""
        candidate = self.committed_repository("empty-tmpdir")
        result = self.cli(candidate, TMPDIR="")
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        self.assertIn("$TMPDIR (the environment): is empty, so Rust programs put their temporary files in their "
                      "working directory, which this check cannot judge; remedy: unset it or set it to an "
                      "absolute path (LD-75)", self.refused(result))

    # -- OD-XHOST-FETCH-TRANSPORT-20261016 (the fifth closure audit) -----------
    def transport_programs(self) -> tuple[Path, Path, Path]:
        """A program in a 0777 directory (another user can replace it), one
        in a private directory, and the candidate checkout."""
        shared = self.base / "shared"
        shared.mkdir(exist_ok=True)
        os.chmod(shared, 0o777)
        private = self.base / "private-bin"
        private.mkdir(exist_ok=True)
        os.chmod(private, 0o700)
        for directory in (shared, private):
            program = directory / "fetch-ssh"
            program.write_text("#!/bin/sh\nexit 1\n")
            os.chmod(program, 0o755)
        return shared / "fetch-ssh", private / "fetch-ssh", self.committed_repository("transport-candidate")

    def test_every_fetch_transport_program_in_the_environment_is_judged_in_every_run(self):
        """The fifth closure audit's first finding (skeptic 1, probe_ssh.py):
        GIT_SSH_COMMAND was judged only with --ssh (an x86-64 executor) and
        only when its first word was absolute, so a program in a 0777
        directory, or named by a relative path into the work tree git fetch
        runs in, ran as the gate's user in an attested run. Now GIT_SSH_COMMAND,
        GIT_SSH and GIT_PROXY_COMMAND are judged in every run, as git runs
        them, and what this check cannot judge refuses by name."""
        evil, private, candidate = self.transport_programs()
        shared = evil.parent
        cases = (
            ("GIT_SSH_COMMAND", str(evil), f"{shared} (GIT_SSH_COMMAND in the environment): writable by every user"),
            ("GIT_SSH_COMMAND", f"{evil} -v", f"{shared} (GIT_SSH_COMMAND in the environment): writable by every "
                                              "user"),
            ("GIT_SSH_COMMAND", "tools/fetch-ssh", "$GIT_SSH_COMMAND (GIT_SSH_COMMAND in the environment): names "
                                                   "the program 'tools/fetch-ssh' by a relative path, which git "
                                                   "runs from its working directory"),
            # OD-XHOST-TRANSPORT-WORDS-20261024: GIT_SSH_COMMAND is a shell
            # command, so ANY later word refuses (the program `env`/`ssh`
            # itself passes; the later word is what this check cannot judge).
            # Findings (2) `=`, (3) bare, and (6) `-i` reach the same rule.
            ("GIT_SSH_COMMAND", f"env {evil}", "$GIT_SSH_COMMAND (GIT_SSH_COMMAND in the environment): runs the "
                                               "shell command"),
            ("GIT_SSH_COMMAND", "env PATH=tools evil-ssh", "$GIT_SSH_COMMAND (GIT_SSH_COMMAND in the environment): "
                                                           "runs the shell command"),
            ("GIT_SSH_COMMAND", "sh evil-ssh", "$GIT_SSH_COMMAND (GIT_SSH_COMMAND in the environment): runs the "
                                               "shell command"),
            ("GIT_SSH_COMMAND", "sh tools/evil=1", "$GIT_SSH_COMMAND (GIT_SSH_COMMAND in the environment): runs the "
                                                   "shell command"),
            ("GIT_SSH_COMMAND", f"ssh -oProxyCommand={evil}", "$GIT_SSH_COMMAND (GIT_SSH_COMMAND in the "
                                                              "environment): runs the shell command"),
            ("GIT_SSH_COMMAND", "ssh -i/tmp/key", "$GIT_SSH_COMMAND (GIT_SSH_COMMAND in the environment): runs the "
                                                  "shell command"),
            ("GIT_SSH_COMMAND", "ssh -F tools/config", "$GIT_SSH_COMMAND (GIT_SSH_COMMAND in the environment): "
                                                       "runs the shell command"),
            # Finding (1): a path into the checker's own /proc or /dev/fd view.
            ("GIT_SSH_COMMAND", "/proc/self/cwd/tools/evil-ssh", "/proc (GIT_SSH_COMMAND in the "
                                                                 "environment): resolves into /proc"),
            ("GIT_SSH_COMMAND", "/dev/fd/../cwd/tools/evil-ssh", "/dev/fd (GIT_SSH_COMMAND in the environment): "
                                                                 "resolves into /dev/fd"),
            ("GIT_SSH_COMMAND", "$SHELL", "$GIT_SSH_COMMAND (GIT_SSH_COMMAND in the environment): holds '$', which "
                                          "the shell gives a meaning this check does not parse"),
            ("GIT_SSH_COMMAND", f"'{evil}'", "$GIT_SSH_COMMAND (GIT_SSH_COMMAND in the environment): holds \"'\""),
            ("GIT_SSH_COMMAND", "PATH=tools ssh", "$GIT_SSH_COMMAND (GIT_SSH_COMMAND in the environment): begins "
                                                  "with the assignment 'PATH=tools'"),
            ("GIT_SSH_COMMAND", " ", "$GIT_SSH_COMMAND (GIT_SSH_COMMAND in the environment): is empty"),
            # The shell does not split at U+00A0: this is one relative path.
            ("GIT_SSH_COMMAND", "ssh tools/fetch-ssh", "$GIT_SSH_COMMAND (GIT_SSH_COMMAND in the environment): "
                                                         "names the program 'ssh\\xa0tools/fetch-ssh' by a "
                                                         "relative path"),
            ("GIT_SSH", str(evil), f"{shared} (GIT_SSH in the environment): writable by every user"),
            ("GIT_SSH", "./fetch-ssh", "$GIT_SSH (GIT_SSH in the environment): names the program './fetch-ssh' by a "
                                       "relative path"),
            ("GIT_SSH", f"{private} -v", "$GIT_SSH (GIT_SSH in the environment): holds whitespace, but git runs the "
                                         "whole value as one program"),
            ("GIT_PROXY_COMMAND", str(evil), f"{shared} (GIT_PROXY_COMMAND in the environment): writable by every "
                                             "user"),
            ("GIT_ALLOW_PROTOCOL", "https:ext", "$GIT_ALLOW_PROTOCOL (the environment): lists ext"),
        )
        for name, value, expected in cases:
            with self.subTest(name=name, value=value):
                result = self.cli(candidate, **{name: value})
                self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                self.assertTrue(any(line.startswith(expected) for line in self.refused(result)), self.refused(result))
        # What passes (OD-XHOST-TRANSPORT-WORDS-20261024): the program ALONE,
        # by a private absolute path or a bare name found on the (private)
        # PATH; options go in ~/.ssh/config, which the check judges. (The run
        # itself may still refuse a place outside these, such as the temporary
        # directory above the fixture.)
        for name, value in (("GIT_SSH_COMMAND", str(private)),
                            ("GIT_SSH_COMMAND", "ssh"), ("GIT_SSH", str(private)),
                            ("GIT_PROXY_COMMAND", str(private)), ("GIT_ALLOW_PROTOCOL", "https:ssh")):
            with self.subTest(name=name, value=value, passes=True):
                result = self.cli(candidate, **{name: value})
                if name != "GIT_ALLOW_PROTOCOL":
                    self.assertIn(f"host_boundary: judged ${name} (a program git's fetch runs)", result.stdout)
                self.assertEqual([line for line in self.refused(result)
                                  if "in the environment)" in line or line.startswith("$GIT_")], [])

    def test_ssh_configuration_is_judged_in_every_run(self):
        """~/.ssh and /etc/ssh were judged only with --ssh (an x86-64
        executor), though a pinned checkout's `git fetch` uses ssh too: a
        0777 ~/.ssh now refuses a run with no executor."""
        candidate = self.committed_repository("ssh-configuration")
        home = self.base / "cli-home"
        home.mkdir(exist_ok=True)
        os.chmod(home, 0o700)
        (home / ".ssh").mkdir(exist_ok=True)
        os.chmod(home / ".ssh", 0o777)
        result = self.cli(candidate)
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        self.assertIn(f"{home / '.ssh'} (ssh configuration): writable by every user (mode 0777)", self.refused(result))
        self.assertIn(f"host_boundary: judged ssh configuration {home / '.ssh'}", result.stdout)
        self.assertIn("host_boundary: judged ssh configuration /etc/ssh", result.stdout)
        os.chmod(home / ".ssh", 0o700)
        self.assertEqual([line for line in self.refused(self.cli(candidate)) if "(ssh configuration)" in line], [])

    def test_fetch_transport_keys_are_judged_as_git_runs_them(self):
        """core.sshCommand's other words, core.gitProxy (which no key rule
        named) and the ext:: transport's policy: each could name a program a
        fetch runs that no rule judged."""
        evil, private, _candidate = self.transport_programs()
        repo = self.committed_repository("transport-keys")
        # The global configuration: a repository's own configuration now
        # refuses these keys by the allowlist (OD-XHOST-GIT-PROGRAM-KEYS-20261024).
        config = self.base / "global.gitconfig"
        plain = ""
        cases = (("core.sshCommand", f"env {evil}", True), ("core.sshCommand", "ssh $FETCH", True),
                 # A transport shell command accepts the program alone: any
                 # later word now refuses (OD-XHOST-TRANSPORT-WORDS-20261024).
                 ("core.sshCommand", f"{private} -o BatchMode=yes", True),
                 ("core.sshCommand", str(private), False),
                 ("core.gitProxy", f"{evil} for example.com", True), ("core.gitProxy", "tools/proxy", True),
                 ("core.gitProxy", f"{private} for example.com", False),
                 ("protocol.ext.allow", "always", True), ("protocol.allow", "user", True),
                 ("protocol.ext.allow", "never", False),
                 # Any key's program is split where the shell splits it, not
                 # at U+00A0 (the LD-75 relative-program rule had been).
                 ("core.fsmonitor", "fs ./tools/ssh", True))
        for key, value, refused in cases:
            with self.subTest(key=key, value=value):
                section, _, name = key.rpartition(".")
                head = f'[{section.split(".")[0]} "{section.split(".")[1]}"]' if "." in section else f"[{section}]"
                config.write_text(plain + f"{head}\n\t{name} = {value}\n", encoding="utf-8")
                with mock.patch.dict(os.environ, {"GIT_CONFIG_GLOBAL": str(config), "GIT_CONFIG_NOSYSTEM": "1"}):
                    boundary = HB.Boundary(self.accounts())
                    HB.judge_git(boundary, "/usr/bin:/bin", [str(repo)])
                self.assertEqual(bool(boundary.refusals), refused, boundary.refusals)

    def test_extra_account_files_never_make_a_group_private(self):
        """The round-3 verifier's extra_accounts_probe: a gid no host group
        entry names, and a member with no host account, stay another member
        whatever the extra files say."""
        unknown = 4247
        while True:
            try:
                grp.getgrgid(unknown)
                unknown += 1
            except KeyError:
                break
        accounts = self.accounts(group=f"phantom:x:{unknown}:{ME}\n")
        self.assertIn(f"no group entry names gid {unknown}, so its members are unknown", accounts.others(unknown))
        accounts = self.accounts(group=f"{GROUP}:x:{GID}:ghostmember\n",
                                 passwd=f"ghostmember:x:{EUID}:{GID}:alias:/nonexistent:/usr/sbin/nologin\n")
        self.assertIn("member ghostmember has no account", accounts.others(GID))
        self.assertRegex(verdict(HB.Boundary(accounts), str(self.existing("f")), fake_stat(0o664)),
                         r"member ghostmember has no account")



    # -- OD-XHOST-TRANSPORT-WORDS-20261024 (the X-HOST-P13 round-5 verifier) ----
    def test_restricted_self_view_prefix_matches_only_proc_and_dev_fd(self):
        """Finding (1), the prefix rule in isolation: /proc and /dev/fd (and
        anything below them) name the checker's own filesystem view; /dev/null,
        /dev/shm and look-alikes such as /proctor or /dev/fdisk do not."""
        for path in ("/proc", "/proc/self", "/proc/self/cwd/tools/x", "/proc/thread-self/cwd/x", "/proc/1/cwd/x"):
            self.assertEqual(HB._restricted_self_view(path), "/proc", path)
        for path in ("/dev/fd", "/dev/fd/0", "/dev/fd/../cwd/x"):
            self.assertEqual(HB._restricted_self_view(path), "/dev/fd", path)
        for path in ("/dev/null", "/dev/shm", "/dev/stdin", "/proctor", "/dev/fdisk", "/home/x/proc", "/"):
            self.assertIsNone(HB._restricted_self_view(path), path)

    def test_a_path_through_proc_or_dev_fd_is_refused_wherever_it_is_used(self):
        """Finding (1): a path named through the checker's own /proc/self/cwd
        or /dev/fd is judged in the checker's working directory, not where git
        runs it, so it is refused outright - in resolve (a transport program or
        a config-key program), in judge_search_path (a PATH entry) and in
        judge_cargo_ancestry. /dev/null and a sticky /dev/shm still pass."""
        for word in ("/proc/self/cwd/tools/evil-ssh", "/proc/thread-self/cwd/x",
                     "/dev/fd/../cwd/tools/evil-ssh", "/dev/fd/0"):
            boundary = HB.Boundary(self.accounts())
            self.assertIsNone(boundary.resolve(word, "a program git runs"))
            self.assertEqual(len(boundary.refusals), 1, boundary.refusals)
            self.assertRegex(boundary.refusals[0], r"resolves into (/proc|/dev/fd), which names the checking process")
        passing = HB.Boundary(self.accounts())
        self.assertEqual(passing.resolve("/dev/null", "devnull"), "/dev/null")
        self.assertEqual(passing.refusals, [])
        if os.path.isdir("/dev/shm"):
            scratch = HB.Boundary(self.accounts())
            scratch.judge_scratch_directory("/dev/shm", "TMPDIR")
            self.assertEqual([r for r in scratch.refusals if "/proc" in r or "/dev/fd" in r], [], scratch.refusals)
        sp = HB.Boundary(self.accounts())
        sp.judge_search_path("/proc/self/cwd/tools")
        self.assertTrue(any("resolves into /proc" in r for r in sp.refusals), sp.refusals)
        ca = HB.Boundary(self.accounts())
        ca.judge_cargo_ancestry("/proc/self/cwd", "test")
        self.assertTrue(any("resolves into /proc" in r for r in ca.refusals), ca.refusals)

    def test_a_transport_shell_command_refuses_every_later_word(self):
        """Findings (2), (3) and (6): GIT_SSH_COMMAND and core.sshCommand are
        shell commands, so the program alone is judged and ANY later word
        refuses - the `=` reproducer `sh tools/evil=1`, the bare words
        `env PATH=tools evil-ssh` and `sh evil-ssh`, the attached option
        `ssh -i/tmp/key` (finding (6), once wrongly called a relative path) and
        `ssh -F tools/config`. The program alone, absolute or a bare PATH name,
        passes; options belong in ~/.ssh/config, which the check judges."""
        for value in ("sh tools/evil=1", "env PATH=tools evil-ssh", "sh evil-ssh", "ssh -i/tmp/key",
                      "ssh -F tools/config", "ssh -oProxyCommand=/x"):
            boundary = HB.Boundary(self.accounts())
            HB.judge_transport_program(boundary, value, "$GIT_SSH_COMMAND", "place", "/usr/bin:/bin", shell=True)
            self.assertTrue(any("runs the shell command" in r for r in boundary.refusals), (value, boundary.refusals))
        for value in ("/usr/bin/true", "ssh"):
            boundary = HB.Boundary(self.accounts())
            HB.judge_transport_program(boundary, value, "$GIT_SSH_COMMAND", "place", "/usr/bin:/bin", shell=True)
            self.assertEqual(boundary.refusals, [], (value, boundary.refusals))

    def judge_command_value(self, repo: Path, plain: str, section: str, name: str, value: str,
                            scope: str = "global") -> list[str]:
        """judge_git's refusals for `repo` (local configuration `plain`) with
        one `[section] name = value` added to the GLOBAL configuration file
        (the default; no system file) or, with scope "local", to the
        repository's own configuration. The word rules of
        judge_git_command_value apply in every scope; since
        OD-XHOST-GIT-PROGRAM-KEYS-20261024 a program key in a repository's own
        configuration also refuses by the allowlist whatever its words, so the
        word-rule cases that must pass are judged in the global scope."""
        config = repo / ".git" / "config"
        global_config = self.base / "global.gitconfig"
        added = f"[{section}]\n\t{name} = {value}\n"
        config.write_text(plain + (added if scope == "local" else ""), encoding="utf-8")
        global_config.write_text(added if scope == "global" else "", encoding="utf-8")
        with mock.patch.dict(os.environ, {"GIT_CONFIG_GLOBAL": str(global_config), "GIT_CONFIG_NOSYSTEM": "1"}):
            boundary = HB.Boundary(self.accounts())
            HB.judge_git(boundary, "/usr/bin:/bin", [str(repo)])
        return boundary.refusals

    def test_a_git_command_key_keeps_the_helper_and_closes_the_bare_word_class(self):
        """Finding (3) for git configuration keys, as repair round 2 restated it
        (OD-XHOST-TRANSPORT-WORDS-20261024). Pass: this host's helper shape
        `!<absolute program> auth git-credential` (and the exact
        `!/usr/bin/gh auth git-credential` where /usr/bin/gh exists), the empty
        reset value, a bare later word (`!sh evil`, resolved in git's working
        directory, which judge_git_layout verifies is the judged work tree:
        repair round 3, test_a_repository_git_uses_differently_than_given_is_refused),
        common plain options (`cache --timeout=3600`,
        `git-lfs clean -- %f`, `less -FRX`), a private absolute file and
        directory named by a later word, and the two newly listed keys. Refuse:
        a shell metacharacter, an environment-assignment later word, an
        absolute later word another user can write, and - over-refused, fail
        closed - a sed script (`s/a/b/` holds a slash but is no path)."""
        repo = self.committed_repository("command-keys")
        plain = (repo / ".git" / "config").read_text()
        shared = self.base / "shared777"
        shared.mkdir()
        os.chmod(shared, 0o777)
        (shared / "evil").write_text("#!/bin/sh\n")
        os.chmod(shared / "evil", 0o755)
        private = self.base / "private-dir"
        private.mkdir()
        os.chmod(private, 0o700)
        (private / "creds").write_text("")
        os.chmod(private / "creds", 0o600)
        cases = [
            ("credential", "helper", "!/usr/bin/true auth git-credential", False),
            ("credential", "helper", "", False),
            ("credential", "helper", "!sh evil", False),
            ("credential", "helper", "cache --timeout=3600", False),
            ('filter "lfs"', "clean", "git-lfs clean -- %f", False),
            ("core", "pager", "less -FRX", False),
            ("credential", "helper", f"store --file={private / 'creds'}", False),
            ("core", "fsmonitor", f"fs {private}", False),
            ("core", "alternateRefsCommand", "/usr/bin/true", False),
            ('gpg "ssh"', "defaultKeyCommand", "/usr/bin/true", False),
            ('filter "x"', "smudge", "sed s/fixture/SUBSTITUTED/", True),
            ("credential", "helper", "!/usr/bin/env PATH=/tmp gh", True),
            ("core", "fsmonitor", "true && tools/evil", True),
            ("core", "fsmonitor", f"fs {shared / 'evil'}", True),
        ]
        if os.path.exists("/usr/bin/gh"):
            cases.insert(0, ("credential", "helper", "!/usr/bin/gh auth git-credential", False))
        for section, name, value, refused in cases:
            with self.subTest(section=section, name=name, value=value):
                refusals = self.judge_command_value(repo, plain, section, name, value)
                self.assertEqual(bool(refusals), refused, (value, refusals))
        # The bare word `!sh evil` is judged where git resolves it: a 0777
        # `evil` at a work-tree root is refused when that tree is judged.
        tree = self.base / "worktree"
        tree.mkdir()
        os.chmod(tree, 0o755)
        (tree / "evil").write_text("#!/bin/sh\n")
        os.chmod(tree / "evil", 0o777)
        judged = HB.Boundary(self.accounts())
        judged.judge_tree(str(tree), "the source work tree")
        self.assertEqual(len(judged.refusals), 1, judged.refusals)
        self.assertIn(f"{tree / 'evil'} (the source work tree): writable by every user (mode 0777)",
                      judged.refusals[0])

    def test_a_git_command_key_word_that_can_leave_the_judged_directory_refuses(self):
        """Repair round 2: the two verifiers' reproducers at 9352c20f1 (repro_unit2.py
        and test_v_r5_e2e.py), each of which judge_git passed although the word
        names or selects a directory outside git's judged working directory and
        PATH, now refuse by name: `..` in any form (`sh ../evil`,
        `env -C .. sh evil`, `env -C.. sh evil`), an option's attached path
        (`env -S/abs`, `sh -e/tmp/x`), `~user`, a first word that is an
        environment assignment (`PATH=.. evil`, `PATH=~ evil`, also under `!`,
        and the over-refused `LESS=FRX less`), a later word that sets the
        environment (`env PATH=tools evil`), a relative path with a slash, a
        path holding a list separator (`env -P /usr/bin:/tmp evil`), a word
        outside the plain-argument characters, and a `~user` program. A later
        word naming an absolute DIRECTORY is judged as a whole tree, so
        `env -C <private dir holding a 0777 evil> sh evil` refuses on the 0777
        file; `/` itself refuses at its first open entry. Since repair round 4
        a `!` alias's later words are judged too (`!sh ../evil` refuses)."""
        repo = self.committed_repository("command-key-words")
        plain = (repo / ".git" / "config").read_text()
        shared = self.base / "shared777"
        shared.mkdir()
        os.chmod(shared, 0o777)
        (shared / "evil").write_text("#!/bin/sh\n")
        os.chmod(shared / "evil", 0o777)
        holder = self.base / "holder"
        holder.mkdir()
        os.chmod(holder, 0o700)
        (holder / "evil").write_text("#!/bin/sh\n")
        os.chmod(holder / "evil", 0o777)
        cases = (
            ("remote \"origin\"", "uploadpack", "sh ../evil", "holds `..`"),
            ("remote \"origin\"", "uploadpack", "env -C .. sh evil", "holds `..`"),
            ("remote \"origin\"", "uploadpack", "/usr/bin/env -C .. sh evil", "holds `..`"),
            ("core", "fsmonitor", "env -C.. sh evil", "holds `..`"),
            ("credential", "helper", "!sh ../evil", "holds `..`"),
            ("remote \"origin\"", "uploadpack", f"env -S{shared / 'evil'}", "nor a plain `--option=`"),
            ("core", "fsmonitor", f"env -S{shared / 'evil'}", "nor a plain `--option=`"),
            ("credential", "helper", f"!env -S{shared / 'evil'}", "nor a plain `--option=`"),
            ("credential", "helper", "!sh -e/tmp/x", "nor a plain `--option=`"),
            ("credential", "helper", "!sh ~root/evil", "nor a plain `--option=`"),
            ("core", "fsmonitor", "sh tools/evil", "nor a plain `--option=`"),
            ("remote \"origin\"", "uploadpack", "PATH=.. evil", "begins with the assignment 'PATH=..'"),
            ("remote \"origin\"", "uploadpack", "PATH=~ evil", "begins with the assignment 'PATH=~'"),
            ("core", "fsmonitor", "PATH=.. evil", "begins with the assignment"),
            ("credential", "helper", "!PATH=.. evil", "begins with the assignment"),
            ("core", "pager", "LESS=FRX less", "begins with the assignment"),
            ("core", "fsmonitor", "env PATH=tools evil", "whose later word 'PATH=tools' sets the environment"),
            ("core", "fsmonitor", "/usr/bin/env -P /usr/bin:/tmp evil", "a path list"),
            ("core", "fsmonitor", "fs --dirs=/usr,/tmp", "a path list"),
            ("core", "fsmonitor", "sh évil", "plain-argument set"),
            ("core", "fsmonitor", "~root/bin/x", "expands to a home directory"),
            ("core", "fsmonitor", "~root", "expands to a home directory"),
            ("remote \"origin\"", "uploadpack", f"env -C {holder} sh evil",
             f"{holder / 'evil'} (git configuration of {repo}: remote.origin.uploadpack): writable by every "
             "user (mode 0777)"),
            ("remote \"origin\"", "uploadpack", f"sh {shared / 'evil'}", "writable by every user (mode 0777)"),
        )
        for section, name, value, expected in cases:
            with self.subTest(section=section, name=name, value=value):
                refusals = self.judge_command_value(repo, plain, section, name, value)
                self.assertTrue(any(expected in refusal for refusal in refusals), (value, refusals))
        # Repair round 4: every alias is judged (a command key can run git with
        # one: test_every_alias_is_judged_as_git_runs_it), so a `!` alias's
        # later `..` refuses like any other key's; 4a0668957 to a6cbba41b
        # judged an alias's first word alone and passed it.
        refusals = self.judge_command_value(repo, plain, "alias", "x", "!sh ../evil")
        self.assertTrue(any("whose later word '../evil' holds `..`" in refusal for refusal in refusals), refusals)
        # `/` as a directory later word is judged as a tree and refuses at its
        # first open entry (/tmp, or /proc or /dev, whichever is listed first).
        refusals = self.judge_command_value(repo, plain, "core", "fsmonitor", "env -C / sh evil")
        self.assertTrue(refusals, refusals)

    def test_a_tree_holding_proc_and_a_shim_into_proc_refuse(self):
        """Finding (1)'s remaining callers. judge_tree refuses an entry at or
        below /proc or /dev/fd (a tree rooted at / or /dev reaches the
        checker's own view; the prefix is patched here to a directory of the
        test's, so the case is deterministic), and _install_root follows an
        atpkg launcher shim's exec target with Boundary.resolve rather than
        os.path.realpath, so a shim that execs `/proc/self/cwd/...` refuses
        (the verifier's low on _install_root)."""
        tree = self.base / "tree-with-view"
        (tree / "view").mkdir(parents=True)
        os.chmod(tree, 0o700)
        os.chmod(tree / "view", 0o700)
        with mock.patch.object(HB, "RESTRICTED_SELF_VIEW_PREFIXES", (str(tree / "view"),)):
            boundary = HB.Boundary(self.accounts())
            boundary.judge_tree(str(tree), "a tree")
        self.assertEqual(len(boundary.refusals), 1, boundary.refusals)
        self.assertIn(f"{tree / 'view'} (a tree): is {tree / 'view'}, which names the checking process's own view",
                      boundary.refusals[0])
        package = self.base / "package"
        (package / "bin").mkdir(parents=True)
        os.chmod(package, 0o700)
        os.chmod(package / "bin", 0o700)
        shim = package / "bin" / "trustc"
        shim.write_text("#!/bin/sh\nexec '/proc/self/cwd/bin/trustc' \"$@\"\n")
        os.chmod(shim, 0o755)
        boundary = HB.Boundary(self.accounts())
        root = HB._install_root(str(shim), boundary, "the Trust package of the PATH trustc")
        self.assertTrue(any("resolves into /proc" in refusal for refusal in boundary.refusals), boundary.refusals)
        self.assertEqual(root, "/proc/self/cwd")
        plain_shim = HB.Boundary(self.accounts())
        self.assertEqual(HB._install_root(str(shim.with_name("missing")), plain_shim, "x"), str(package))

    def test_a_relative_shell_refuses_and_bin_sh_and_the_passwd_home_ssh_are_judged(self):
        """Findings (4) and (5). (4) ssh runs a ProxyCommand through $SHELL with
        no PATH search, so a relative $SHELL would resolve in ssh's working
        directory and refuses; an absolute $SHELL and /bin/sh are judged as
        tools. (5) OpenSSH reads ~/.ssh of the passwd home, not of $HOME, so a
        0777 .ssh at the passwd home refuses even when $HOME points elsewhere."""
        import types
        candidate = self.committed_repository("shell-candidate")
        relative = self.cli(candidate, SHELL="evil-shell")
        self.assertTrue(any(line.startswith("$SHELL (the environment): is 'evil-shell', not an absolute path")
                            for line in self.refused(relative)), relative.stdout[-2000:])
        absolute = self.cli(candidate, SHELL="/bin/sh")
        self.assertIn("host_boundary: judged $SHELL /bin/sh", absolute.stdout)
        self.assertIn("host_boundary: judged the system shell /bin/sh", absolute.stdout)
        self.assertEqual([line for line in self.refused(absolute) if line.startswith("$SHELL ")], [])
        # (5) in process: the passwd home is judged even when $HOME differs.
        passwd_home = self.base / "passwd-home"
        (passwd_home / ".ssh").mkdir(parents=True)
        os.chmod(passwd_home, 0o700)
        os.chmod(passwd_home / ".ssh", 0o777)
        other_home = self.base / "env-home"
        (other_home / "bin").mkdir(parents=True)
        os.chmod(other_home, 0o700)
        os.chmod(other_home / "bin", 0o700)
        args = types.SimpleNamespace(search_path=str(other_home / "bin"), candidate=str(candidate),
                                     git_repo=[], tool=[], tool_root=[], cargo_root=[])
        fake = types.SimpleNamespace(pw_dir=str(passwd_home), pw_name=ME, pw_uid=EUID)
        real_getpwuid = HB.pwd.getpwuid
        boundary = HB.Boundary(self.accounts())
        with mock.patch.dict(os.environ, {"HOME": str(other_home), "TMPDIR": str(self.base)}), \
             mock.patch.object(HB.pwd, "getpwuid", side_effect=lambda uid: fake if uid == EUID else real_getpwuid(uid)):
            try:
                HB.judge_all(args, boundary)
            except HB._TooMany:
                pass
        self.assertIn(f"ssh configuration {passwd_home / '.ssh'}", boundary.places)
        self.assertTrue(any(str(passwd_home / ".ssh") in r and "writable by every user" in r
                            for r in boundary.refusals), boundary.refusals)

    # -- repair round 3 of OD-XHOST-TRANSPORT-WORDS-20261024 ---------------
    def layout_refusals(self, repo: Path, **environment: str) -> list[str]:
        """judge_git's refusals for `repo` alone (no global or system file)."""
        with mock.patch.dict(os.environ, {"GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
                                          **environment}):
            boundary = HB.Boundary(self.accounts())
            HB.judge_git(boundary, "/usr/bin:/bin", [str(repo)])
        return boundary.refusals

    def test_a_repository_git_uses_differently_than_given_is_refused(self):
        """Blocking findings 1 and 2 of the round-3 verifier (e2e_probe.py A, A2,
        B and B2): the work-tree rule judged the directory given, but git chdirs
        to core.worktree when it names an ancestor (or any other directory), and
        a subdirectory of a repository has no .git of its own, so judge_git
        skipped it while `git -C <subdir> fetch` used the parent repository's
        configuration and ran its uploadpack from the parent's top level.
        judge_git now asks git (rev-parse) which work tree and git directory it
        uses and refuses unless they are the ones judged: core.worktree at an
        ancestor, at a descendant, a subdirectory, a directory in no
        repository, core.bare on a work tree's .git, and a GIT_DIR naming
        another repository. A plain repository, core.worktree naming the
        repository itself, a linked worktree, a bare repository, a submodule
        (whose git directory names its work tree as core.worktree) and a
        missing directory pass. The candidate goes through the same function (it is
        judge_git's first repository)."""
        repo = self.committed_repository("layout")
        (repo / "sub").mkdir()
        (repo / "sub" / "file").write_text("x\n")
        self.git("-C", str(repo), "add", "-A")
        self.git("-C", str(repo), "commit", "-q", "-m", "sub")
        self.assertEqual(self.layout_refusals(repo), [])
        place = "(the git repository {})"

        def refusal(path: Path, refusals: list[str]) -> str:
            found = [line for line in refusals if line.startswith(f"{path} {place.format(path)}: ")]
            self.assertEqual(len(found), 1, refusals)
            return found[0]

        for worktree, top in ((self.base, self.base), (repo / "sub", repo / "sub")):
            with self.subTest(core_worktree=str(worktree)):
                self.git("-C", str(repo), "config", "core.worktree", str(worktree))
                why = refusal(repo, self.layout_refusals(repo))
                self.assertIn(f"git's work tree for it is {top} (a core.worktree", why)
                self.assertIn("remedy: point the variable at the repository's own top level", why)
        self.git("-C", str(repo), "config", "core.worktree", str(repo))
        self.assertEqual(self.layout_refusals(repo), [])
        self.git("-C", str(repo), "config", "--unset", "core.worktree")
        self.assertIn("holds no git repository of its own (no .git)", refusal(repo / "sub",
                                                                            self.layout_refusals(repo / "sub")))
        plain = self.base / "plain"
        plain.mkdir()
        self.assertIn("holds no git repository of its own", refusal(plain, self.layout_refusals(plain)))
        other = self.committed_repository("other")
        why = refusal(repo, self.layout_refusals(repo, GIT_DIR=str(other / ".git")))
        self.assertIn(f"git uses the git directory {other / '.git'} there, not {repo / '.git'}", why)
        self.git("-C", str(repo), "config", "core.bare", "true")
        self.assertIn("git treats it as a bare repository", refusal(repo, self.layout_refusals(repo)))
        self.git("--git-dir", str(repo / ".git"), "config", "core.bare", "false")
        self.assertEqual(self.layout_refusals(repo), [])
        linked = self.base / "linked"
        self.git("-C", str(repo), "worktree", "add", "-q", "--detach", str(linked), "HEAD")
        self.assertEqual(self.layout_refusals(linked), [])
        bare = self.base / "bare.git"
        self.git("clone", "-q", "--bare", str(repo), str(bare))
        self.assertEqual(self.layout_refusals(bare), [])
        self.assertEqual(self.layout_refusals(self.base / "missing"), [])
        # A submodule's git directory sets core.worktree to its own work tree,
        # which git then reports as the top: it passes.
        superproject = self.committed_repository("superproject")
        self.git("-C", str(superproject), "-c", "protocol.file.allow=always", "submodule", "add", "-q", str(repo),
                 "module")
        self.assertIn("worktree = ../../../module",
                      (superproject / ".git" / "modules" / "module" / "config").read_text())
        self.assertEqual(self.layout_refusals(superproject / "module"), [])

    def test_each_cargo_git_database_is_judged_as_a_repository(self):
        """Cargo runs `git fetch` in each $CARGO_HOME/git/db/<name> (bare) with
        net.git-fetch-with-cli, and judge_git never listed their own
        configuration (a residual until repair round 3): judge_all now hands
        each database to judge_git, which judges git's view of it and the
        programs its configuration names."""
        import types
        cargo_home = self.base / "cargo-home"
        database = cargo_home / "git" / "db" / "dep-0123456789abcdef"
        database.parent.mkdir(parents=True)
        self.git("init", "-q", "--bare", str(database))
        home = self.base / "db-home"
        (home / "bin").mkdir(parents=True)
        for directory in (home, home / "bin"):
            os.chmod(directory, 0o700)
        args = types.SimpleNamespace(search_path=str(home / "bin"), candidate=str(self.committed_repository("db-cg")),
                                     git_repo=[], tool=[], tool_root=[], cargo_root=[])
        captured: list[str] = []
        with mock.patch.dict(os.environ, {"HOME": str(home), "TMPDIR": str(self.base), "CARGO_HOME": str(cargo_home)}), \
             mock.patch.object(HB, "judge_git",
                               side_effect=lambda boundary, search_path, repos, *rest: captured.extend(repos)):
            HB.judge_all(args, HB.Boundary(self.accounts()))
        self.assertIn(str(database), captured)
        self.assertEqual(self.layout_refusals(database), [])
        shared = self.base / "shared777"
        shared.mkdir()
        os.chmod(shared, 0o777)
        (shared / "evil").write_text("#!/bin/sh\n")
        os.chmod(shared / "evil", 0o755)
        self.git("--git-dir", str(database), "config", "credential.helper", str(shared / "evil"))
        refusals = self.layout_refusals(database)
        self.assertTrue(any(line.startswith(f"{shared} (git configuration of {database}: credential.helper): "
                                            "writable by every user") for line in refusals), refusals)

    def test_a_bang_command_is_split_only_where_the_shell_splits(self):
        """Blocking finding 3 of the round-3 verifier (unit_probe.py): 9352c20f1
        stripped a credential.helper's `!` prefix with str.lstrip(), which
        removes U+00A0 and the other Unicode whitespace too, so
        `!<U+00A0>/usr/bin/true` was judged as the absolute /usr/bin/true and
        passed, while /bin/sh runs the RELATIVE program `<U+00A0>/usr/bin/true`
        from git's working directory (4a0668957 refused it). Only blanks and
        newlines are skipped now: U+00A0, U+2003 and a vertical tab after the
        `!` refuse as a relative program; a space or tab after it passes."""
        repo = self.committed_repository("bang")
        plain = (repo / ".git" / "config").read_text()
        for value, refused in (("!\u00a0/usr/bin/true", True), ("!\u2003/usr/bin/true", True),
                               ("!\x0b/usr/bin/true", True), ("! /usr/bin/true", False),
                               ("!\t/usr/bin/true", False), ("!/usr/bin/true", False)):
            with self.subTest(value=value):
                refusals = self.judge_command_value(repo, plain, "credential", "helper", value)
                self.assertEqual(bool(refusals), refused, (value, refusals))
                if refused:
                    self.assertIn("by a relative path, which git runs from its working directory", refusals[0])

    def test_a_configured_path_is_judged_as_git_reads_it_unstripped(self):
        """_expand stripped a core.hooksPath (and an origin, core.attributesFile)
        with str.strip(), but git's parser already removed the unquoted
        whitespace, so a quoted `"<dir> "` names `<dir> ` to git: the check
        judged the private `<dir>` while git ran hooks from the 0777 `<dir> `.
        The value is judged as git reads it (found in repair round 3)."""
        repo = self.committed_repository("hooks-space")
        private = self.base / "hooks"
        private.mkdir()
        os.chmod(private, 0o700)
        spaced = self.base / "hooks "
        spaced.mkdir()
        os.chmod(spaced, 0o777)
        plain = (repo / ".git" / "config").read_text()
        refusals = self.judge_command_value(repo, plain, "core", "hooksPath", f'"{spaced}"')
        self.assertTrue(any(line.startswith(f"{spaced} (git configuration of {repo}: core.hooksPath): writable by "
                                            "every user") for line in refusals), refusals)
        self.assertEqual(self.judge_command_value(repo, plain, "core", "hooksPath", str(private)), [])

    def test_a_cargo_root_through_proc_refuses_before_realpath(self):
        """The round-3 verifier's two notes on judge_cargo_ancestry: a lexical
        /proc/1/cwd reached os.path.realpath first (PermissionError, refused
        only as `could not be examined`), and a symlink named like a cargo root
        that points at /proc/self/cwd was followed by realpath into the
        checker's own cwd. Both are followed hop by hop now and refuse as
        resolving into /proc."""
        link = self.base / "cargo-root-link"
        link.symlink_to("/proc/self/cwd")
        for path in (str(link), "/proc/1/cwd", "/proc/self/cwd/x"):
            with self.subTest(path=path):
                boundary = HB.Boundary(self.accounts())
                boundary.judge_cargo_ancestry(path, "test")
                self.assertEqual(len(boundary.refusals), 1, boundary.refusals)
                self.assertIn(f"{path} (test): resolves into /proc", boundary.refusals[0])
        self.assertIsNone(HB._self_view_on_the_way(str(self.base)))
        # Repair round 4: the hop-by-hop walk stops at a missing component,
        # where os.path.realpath goes on lexically (a `mkdir -p` of the path
        # creates the component and then lands in /proc), so the lexical
        # normal form is tested too, as f7919800a tested it; a6cbba41b had
        # dropped that test and judged the checker's cwd instead.
        missing = str(self.base / "missing") + "/.." * len(self.base.parts) + "/proc/self/cwd"
        for path in (missing, "/nonexistent-host-boundary/../proc/1/cwd"):
            with self.subTest(path=path):
                self.assertIsNone(HB._self_view_on_the_way(path))
                boundary = HB.Boundary(self.accounts())
                boundary.judge_cargo_ancestry(path, "test")
                self.assertEqual(len(boundary.refusals), 1, boundary.refusals)
                self.assertIn(f"{path} (test): resolves into /proc", boundary.refusals[0])

    # -- repair round 4 of OD-XHOST-TRANSPORT-WORDS-20261024 ---------------
    def test_every_alias_is_judged_as_git_runs_it(self):
        """The round-3 verifier's B1 against a6cbba41b: an alias's first word
        alone was judged ('the gate never runs an alias'), but a judged command
        key can run git with one: `remote.origin.uploadpack = git x` passes
        (`git` a PATH program, `x` a plain word) and the preflight's fetch then
        runs alias x from the Clean work tree. Every alias is judged now. A `!`
        alias is a shell command under every other key's rules; an alias
        without `!` is a git argument list, whose every word is read by
        command_later_word and whose first word refuses by name when it is a
        git option (`-c`, `-C`, `--exec-path`, `--git-dir`, `--work-tree`,
        `--config-env`, ...), since git's options run programs
        (`fetch --upload-pack=<path>`, `-c core.sshCommand=<path> fetch`). In
        any command, a word naming git followed by a git option refuses
        (`git -C <dir> x` would use the configuration of a repository found
        there). Ordinary aliases (`status -s`, `log --oneline --graph -20`,
        `checkout`, `!git status`, `!/usr/bin/true`) and `uploadpack = git x`
        with a plain alias pass."""
        repo = self.committed_repository("aliases")
        plain = (repo / ".git" / "config").read_text()
        shared = self.base / "shared777"
        shared.mkdir()
        os.chmod(shared, 0o777)
        (shared / "evil").write_text("#!/bin/sh\n")
        os.chmod(shared / "evil", 0o755)
        writable = f"{shared} (git configuration of {repo}: alias.x): writable by every user (mode 0777)"
        option = "is a git option (`-c`, `-C`, `--exec-path`, `--git-dir`, `--work-tree`, `--config-env`, ...)"
        refused = (
            ("alias", "x", f"!sh {shared / 'evil'}", writable),
            ("alias", "x", "!sh ../evil", "whose later word '../evil' holds `..`"),
            ("alias", "x", "!env PATH=/tmp gh", "whose later word 'PATH=/tmp' sets the environment"),
            ("alias", "x", "!sh evil | true", "a shell metacharacter"),
            ("alias", "x", f"fetch --upload-pack={shared / 'evil'}", writable),
            ("alias", "x", "fetch --upload-pack=../evil", "whose word '--upload-pack=../evil' holds `..`"),
            ("alias", "x", "fetch --upload-pack=tools/evil", "nor a plain `--option=`"),
            ("alias", "x", "-c core.sshCommand=/usr/bin/true fetch", f"whose first word '-c' {option}"),
            ("alias", "x", "-C .. status", f"whose first word '-C' {option}"),
            ("alias", "x", "--exec-path=/usr status", f"whose first word '--exec-path=/usr' {option}"),
            ("alias", "x", "--git-dir=sub status", f"whose first word '--git-dir=sub' {option}"),
            ("alias", "x", "--work-tree=sub status", "is a git option"),
            ("alias", "x", "--config-env=core.pager=PAGER log", "is a git option"),
            ("alias", "x", "log '--format=%h'", "plain-argument set"),
            ("alias", "x", "submodule foreach git -C sub y",
             "whose word 'git' names git and is followed by the git option '-C'"),
            ("alias", "x", "!git -C sub status", "whose word 'git' names git and is followed by the git option '-C'"),
            ("remote \"origin\"", "uploadpack", "git -C sub x",
             "whose word 'git' names git and is followed by the git option '-C'"),
            ("remote \"origin\"", "uploadpack", "/usr/bin/git --git-dir=sub x",
             "whose word '/usr/bin/git' names git and is followed by the git option '--git-dir=sub'"),
            ("remote \"origin\"", "uploadpack", "env git -c alias.y=status y",
             "whose word 'git' names git and is followed by the git option '-c'"),
        )
        for section, name, value, expected in refused:
            with self.subTest(section=section, name=name, value=value):
                refusals = self.judge_command_value(repo, plain, section, name, value)
                self.assertTrue(any(expected in refusal for refusal in refusals), (value, refusals))
        for section, name, value in (("alias", "st", "status -s"), ("alias", "lg", "log --oneline --graph -20"),
                                     ("alias", "co", "checkout"), ("alias", "x", "!git status"),
                                     ("alias", "x", "!/usr/bin/true"), ("alias", "x", "! /usr/bin/true"),
                                     ("alias", "x", "")):
            with self.subTest(section=section, name=name, value=value):
                self.assertEqual(self.judge_command_value(repo, plain, section, name, value), [])
        # OD-XHOST-GIT-PROGRAM-KEYS-20261024: a configured upload-pack refuses
        # outright in every scope (it passed here before, `git x` being a PATH
        # program and a plain word), and so does `uploadpack = git x` with a
        # plain alias x in the repository's own configuration.
        refusals = self.judge_command_value(repo, plain, "remote \"origin\"", "uploadpack", "git x")
        self.assertTrue(any("refused outright in every scope" in line for line in refusals), refusals)
        config = repo / ".git" / "config"
        config.write_text(plain + "[remote \"origin\"]\n\tuploadpack = git x\n[alias]\n\tx = upload-pack\n")
        refusals = self.layout_refusals(repo)
        self.assertTrue(any("refused outright in every scope" in line for line in refusals), refusals)
        self.assertTrue(any(line.startswith(f"{repo} alias.x (") and "not on the allowlist" in line
                            for line in refusals), refusals)

    def test_a_shell_command_whose_first_word_is_reserved_refuses(self):
        """The round-3 verifier's B2 against a6cbba41b: repair round 3 stripped
        exactly one `!` (as git does) where 4a0668957 stripped every leading
        `!`, so `alias.x = !! <program in a 0777 directory>` was judged as the
        program `!` (the shell's reserved word, an unfound PATH name) and
        passed, while git strips one `!` and /bin/sh runs `! <program>`, which
        runs the program: a weakened refusal. A shell command whose first word
        the shell reads as reserved, or that begins with `!`, now refuses by
        name, whichever key holds it: `!! /x`, `! ! /x`, `!!/x`, `!if true`,
        `!time sh evil`, a credential helper's `!! /x`, a core.fsmonitor
        `!/usr/bin/true` (git strips no `!` there, so the shell runs the
        relative `!/usr/bin/true`) and `time sh evil`, and GIT_SSH_COMMAND
        `! ssh` and `time ssh`. This host's `!/usr/bin/gh auth
        git-credential` (where /usr/bin/gh exists), the same shape with
        /usr/bin/true in a `credential.<url>.helper`, the empty reset value,
        `! /usr/bin/true` and the transport `ssh` keep passing."""
        repo = self.committed_repository("reserved")
        plain = (repo / ".git" / "config").read_text()
        shared = self.base / "shared777"
        shared.mkdir()
        os.chmod(shared, 0o777)
        (shared / "evil").write_text("#!/bin/sh\n")
        os.chmod(shared / "evil", 0o755)
        reserved = "its first word {!r} is a word the shell reads as reserved where a command begins"
        bang = "its first word {!r} begins with `!`: git strips only one `!`"
        refused = (
            ("alias", "x", f"!! {shared / 'evil'}", reserved.format("!")),
            ("alias", "x", "!! /usr/bin/true", reserved.format("!")),
            ("alias", "x", "! ! /usr/bin/true", reserved.format("!")),
            ("alias", "x", "!!/usr/bin/true", bang.format("!/usr/bin/true")),
            ("alias", "x", "!if true", reserved.format("if")),
            ("alias", "x", "!time sh evil", reserved.format("time")),
            ("alias", "x", "!function", reserved.format("function")),
            ("credential", "helper", "!! /usr/bin/true", reserved.format("!")),
            ('credential "https://example.com"', "helper", "!!/usr/bin/true", bang.format("!/usr/bin/true")),
            ("core", "fsmonitor", "!/usr/bin/true", bang.format("!/usr/bin/true")),
            ("core", "fsmonitor", "time sh evil", reserved.format("time")),
            ("remote \"origin\"", "uploadpack", "! /usr/bin/true", reserved.format("!")),
        )
        for section, name, value, expected in refused:
            with self.subTest(section=section, name=name, value=value):
                refusals = self.judge_command_value(repo, plain, section, name, value)
                self.assertTrue(any(expected in refusal for refusal in refusals), (value, refusals))
        passing = [("credential", "helper", "!/usr/bin/true auth git-credential"),
                   ('credential "https://github.com"', "helper", "!/usr/bin/true auth git-credential"),
                   ("credential", "helper", ""), ("alias", "x", "! /usr/bin/true")]
        if os.path.exists("/usr/bin/gh"):
            passing += [("credential", "helper", "!/usr/bin/gh auth git-credential"),
                        ('credential "https://github.com"', "helper", "!/usr/bin/gh auth git-credential")]
        for section, name, value in passing:
            with self.subTest(section=section, name=name, value=value):
                self.assertEqual(self.judge_command_value(repo, plain, section, name, value), [])
        for value, refused_value in (("! ssh", True), ("time ssh", True), ("!", True), ("ssh", False)):
            with self.subTest(transport=value):
                boundary = HB.Boundary(self.accounts())
                HB.judge_transport_program(boundary, value, "$GIT_SSH_COMMAND", "place", "/usr/bin:/bin",
                                           shell=True)
                self.assertEqual(bool(boundary.refusals), refused_value, boundary.refusals)
                if refused_value:
                    self.assertIn("is a word the shell reads as reserved", boundary.refusals[0])

    def test_a_repository_key_off_the_allowlist_refuses(self):
        """R1 of OD-XHOST-GIT-PROGRAM-KEYS-20261024: a configured git command
        key reaches a program-valued key the check never lists through a git
        helper subcommand (`remote.origin.uploadpack = git web--browse -b
        <tool>` runs browser.<tool>.cmd; `--ext-diff`/diff.external and the
        difftool/mergetool `.cmd` keys are the same shape). Rather than name
        every such key, every key of a repository's own configuration is
        refused unless it is on the allowlist of keys that name no program.
        A data key (`core.autocrlf`, `branch.main.remote`, `advice.*`,
        `submodule.<n>.url`), and the path keys judge_git judges
        (core.hooksPath to a private directory), pass; a browser/diff/difftool/
        mergetool command, diff.external, a .cmd key, sendemail.smtpServer,
        remote.<n>.proxy, submodule.<n>.update and an unknown key refuse."""
        repo = self.committed_repository("local-allowlist")
        private = self.base / "hooks"
        private.mkdir()
        os.chmod(private, 0o700)
        # Each case adds its key to the configuration the previous ones left,
        # so remote.origin.url is configured before branch.main.remote names
        # it (a branch remote naming no configured remote is judged as a
        # location: test_a_branch_remote_naming_no_configured_remote_is_judged).
        allowed = (("core", None, "autocrlf", "false"),
                   ("remote \"origin\"", None, "url", "https://example.invalid/x.git"),
                   ("branch \"main\"", None, "remote", "origin"),
                   ("branch \"main\"", None, "merge", "refs/heads/main"),
                   ("branch \"main\"", None, "pushRemote", "."),
                   ("submodule \"vendor/x\"", None, "url", "https://example.invalid/s.git"),
                   ("submodule \"vendor/x\"", None, "active", "true"),
                   ("submodule", None, "recurse", "true"),
                   ("advice", None, "detachedHead", "false"),
                   ("core", None, "hooksPath", str(private)),
                   ("extensions", None, "worktreeConfig", "false"))
        for section, _sub, name, value in allowed:
            with self.subTest(allowed=f"{section}.{name}"):
                self.assertEqual(self.judge_command_value(repo, plain=(repo / ".git" / "config").read_text(),
                                 section=section, name=name, value=value, scope="local"), [])
        refused = (("web", "browser", "false"), ("diff", "external", "/usr/bin/true"),
                   ('difftool "vimdiff"', "cmd", "vimdiff"), ('mergetool "vimdiff"', "cmd", "vimdiff"),
                   ('browser "x"', "cmd", "/usr/bin/true"), ('browser "x"', "path", "/usr/bin/true"),
                   ("sendemail", "smtpServer", "/usr/sbin/sendmail"), ("pager", "log", "less"),
                   ("interactive", "diffFilter", "/usr/bin/true"), ("man", "viewer", "/usr/bin/true"),
                   ("remote \"origin\"", "proxy", "/usr/bin/true"),
                   ("submodule \"vendor/x\"", "update", "!/usr/bin/true"),
                   ("uploadpack", "packObjectsHook", "/usr/bin/true"), ("core", "whatever", "x"))
        for section, name, value in refused:
            with self.subTest(refused=f"{section}.{name}"):
                refusals = self.judge_command_value(repo, plain=(repo / ".git" / "config").read_text(),
                                                    section=section, name=name, value=value, scope="local")
                self.assertTrue(any("not on the allowlist" in r or "refused outright in every scope" in r
                                    or "names a program git or a git helper runs" in r for r in refusals),
                                (section, name, refusals))

    def test_a_local_path_remote_is_judged_as_a_repository(self):
        """R2 of OD-XHOST-GIT-PROGRAM-KEYS-20261024: git runs upload-pack in a
        local-path remote's own repository (and passes that path to a
        configured upload-pack command as its last argument), so a
        remote.*.url (and pushurl, submodule.*.url) that names a local path is
        judged as a repository: its tree, git directories and configuration.
        A local remote whose work tree holds a 0777 file refuses; a network
        URL and an scp-like ssh location are not judged here (ssh's own
        config is); a relative or ext:: location refuses as unjudgeable; a
        remote.*.uploadpack refuses outright."""
        repo = self.committed_repository("remote-url")
        plain = (repo / ".git" / "config").read_text()
        # A private local origin: judged and accepted.
        origin = self.committed_repository("local-origin")
        self.assertEqual(self.judge_command_value(repo, plain, "remote \"o\"", "url", str(origin),
                                                  scope="local"), [])
        # Its work tree holds a 0777 file: the remote is judged and refuses.
        (origin / "evil").write_text("#!/bin/sh\n")
        os.chmod(origin / "evil", 0o777)
        refusals = self.judge_command_value(repo, plain, "remote \"o\"", "url", str(origin), scope="local")
        self.assertTrue(any(str(origin / "evil") in r and "writable by every user" in r for r in refusals), refusals)
        os.chmod(origin / "evil", 0o644)
        # file:// to the same repository: judged. A network URL and an
        # scp-like ssh location: not judged as a local repository (no refusal
        # about a missing repository).
        for value in ("https://example.invalid/x.git", "git@example.invalid:x.git", f"file://{origin}"):
            with self.subTest(url=value):
                self.assertEqual(self.judge_command_value(repo, plain, "remote \"o\"", "url", value,
                                 scope="local"), [])
        for value, why in ((f"ext::sh -c {origin}", "ext:: location"), ("../sibling", "relative or `~` path"),
                           (f"file://{origin}/%2e", "not a plain absolute path")):
            with self.subTest(url=value):
                refusals = self.judge_command_value(repo, plain, "remote \"o\"", "url", value, scope="local")
                self.assertTrue(any(why in r for r in refusals), (value, refusals))
        # A local path that is no repository refuses.
        empty = self.base / "not-a-repo"
        empty.mkdir()
        refusals = self.judge_command_value(repo, plain, "remote \"o\"", "url", str(empty), scope="local")
        self.assertTrue(any("not a directory holding a git repository" in r for r in refusals), refusals)
        # uploadpack refuses outright, in the global scope too.
        for scope in ("local", "global"):
            refusals = self.judge_command_value(repo, plain, "remote \"o\"", "uploadpack", "/usr/bin/true",
                                                scope=scope)
            self.assertTrue(any("refused outright in every scope" in r for r in refusals), (scope, refusals))

    def test_a_submodule_configuration_is_judged(self):
        """R1, one step in: git runs in a populated submodule's git directory
        below <git-dir>/modules, so each submodule's config and config.worktree
        are judged against the same allowlist. A submodule core.fsmonitor
        naming a 0777 program refuses; a data key passes."""
        repo = self.committed_repository("superproject")
        module = repo / ".git" / "modules" / "vendor" / "sub"
        module.mkdir(parents=True)
        self.git("init", "-q", "--bare", str(module))
        self.git("--git-dir", str(module), "config", "core.autocrlf", "false")
        self.assertEqual(self.layout_refusals(repo), [])
        shared = self.base / "shared777"
        shared.mkdir()
        os.chmod(shared, 0o777)
        (shared / "evil").write_text("#!/bin/sh\n")
        os.chmod(shared / "evil", 0o755)
        self.git("--git-dir", str(module), "config", "core.fsmonitor", str(shared / "evil"))
        refusals = self.layout_refusals(repo)
        self.assertTrue(any(f"{shared} (git configuration of {module}: core.fsmonitor): writable by every user"
                            in r for r in refusals), refusals)
        # A key off the allowlist in the submodule's config.worktree refuses too.
        self.git("--git-dir", str(module), "config", "core.fsmonitor", "/usr/bin/true")
        self.git("--git-dir", str(module), "config", "extensions.worktreeConfig", "true")
        (module / "config.worktree").write_text("[diff]\n\texternal = /usr/bin/true\n")
        refusals = self.layout_refusals(repo)
        self.assertTrue(any(f"{module} diff.external" in r and "not on the allowlist" in r for r in refusals),
                        refusals)

    def superproject_with_submodule(self, name: str, layout: str) -> tuple[Path, Path, Path]:
        """A committed superproject whose index holds the gitlink vendor/sub,
        populated with a one-commit repository whose git directory is
        `layout`: "embedded" (vendor/sub/.git is a directory, as a plain clone
        into the path or Cargo's checkout submodules leave it), "elsewhere"
        (vendor/sub/.git is a `gitdir:` file naming a directory outside the
        superproject) or "absorbed" (below <git-dir>/modules, as `git
        submodule absorbgitdirs` leaves it). Returns (superproject, the
        submodule's path, its git directory)."""
        repo = self.committed_repository(name)
        sub = repo / "vendor" / "sub"
        sub.mkdir(parents=True)
        self.git("init", "-q", "-b", "main", str(sub))
        (sub / "lib.rs").write_text("pub fn f() {}\n")
        self.git("-C", str(sub), "add", "-A")
        self.git("-C", str(sub), "commit", "-q", "-m", "sub")
        head = self.git("-C", str(sub), "rev-parse", "HEAD")
        (repo / ".gitmodules").write_text('[submodule "vendor/sub"]\n\tpath = vendor/sub\n'
                                          '\turl = https://example.invalid/sub.git\n')
        self.git("-C", str(repo), "update-index", "--add", "--cacheinfo", f"160000,{head},vendor/sub")
        self.git("-C", str(repo), "add", ".gitmodules")
        self.git("-C", str(repo), "commit", "-q", "-m", "submodule")
        git_dir = sub / ".git"
        if layout == "elsewhere":
            git_dir = self.base / f"{name}-elsewhere-gitdir"
            os.rename(sub / ".git", git_dir)
            (sub / ".git").write_text(f"gitdir: {git_dir}\n")
        elif layout == "absorbed":
            self.git("-C", str(repo), "submodule", "absorbgitdirs")
            git_dir = repo / ".git" / "modules" / "vendor" / "sub"
        return repo, sub, git_dir

    def judge_git_config_main(self, repo: Path) -> tuple[int, str]:
        """`host_boundary.py --judge-git-config <repo>` (a pinned checkout's
        check) with no global or system file: (exit code, report)."""
        output = io.StringIO()
        with mock.patch.dict(os.environ, {"GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}), \
                contextlib.redirect_stdout(output):
            rc = HB.main(["--search-path", "/usr/bin:/bin", "--judge-git-config", str(repo)])
        return rc, output.getvalue()

    def test_a_repository_nested_in_a_judged_work_tree_is_judged(self):
        """Repair round 2 of OD-XHOST-GIT-PROGRAM-KEYS-20261024 (both
        verifiers' blocking finding): git status runs `cd <path>; GIT_DIR=.git
        git status` in every populated submodule, with that repository's own
        configuration, whatever its layout, but only git directories below
        <git-dir>/modules were judged, so an EMBEDDED submodule (a .git
        directory in the path) or a `gitdir:` file naming a directory
        elsewhere passed with any key (the verifier's color.ui and
        core.fsmonitor probes). Now every repository nested in the work tree of
        one the run uses git in is judged as a repository: in each layout an
        off-allowlist key refuses naming the nested repository, a
        core.fsmonitor naming a 0777 program refuses on the program too, and
        the private control (data keys only) passes. A git directory
        elsewhere is judged as a tree; a core.worktree naming another
        directory refuses (git status would run there); a symlinked gitlink
        path (git status follows it) and an untracked clone in the work tree
        (Lake's packages, a judged program's `env -C <word> git`) are judged
        too; a `.git` that is no repository refuses; and --judge-git-config
        (a pinned checkout) judges the same."""
        shared = self.base / "shared777"
        shared.mkdir()
        os.chmod(shared, 0o777)
        (shared / "evil").write_text("#!/bin/sh\n")
        os.chmod(shared / "evil", 0o755)
        for layout in ("embedded", "elsewhere", "absorbed"):
            with self.subTest(layout=layout):
                repo, sub, git_dir = self.superproject_with_submodule(f"super-{layout}", layout)
                self.git("-C", str(repo), "config", "submodule.recurse", "true")
                # The private control: the submodule's own configuration holds
                # data keys only.
                self.assertEqual(self.layout_refusals(repo), [])
                self.assertEqual(self.judge_git_config_main(repo)[0], 0)
                self.git("--git-dir", str(git_dir), "config", "color.ui", "auto")
                refusals = self.layout_refusals(repo)
                owner = git_dir if layout == "absorbed" else sub
                self.assertTrue(any(f"{owner} color.ui" in r and "not on the allowlist" in r for r in refusals),
                                (layout, refusals))
                rc, report = self.judge_git_config_main(repo)
                self.assertEqual(rc, 1, report)
                self.assertIn(f"REFUSED {owner} color.ui", report)
                self.git("--git-dir", str(git_dir), "config", "--unset", "color.ui")
                self.git("--git-dir", str(git_dir), "config", "core.fsmonitor", str(shared / "evil"))
                refusals = self.layout_refusals(repo)
                self.assertTrue(any(f"{shared} (git configuration of " in r and "core.fsmonitor): writable by "
                                    "every user" in r for r in refusals), (layout, refusals))
                self.git("--git-dir", str(git_dir), "config", "--unset", "core.fsmonitor")
                self.assertEqual(self.layout_refusals(repo), [])
                if layout == "elsewhere":
                    # The git directory elsewhere is judged as a tree.
                    (git_dir / "hooks" / "open").write_text("")
                    os.chmod(git_dir / "hooks" / "open", 0o666)
                    refusals = self.layout_refusals(repo)
                    self.assertTrue(any(f"{git_dir / 'hooks' / 'open'}" in r and "writable by every user" in r
                                        for r in refusals), refusals)
                    os.chmod(git_dir / "hooks" / "open", 0o644)
                if layout == "embedded":
                    # core.worktree naming another directory: git status would
                    # run in it.
                    other = self.base / "other-work-tree"
                    other.mkdir()
                    self.git("--git-dir", str(git_dir), "config", "core.worktree", str(other))
                    refusals = self.layout_refusals(repo)
                    self.assertTrue(any(f"git's work tree for it is {other}" in r for r in refusals), refusals)
                    self.git("--git-dir", str(git_dir), "config", "--unset", "core.worktree")
        # A symlinked gitlink path: git status follows it into a repository
        # outside the superproject's work tree.
        repo, sub, git_dir = self.superproject_with_submodule("super-link", "embedded")
        moved = self.base / "moved-sub"
        os.rename(sub, moved)
        os.symlink(moved, sub)
        self.git("--git-dir", str(moved / ".git"), "config", "diff.external", "/usr/bin/true")
        refusals = self.layout_refusals(repo)
        self.assertTrue(any(f"{moved} diff.external" in r and "not on the allowlist" in r for r in refusals),
                        refusals)
        # An untracked clone in the work tree (no gitlink): judged too.
        repo = self.committed_repository("super-untracked")
        package = repo / ".lake" / "packages" / "dep"
        package.parent.mkdir(parents=True)
        self.git("init", "-q", "-b", "main", str(package))
        self.assertEqual(self.layout_refusals(repo), [])
        self.git("-C", str(package), "config", "diff.external", "/usr/bin/true")
        refusals = self.layout_refusals(repo)
        self.assertTrue(any(f"{package} diff.external" in r and "not on the allowlist" in r for r in refusals),
                        refusals)
        # A `.git` that is no repository refuses.
        junk = repo / "junk"
        junk.mkdir()
        (junk / ".git").write_text("not a gitdir line\n")
        self.git("-C", str(package), "config", "--unset", "diff.external")
        refusals = self.layout_refusals(repo)
        self.assertTrue(any(f"{junk / '.git'}" in r and "cannot read as a repository" in r for r in refusals),
                        refusals)

    def judged_boundary(self, repo: Path) -> HB.Boundary:
        """judge_git's Boundary for `repo` alone (no global or system file)."""
        with mock.patch.dict(os.environ, {"GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}):
            boundary = HB.Boundary(self.accounts())
            HB.judge_git(boundary, "/usr/bin:/bin", [str(repo)])
        return boundary

    def test_a_local_remote_that_is_also_a_submodule_gets_the_nested_judgement(self):
        """Repair round 3 of OD-XHOST-GIT-PROGRAM-KEYS-20261024 (the round-2
        regression verifier's blocking finding at 850f69fd0): the candidate's
        remote.mirror.url names its own populated submodule vendor/sub, so
        judge_local_remote judged that repository first (its tree, git
        directories and local configuration, but not git's view of its work
        tree: upload-pack uses none) and recorded its identity; the nested
        judgement then returned early on that identity, so the submodule's
        core.worktree naming a 0777 directory passed although git status
        enters the submodule and runs git there. The memo is now keyed on
        (identity, kind of judgement): the private control (no core.worktree)
        passes and records the submodule's nested judgement after its
        local-remote one; with core.worktree naming the 0777 directory the
        nested judgement asks git and refuses."""
        repo, sub, git_dir = self.superproject_with_submodule("super-mirror", "embedded")
        self.git("-C", str(repo), "remote", "add", "mirror", str(sub))
        boundary = self.judged_boundary(repo)
        self.assertEqual(boundary.refusals, [])
        self.assertTrue(boundary.has_judgement(str(sub), "local remote"))
        self.assertTrue(boundary.has_judgement(str(sub), "nested repository"))
        local = f"the local repository {repo} remote.mirror.url names {sub}"
        nested = f"the repository {sub} nested in {repo}"
        self.assertIn(local, boundary.places)
        self.assertIn(nested, boundary.places)
        self.assertLess(boundary.places.index(local), boundary.places.index(nested),
                        "the local remote is judged first: the order the round-2 verifier's finding needs")
        shared = self.base / "shared777"
        shared.mkdir()
        os.chmod(shared, 0o777)
        self.git("--git-dir", str(git_dir), "config", "core.worktree", str(shared))
        refusals = self.layout_refusals(repo)
        self.assertTrue(any(r.startswith(f"{sub} ({nested}): git's work tree for it is {shared}") for r in refusals),
                        refusals)
        # The same repository named by a local remote only (no gitlink, no
        # .git in a judged work tree: git uses no work tree there) keeps the
        # documented boundary: its core.worktree is not asked.
        lone = self.committed_repository("lone-remote")
        self.git("-C", str(lone), "config", "core.worktree", str(shared))
        plain = self.committed_repository("names-a-lone-remote")
        self.git("-C", str(plain), "remote", "add", "lone", str(lone))
        self.assertEqual(self.layout_refusals(plain), [])

    def test_each_kind_of_repository_judgement_is_made_once_per_identity(self):
        """Boundary.judged is keyed on (directory identity, kind): one kind
        recorded never answers for another, two spellings of one directory are
        one repository, and an unknown kind is an error, not a pass."""
        boundary = HB.Boundary(self.accounts())
        repo = self.committed_repository("memo")
        link = self.base / "memo-link"
        os.symlink(repo, link)
        self.assertTrue(boundary.first_judgement(str(repo), "local remote"))
        self.assertFalse(boundary.first_judgement(str(link), "local remote"))
        self.assertFalse(boundary.has_judgement(str(repo), "nested repository"))
        self.assertTrue(boundary.first_judgement(str(link), "nested repository"))
        self.assertFalse(boundary.first_judgement(str(repo), "nested repository"))
        self.assertEqual(set(HB.REPOSITORY_JUDGEMENTS), {"configuration", "local configuration", "nested walk",
                                                         "nested repository", "local remote"})
        with self.assertRaises(ValueError):
            boundary.has_judgement(str(repo), "repository")
        self.assertFalse(hasattr(boundary, "repositories"), "the identity-only memo is gone")

    def test_the_fail_line_names_the_writability_remedy_only_for_writable_paths(self):
        """The round-2 verifier's tidy item: the FAIL summary said every
        refusal was a path another user can write and gave `chmod go-w`,
        also for a refusal that is no such path. A refusal of another kind
        alone now says so; a writable path keeps the remedy."""
        shared = self.base / "shared"
        shared.mkdir()
        os.chmod(shared, 0o777)

        def fail_line(*writable_paths: Path) -> str:
            def judge(_args, boundary):
                boundary.refuse("/x/repo core.fsmonitor", "git configuration of /x/repo: core.fsmonitor",
                                "is a key of the repository's own (local) configuration that is not on the allowlist")
                for path in writable_paths:
                    boundary.judge(str(path), os.lstat(path), "a tree")
            output = io.StringIO()
            with mock.patch.object(HB, "judge_all", judge), contextlib.redirect_stdout(output):
                self.assertEqual(HB.main(["--search-path", "/usr/bin:/bin", "--candidate", str(self.base)]), 1)
            return output.getvalue().strip().splitlines()[-1]

        last = fail_line()
        self.assertTrue(last.startswith("host_boundary: FAIL: 1 refusal(s): 1 refusal(s) of a setting, location, "
                                        "repository or git configuration key"), last)
        self.assertNotIn("chmod go-w", last)
        self.assertNotIn("can be written by another user", last)
        last = fail_line(shared)
        self.assertTrue(last.startswith("host_boundary: FAIL: 2 refusal(s): 1 refusal(s) of a setting"), last)
        self.assertIn("and 1 path(s) this run would execute or read can be written by another user; remedy: make "
                      "it writable by you alone (`chmod go-w <path>`", last)
        # Writable paths only: the summary is the one it always was.
        boundary = HB.Boundary(self.accounts())
        boundary.judge(str(shared), os.lstat(shared), "a tree")
        self.assertEqual(boundary.writable_refusals, 1)

    def test_a_branch_remote_naming_no_configured_remote_is_judged(self):
        """Repair round 2: git fetches a branch's remote (and remote.pushDefault)
        by name, and a name the configuration does not define is a location
        git uses as given, a relative one being a path in git's working
        directory. Such a local branch.<name>.remote, pushRemote or
        remote.pushDefault is judged as a location: `.` and a configured
        remote pass, an unconfigured name refuses as a relative path, a local
        repository is judged as one. A remotes/ or branches/ file (a remote
        defined outside the configuration) refuses."""
        repo = self.committed_repository("branch-remote")
        plain = (repo / ".git" / "config").read_text()
        origin = self.committed_repository("branch-remote-origin")
        configured = plain + '[remote "origin"]\n\turl = https://example.invalid/x.git\n'
        for section, name, value, refused in (('branch "main"', "remote", "origin", False),
                                              ('branch "main"', "remote", ".", False),
                                              ('branch "main"', "remote", "upstream", True),
                                              ('branch "main"', "pushRemote", "upstream", True),
                                              ("remote", "pushDefault", "upstream", True),
                                              ('branch "main"', "remote", str(origin), False)):
            with self.subTest(key=f"{section}.{name}", value=value):
                refusals = self.judge_command_value(repo, configured, section, name, value, scope="local")
                if refused:
                    self.assertTrue(any("names a repository by a relative or `~` path" in r for r in refusals),
                                    refusals)
                else:
                    self.assertEqual(refusals, [])
        # The local repository a branch remote names is judged as one.
        (origin / "evil").write_text("")
        os.chmod(origin / "evil", 0o666)
        refusals = self.judge_command_value(repo, configured, 'branch "main"', "remote", str(origin), scope="local")
        self.assertTrue(any(str(origin / "evil") in r and "writable by every user" in r for r in refusals), refusals)
        os.chmod(origin / "evil", 0o644)
        (repo / ".git" / "config").write_text(configured)
        for directory in ("remotes", "branches"):
            with self.subTest(legacy=directory):
                legacy = repo / ".git" / directory
                legacy.mkdir(exist_ok=True)
                self.assertEqual(self.layout_refusals(repo), [], "an empty directory passes")
                (legacy / "origin").write_text(f"URL: {origin}\n")
                refusals = self.layout_refusals(repo)
                self.assertTrue(any(f"{legacy} (git configuration of {repo}): defines the remote(s) origin" in r
                                    for r in refusals), refusals)
                (legacy / "origin").unlink()

    def test_the_gate_git_configuration_carries_only_judged_keys(self):
        """The run's own git configuration file (--gate-git-config): it carries
        the credential helpers, identity and core.excludesFile judged from the
        user's system and global configuration and nothing else (no alias,
        pager, filter, url.*.insteadOf), sets fetch.recurseSubmodules=false,
        reads back exactly as written, and is a 0600 file in a 0700 directory.
        A carried helper whose own value is unjudgeable would have refused at
        the boundary already; here the carried keys are the input."""
        carried = [("user.name", b"Fixture"), ("user.email", b"fixture@example.invalid"),
                   ("credential.https://github.com.helper", b""),
                   ("credential.https://github.com.helper", b"!/usr/bin/gh auth git-credential"),
                   ("core.excludesFile", b"/home/u/.gitignore")]
        text, expected = HB.gate_git_config_text(carried)
        self.assertIsNotNone(text, expected)
        self.assertIn('[credential "https://github.com"]', text)
        self.assertIn("recurseSubmodules = ", text)
        self.assertIn(("fetch.recursesubmodules", "false"), expected)
        self.assertIn(("credential.https://github.com.helper", "!/usr/bin/gh auth git-credential"), expected)
        self.assertNotIn("insteadof", text.lower())
        git = shutil.which("git")
        if git:
            path = self.base / "gate-config"
            path.write_text(text)
            listed = subprocess.run([git, "config", "--file", str(path), "--list", "-z"],
                                    capture_output=True, text=True, check=True).stdout
            read = [tuple(field.split("\n", 1)) for field in listed.split("\0")[:-1]]
            read = [(k, v) for k, v in read]
            self.assertEqual(read, expected)
        # A subsection or value this writer cannot spell refuses.
        bad, why = HB.gate_git_config_text([("credential.https://x\n/.helper", b"x")])
        self.assertIsNone(bad, why)
        # A carried key written with no value (git reads `[credential]
        # useHttpPath` as true) is carried exactly, not refused as "not UTF-8"
        # (a round-2 verifier's over-refusal finding).
        text, expected = HB.gate_git_config_text([("credential.useHttpPath", None)])
        self.assertIsNotNone(text, expected)
        self.assertIn(("credential.usehttppath", None), expected)
        if git:
            path = self.base / "gate-config-valueless"
            path.write_text(text)
            listed = subprocess.run([git, "config", "--file", str(path), "--list", "-z"], capture_output=True,
                                    check=True).stdout.decode()
            self.assertEqual(listed.split("\0")[:-1][-1], "credential.usehttppath", listed)
            self.assertEqual(subprocess.run([git, "config", "--file", str(path), "--bool", "credential.useHttpPath"],
                                            capture_output=True, text=True, check=True).stdout.strip(), "true")

    def test_the_files_cargo_libgit2_reads_are_judged_whatever_git_config_global_names(self):
        """Repair round 2: Cargo's built-in libgit2 reads ~/.gitconfig, the XDG
        file and /etc/gitconfig itself, ignoring GIT_CONFIG_GLOBAL and
        GIT_CONFIG_NOSYSTEM, and runs the credential helpers they configure.
        With the caller's GIT_CONFIG_GLOBAL naming another (empty) file, a
        helper in ~/.gitconfig (or the XDG file, or the system file, or a file
        one of them includes) naming a program in a 0777 directory was judged
        by nothing; it now refuses, and nothing of those files is carried into
        the gate's own file. A private helper there passes."""
        home = self.base / "home"
        (home / ".config" / "git").mkdir(parents=True)
        os.chmod(home, 0o700)
        shared = self.base / "shared777"
        shared.mkdir()
        os.chmod(shared, 0o777)
        (shared / "evil").write_text("#!/bin/sh\n")
        os.chmod(shared / "evil", 0o755)
        private = self.base / "private-helper"
        private.write_text("#!/bin/sh\n")
        os.chmod(private, 0o755)
        repo = self.committed_repository("libgit2-files")
        system = self.base / "system-gitconfig"
        included = self.base / "included-gitconfig"
        empty = self.base / "empty-global"
        empty.write_text("")
        cases = (("home", home / ".gitconfig", ""), ("xdg", home / ".config" / "git" / "config", ""),
                 ("system", system, ""), ("include", home / ".gitconfig", f"[include]\n\tpath = {included}\n"))
        for name, path, prefix in cases:
            for helper, refused in ((shared / "evil", True), (private, False)):
                with self.subTest(file=name, refused=refused):
                    for stale in (home / ".gitconfig", home / ".config" / "git" / "config", system, included):
                        if stale.exists():
                            stale.unlink()
                    target = included if name == "include" else path
                    path.write_text(prefix)
                    with target.open("a") as handle:
                        handle.write(f"[credential]\n\thelper = {helper}\n")
                    environment = {"HOME": str(home), "XDG_CONFIG_HOME": str(home / ".config"),
                                   "GIT_CONFIG_GLOBAL": str(empty), "GIT_CONFIG_NOSYSTEM": "1"}
                    with mock.patch.dict(os.environ, environment), \
                            mock.patch.object(HB, "LIBGIT2_SYSTEM_CONFIG", str(system), create=True):
                        boundary = HB.Boundary(self.accounts())
                        HB.judge_git(boundary, "/usr/bin:/bin", [str(repo)])
                    if refused:
                        self.assertTrue(any(f"{shared} (git configuration of {path}: credential.helper): writable "
                                            "by every user" in r for r in boundary.refusals), boundary.refusals)
                    else:
                        self.assertEqual(boundary.refusals, [])
                        self.assertEqual(boundary.carried, [], "nothing of the libgit2 files is carried")

    # -- the import path of a python3 run without -I (OD-XHOST-GATE-CWD-20261025, repair round 2) --
    def private_directory(self, name: str) -> Path:
        directory = self.base / name
        directory.mkdir()
        os.chmod(directory, 0o700)
        return directory

    @staticmethod
    def private_file(path: Path, content: bytes | str = b"") -> Path:
        path.write_bytes(content if isinstance(content, bytes) else content.encode())
        os.chmod(path, 0o600)
        return path

    def judged_user_site(self, site: Path) -> HB.Boundary:
        boundary = HB.Boundary(self.accounts())
        boundary.judge_tree(str(site), "python3's user site-packages")
        HB.judge_user_site(boundary, str(site))
        return boundary

    def test_each_directory_a_user_site_pth_file_names_is_judged_as_a_tree(self):
        """The repair round 2 verifier's probe.pth: a path line naming a
        0777 directory put it on the import path of every python3 run without
        -I, after the standard library, and the check never judged it. Every
        path line now names a judged tree, resolved as site.py resolves it
        (joined to the site directory, made absolute, `..` folded, stripped
        at its end only); a comment, a blank line and a line with a leading
        space before `import` are read as python3 reads them, and the
        directories judged are the ones site.addsitedir puts on sys.path."""
        site = self.private_directory("user-site")
        shared = self.base / "shared-pylib"
        shared.mkdir()
        os.chmod(shared, 0o777)
        self.private_file(shared / "v1_pth_marker.py")
        private = self.private_directory("private-pylib")
        self.private_file(site / "probe.pth",
                          f"# a comment\n\n{shared}\r\n../private-pylib  \n import-like\nmissing-dir\n")
        boundary = self.judged_user_site(site)
        self.assertEqual(len(boundary.refusals), 1, boundary.refusals)
        self.assertIn(f"{shared} (a directory {site / 'probe.pth'} names): writable by every user",
                      boundary.refusals[0])
        prefix = f"a directory {site / 'probe.pth'} names "
        self.assertEqual([place[len(prefix):] for place in boundary.places if place.startswith(prefix)],
                         [str(shared), str(private), str(site / " import-like"), str(site / "missing-dir")])
        self.private_directory("user-site/ import-like")
        probe = subprocess.run(
            [sys.executable, "-I", "-c", "import json, site, sys; before = list(sys.path); "
             "site.addsitedir(sys.argv[1]); print(json.dumps([p for p in sys.path if p not in before]))", str(site)],
            capture_output=True, text=True, timeout=60, check=True)
        self.assertEqual(json.loads(probe.stdout), [str(site), str(shared), str(private), str(site / " import-like")])
        os.chmod(shared, 0o700)
        self.assertEqual(self.judged_user_site(site).refusals, [], "the private tree alone passes")

    def test_code_a_python3_run_without_isolation_executes_at_startup_refuses(self):
        """A .pth line python3 executes (`import ...`), and a sitecustomize or
        usercustomize module in the user site-packages or a directory a .pth
        file there names, run at every start of a python3 without -I; what
        they put on the import path can be judged only by running them, so
        each refuses (not as a path another user can write). A hidden .pth
        and a directory named *.pth, which python3 skips, are not read; a .pth
        that is not a regular file or holds a byte outside ASCII refuses."""
        named = self.private_directory("named")
        cases = (
            ("probe.pth", "import v1_pth_marker\n", "line 1 is code python3 executes"),
            ("tab.pth", f"{named}\nimport\tos\n", "line 2 is code python3 executes"),
            ("usercustomize.py", "", "is a usercustomize module"),
            ("sitecustomize.cpython-312.so", "", "is a sitecustomize module"),
            ("latin.pth", b"/caf\xe9\n", "holds a byte outside ASCII"),
        )
        for name, content, why in cases:
            with self.subTest(name=name):
                site = self.private_directory(f"site-{name}")
                path = self.private_file(site / name, content)
                boundary = self.judged_user_site(site)
                self.assertEqual(len(boundary.refusals), 1, boundary.refusals)
                self.assertIn(why, boundary.refusals[0])
                self.assertTrue(boundary.refusals[0].startswith(f"{path} ("), boundary.refusals[0])
                self.assertEqual(boundary.writable_refusals, 0, "not a writability refusal")
        with self.subTest(name="a startup module in a directory a .pth names"):
            site = self.private_directory("site-named")
            self.private_file(site / "named.pth", f"{named}\n")
            (named / "usercustomize").mkdir()
            os.chmod(named / "usercustomize", 0o700)
            boundary = self.judged_user_site(site)
            self.assertEqual(len(boundary.refusals), 1, boundary.refusals)
            self.assertIn(f"{named / 'usercustomize'} (a module python3 imports at startup): is a usercustomize "
                          "module", boundary.refusals[0])
        with self.subTest(name="skipped as python3 skips them"):
            site = self.private_directory("site-skipped")
            self.private_file(site / ".hidden.pth", "import v1_pth_marker\n")
            self.private_directory("site-skipped/directory.pth")
            self.private_file(site / "notes.txt", "import v1_pth_marker\n")
            self.assertEqual(self.judged_user_site(site).refusals, [])
        with self.subTest(name="a FIFO"):
            site = self.private_directory("site-fifo")
            os.mkfifo(site / "fifo.pth", 0o600)
            boundary = self.judged_user_site(site)
            self.assertEqual(len(boundary.refusals), 1, boundary.refusals)
            self.assertIn("is not a regular file", boundary.refusals[0])
        with self.subTest(name="no user site-packages"):
            self.assertEqual(self.judged_user_site(self.base / "no-such-site").refusals, [])

    # -- repair round 3 of OD-XHOST-GATE-CWD-20261025 ----------------------
    def test_a_pth_file_holding_another_line_separator_refuses(self):
        """(C) CPython 3.13's site.addpackage reads a .pth file's lines with
        str.splitlines (gh-117802); 3.12 and earlier read them with universal
        newlines (\\n, \\r, \\r\\n only), as this check did. For a .pth
        holding another character str.splitlines splits at, the lines judged
        were not the lines a 3.13 python3 acts on: `<dir>\\x0bimport m` is
        one path line to the check (and to 3.12) and a path line plus an
        `import` line to 3.13. Each such character now refuses the file by
        name (not as a writability refusal): the fail-closed form, since no
        python3 that reads it is then certain to read the lines judged,
        where judging both splittings would still depend on which python3
        runs. The refused set is exactly what str.splitlines splits at
        beyond \\n and \\r; the three outside ASCII refuse as a byte outside
        ASCII; a .pth broken at \\r\\n or a lone \\r is still read and
        judged."""
        derived = {chr(code) for code in range(sys.maxunicode + 1)
                   if len(f"a{chr(code)}b".splitlines()) == 2} - {"\n", "\r"}
        self.assertEqual(HB.PTH_OTHER_LINE_SEPARATORS, frozenset(derived))
        named = self.private_directory("separator-named")
        for character in sorted(character for character in HB.PTH_OTHER_LINE_SEPARATORS if ord(character) < 0x80):
            label = f"U+{ord(character):04X}"
            with self.subTest(separator=label):
                text = f"{named}{character}import v1_pth_marker\n"
                self.assertEqual(text.splitlines(), [str(named), "import v1_pth_marker"], "3.13 reads an import line")
                self.assertEqual(list(io.StringIO(text, newline=None)), [text], "3.12 reads one path line")
                site = self.private_directory(f"site-separator-{ord(character):x}")
                path = self.private_file(site / "probe.pth", text)
                boundary = self.judged_user_site(site)
                self.assertEqual(len(boundary.refusals), 1, boundary.refusals)
                self.assertTrue(boundary.refusals[0].startswith(f"{path} (a .pth file of python3's user "
                                                                "site-packages): "), boundary.refusals[0])
                self.assertIn(f"holds {label}, which python3 3.13 reads as a line break", boundary.refusals[0])
                self.assertEqual(boundary.writable_refusals, 0, "not a writability refusal")
        for character in sorted(character for character in HB.PTH_OTHER_LINE_SEPARATORS if ord(character) >= 0x80):
            with self.subTest(separator=f"U+{ord(character):04X}"):
                site = self.private_directory(f"site-separator-{ord(character):x}")
                self.private_file(site / "probe.pth", f"{named}{character}import v1_pth_marker\n".encode())
                boundary = self.judged_user_site(site)
                self.assertEqual(len(boundary.refusals), 1, boundary.refusals)
                self.assertIn("holds a byte outside ASCII", boundary.refusals[0])
        with self.subTest(name="CRLF and a lone CR"):
            other = self.private_directory("separator-other")
            site = self.private_directory("site-crlf")
            self.private_file(site / "probe.pth", f"{named}\r\n{other}\r")
            boundary = self.judged_user_site(site)
            self.assertEqual(boundary.refusals, [])
            prefix = f"a directory {site / 'probe.pth'} names "
            self.assertEqual([place[len(prefix):] for place in boundary.places if place.startswith(prefix)],
                             [str(named), str(other)])

    def test_the_pinned_interpreter_is_judged_as_exactly_the_file_running_the_check(self):
        """(A) soundness_check.sh pins ONE python3 by its canonical path
        before its prelude changes PATH, starts the check by it and names it
        with --python3. The check judges that file with every directory it is
        looked up in and refuses it unless it is the interpreter running the
        check, by canonical path and by device and inode: a path through a
        symlink, a byte copy of the interpreter (another inode), another
        executable, a relative or empty path and a missing file each refuse,
        as does the running interpreter reached through a directory every
        user can write; the running interpreter's canonical path passes and
        is listed as a judged place, on the command line too."""
        running = os.path.realpath(sys.executable)

        def judged(pinned: str) -> HB.Boundary:
            boundary = HB.Boundary(self.accounts())
            HB.judge_pinned_python3(boundary, pinned)
            return boundary

        passing = judged(running)
        self.assertEqual(passing.refusals, [])
        self.assertIn(f"the gate's pinned python3 (SOUNDNESS_PYTHON3) {running}", passing.places)
        link = self.base / "python3-link"
        link.symlink_to(running)
        copy = self.base / "python3-copy"
        shutil.copy2(running, copy)
        other = self.private_file(self.base / "other-python3", "#!/bin/sh\nexit 0\n")
        os.chmod(other, 0o700)
        shared = self.base / "shared-bin"
        shared.mkdir()
        os.chmod(shared, 0o777)
        shutil.copy2(other, shared / "python3")
        cases = (
            (str(link), f"is not a canonical path (it resolves to {running})"),
            (str(copy), "is not the interpreter running this check"),
            (str(other), "is not the interpreter running this check"),
            ("python3", "is not an absolute path"),
            ("", "is not an absolute path"),
            (str(self.base / "missing-python3"), "does not exist"),
        )
        for pinned, why in cases:
            with self.subTest(pinned=pinned):
                boundary = judged(pinned)
                self.assertEqual(len(boundary.refusals), 1, boundary.refusals)
                self.assertIn(f"(the gate's pinned python3 (SOUNDNESS_PYTHON3)): {why}", boundary.refusals[0])
        with self.subTest(pinned="in a directory every user can write"):
            # Every directory the pin is looked up in is judged: the shared
            # one refuses as such, besides the file not being the interpreter.
            boundary = judged(str(shared / "python3"))
            self.assertEqual(len(boundary.refusals), 2, boundary.refusals)
            self.assertTrue(boundary.refusals[0].startswith(f"{shared} (the gate's pinned python3 "
                                                            "(SOUNDNESS_PYTHON3)): writable by every user"),
                            boundary.refusals)
            self.assertIn("is not the interpreter running this check", boundary.refusals[1])
        candidate = self.private_directory("pin-candidate")
        result = self.cli(candidate, "--python3", running)
        self.assertIn(f"host_boundary: judged the gate's pinned python3 (SOUNDNESS_PYTHON3) {running}",
                      result.stdout)
        self.assertEqual([line for line in self.refused(result) if "pinned python3" in line], [])
        result = self.cli(candidate, "--python3", str(copy))
        self.assertTrue(any(line.startswith(f"{copy} (the gate's pinned python3 (SOUNDNESS_PYTHON3)): is not the "
                                            "interpreter running this check") for line in self.refused(result)),
                        result.stdout[-3000:])
        self.assertEqual(result.returncode, 1)

    # -- repair round 4 of OD-XHOST-GATE-CWD-20261025 ---------------------
    LEG_PLACE = "the python3 a leg starts by name (the first on the run's PATH)"

    def judged_leg(self, search_path: str) -> HB.Boundary:
        boundary = HB.Boundary(self.accounts())
        HB.judge_leg_python3(boundary, search_path, os.path.realpath(sys.executable))
        return boundary

    def test_the_python3_a_leg_starts_by_name_must_be_the_pinned_interpreter_with_its_import_path(self):
        """(A, round 4) The round-3 repair judged the pinned interpreter's
        import path and user site alone, while a leg starts python3 BY NAME
        on the prelude's PATH: a python3 in $HOME/.elan/bin (a wrapper running
        a virtual environment's interpreter, whose 0777 site-packages no rule
        judged) was the legs' and the run attested, where 8b127f2a4 refused.
        The first python3 on the legs' PATH must now be the pinned file
        (canonical path, device and inode), and python3 must read the same
        pyvenv.cfg for the name it is found by as for the pinned one: a
        wrapper script, a byte copy, a virtual environment's bin/python3
        (python3 -m venv: a symlink to the very pinned file), a symlink with
        a pyvenv.cfg beside it or above it, a missing python3, and a pyvenv.cfg
        another user could create (in a sticky directory every user can
        write) each refuse; a symlink to the pinned file in a private
        directory with no pyvenv.cfg around it passes and is
        listed as judged. None of them is run."""
        running = os.path.realpath(sys.executable)
        linked = self.private_directory("leg-linked")
        (linked / "python3").symlink_to(running)
        # A versioned interpreter need not have an identical "python3"
        # sibling; managed packages may install a distinct executable there.
        passing = self.judged_leg(str(linked))
        self.assertEqual(passing.refusals, [])
        self.assertIn(f"{self.LEG_PLACE} {linked / 'python3'}", passing.places)
        boundary = self.judged_leg(f"{linked}:{os.path.dirname(running)}")
        self.assertEqual(boundary.refusals, [])
        self.assertIn(f"{self.LEG_PLACE} {linked / 'python3'}", boundary.places)
        log = self.base / "leg-wrapper.log"
        wrapper = self.private_directory("leg-wrapper")
        (wrapper / "python3").write_text(f"#!/bin/sh\necho ran >> {log}\nexec {running} \"$@\"\n")
        os.chmod(wrapper / "python3", 0o700)
        copy = self.private_directory("leg-copy")
        shutil.copy2(running, copy / "python3")
        venv = self.base / "leg-venv"
        subprocess.run([running, "-I", "-m", "venv", "--without-pip", str(venv)], check=True, timeout=120,
                       capture_output=True)
        self.assertEqual(os.path.realpath(venv / "bin" / "python3"), running, "venv's python3 is the pinned file")
        os.chmod(venv / "lib", 0o777)
        beside = self.private_directory("leg-beside")
        (beside / "python3").symlink_to(running)
        self.private_file(beside / "pyvenv.cfg", f"home = {os.path.dirname(running)}\n")
        above = self.private_directory("leg-above")
        (above / "bin").mkdir(mode=0o700)
        (above / "bin" / "python3").symlink_to(running)
        self.private_file(above / "pyvenv.cfg", f"home = {os.path.dirname(running)}\n")
        sticky = self.base / "leg-sticky"
        sticky.mkdir()
        os.chmod(sticky, 0o1777)
        (sticky / "bin").mkdir(mode=0o700)
        (sticky / "bin" / "python3").symlink_to(running)
        empty = self.private_directory("leg-empty")
        cases = (
            ("wrapper", wrapper, f"{wrapper / 'python3'} ({self.LEG_PLACE}): is not the gate's pinned python3 "
             f"{running} (it resolves to {wrapper / 'python3'})"),
            ("copy", copy, f"{copy / 'python3'} ({self.LEG_PLACE}): is not the gate's pinned python3 {running}"),
            ("venv", venv / "bin", f"{venv / 'pyvenv.cfg'} ({self.LEG_PLACE}): is a virtual environment's "
             f"configuration python3 reads at startup, and a leg runs the pinned interpreter as "
             f"{venv / 'bin' / 'python3'} while the gate runs it as {running}"),
            ("beside", beside, f"{beside / 'pyvenv.cfg'} ({self.LEG_PLACE}): is a virtual environment's"),
            ("above", above / "bin", f"{above / 'pyvenv.cfg'} ({self.LEG_PLACE}): is a virtual environment's"),
            ("sticky", sticky / "bin", f"{sticky} ({HB.VENV_PLACE}): writable by every user (mode 1777) (a missing "
             "name could be created in it)"),
            ("missing", empty, f"python3 ({self.LEG_PLACE}): is not found on the run's PATH"),
        )
        for name, directory, refusal in cases:
            with self.subTest(case=name):
                search = str(directory) if name == "missing" else f"{directory}:{os.path.dirname(running)}"
                boundary = self.judged_leg(search)
                self.assertTrue(boundary.refusals, "refused")
                self.assertTrue(boundary.refusals[0].startswith(refusal), boundary.refusals)
        self.assertFalse(log.exists(), "the wrapper never ran")
        result = self.cli(self.private_directory("leg-candidate"), "--python3", running,
                          "--search-path", f"{venv / 'bin'}:{os.path.dirname(running)}")
        self.assertEqual(result.returncode, 1)
        self.assertIn(f"host_boundary: judged {self.LEG_PLACE} {venv / 'bin' / 'python3'}", result.stdout)
        self.assertTrue(any(line.startswith(f"{venv / 'pyvenv.cfg'} ({self.LEG_PLACE})")
                            for line in self.refused(result)), result.stdout[-3000:])

    @unittest.skipUnless(sys.platform.startswith("linux"), "/proc/self/exe is Linux's")
    def test_a_pinned_interpreter_that_names_another_program_than_the_one_running_refuses(self):
        """(A, round 4; the verifier's exec -a probe) sys.executable is what
        python3 derives from its argv[0], so a wrapper that runs another
        binary under its own name (`exec -a "$0" <copy> "$@"`) made the pin
        and the boundary's check name the wrapper while every gate python3
        ran a binary nobody judged, and 8d3e1a608 and 8b127f2a4 both attested.
        A pin that is a `#!` script now refuses, and so, on Linux, does one
        that is not the file /proc/self/exe names: here the check runs as
        this interpreter with argv[0] naming a wrapper script, then a byte
        copy (an ELF file of its own, another inode). The control: argv[0]
        naming the running file passes."""
        running = os.path.realpath(sys.executable)
        candidate = self.private_directory("argv0-candidate")
        bin_dir = self.private_directory("argv0-bin")
        (bin_dir / "python3").symlink_to(running)
        script = self.private_directory("argv0-script") / "python3"
        script.write_text(f"#!/bin/sh\nexec -a \"$0\" {running} \"$@\"\n")
        os.chmod(script, 0o700)
        copy = self.private_directory("argv0-copy") / "python3"
        shutil.copy2(running, copy)
        home, tmp = self.private_directory("argv0-home"), self.private_directory("argv0-tmp")

        def run(argv0: Path) -> subprocess.CompletedProcess:
            return subprocess.run([str(argv0), "-I", "-B", str(ROOT / "scripts" / "host_boundary.py"),
                                   "--search-path", str(bin_dir), "--candidate", str(candidate),
                                   "--python3", str(argv0)], executable=running, capture_output=True, text=True,
                                  env={"HOME": str(home), "TMPDIR": str(tmp), "PATH": "/usr/bin:/bin", "LANG": "C"},
                                  timeout=300)

        place = "the gate's pinned python3 (SOUNDNESS_PYTHON3)"
        for argv0, why in ((script, "is a script (it begins with #!)"),
                           (copy, f"is the name the interpreter running this check gives itself (its argv[0]), but "
                                  f"the kernel runs {running} (/proc/self/exe)")):
            with self.subTest(argv0=argv0.parent.name):
                result = run(argv0)
                self.assertEqual(result.returncode, 1, result.stdout[-3000:] + result.stderr[-2000:])
                self.assertTrue(any(line.startswith(f"{argv0} ({place}): {why}") for line in self.refused(result)),
                                result.stdout[-3000:] + result.stderr[-2000:])
        control = run(Path(running))
        self.assertEqual([line for line in self.refused(control) if "python3" in line], [],
                         control.stdout[-3000:] + control.stderr[-2000:])


class GateTests(unittest.TestCase):
    """The production gate in the fixture constellation."""

    def world(self, prefix: str, mask: int, shared: bool) -> tuple[fixture.Constellation, dict, Path]:
        directory = fixture.FixtureDirectory(prefix)
        self.addCleanup(directory.cleanup)
        previous = os.umask(mask)
        try:
            world = fixture.Constellation(Path(directory.name))
        finally:
            os.umask(previous)
        cache = Path(directory.name, "xdg-cache")
        cache.mkdir(mode=0o700)
        os.chmod(cache, 0o700)
        extra = {"SOUNDNESS_DEPS_DIR": None, "XDG_CACHE_HOME": str(cache)}
        if shared:
            group = self.account_file(Path(directory.name, "extra-group"), f"{GROUP}:x:{GID}:cogroup\n")
            passwd = self.account_file(Path(directory.name, "extra-passwd"),
                                       "cogroup:x:4242:4242::/nonexistent:/usr/sbin/nologin\n")
            extra.update(SOUNDNESS_EXTRA_GROUP_FILE=str(group), SOUNDNESS_EXTRA_PASSWD_FILE=str(passwd))
        return world, extra, Path(directory.name)

    @staticmethod
    def account_file(path: Path, text: str) -> Path:
        """An extra account file, 0644 (the check judges it too)."""
        path.write_text(text)
        os.chmod(path, 0o644)
        return path

    def substitute(self, world: fixture.Constellation, base: Path) -> Path:
        """The sixth closure audit's two substitutes, by rename into the
        directories a co-group writer could write: rustup in the fixture's
        PATH bin (~/.cargo/bin) and lake in ~/.elan/bin. Each logs that it
        ran."""
        log = base / "substitute.log"
        for directory, name in ((world.bin, "rustup"), (world.home / ".elan" / "bin", "lake")):
            os.chmod(directory, 0o775)
            staged = base / f"cogroup-{name}"
            staged.write_text(f"#!/bin/sh\necho \"substitute {name} ran: $*\" >> {log}\nexit 0\n")
            staged.chmod(0o755)
            os.rename(staged, directory / name)
        return log

    def test_a_shared_group_refuses_the_run_before_anything_runs(self):
        """Umask 0002 makes the fixture's tool directories, git
        configuration and checkout group-writable; with the group shared,
        the run records FAIL naming each place and the remedy and stops
        there, even with --keep-going: no fixture tool ran (neither the
        substitute rustup nor lake), and no attestation exists."""
        world, extra, base = self.world("host-boundary-shared-", 0o002, shared=True)
        log = self.substitute(world, base)
        result = world.run_gate("--attest", "--keep-going", umask=0o002, **extra)
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        self.assertRegex(result.stdout, r"\[FAIL\] preflight: host trust boundary\s+host_boundary: FAIL: ")
        self.assertIn(f"host_boundary: REFUSED {world.bin} (PATH entry", result.stdout)
        self.assertIn(f"by group {GROUP} (gid {GID}), which has another member: member cogroup", result.stdout)
        self.assertIn(f"host_boundary: REFUSED {world.home / '.elan'}", result.stdout)
        self.assertIn("`chmod go-w <path>`", result.stdout)
        self.assertIn("STOPPED at the first failure (preflight: host trust boundary): nothing else ran.",
                      result.stdout)
        self.assertIn("no attestation record", result.stdout)
        self.assertEqual(world.workloads(), [], "no fixture tool ran")
        self.assertFalse(log.exists(), "neither substitute ran")
        self.assertIsNone(fixture.logdir_of(result), "nothing ran after the check, mktemp included")
        self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")
        # A usage error is reported before the check (exit 2, nothing judged).
        usage = world.run_gate("--attest", "--list", umask=0o002, **extra)
        self.assertEqual(usage.returncode, 2, usage.stdout[-2000:] + usage.stderr[-2000:])
        self.assertIn("that mode cannot be combined with another mode", usage.stderr)
        self.assertNotIn("host_boundary", usage.stdout + usage.stderr)

    def test_an_account_whose_primary_group_it_is_refuses_the_run_too(self):
        world, extra, base = self.world("host-boundary-primary-", 0o002, shared=False)
        passwd = self.account_file(base / "extra-passwd", f"cogroup:x:4242:{GID}::/nonexistent:/usr/sbin/nologin\n")
        extra["SOUNDNESS_EXTRA_PASSWD_FILE"] = str(passwd)
        result = world.run_gate("--attest", "--preflight-only", umask=0o002, **extra)
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        self.assertIn("cogroup (uid 4242) has it as primary group", result.stdout)
        self.assertEqual(world.workloads(), [])

    @NEEDS_PRIVATE_GROUP
    def test_a_private_group_passes_and_records_the_check(self):
        """The same umask 0002 world with this host's group (no other
        member): the check passes, the run records its row, and the
        report is kept with the logs."""
        world, extra, _base = self.world("host-boundary-private-", 0o002, shared=False)
        result = world.run_gate("--attest", "--preflight-only", umask=0o002, **extra)
        self.assertEqual(result.returncode, 0, result.stdout[-3000:])
        self.assertRegex(result.stdout, r"\[PASS\] preflight: host trust boundary")
        logdir = fixture.logdir_of(result)
        report = (logdir / "host-boundary.log").read_text()
        self.assertIn(f"host_boundary: judged PATH {world.bin}", report)
        self.assertIn(f"host_boundary: judged ELAN_HOME {world.home / '.elan'}", report)
        self.assertIn(f"host_boundary: judged the candidate checkout {world.cg}", report)
        self.assertIn(f"host_boundary: judged git configuration {world.git_config}", report)
        self.assertIn(f"host_boundary: judged TMPDIR {world.tmp}", report)
        self.assertRegex(report.splitlines()[-1], r"^host_boundary: PASS: \d+ entries")

    def test_an_open_tmpdir_user_site_or_node_folder_refuses_the_run(self):
        """The places a leg reads or writes besides the tools: a TMPDIR
        others can write without the sticky bit, a python3 user
        site-packages (a python3 run without -I runs its .pth files) and
        node's global module folder, each with an entry every user can
        write. Umask 0022, so nothing else is open. The user site-packages
        is the one the check itself judges: that of the `python3 -I` the
        gate finds on the run's PATH, under the run's HOME
        (`~/.local/lib/pythonX.Y/site-packages` on Linux, a framework
        build's `~/Library/Python/X.Y/lib/python/site-packages` on macOS)."""
        for case in ("tmpdir", "user-site", "node"):
            with self.subTest(case=case):
                world, extra, _base = self.world(f"host-boundary-{case}-", 0o022, shared=False)
                if case == "tmpdir":
                    os.chmod(world.tmp, 0o777)
                    expected = f"host_boundary: REFUSED {world.tmp} (TMPDIR): writable by every user (mode 0777)"
                else:
                    if case == "user-site":
                        folder = Path(subprocess.run(
                            ["python3", "-I", "-c", "import site; print(site.getusersitepackages())"],
                            env=world.env(**extra), capture_output=True, text=True, check=True).stdout.strip())
                        self.assertTrue(str(folder).startswith(f"{world.home}{os.sep}"), folder)
                    else:
                        folder = world.home / ".node_modules"
                    folder.mkdir(parents=True)
                    planted = folder / ("startup.pth" if case == "user-site" else "index.js")
                    planted.write_text("")
                    os.chmod(planted, 0o666)
                    expected = f"host_boundary: REFUSED {planted} ("
                result = world.run_gate("--attest", "--preflight-only", umask=0o022, **extra)
                self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                self.assertIn(expected, result.stdout)
                self.assertEqual(world.workloads(), [])

    def test_nothing_group_writable_passes_even_with_a_shared_group(self):
        world, extra, _base = self.world("host-boundary-0022-", 0o022, shared=True)
        result = world.run_gate("--attest", "--preflight-only", umask=0o022, **extra)
        self.assertEqual(result.returncode, 0, result.stdout[-3000:])
        self.assertRegex(result.stdout, r"\[PASS\] preflight: host trust boundary")

    def test_a_global_git_config_filter_never_reaches_the_proof_export(self):
        """The sixth closure audit's git-configuration attack: a smudge
        filter and an attributes file in the global git configuration name
        a proof Clean rejects. `git archive` applied them, and the export
        held the substitute. The export is now read from the object store by
        hash: it holds the committed bytes, Clean rejects them, nothing is
        recorded. (Umask 0022: the configuration is not group-writable, so
        the boundary passes whatever this host's groups are.) The filter is a
        private wrapper named by its absolute path: the bare `sed
        s/fixture/SUBSTITUTED/` the audit used is now refused at the boundary
        itself (a slash in a word that is no path; repair round 2 of
        OD-XHOST-TRANSPORT-WORDS-20261024), and this case is about the export,
        which must hold the committed bytes even when a filter passes."""
        world, extra, base = self.world("host-boundary-gitconfig-", 0o022, shared=False)
        marker = base / "clean-read.log"
        block = ('if name == "clean" and args[:1] == ["check"] and Path(args[-1]).stem == "sentinel_decide_spec":\n'
                 '    _c = Path(args[-1]).read_text()\n'
                 f'    open({str(marker)!r}, "a").write(args[-1] + " " + repr(_c) + "\\n")\n'
                 '    if "SUBSTITUTED" not in _c:\n'
                 '        print("Checked 5 declarations\\n  4 passed, 1 failed"); sys.exit(1)\n'
                 '    print("Checked 5 declarations\\n  5 passed, 0 failed"); sys.exit(0)\n')
        tool = world.bin / "fake-tool"
        anchor = 'if name == "clean":'
        tool.write_text(tool.read_text().replace(anchor, block + anchor))
        attributes = base / "attacker-attributes"
        attributes.write_text("proofs/sentinel_decide_spec.lean filter=cogroup\n")
        wrapper_dir = base / "filter-bin"
        wrapper_dir.mkdir()
        os.chmod(wrapper_dir, 0o700)
        wrapper = wrapper_dir / "substitute"
        wrapper.write_text("#!/bin/sh\nexec sed s/fixture/SUBSTITUTED/\n")
        os.chmod(wrapper, 0o755)
        with open(world.git_config, "a") as config:
            config.write(f'[filter "cogroup"]\n\tsmudge = {wrapper}\n'
                         f'[core]\n\tattributesFile = {attributes}\n')
        archived = subprocess.run(["git", "-C", str(world.cg), "archive", "HEAD", "--",
                                   "proofs/sentinel_decide_spec.lean"], capture_output=True,
                                  env=dict(os.environ, GIT_CONFIG_GLOBAL=str(world.git_config)), check=True).stdout
        self.assertIn(b"SUBSTITUTED", archived, "the filter does act on `git archive`")
        result = world.run_gate("--attest", "--keep-going", umask=0o022, **extra)
        self.assertNotEqual(result.returncode, 0, result.stdout[-3000:])
        self.assertRegex(result.stdout, r"\[FAIL\] clean-check trust-cg proofs/sentinel_decide_spec[^\n]*4 passed, "
                                        r"1 failed")
        export = Path(os.path.realpath(fixture.logdir_of(result) / "candidate-proofs"))
        self.assertEqual(marker.read_text(),
                         f"{export / 'proofs' / 'sentinel_decide_spec.lean'} '-- fixture\\n'\n")
        self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")

    @NEEDS_PRIVATE_GROUP
    def test_everything_an_attested_run_starts_runs_under_umask_077(self):
        """The round-3 verifier's second finding: the trust-cg Cargo legs ran
        under the caller's umask 0002, so what they created was
        group-writable. Every fixture program an attested run starts now
        records umask 0077, and the run's logs are its owner's alone."""
        world, extra, base = self.world("host-boundary-umask-", 0o002, shared=False)
        umask_log = base / "umask.log"
        result = world.run_gate("--attest", "--keep-going", umask=0o002, FIXTURE_UMASK_LOG=str(umask_log), **extra)
        self.assertRegex(result.stdout, r"\[PASS\] preflight: host trust boundary")
        lines = umask_log.read_text().splitlines()
        self.assertTrue(any(line.startswith("targo 0077 --unverified test") for line in lines), lines)
        self.assertTrue(any(line.startswith("lake ") for line in lines), lines)
        self.assertEqual([line for line in lines if line.split()[1] != "0077"], [])
        logdir = fixture.logdir_of(result)
        self.assertIsNotNone(logdir)
        opened = [f"{path} {stat.S_IMODE(path.lstat().st_mode):04o}" for path in [logdir, *logdir.rglob("*")]
                  if not path.is_symlink() and stat.S_IMODE(path.lstat().st_mode) & 0o077]
        self.assertEqual(opened, [])

    def test_a_relative_location_refuses_the_run_before_anything_runs(self):
        """The round-4 verifier's test_v4_relative_roots: SOUNDNESS_DEPS_DIR
        `private` with the gate started from a sticky directory, and
        CARGO_HOME or CARGO_TARGET_DIR `../shared` naming a 0777 directory,
        passed the attested preflight where the absolute forms are refused
        (the pinned checkouts were made below the sticky directory). Each is
        now refused at the boundary by name, before anything runs."""
        for variable, value in (("SOUNDNESS_DEPS_DIR", "private"), ("CARGO_HOME", "../shared"),
                                ("CARGO_TARGET_DIR", "../shared")):
            with self.subTest(variable=variable):
                world, extra, base = self.world(f"host-boundary-relative-{variable}-", 0o022, shared=False)
                sticky = base / "sticky"
                sticky.mkdir()
                os.chmod(sticky, 0o1777)
                (sticky / "private").mkdir(mode=0o700)
                os.chmod(sticky / "private", 0o700)
                shared = base / "shared"
                shared.mkdir()
                os.chmod(shared, 0o777)
                extra[variable] = value
                start = sticky if variable == "SOUNDNESS_DEPS_DIR" else world.cg
                result = world.run_gate("--attest", "--preflight-only", umask=0o022, cwd=start, **extra)
                self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                self.assertIn(f"host_boundary: REFUSED ${variable} (the environment): is {value!r}, not an absolute "
                              "path", result.stdout)
                self.assertRegex(result.stdout, r"\[FAIL\] preflight: host trust boundary\s+host_boundary: FAIL: ")
                self.assertEqual(world.workloads(), [])
                self.assertEqual(sorted((sticky / "private").iterdir()), [], "no checkout below the sticky directory")

    def test_a_fetch_transport_program_others_can_write_refuses_the_run(self):
        """Judge fetch transport settings before native transport can refuse
        an arbitrary SSH-style origin. Shared and relative commands must fail
        at the host boundary; a private command passes that boundary but must
        never execute as a fallback for an unsupported location. Rejected runs
        must not write attestation refs."""
        for form in ("absolute", "relative", "private"):
            with self.subTest(form=form):
                world, extra, base = self.world(f"host-boundary-transport-{form}-", 0o022, shared=False)
                marker = base / "fetch-ssh-ran.log"
                directory = base / ("private-bin" if form == "private" else "shared")
                directory.mkdir()
                os.chmod(directory, 0o700 if form == "private" else 0o777)
                program = directory / "fetch-ssh"
                program.write_text(f"#!/bin/sh\necho \"fetch-ssh ran: $*\" >> {marker}\nexit 1\n")
                os.chmod(program, 0o755)
                env = dict(os.environ, GIT_CONFIG_GLOBAL=str(world.git_config), GIT_CONFIG_NOSYSTEM="1")
                fixture.git(world.clean, "remote", "add", "origin", "fixture-remote:clean.git", env=env)
                world.clean_rev = "ab" * 20
                for lock in (world.cg / "Cargo.lock", world.cg / "crates" / "rustc-codegen-trust-cg" / "Cargo.lock"):
                    lock.write_text(world.lock())
                (world.cg / "fuzz" / "Cargo.lock").write_text(world.lock(with_ay=False))
                world.commit_all("pin a Clean revision the source lacks")
                command = str(program)
                expected = (f"host_boundary: REFUSED {os.path.realpath(directory)} (GIT_SSH_COMMAND in the "
                            "environment): writable by every user (mode 0777)")
                if form == "relative":
                    tools = world.clean / "tools"
                    tools.mkdir()
                    os.chmod(tools, 0o777)
                    os.rename(program, tools / "fetch-ssh")
                    command = "tools/fetch-ssh"
                    expected = ("host_boundary: REFUSED $GIT_SSH_COMMAND (GIT_SSH_COMMAND in the environment): names "
                                "the program 'tools/fetch-ssh' by a relative path, which git runs from its working "
                                "directory")
                extra.update(GIT_SSH_COMMAND=command, SOUNDNESS_X86_HOST=None)
                result = world.run_gate("--attest", "--scope", "portable", "--preflight-only", umask=0o022, **extra)
                if form == "private":
                    self.assertRegex(result.stdout, r"\[PASS\] preflight: host trust boundary")
                    self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                    self.assertIn("remote must be canonical GitHub or a local repository path", result.stdout + result.stderr)
                    self.assertFalse(marker.exists(), "native transport must not fall back to arbitrary SSH")
                    self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")
                    continue
                self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                self.assertIn(expected, result.stdout)
                self.assertRegex(result.stdout, r"\[FAIL\] preflight: host trust boundary\s+host_boundary: FAIL: ")
                self.assertFalse(marker.exists(), "the program never ran")
                self.assertEqual(world.workloads(), [])
                self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")

    def test_a_cache_below_a_directory_others_can_create_entries_in_refuses_the_run(self):
        """A user cache (and so SOUNDNESS_DEPS_DIR, where the Clean and AY
        checkouts are built), or an explicit SOUNDNESS_DEPS_DIR, below a
        sticky directory: the run is refused at the boundary, before
        anything runs."""
        for case in ("XDG_CACHE_HOME", "SOUNDNESS_DEPS_DIR"):
            with self.subTest(case=case):
                world, extra, base = self.world(f"host-boundary-sticky-{case}-", 0o022, shared=False)
                sticky = base / "sticky"
                sticky.mkdir()
                os.chmod(sticky, 0o1777)
                below = sticky / "private"
                below.mkdir(mode=0o700)
                os.chmod(below, 0o700)
                extra[case] = str(below)
                result = world.run_gate("--attest", "--preflight-only", umask=0o022, **extra)
                self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                place = ("the user cache's trust-cg directory" if case == "XDG_CACHE_HOME"
                         else "a directory the gate runs Cargo in")
                self.assertIn(f"host_boundary: REFUSED {sticky} (Cargo's configuration search above {place}): "
                              "writable by every user (mode 1777)", result.stdout)
                self.assertRegex(result.stdout, r"\[FAIL\] preflight: host trust boundary\s+host_boundary: FAIL: ")
                self.assertEqual(world.workloads(), [])



    def test_round5_fail_opens_refuse_before_the_program_runs(self):
        """The X-HOST-P13 round-5 verifier's three fail-opens, each end to end
        in the fixture: a full portable-scope attested run (no x86-64
        executor) whose candidate pins a Clean revision only an ssh-style
        origin has, so the preflight's `git fetch origin` would run the
        transport in the Clean source work tree. Each is refused at the host
        trust boundary, the run stops there, no fixture program runs and no
        attestation ref is written (OD-XHOST-TRANSPORT-WORDS-20261024):
        (1) GIT_SSH_COMMAND through the checker's own /proc/self/cwd;
        (2) the `=` later word `sh tools/evil=1`;
        (3) the bare words `sh evil-ssh` (a 0777 script at the Clean work-tree
        root) and `env PATH=tools evil-ssh` (a 0777 tools/ there): refused
        twice over, by the transport rule (any later word) and by the work
        tree being judged as a whole tree. The command-key form of (3) is
        test_a_command_key_word_that_leaves_the_judged_directory_refuses_the_run."""
        for cls in ("proc", "equals-word", "bare-word", "bare-word-path"):
            with self.subTest(cls=cls):
                world, extra, base = self.world(f"host-boundary-r5-{cls}-", 0o022, shared=False)
                env = dict(os.environ, GIT_CONFIG_GLOBAL=str(world.git_config), GIT_CONFIG_NOSYSTEM="1")
                fixture.git(world.clean, "remote", "add", "origin", "fixture-remote:clean.git", env=env)
                world.clean_rev = "cd" * 20
                for lock in (world.cg / "Cargo.lock", world.cg / "crates" / "rustc-codegen-trust-cg" / "Cargo.lock"):
                    lock.write_text(world.lock())
                (world.cg / "fuzz" / "Cargo.lock").write_text(world.lock(with_ay=False))
                world.commit_all("pin a Clean revision the source lacks")
                extra["SOUNDNESS_X86_HOST"] = None
                transport = "$GIT_SSH_COMMAND (GIT_SSH_COMMAND in the environment): runs the shell command"
                if cls == "proc":
                    extra["GIT_SSH_COMMAND"] = "/proc/self/cwd/tools/evil-ssh"
                    expected = ["/proc (GIT_SSH_COMMAND in the environment): resolves into /proc"]
                elif cls == "equals-word":
                    extra["GIT_SSH_COMMAND"] = "sh tools/evil=1"
                    expected = [transport + " 'sh tools/evil=1', whose later word 'tools/evil=1'"]
                elif cls == "bare-word":
                    evil = world.clean / "evil-ssh"
                    evil.write_text("#!/bin/sh\nexit 0\n")
                    os.chmod(evil, 0o777)
                    extra["GIT_SSH_COMMAND"] = "sh evil-ssh"
                    expected = [f"{evil} (the source work tree {world.clean}): writable by every user (mode 0777)",
                                transport + " 'sh evil-ssh', whose later word 'evil-ssh'"]
                else:
                    tools = world.clean / "tools"
                    tools.mkdir()
                    os.chmod(tools, 0o777)
                    (tools / "evil-ssh").write_text("#!/bin/sh\nexit 0\n")
                    os.chmod(tools / "evil-ssh", 0o755)
                    extra["GIT_SSH_COMMAND"] = "env PATH=tools evil-ssh"
                    expected = [f"{tools} (the source work tree {world.clean}): writable by every user (mode 0777)",
                                transport + " 'env PATH=tools evil-ssh', whose later word 'PATH=tools'"]
                result = world.run_gate("--attest", "--scope", "portable", umask=0o022, **extra)
                self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                for line in expected:
                    self.assertIn(f"host_boundary: REFUSED {line}", result.stdout)
                self.assertRegex(result.stdout, r"\[FAIL\] preflight: host trust boundary\s+host_boundary: FAIL: ")
                self.assertIn("STOPPED at the first failure (preflight: host trust boundary)", result.stdout)
                self.assertEqual(world.workloads(), [], "no program ran after the refusal")
                self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")

    def test_a_program_key_a_git_helper_reaches_refuses_the_run(self):
        """R1 of OD-XHOST-GIT-PROGRAM-KEYS-20261024, end to end: Clean's
        configuration reaches a program-valued key the old check never listed.
        `remote.origin.uploadpack = git web--browse -b x` ran browser.x.cmd,
        and diff.external and the difftool/mergetool .cmd keys are the same
        shape. Each full portable-scope attested run now refuses at the host
        trust boundary: a configured upload-pack refuses outright, and a key
        off the allowlist (browser.x.cmd, diff.external) refuses by name; the
        planted program never runs and no attestation ref is written. The
        private control (the same world without the planted keys) passes the
        boundary and its preflight fetches the pinned revision from the local
        origin, so the refused runs did reach that fetch."""
        for form in ("web-browse", "diff-external", "difftool", "control"):
            with self.subTest(form=form):
                world, extra, base = self.world(f"host-boundary-r1-{form}-", 0o022, shared=False)
                env = self.pin_a_revision_only_a_local_origin_has(world, base)
                if form == "control":
                    self.assert_the_private_control_fetches(world, extra, env)
                    continue
                marker = base / "helper-ran.log"
                shared = base / "shared777"
                shared.mkdir()
                os.chmod(shared, 0o777)
                planted = shared / "evil"
                planted.write_text(f"#!/bin/sh\necho \"helper ran: $(pwd) $*\" >> {marker}\nexit 0\n")
                os.chmod(planted, 0o755)
                base_place = f"(git configuration of {world.clean}:"
                if form == "web-browse":
                    fixture.git(world.clean, "config", "remote.origin.uploadpack", "git web--browse -b x", env=env)
                    fixture.git(world.clean, "config", "browser.x.cmd", str(planted), env=env)
                    expected = f"{world.clean} browser.x.cmd {base_place} browser.x.cmd): is a key of the " \
                               "repository's own (local) configuration that is not on the allowlist"
                elif form == "diff-external":
                    fixture.git(world.clean, "config", "diff.external", str(planted), env=env)
                    expected = f"{world.clean} diff.external {base_place} diff.external): is a key of the " \
                               "repository's own (local) configuration that is not on the allowlist"
                else:
                    fixture.git(world.clean, "config", "difftool.x.cmd", str(planted), env=env)
                    fixture.git(world.clean, "config", "mergetool.x.cmd", str(planted), env=env)
                    expected = f"{world.clean} difftool.x.cmd {base_place} difftool.x.cmd): is a key of the " \
                               "repository's own (local) configuration that is not on the allowlist"
                extra["SOUNDNESS_X86_HOST"] = None
                result = world.run_gate("--attest", "--scope", "portable", umask=0o022, **extra)
                self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                self.assertIn(f"host_boundary: REFUSED {expected}", result.stdout)
                self.assertRegex(result.stdout, r"\[FAIL\] preflight: host trust boundary\s+host_boundary: FAIL: ")
                self.assertIn("STOPPED at the first failure (preflight: host trust boundary)", result.stdout)
                self.assertFalse(marker.exists(), marker.read_text() if marker.exists() else "the program never ran")
                self.assertEqual(world.workloads(), [])
                self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")

    def test_a_nested_submodule_program_key_refuses_the_run(self):
        """Repair round 2 of OD-XHOST-GIT-PROGRAM-KEYS-20261024, end to end:
        the second verifier's e2e_submodule.py. The candidate holds a
        populated submodule vendor/sub whose git directory is EMBEDDED (a
        plain clone into the path) or a `gitdir:` file naming a directory
        elsewhere, with core.fsmonitor naming a logging program in a 0777
        directory. At 0baa9650f the boundary passed (it judged only
        <git-dir>/modules), the gate's `git status --porcelain` of the
        candidate ran the program in vendor/sub, and an attestation was
        written. Now every repository nested in the candidate's work tree is
        judged: each full portable-scope attested run refuses at the host
        trust boundary naming the key and the 0777 directory, the program
        never runs and no attestation ref exists. The private control (the
        same embedded submodule with data keys only) passes the boundary and
        its preflight, so git status did enter the submodule."""
        for form in ("embedded", "gitfile-elsewhere", "control"):
            with self.subTest(form=form):
                world, extra, base = self.world(f"host-boundary-nested-{form}-", 0o022, shared=False)
                env = dict(os.environ, GIT_CONFIG_GLOBAL=str(world.git_config), GIT_CONFIG_NOSYSTEM="1")
                upstream = base / "sub-upstream"
                upstream.mkdir(mode=0o700)
                fixture.git(upstream, "init", "-q", "-b", "main", env=env)
                (upstream / "lib.rs").write_text("pub fn f() {}\n")
                fixture.git(upstream, "add", "-A", env=env)
                fixture.git(upstream, "commit", "-qm", "sub", env=env)
                sub = world.cg / "vendor" / "sub"
                sub.parent.mkdir(parents=True, exist_ok=True)
                subprocess.run(["git", "clone", "-q", str(upstream), str(sub)], check=True, env=env,
                               capture_output=True)
                (world.cg / ".gitmodules").write_text('[submodule "vendor/sub"]\n\tpath = vendor/sub\n'
                                                      '\turl = https://example.invalid/sub.git\n')
                git_dir = sub / ".git"
                if form == "gitfile-elsewhere":
                    git_dir = base / "elsewhere-gitdir"
                    os.rename(sub / ".git", git_dir)
                    (sub / ".git").write_text(f"gitdir: {git_dir}\n")
                world.commit_all("a populated submodule")
                fixture.git(world.cg, "config", "submodule.recurse", "true", env=env)
                marker = base / "fsmonitor-ran.log"
                shared = base / "shared777"
                shared.mkdir()
                os.chmod(shared, 0o777)
                planted = shared / "evil"
                planted.write_text(f"#!/bin/sh\necho \"fsmonitor ran in $(pwd)\" >> {marker}\nexit 0\n")
                os.chmod(planted, 0o755)
                if form != "control":
                    fixture.git(sub, "--git-dir", str(git_dir), "config", "core.fsmonitor", str(planted), env=env)
                extra["SOUNDNESS_X86_HOST"] = None
                if form == "control":
                    result = world.run_gate("--attest", "--scope", "portable", "--preflight-only", umask=0o022,
                                            **extra)
                    self.assertEqual(result.returncode, 0, result.stdout[-3000:])
                    self.assertRegex(result.stdout, r"\[PASS\] preflight: host trust boundary")
                    self.assertRegex(result.stdout, r"\[PASS\] attest: trust-cg worktree clean")
                    report = (fixture.logdir_of(result) / "host-boundary.log").read_text()
                    self.assertIn(f"host_boundary: judged the repository {sub} nested in {world.cg}", report)
                    continue
                result = world.run_gate("--attest", "--scope", "portable", umask=0o022, **extra)
                self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                self.assertIn(f"host_boundary: REFUSED {sub} core.fsmonitor (git configuration of {sub}: "
                              "core.fsmonitor): is a key of the repository's own (local) configuration that is not "
                              "on the allowlist", result.stdout)
                self.assertIn(f"host_boundary: REFUSED {shared} (git configuration of {sub}: core.fsmonitor): "
                              "writable by every user (mode 0777)", result.stdout)
                self.assertRegex(result.stdout, r"\[FAIL\] preflight: host trust boundary\s+host_boundary: FAIL: ")
                self.assertIn("STOPPED at the first failure (preflight: host trust boundary)", result.stdout)
                self.assertFalse(marker.exists(), marker.read_text() if marker.exists() else "the program never ran")
                self.assertEqual(world.workloads(), [])
                self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")

    @staticmethod
    def submodule_that_is_a_local_remote(world: fixture.Constellation, base: Path, form: str) -> tuple[Path, Path,
                                                                                                     Path]:
        """The round-2 regression verifier's shape: the candidate holds the
        populated submodule vendor/sub (an embedded clone) whose own index
        holds the gitlink `inner`, and the candidate's remote.mirror.url names
        vendor/sub, so the boundary judges that repository first as a local
        remote. With form "worktree-777", vendor/sub's core.worktree names
        base/shared777 (mode 0777), which holds a copy of the submodule's
        files, a clone of `inner` whose core.fsmonitor names
        base/shared777/prog, and that logging program: `git status` of the
        candidate runs `git status` in vendor/sub, whose work tree is then
        base/shared777, and from there in base/shared777/inner, which runs
        the program (measured with git 2.43). With form "control", vendor/sub
        keeps its own path as its work tree and `inner` is populated there with
        data keys only. Returns (vendor/sub, base/shared777, the program's
        log)."""
        env = dict(os.environ, GIT_CONFIG_GLOBAL=str(world.git_config), GIT_CONFIG_NOSYSTEM="1")
        inner_upstream = base / "inner-upstream"
        inner_upstream.mkdir(mode=0o700)
        fixture.git(inner_upstream, "init", "-q", "-b", "main", env=env)
        (inner_upstream / "inner.rs").write_text("pub fn g() {}\n")
        fixture.git(inner_upstream, "add", "-A", env=env)
        fixture.git(inner_upstream, "commit", "-qm", "inner", env=env)
        inner_head = fixture.git(inner_upstream, "rev-parse", "HEAD", env=env)
        upstream = base / "sub-upstream"
        upstream.mkdir(mode=0o700)
        fixture.git(upstream, "init", "-q", "-b", "main", env=env)
        (upstream / "lib.rs").write_text("pub fn f() {}\n")
        (upstream / ".gitmodules").write_text('[submodule "inner"]\n\tpath = inner\n'
                                              '\turl = https://example.invalid/inner.git\n')
        fixture.git(upstream, "update-index", "--add", "--cacheinfo", f"160000,{inner_head},inner", env=env)
        # Not `add -A`: it would stage the unpopulated gitlink's removal.
        fixture.git(upstream, "add", "lib.rs", ".gitmodules", env=env)
        fixture.git(upstream, "commit", "-qm", "sub", env=env)
        sub = world.cg / "vendor" / "sub"
        sub.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "clone", "-q", str(upstream), str(sub)], check=True, env=env, capture_output=True)
        (world.cg / ".gitmodules").write_text('[submodule "vendor/sub"]\n\tpath = vendor/sub\n'
                                              '\turl = https://example.invalid/sub.git\n')
        fixture.git(world.cg, "remote", "add", "mirror", str(sub), env=env)
        marker = base / "fsmonitor-ran.log"
        shared = base / "shared777"
        shared.mkdir()
        os.chmod(shared, 0o777)
        if form == "control":
            subprocess.run(["git", "clone", "-q", str(inner_upstream), str(sub / "inner")], check=True, env=env,
                           capture_output=True)
        else:
            for name in ("lib.rs", ".gitmodules"):
                shutil.copyfile(sub / name, shared / name)
            subprocess.run(["git", "clone", "-q", str(inner_upstream), str(shared / "inner")], check=True, env=env,
                           capture_output=True)
            planted = shared / "prog"
            planted.write_text(f"#!/bin/sh\necho \"fsmonitor ran in $(pwd)\" >> {marker}\nexit 1\n")
            os.chmod(planted, 0o755)
            fixture.git(shared / "inner", "config", "core.fsmonitor", str(planted), env=env)
        world.commit_all("a populated submodule the candidate also names as a local remote")
        if form != "control":
            fixture.git(sub, "config", "core.worktree", str(shared), env=env)
        return sub, shared, marker

    def test_a_submodule_that_is_also_a_local_remote_is_judged_as_one(self):
        """Repair round 3 of OD-XHOST-GIT-PROGRAM-KEYS-20261024, end to end
        (the round-2 regression verifier's blocking finding at 850f69fd0): the
        candidate's remote.mirror.url names its own populated submodule
        vendor/sub, whose core.worktree names a 0777 directory holding a
        nested repository whose core.fsmonitor names a logging program there
        (submodule_that_is_a_local_remote). The local remote's judgement
        recorded the submodule's identity and the nested judgement returned
        early on it, so git's view of the submodule's work tree was never
        asked: the boundary passed and the gate's `git status --porcelain`
        ran the program (this test's form, run against 850f69fd0's
        host_boundary.py: PASS at the boundary, the log written). Now a full
        portable-scope attested run refuses at the host trust boundary naming
        the submodule and the work tree git would use, the program never runs
        and no attestation ref exists. The private control (the same
        submodule and remote, no core.worktree, `inner` populated in place
        with data keys only) passes the boundary and its preflight, and its
        report records the submodule's nested judgement after its local-remote
        one."""
        for form in ("worktree-777", "control"):
            with self.subTest(form=form):
                world, extra, base = self.world(f"host-boundary-mirror-{form}-", 0o022, shared=False)
                sub, shared, marker = self.submodule_that_is_a_local_remote(world, base, form)
                extra["SOUNDNESS_X86_HOST"] = None
                if form == "control":
                    result = world.run_gate("--attest", "--scope", "portable", "--preflight-only", umask=0o022,
                                            **extra)
                    self.assertEqual(result.returncode, 0, result.stdout[-3000:])
                    self.assertRegex(result.stdout, r"\[PASS\] preflight: host trust boundary")
                    self.assertRegex(result.stdout, r"\[PASS\] attest: trust-cg worktree clean")
                    report = (fixture.logdir_of(result) / "host-boundary.log").read_text()
                    local = f"host_boundary: judged the local repository {world.cg} remote.mirror.url names {sub}"
                    nested = f"host_boundary: judged the repository {sub} nested in {world.cg}"
                    self.assertIn(local, report)
                    self.assertIn(nested, report)
                    self.assertLess(report.index(local), report.index(nested))
                    self.assertIn(f"host_boundary: judged the repository {sub / 'inner'} nested in {sub}", report)
                    continue
                result = world.run_gate("--attest", "--scope", "portable", umask=0o022, **extra)
                self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                self.assertIn(f"host_boundary: REFUSED {sub} (the repository {sub} nested in {world.cg}): git's work "
                              f"tree for it is {shared} (a core.worktree, or {sub} being a subdirectory of that "
                              "repository's work tree)", result.stdout)
                self.assertRegex(result.stdout, r"\[FAIL\] preflight: host trust boundary\s+host_boundary: FAIL: ")
                self.assertIn("STOPPED at the first failure (preflight: host trust boundary)", result.stdout)
                fail = [line for line in result.stdout.splitlines() if "host_boundary: FAIL: " in line]
                self.assertTrue(fail and all("chmod go-w" not in line for line in fail), fail)
                self.assertFalse(marker.exists(), marker.read_text() if marker.exists() else "the program never ran")
                self.assertEqual(world.workloads(), [])
                self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")

    def assert_the_private_control_fetches(self, world: fixture.Constellation, extra: dict, env: dict) -> None:
        """The control of an end-to-end refusal whose world pins a revision
        only Clean's local origin has (pin_a_revision_only_a_local_origin_has):
        with no planted key, the attested preflight passes the host trust
        boundary and pins the Clean checkout, which needed `git fetch origin`,
        so a refused run with a planted key did reach that fetch."""
        extra["SOUNDNESS_X86_HOST"] = None
        result = world.run_gate("--attest", "--scope", "portable", "--preflight-only", umask=0o022, **extra)
        self.assertEqual(result.returncode, 0, result.stdout[-3000:])
        self.assertRegex(result.stdout, r"\[PASS\] preflight: host trust boundary")
        self.assertRegex(result.stdout, r"\[PASS\] preflight: clean checkout\s+pinned worktree")
        self.assertEqual(fixture.git(world.clean, "cat-file", "-t", world.clean_rev, env=env), "commit",
                         "the fetch from the local origin ran")
        # The run's own git configuration file and its directory are removed
        # when the run exits.
        report = (fixture.logdir_of(result) / "host-boundary.log").read_text()
        written = [line for line in report.splitlines() if line.startswith("host_boundary: gate git configuration /")]
        self.assertEqual(len(written), 1, report[-2000:])
        self.assertTrue(written[0].endswith("/config") and str(world.tmp) in written[0], written)
        self.assertEqual(sorted(world.tmp.glob("soundness-git.*")), [], "the run removed its git configuration")

    def test_a_fetch_from_an_origin_the_configuration_does_not_define_refuses(self):
        """Repair round 2: the preflight fetches `origin` by name. When the
        Clean source's configuration defines no remote.origin.url, git reads a
        legacy remotes/ file or uses the name as a path in its working
        directory, here a clone at <clean>/origin holding the pinned revision,
        which 0baa9650f's gate fetched from. The pinned checkout is now
        refused before any fetch, naming the missing remote.origin.url; the
        boundary itself passes (the nested clone holds data keys only)."""
        world, extra, base = self.world("host-boundary-undefined-origin-", 0o022, shared=False)
        env = dict(os.environ, GIT_CONFIG_GLOBAL=str(world.git_config), GIT_CONFIG_NOSYSTEM="1")
        nested = world.clean / "origin"
        subprocess.run(["git", "clone", "-q", str(world.clean), str(nested)], check=True, env=env,
                       capture_output=True)
        (nested / "NEXT").write_text("only the nested origin has this\n")
        fixture.git(nested, "add", "-A", env=env)
        fixture.git(nested, "commit", "-qm", "nested origin only", env=env)
        world.clean_rev = fixture.git(nested, "rev-parse", "HEAD", env=env)
        for lock in (world.cg / "Cargo.lock", world.cg / "crates" / "rustc-codegen-trust-cg" / "Cargo.lock"):
            lock.write_text(world.lock())
        (world.cg / "fuzz" / "Cargo.lock").write_text(world.lock(with_ay=False))
        world.commit_all("pin a Clean revision only <clean>/origin has")
        extra["SOUNDNESS_X86_HOST"] = None
        result = world.run_gate("--attest", "--scope", "portable", "--preflight-only", umask=0o022, **extra)
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        self.assertRegex(result.stdout, r"\[PASS\] preflight: host trust boundary")
        self.assertRegex(result.stdout, r"\[FAIL\] preflight: clean checkout\s+refusing the candidate's clean "
                                        r"checkout .*whose own configuration defines no remote\.origin\.url")
        with self.assertRaises(subprocess.CalledProcessError):
            fixture.git(world.clean, "cat-file", "-e", world.clean_rev, env=env)
        self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")

    def test_a_local_path_remote_upload_pack_refuses_the_run(self):
        """R2 of OD-XHOST-GIT-PROGRAM-KEYS-20261024, end to end: git passes a
        local-path remote's path to a configured upload-pack command as its
        last argument, so with `remote.origin.uploadpack = sh` and a
        remote.origin.url naming a script, the preflight's `git fetch origin`
        runs that script (measured with git 2.43: `sh <url>`; the round-2
        verifier found the earlier form of this test vacuous, its origin being
        a directory `sh` cannot run). The upload-pack key refuses outright at
        the host trust boundary in a full portable-scope attested run, and the
        url refuses as naming no repository; the script never runs and no
        attestation ref is written. The private control (a local origin that
        is a repository, no upload-pack key) passes and fetches."""
        for form in ("script-origin", "control"):
            with self.subTest(form=form):
                world, extra, base = self.world(f"host-boundary-r2-{form}-", 0o022, shared=False)
                env = self.pin_a_revision_only_a_local_origin_has(world, base)
                if form == "control":
                    self.assert_the_private_control_fetches(world, extra, env)
                    continue
                marker = base / "uploadpack-sh-ran.log"
                payload = base / "payload.sh"
                payload.write_text(f"#!/bin/sh\necho \"payload ran: $*\" >> {marker}\n")
                os.chmod(payload, 0o755)
                fixture.git(world.clean, "remote", "set-url", "origin", str(payload), env=env)
                fixture.git(world.clean, "config", "remote.origin.uploadpack", "sh", env=env)
                extra["SOUNDNESS_X86_HOST"] = None
                result = world.run_gate("--attest", "--scope", "portable", umask=0o022, **extra)
                self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                self.assertIn(f"host_boundary: REFUSED {world.clean} remote.origin.uploadpack (git configuration of "
                              f"{world.clean}: remote.origin.uploadpack): names the program git runs for a fetch or "
                              "push", result.stdout)
                self.assertIn(f"host_boundary: REFUSED {world.clean} remote.origin.url (git configuration of "
                              f"{world.clean}: remote.origin.url): names {str(payload)!r}, which is not a directory "
                              "holding a git repository", result.stdout)
                self.assertRegex(result.stdout, r"\[FAIL\] preflight: host trust boundary\s+host_boundary: FAIL: ")
                self.assertFalse(marker.exists(), marker.read_text() if marker.exists()
                                 else "the upload-pack sh never ran the script")
                self.assertEqual(world.workloads(), [])
                self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")

    def test_a_fake_git_first_on_path_never_runs_before_the_boundary(self):
        """R3 of OD-XHOST-GIT-PROGRAM-KEYS-20261024, end to end: a logging git
        first on PATH, in a 0777 directory. Before the fix,
        soundness_attestation.py's exec-scrubbed re-exec ran `git rev-parse
        --local-env-vars` with the caller's PATH before anything was judged,
        so that git ran. Now isolate_git_environment runs no program; the host
        trust boundary then refuses the 0777 PATH directory, and the planted
        git never ran. A full portable-scope attested run refuses, the fake
        git's log is empty, and no attestation ref is written. The control: the
        same logging git in a 0700 directory passes the boundary, and git then
        runs (its log is written), after the boundary, not before it."""
        git_binary = shutil.which("git")
        for private in (False, True):
            with self.subTest(private=private):
                world, extra, base = self.world(f"host-boundary-r3-{'priv' if private else 'open'}-", 0o022,
                                                shared=False)
                marker = base / "fake-git-ran.log"
                evildir = base / ("private-git" if private else "open-git")
                evildir.mkdir()
                os.chmod(evildir, 0o700 if private else 0o777)
                fake = evildir / "git"
                fake.write_text(
                    f"#!/bin/sh\necho \"fake git ran: $*\" >> {shlex.quote(str(marker))}\n"
                    f"exec {shlex.quote(git_binary)} \"$@\"\n"
                )
                os.chmod(fake, 0o755)
                extra["SOUNDNESS_X86_HOST"] = None
                extra["PATH"] = f"{evildir}:{world.base_env()['PATH']}"
                result = world.run_gate("--attest", "--scope", "portable", "--preflight-only", umask=0o022, **extra)
                if private:
                    self.assertRegex(result.stdout, r"\[PASS\] preflight: host trust boundary", result.stdout[-3000:])
                    # The boundary ran git (through the fake) only after it had
                    # judged PATH: the fake did run, which proves it is first.
                    self.assertTrue(marker.exists(), "the control's git did run, after the boundary")
                else:
                    self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                    self.assertIn(f"host_boundary: REFUSED {evildir} (PATH entry", result.stdout)
                    self.assertIn("writable by every user (mode 0777)", result.stdout)
                    self.assertRegex(result.stdout,
                                     r"\[FAIL\] preflight: host trust boundary\s+host_boundary: FAIL: ")
                    self.assertFalse(marker.exists(), marker.read_text() if marker.exists()
                                     else "the fake git never ran before the boundary refused")
                    self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")

    def pin_a_revision_only_a_local_origin_has(self, world: fixture.Constellation, base: Path) -> dict:
        """Clean's origin becomes a private local clone holding one more
        commit, and the candidate pins that commit, so the preflight's
        `git -C <clean> fetch --quiet origin` runs, and git runs
        remote.origin.uploadpack through /bin/sh from the Clean work tree (the
        setup of the round-2 verifier's test_v_r5_e2e.py). Returns the git
        environment used."""
        env = dict(os.environ, GIT_CONFIG_GLOBAL=str(world.git_config), GIT_CONFIG_NOSYSTEM="1")
        origin = base / "clean-origin"
        subprocess.run(["git", "clone", "-q", str(world.clean), str(origin)], check=True, env=env,
                       capture_output=True)
        os.chmod(origin, 0o700)
        (origin / "NEXT").write_text("only the origin has this\n")
        fixture.git(origin, "add", "-A", env=env)
        fixture.git(origin, "commit", "-qm", "origin only", env=env)
        world.clean_rev = fixture.git(origin, "rev-parse", "HEAD", env=env)
        fixture.git(world.clean, "remote", "add", "origin", str(origin), env=env)
        for lock in (world.cg / "Cargo.lock", world.cg / "crates" / "rustc-codegen-trust-cg" / "Cargo.lock"):
            lock.write_text(world.lock())
        (world.cg / "fuzz" / "Cargo.lock").write_text(world.lock(with_ay=False))
        world.commit_all("pin a Clean revision only the origin has")
        return env

    def test_a_command_key_word_that_leaves_the_judged_directory_refuses_the_run(self):
        """Repair round 2 of OD-XHOST-TRANSPORT-WORDS-20261024, end to end: the
        two verifiers' reproducers at 9352c20f1, each of which passed the host
        trust boundary, ran a 0777 program from the Clean source's
        remote.origin.uploadpack during the preflight's fetch, and reached an
        attestation. Each full `--attest --scope portable` run (no x86-64
        executor) now refuses at `preflight: host trust boundary`; the planted
        program never runs and no attestation ref exists. Forms: finding (3)'s
        bare word with the program in the Clean work tree (`sh evil-up`,
        refused by the work-tree rule), `sh ../evil-up`, `env -C .. sh
        evil-up`, an option's attached absolute path (`env -S<0777>/evil-up`),
        a first-word assignment (`PATH=.. evil-up`, `PATH=~ evil-up`), and an
        absolute directory word whose tree holds the 0777 program (`env -C
        <dir> sh evil-up`). The control, a private program named alone by its
        absolute path, passes the boundary and is run by the fetch, so the
        refused runs did reach the configured command."""
        git_binary = shutil.which("git")
        forms = ("bare-worktree", "parent-relative", "env-C-parent", "env-S-attached", "assign-parent",
                 "assign-home", "directory-word", "private")
        for form in forms:
            with self.subTest(form=form):
                world, extra, base = self.world(f"host-boundary-r5w-{form}-", 0o022, shared=False)
                env = self.pin_a_revision_only_a_local_origin_has(world, base)
                marker = base / "uploadpack-ran.log"
                script = (f"#!/bin/sh\necho \"uploadpack ran: $(pwd)\" >> {marker}\n"
                          f"exec {git_binary} upload-pack \"$@\"\n")

                def plant(directory: Path, bits: int = 0o777) -> Path:
                    path = directory / "evil-up"
                    path.write_text(script)
                    os.chmod(path, bits)
                    return path

                prefix = f"{world.clean} remote.origin.uploadpack (git configuration of {world.clean}: " \
                         "remote.origin.uploadpack): runs the shell command "
                if form == "bare-worktree":
                    planted = plant(world.clean)
                    value = "sh evil-up"
                    expected = f"{planted} (the source work tree {world.clean}): writable by every user (mode 0777)"
                elif form == "parent-relative":
                    plant(base)
                    value = "sh ../evil-up"
                    expected = prefix + "'sh ../evil-up', whose later word '../evil-up' holds `..`"
                elif form == "env-C-parent":
                    plant(base)
                    value = "env -C .. sh evil-up"
                    expected = prefix + "'env -C .. sh evil-up', whose later word '..' holds `..`"
                elif form == "env-S-attached":
                    shared = base / "shared777"
                    shared.mkdir()
                    os.chmod(shared, 0o777)
                    planted = plant(shared)
                    value = f"env -S{planted}"
                    expected = prefix + f"{value!r}, whose later word '-S{planted}' holds a `/` or `~`"
                elif form == "assign-parent":
                    plant(base)
                    value = "PATH=.. evil-up"
                    expected = prefix + "'PATH=.. evil-up', which begins with the assignment 'PATH=..'"
                elif form == "assign-home":
                    plant(world.home)
                    value = "PATH=~ evil-up"
                    expected = prefix + "'PATH=~ evil-up', which begins with the assignment 'PATH=~'"
                elif form == "directory-word":
                    holder = base / "holder"
                    holder.mkdir()
                    os.chmod(holder, 0o700)
                    planted = plant(holder)
                    value = f"env -C {holder} sh evil-up"
                    expected = (f"{planted} (git configuration of {world.clean}: remote.origin.uploadpack): "
                                "writable by every user (mode 0777)")
                else:
                    # The former control: a private program named alone. Since
                    # OD-XHOST-GIT-PROGRAM-KEYS-20261024 a configured
                    # upload-pack refuses outright, so the control refuses too
                    # (it passed the boundary and ran during the fetch before).
                    private = base / "private-bin"
                    private.mkdir()
                    os.chmod(private, 0o700)
                    value = str(plant(private, 0o755))
                    expected = (f"{world.clean} remote.origin.uploadpack (git configuration of {world.clean}: "
                                "remote.origin.uploadpack): names the program git runs for a fetch or push")
                fixture.git(world.clean, "config", "remote.origin.uploadpack", value, env=env)
                extra["SOUNDNESS_X86_HOST"] = None
                result = world.run_gate("--attest", "--scope", "portable", umask=0o022, **extra)
                self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                self.assertIn(f"host_boundary: REFUSED {expected}", result.stdout)
                self.assertRegex(result.stdout, r"\[FAIL\] preflight: host trust boundary\s+host_boundary: FAIL: ")
                self.assertIn("STOPPED at the first failure (preflight: host trust boundary)", result.stdout)
                self.assertFalse(marker.exists(), "the planted program never ran")
                self.assertEqual(world.workloads(), [])
                self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")

    def test_a_source_git_uses_from_elsewhere_refuses_the_run(self):
        """Repair round 3 of OD-XHOST-TRANSPORT-WORDS-20261024, end to end: the
        round-3 verifier's e2e_probe.py A, A2 and B2, each of which passed the
        host trust boundary at f7919800a (and at 4a0668957), ran a 0777 program
        from the Clean source's remote.origin.uploadpack during the
        preflight's `git fetch origin` and reached an attestation. Forms:
        core.worktree naming the fixture root, an ancestor of the Clean source,
        with uploadpack `sh evil-up` (a 0777 evil-up at that root) and `env -C
        tools sh evil-up` (a 0777 tools/ there); and CLEAN_SOURCE_DIR set to
        Clean's proofs/ subdirectory, with uploadpack an absolute program in a
        0777 directory (Clean's configuration was never listed) and `sh
        evil-up` (a 0777 evil-up at Clean's top level). Each full `--attest
        --scope portable` run (no x86-64 executor) now refuses at `preflight:
        host trust boundary` naming the source: the planted program never
        runs and no attestation ref exists."""
        git_binary = shutil.which("git")
        for form in ("worktree-ancestor-bare", "worktree-ancestor-env-C", "subdirectory-absolute",
                     "subdirectory-bare"):
            with self.subTest(form=form):
                world, extra, base = self.world(f"host-boundary-r5l-{form}-", 0o022, shared=False)
                env = self.pin_a_revision_only_a_local_origin_has(world, base)
                marker = base / "uploadpack-ran.log"
                script = (f"#!/bin/sh\necho \"uploadpack ran: $(pwd)\" >> {marker}\n"
                          f"exec {git_binary} upload-pack \"$@\"\n")
                source = world.clean
                if form == "worktree-ancestor-bare":
                    (base / "evil-up").write_text(script)
                    os.chmod(base / "evil-up", 0o777)
                    fixture.git(world.clean, "config", "core.worktree", str(base), env=env)
                    value = "sh evil-up"
                    why = f"git's work tree for it is {base} (a core.worktree"
                elif form == "worktree-ancestor-env-C":
                    tools = base / "tools"
                    tools.mkdir()
                    os.chmod(tools, 0o777)
                    (tools / "evil-up").write_text(script)
                    os.chmod(tools / "evil-up", 0o755)
                    fixture.git(world.clean, "config", "core.worktree", str(base), env=env)
                    value = "env -C tools sh evil-up"
                    why = f"git's work tree for it is {base} (a core.worktree"
                elif form == "subdirectory-absolute":
                    shared = base / "shared777"
                    shared.mkdir()
                    os.chmod(shared, 0o777)
                    (shared / "evil-up").write_text(script)
                    os.chmod(shared / "evil-up", 0o755)
                    source = world.clean / "proofs"
                    value = str(shared / "evil-up")
                    why = "holds no git repository of its own (no .git)"
                else:
                    (world.clean / "evil-up").write_text(script)
                    os.chmod(world.clean / "evil-up", 0o777)
                    with open(world.clean / ".git" / "info" / "exclude", "a") as handle:
                        handle.write("/evil-up\n")
                    source = world.clean / "proofs"
                    value = "sh evil-up"
                    why = "holds no git repository of its own (no .git)"
                fixture.git(world.clean, "config", "remote.origin.uploadpack", value, env=env)
                extra.update(SOUNDNESS_X86_HOST=None, CLEAN_SOURCE_DIR=str(source))
                result = world.run_gate("--attest", "--scope", "portable", umask=0o022, **extra)
                self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                self.assertIn(f"host_boundary: REFUSED {source} (the git repository {source}): {why}", result.stdout)
                self.assertRegex(result.stdout, r"\[FAIL\] preflight: host trust boundary\s+host_boundary: FAIL: ")
                self.assertIn("STOPPED at the first failure (preflight: host trust boundary)", result.stdout)
                self.assertFalse(marker.exists(), "the planted program never ran")
                self.assertEqual(world.workloads(), [])
                self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")

    def test_an_alias_a_command_key_runs_refuses_the_run(self):
        """Repair round 4 of OD-XHOST-TRANSPORT-WORDS-20261024, end to end: the
        round-3 verifier's B1 and B2 against a6cbba41b. Clean's
        remote.origin.uploadpack is `git x` (a PATH program and a plain word,
        which pass), so the preflight's `git fetch origin` runs alias x from
        the Clean work tree. Forms of alias x, each naming a program in a 0777
        directory: B1's `!` alias with a later word (`!sh <dir>/evil-up`), a
        non-`!` alias whose option word names the program (`fetch
        --upload-pack=<dir>/evil-up`), a non-`!` alias that runs it through a
        git option (`-c uploadpack.packObjectsHook=<dir>/evil-hook
        upload-pack`), and B2's `!! <dir>/evil-up` (git strips one `!` and the
        shell runs `! <dir>/evil-up`). Each full `--attest --scope portable`
        run (no x86-64 executor) now refuses at `preflight: host trust
        boundary` naming the alias: the planted program never runs and no
        attestation ref exists. The control, `!<private program>`, passes the
        boundary and the fetch runs it through `git x`, so the refused runs
        did reach the alias."""
        git_binary = shutil.which("git")
        for form in ("bang-later-word", "option-word", "git-option", "double-bang", "private"):
            with self.subTest(form=form):
                world, extra, base = self.world(f"host-boundary-r5a-{form}-", 0o022, shared=False)
                env = self.pin_a_revision_only_a_local_origin_has(world, base)
                marker = base / "alias-ran.log"
                shared = base / "shared777"
                shared.mkdir()
                os.chmod(shared, 0o777)
                planted = shared / "evil-up"
                planted.write_text(f"#!/bin/sh\necho \"alias program ran: $(pwd)\" >> {marker}\n"
                                   f"exec {git_binary} upload-pack \"$@\"\n")
                os.chmod(planted, 0o755)
                hook = shared / "evil-hook"
                hook.write_text(f"#!/bin/sh\necho \"alias hook ran: $(pwd)\" >> {marker}\nexec \"$@\"\n")
                os.chmod(hook, 0o755)
                label = f"{world.clean} alias.x (git configuration of {world.clean}: alias.x): "
                writable = f"{shared} (git configuration of {world.clean}: alias.x): writable by every user (mode 0777)"
                if form == "bang-later-word":
                    value = f"!sh {planted}"
                    expected = writable
                elif form == "option-word":
                    value = f"fetch --upload-pack={planted}"
                    expected = writable
                elif form == "git-option":
                    value = f"-c uploadpack.packObjectsHook={hook} upload-pack"
                    expected = label + f"is the git argument list {value!r}, whose first word '-c' is a git option"
                elif form == "double-bang":
                    value = f"!! {planted}"
                    expected = label + (f"runs the shell command '! {planted}': its first word '!' is a word the "
                                        "shell reads as reserved where a command begins")
                else:
                    # The former control (a private `!` alias), which passed
                    # and ran through `git x`: since
                    # OD-XHOST-GIT-PROGRAM-KEYS-20261024 both keys refuse in a
                    # repository's own configuration (the upload-pack outright,
                    # the alias as a key off the allowlist).
                    private = base / "private-bin"
                    private.mkdir()
                    os.chmod(private, 0o700)
                    moved = private / "evil-up"
                    os.rename(planted, moved)
                    value = f"!{moved}"
                    expected = label + "is a key of the repository's own (local) configuration that is not on the"
                fixture.git(world.clean, "config", "remote.origin.uploadpack", "git x", env=env)
                fixture.git(world.clean, "config", "alias.x", value, env=env)
                extra["SOUNDNESS_X86_HOST"] = None
                result = world.run_gate("--attest", "--scope", "portable", umask=0o022, **extra)
                self.assertEqual(result.returncode, 1, result.stdout[-3000:])
                self.assertIn(f"host_boundary: REFUSED {expected}", result.stdout)
                self.assertRegex(result.stdout, r"\[FAIL\] preflight: host trust boundary\s+host_boundary: FAIL: ")
                self.assertIn("STOPPED at the first failure (preflight: host trust boundary)", result.stdout)
                self.assertFalse(marker.exists(), marker.read_text() if marker.exists() else "")
                self.assertEqual(world.workloads(), [])
                self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")

    def test_a_pinned_checkout_git_uses_from_elsewhere_refuses_before_status(self):
        """Repair round 3, the same class one step later: a pinned Clean
        checkout the gate reuses (its .git exists) whose per-worktree
        config.worktree (extensions.worktreeConfig) names the fixture root as
        core.worktree. The host trust boundary judges the Clean source, whose
        own work tree and configuration are unaffected, and passes; then the
        preflight's `git -C <checkout> status` would chdir to the root and run
        core.fsmonitor (`/bin/sh evil`, a 0777 evil there) from it.
        pin_dependency_checkout now asks git for the checkout's work-tree top
        and common git directory before that status and refuses the checkout
        unless they are the checkout and the source's: the preflight fails,
        the planted program never runs and no attestation ref exists."""
        world, extra, base = self.world("host-boundary-r5p-", 0o022, shared=False)
        env = dict(os.environ, GIT_CONFIG_GLOBAL=str(world.git_config), GIT_CONFIG_NOSYSTEM="1")
        marker = base / "fsmonitor-ran.log"
        (base / "evil").write_text(f"#!/bin/sh\necho \"fsmonitor ran: $(pwd)\" >> {marker}\nexit 1\n")
        os.chmod(base / "evil", 0o777)
        deps = base / "xdg-cache" / "trust-cg" / "soundness-deps"
        deps.mkdir(parents=True)
        for directory in (deps.parent, deps):
            os.chmod(directory, 0o700)
        checkout = deps / f"clean-{world.clean_rev}"
        previous = os.umask(0o077)
        try:
            fixture.git(world.clean, "worktree", "add", "--quiet", "--detach", str(checkout), world.clean_rev,
                        env=env)
        finally:
            os.umask(previous)
        fixture.git(world.clean, "config", "extensions.worktreeConfig", "true", env=env)
        fixture.git(checkout, "config", "--worktree", "core.worktree", str(base), env=env)
        # In the checkout's own config.worktree, which the host trust boundary
        # (judging the Clean source) does not read: in the source's config the
        # key now refuses at the boundary (OD-XHOST-GIT-PROGRAM-KEYS-20261024).
        fixture.git(checkout, "config", "--worktree", "core.fsmonitor", "/bin/sh evil", env=env)
        extra["SOUNDNESS_X86_HOST"] = None
        result = world.run_gate("--attest", "--scope", "portable", umask=0o022, **extra)
        self.assertEqual(result.returncode, 1, result.stdout[-3000:])
        self.assertRegex(result.stdout, r"\[PASS\] preflight: host trust boundary")
        self.assertRegex(result.stdout, r"\[FAIL\] preflight: clean checkout\s+refusing the candidate's clean "
                         r"checkout under .*: git uses the work tree " + re.escape(str(base)) + " and the git "
                         "directory " + re.escape(str(world.clean / ".git")) + " for the checkout ")
        self.assertFalse(marker.exists(), marker.read_text() if marker.exists() else "")
        self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")

    @staticmethod
    def legs_of(result: subprocess.CompletedProcess) -> list[tuple[str, str]]:
        """The (row, status) pairs of a run's legs.tsv, in the order recorded."""
        logdir = fixture.logdir_of(result)
        assert logdir is not None, result.stdout[-2000:]
        return [tuple(line.split("\t")[:2]) for line in (logdir / "legs.tsv").read_text().splitlines()]

    def test_nothing_an_attested_run_starts_runs_in_the_callers_working_directory(self):
        """OD-XHOST-GATE-CWD-20261025: the sixth closure audit's F1 and F3 end
        to end. A full portable attested run started in a 0777 directory
        holding 0666 marker modules json.py, hashlib.py and datetime.py (and a
        lean-toolchain naming another Lean) passed the boundary, imported the
        markers through the gate's own `python3 -c` (leg inventory, host
        identity) and `python3 -` (aterm json), ran the identities step's
        `lake --version` in that directory and wrote refs/attest. Now the run
        works in / until the boundary has passed and in the judged candidate
        from then on, and every inline python3 runs with -I: no marker is
        imported, no fixture program starts in the caller's directory (the
        identities step's lake runs in the candidate), the run still ends
        green and writes its record, and it records the same rows with the
        same statuses as the control started in the candidate, as the landing
        train starts it. The markers' positive control: a `python3 -c` started
        there imports all three, and the import still works."""
        world, extra, base = self.world("host-boundary-cwd-", 0o022, shared=False)
        extra["SOUNDNESS_X86_HOST"] = None
        caller = base / "caller-cwd"
        caller.mkdir()
        os.chmod(caller, 0o777)
        marker = base / "planted-modules.log"
        fixture.plant_marker_modules(caller, marker)
        (caller / "lean-toolchain").write_text("leanprover/lean4:v4.8.0\n")
        probe = subprocess.run(["python3", "-c", "import json, hashlib, datetime; print(json.dumps(1))"],
                               cwd=caller, capture_output=True, text=True, timeout=60)
        self.assertEqual((probe.returncode, probe.stdout), (0, "1\n"), probe.stderr)
        self.assertEqual(len(marker.read_text().splitlines()), 3, "the markers' positive control imports all three")
        marker.unlink()
        cwd_log = base / "cwd.log"
        result = world.run_gate("--attest", "--scope", "portable", umask=0o022, cwd=caller,
                                FIXTURE_CWD_LOG=str(cwd_log), **extra)
        self.assertEqual(result.returncode, 0, result.stdout[-3000:] + result.stderr[-2000:])
        self.assertRegex(result.stdout, r"\[PASS\] preflight: host trust boundary")
        self.assertFalse(marker.exists(), marker.read_text() if marker.exists() else "no marker module was imported")
        ran = [line.split("\t") for line in cwd_log.read_text().splitlines()]
        self.assertTrue(ran, "the fixture programs recorded where they ran")
        in_caller = [entry for entry in ran
                     if entry[1] == str(caller) or entry[1].startswith(str(caller) + os.sep)]
        self.assertEqual(in_caller, [], "no program the run started ran in the caller's working directory")
        self.assertIn(["lake", str(world.cg), "--version"], ran, "the identities step's lake runs in the candidate")
        refs = fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/")
        self.assertRegex(refs, r"^refs/attest/soundness/[0-9a-f]{40}/", "the run wrote its record")
        legs = self.legs_of(result)
        self.assertTrue(legs and all(status == "PASS" for _row, status in legs), legs)
        control = world.run_gate("--attest", "--scope", "portable", umask=0o022, **extra)
        self.assertEqual(control.returncode, 0, control.stdout[-3000:] + control.stderr[-2000:])
        self.assertEqual(self.legs_of(control), legs, "the same rows and statuses as a run started in the candidate")
        summary = [line for line in result.stdout.splitlines() if line.startswith("gates:")]
        self.assertEqual(summary, [line for line in control.stdout.splitlines() if line.startswith("gates:")])

    # -- repair round 2 of OD-XHOST-GATE-CWD-20261025 ---------------------
    PLANTED_TOOL = '''# benign marker (X-HOST-P13 sixth audit, repair round 2 of OD-XHOST-GATE-CWD-20261025)
import sys
with open({log!r}, "a") as handle:
    handle.write("planted soundness_attestation.py ran: argv=%r\\n" % (sys.argv[1:3],))
sys.exit(3)
'''

    @staticmethod
    def gate_environment(world: fixture.Constellation, **extra) -> dict:
        """The environment run_gate gives the gate (no steering variable)."""
        return {key: value for key, value in world.env(**extra).items()
                if not (key.startswith(("FIXTURE_", "SOUNDNESS_FIXTURE_")) or key == "FAKE_X86_GATE")}

    def test_an_attested_run_finds_its_own_directory_without_the_callers_cdpath(self):
        """The repair round 2 verifier's probe_cdpath.py: started as
        `bash scripts/soundness_check.sh --attest` (SOUNDNESS_CHECK.md's
        relative form) with an exported CDPATH naming a 0777 directory D that
        holds a `scripts`, the gate's `cd` of its own directory found
        D/scripts first (and printed it, so the value was two lines), and the
        pre-boundary scrub ran a 0666 soundness_attestation.py planted at that
        path; the scrubbed run never saw CDPATH. Now `CDPATH= cd` finds the
        candidate's own scripts directory and checks it holds the file bash
        runs: the planted tool never runs, the boundary passes, and the
        caller's CDPATH reaches the scrub, whose refusal fails the run at
        `preflight: leg-weakening settings` with no record. The positive
        control: a plain `cd scripts` there with that CDPATH lands in D; the
        relative invocation without CDPATH attests as before."""
        world, extra, base = self.world("host-boundary-cdpath-", 0o022, shared=False)
        extra["SOUNDNESS_X86_HOST"] = None
        planted_dir = base / "cdpath-dir"
        (planted_dir / "scripts").mkdir(parents=True)
        for directory in (planted_dir, planted_dir / "scripts"):
            os.chmod(directory, 0o777)
        log = base / "planted.log"
        # The directory the gate computed: `<D>/scripts` printed by the CDPATH
        # lookup, then by pwd, on two lines.
        computed = Path(f"{planted_dir}/scripts\n{planted_dir}/scripts")
        computed.mkdir(parents=True)
        planted = computed / "soundness_attestation.py"
        planted.write_text(self.PLANTED_TOOL.format(log=str(log)))
        os.chmod(planted, 0o666)
        control = subprocess.run(["bash", "-c", "cd scripts && pwd"], cwd=world.cg, capture_output=True, text=True,
                                 env={"CDPATH": str(planted_dir), "PATH": world.env()["PATH"]}, timeout=60)
        self.assertEqual(control.stdout, f"{planted_dir}/scripts\n{planted_dir}/scripts\n",
                         "a plain cd with that CDPATH lands in the planted directory")
        result = world.run_gate("--attest", "--scope", "portable", umask=0o022, script="scripts/soundness_check.sh",
                                CDPATH=str(planted_dir), **extra)
        self.assertFalse(log.exists(), log.read_text() if log.exists() else "")
        self.assertEqual(result.returncode, 1, result.stdout[-3000:] + result.stderr[-2000:])
        self.assertRegex(result.stdout, r"\[PASS\] preflight: host trust boundary")
        self.assertRegex(result.stdout, r"\[FAIL\] preflight: leg-weakening settings .*CDPATH")
        self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")
        relative = world.run_gate("--attest", "--scope", "portable", umask=0o022, script="scripts/soundness_check.sh",
                                  **extra)
        self.assertEqual(relative.returncode, 0, relative.stdout[-3000:] + relative.stderr[-2000:])
        self.assertRegex(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"),
                         r"^refs/attest/soundness/[0-9a-f]{40}/")
        self.assertFalse(log.exists())

    def test_an_attested_run_refuses_a_script_directory_that_is_not_the_one_bash_runs(self):
        """The script directory an --attest run computes must hold the very
        file bash runs (`-ef`). Started as `bash ../trust-cg/scripts/
        soundness_check.sh` from a symlinked working directory whose LOGICAL
        parent holds another trust-cg/scripts, bash reads the fixture's
        script (the kernel resolves `..` physically) while a logical `cd ..`
        names the other directory, whose soundness_attestation.py the scrub
        then ran before any check. It now refuses before any program
        starts, naming the remedy. The control shows the divergence."""
        world, extra, base = self.world("host-boundary-self-", 0o022, shared=False)
        physical = world.cg.parent / "physical-cwd"
        physical.mkdir()
        other = base / "logical-parent"
        other.mkdir()
        link = other / "link"
        link.symlink_to(physical)
        planted = other / world.cg.name / "scripts"
        planted.mkdir(parents=True)
        log = base / "planted.log"
        (planted / "soundness_check.sh").write_text("exit 0\n")
        (planted / "soundness_attestation.py").write_text(self.PLANTED_TOOL.format(log=str(log)))
        script = f"../{world.cg.name}/scripts/soundness_check.sh"
        env = self.gate_environment(world, SOUNDNESS_X86_HOST=None, **extra)
        control = subprocess.run(["bash", "-c", 'cd "$1" && export PWD && exec bash -c "cd ${2%/*} && pwd"', "probe",
                                  str(link), script], env=env, capture_output=True, text=True, timeout=60)
        self.assertEqual(control.stdout.strip(), str(planted), control.stderr)
        self.assertTrue(os.path.samefile(physical / script, world.cg / "scripts" / "soundness_check.sh"))
        result = subprocess.run(["bash", "-c", 'cd "$1" && export PWD && exec bash "$2" --attest --scope portable',
                                 "probe", str(link), script], env=env, capture_output=True, text=True, timeout=600)
        self.assertFalse(log.exists(), log.read_text() if log.exists() else "")
        self.assertEqual(result.returncode, 1, result.stdout[-3000:] + result.stderr[-2000:])
        self.assertIn("cannot name the directory of the script it runs", result.stdout)
        self.assertIn("no attestation record", result.stdout)
        self.assertNotIn("host_boundary:", result.stdout)

    def test_a_relative_or_empty_path_entry_refuses_before_the_scrub_starts_python3(self):
        """A relative PATH entry found the scrub's python3 relative to the
        working directory before the boundary could refuse it (605107820: the
        caller's; the round-1 repair: /). It is now refused first, with bash
        builtins, as the boundary refuses it: no python3 the entry names
        starts (a marker python3 there would log), nothing runs and no record
        is written. An empty entry (a trailing colon) refuses the same way."""
        world, extra, base = self.world("host-boundary-relpath-", 0o022, shared=False)
        caller = base / "caller"
        (caller / "rel-bin").mkdir(parents=True)
        log = base / "relative-python3.log"
        marker = caller / "rel-bin" / "python3"
        marker.write_text(f"#!/bin/sh\necho \"relative python3 ran: $*\" >> {log}\nexit 3\n")
        os.chmod(marker, 0o755)
        path = world.env()["PATH"]
        for value, entry in ((f"rel-bin:{path}", "rel-bin"), (f"{path}:", "")):
            with self.subTest(entry=entry):
                result = world.run_gate("--attest", "--scope", "portable", umask=0o022, cwd=caller, PATH=value,
                                        SOUNDNESS_X86_HOST=None, **extra)
                self.assertEqual(result.returncode, 1, result.stdout[-3000:] + result.stderr[-2000:])
                self.assertIn(f"PATH entry '{entry}' is relative or empty", result.stdout)
                self.assertIn("no attestation record", result.stdout)
                self.assertNotIn("host_boundary:", result.stdout, "refused before the boundary ran")
                self.assertFalse(log.exists(), log.read_text() if log.exists() else "")
                self.assertEqual(world.workloads(), [])

    def user_site(self, world: fixture.Constellation) -> Path:
        """python3's user site-packages under the fixture's HOME, by the
        python3 the fixture's PATH finds (the gate's), created 0755."""
        env = {"HOME": str(world.home), "PATH": world.env()["PATH"]}
        out = subprocess.run(["python3", "-I", "-c", "import site; print(site.getusersitepackages())"], env=env,
                             capture_output=True, text=True, timeout=60, check=True).stdout.strip()
        site = Path(out)
        self.assertTrue(site.is_relative_to(world.home), site)
        for directory in reversed((site, *site.parents)):
            if directory.is_relative_to(world.home) and directory != world.home and not directory.exists():
                directory.mkdir()
                os.chmod(directory, 0o755)
        return site

    MARKER = '''# benign marker module (X-HOST-P13 sixth audit, repair round 2 of OD-XHOST-GATE-CWD-20261025)
import os as _os, sys as _sys
with open({log!r}, "a") as _handle:
    _handle.write("%s\\t%s\\n" % (_sys.argv[0] if _sys.argv else "", _os.getpid()))
'''

    def test_a_user_site_pth_file_that_names_a_shared_directory_or_runs_code_refuses_the_run(self):
        """The repair round 2 verifier's probe_pth.py: the fixture HOME's user
        site-packages (0755) held probe.pth naming a 0777 shared-pylib with a
        0666 marker module, plus `import v1_pth_marker`. The boundary passed,
        the run attested 134/134 and the marker was imported 528 times
        (run_with_timeout.py, trust_toolchain.py and the fixture's python
        fakes, all python3 runs without -I); with the path line alone it
        attested too, shared-pylib on every such sys.path. Now the boundary
        judges each directory a .pth path line names and refuses a .pth line
        python3 executes: both runs stop at the boundary, nothing else runs,
        no marker is imported, no record. A .pth naming a private directory
        passes and attests (the control)."""
        world, extra, base = self.world("host-boundary-pth-", 0o022, shared=False)
        extra["SOUNDNESS_X86_HOST"] = None
        site = self.user_site(world)
        shared = base / "shared-pylib"
        shared.mkdir()
        os.chmod(shared, 0o777)
        log = base / "pth-marker.log"
        (shared / "v1_pth_marker.py").write_text(self.MARKER.format(log=str(log)))
        os.chmod(shared / "v1_pth_marker.py", 0o666)
        probe = site / "probe.pth"
        cases = (
            ("named", f"{shared}\n",
             f"host_boundary: REFUSED {shared} (a directory {probe} names): writable by every user"),
            ("import-line", f"{shared}\nimport v1_pth_marker\n",
             f"host_boundary: REFUSED {probe} (a .pth file of python3's user site-packages): line 2 is code python3 "
             "executes"),
        )
        for name, content, refusal in cases:
            with self.subTest(case=name):
                probe.write_text(content)
                os.chmod(probe, 0o644)
                result = world.run_gate("--attest", "--scope", "portable", umask=0o022, **extra)
                self.assertEqual(result.returncode, 1, result.stdout[-3000:] + result.stderr[-2000:])
                self.assertIn(refusal, result.stdout)
                self.assertRegex(result.stdout, r"\[FAIL\] preflight: host trust boundary")
                self.assertIn("STOPPED at the first failure (preflight: host trust boundary): nothing else ran.",
                              result.stdout)
                self.assertEqual(world.workloads(), [], "no fixture tool ran")
                self.assertFalse(log.exists(), log.read_text() if log.exists() else "")
                self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")
        private = base / "private-pylib"
        private.mkdir()
        os.chmod(private, 0o755)
        probe.write_text(f"{private}\n")
        os.chmod(probe, 0o644)
        result = world.run_gate("--attest", "--scope", "portable", umask=0o022, **extra)
        self.assertEqual(result.returncode, 0, result.stdout[-3000:] + result.stderr[-2000:])
        logdir = fixture.logdir_of(result)
        self.assertIsNotNone(logdir, result.stdout[-2000:])
        self.assertIn(f"host_boundary: judged a directory {probe} names {private}",
                      (logdir / "host-boundary.log").read_text())
        self.assertRegex(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"),
                         r"^refs/attest/soundness/[0-9a-f]{40}/")

    def test_no_python3_the_gate_starts_reads_the_user_site_packages(self):
        """Every python3 the gate scripts and their Python tools start runs
        with -I, so none imports a usercustomize from the user site-packages
        (at the base the bounded runner, started by its `#!/usr/bin/env
        python3` line, and trust_cargo.sh's, the attestation tool's and
        check_x86_icmp_certificates.py's resolver runs did). A census run (no
        boundary, which now refuses that module outright) with a marker
        usercustomize logs every python3 that imports it: only the fixture's
        own fakes (python scripts standing in for cargo, trustc, lake and the
        rest) do, no gate script or tool and no inline program. The positive
        control: a plain `python3 -c` imports the marker."""
        world, extra, base = self.world("host-boundary-usersite-", 0o022, shared=False)
        site = self.user_site(world)
        log = base / "usercustomize.log"
        (site / "usercustomize.py").write_text(self.MARKER.format(log=str(log)))
        env = {"HOME": str(world.home), "PATH": world.env()["PATH"]}
        subprocess.run(["python3", "-c", "pass"], env=env, check=True, timeout=60)
        self.assertEqual(len(log.read_text().splitlines()), 1, "the marker's positive control")
        log.unlink()
        result = world.run_gate("--scope", "portable", umask=0o022, SOUNDNESS_X86_HOST=None, **extra)
        self.assertIn("gates:", result.stdout, result.stdout[-3000:] + result.stderr[-2000:])
        imported = sorted({line.split("\t")[0] for line in log.read_text().splitlines()} if log.exists() else set())
        self.assertTrue(imported, "the fakes, python scripts run without -I, import it (non-vacuity)")
        # The gate's own python3 runs: an inline program, or a script of the
        # candidate checkout (its scripts/ and anything else in it). The fakes
        # live outside it (~/.cargo/bin, the sysroot, the Clean build's
        # target/ under the cache).
        gate = [argv0 for argv0 in imported
                if argv0 in ("-c", "-", "") or Path(argv0).resolve().is_relative_to(world.cg.resolve())]
        self.assertEqual(gate, [], "no python3 the gate starts imports the user site's usercustomize")

    # -- repair round 3 of OD-XHOST-GATE-CWD-20261025 ---------------------
    LOGGING_PYTHON3 = '''#!/bin/sh
# benign marker (X-HOST-P13, repair round 3 of OD-XHOST-GATE-CWD-20261025)
printf '%s\\t%s\\n' "$PWD" "$*" >> {log}
exec {python} "$@"
'''

    @staticmethod
    def pinned_python3(world: fixture.Constellation) -> str:
        """The interpreter the gate pins: the canonical path of the python3
        the fixture run's PATH finds before the prelude."""
        found = shutil.which("python3", path=world.env()["PATH"])
        assert found, world.env()["PATH"]
        return os.path.realpath(found)

    LEG_PLACE = "the python3 a leg starts by name (the first on the run's PATH)"
    PTH_MARKER = ('import os; open({log!r}, "a").write("pth ran in %s\\n" % os.path.realpath(__import__("sys")'
                  '.executable))\n')

    @staticmethod
    def venv(path: Path, shared_site: bool) -> Path:
        """A virtual environment at `path` (python3 -m venv --without-pip, by
        this test's interpreter: its bin/python3 is a symlink to that very
        file), and its site-packages, made 0777 when `shared_site`."""
        subprocess.run([fixture.FIXTURE_PYTHON3, "-I", "-m", "venv", "--without-pip", str(path)], check=True,
                       timeout=120, capture_output=True)
        out = subprocess.run([str(path / "bin" / "python3"), "-I", "-c",
                              "import site; print(site.getsitepackages()[0])"], check=True, timeout=60,
                             capture_output=True, text=True, cwd="/").stdout.strip()
        site = Path(out)
        assert site.is_relative_to(path), site
        if shared_site:
            os.chmod(site, 0o777)
        return site

    def test_a_python3_the_prelude_puts_first_on_path_refuses_the_run_without_running(self):
        """(A) The repair round 2 verifiers' probe: gate_env.sh's prelude puts
        $HOME/.elan/bin first on PATH, and the boundary's own python3, found
        by name after it, was a logging python3 planted there (0755), which
        ran the boundary and every later gate python3 and the run attested.
        Round 3 pinned python3 before the prelude, but judged that pinned
        interpreter's import path alone while the legs start python3 BY NAME
        on the prelude's PATH: the round-3 verifiers' probe, a planted
        wrapper there running a virtual environment's python3 whose
        site-packages is 0777, attested 136/136 at 8d3e1a608, where 8b127f2a4
        refused (round 3's test passed only because the fixture's fakes named
        their interpreter by an absolute path; they name python3 again, as a
        real leg does). Now the boundary refuses the run by name, judging the
        pinned file: the planted python3 and the site-packages .pth never run,
        no fixture tool runs, no record. The positive control: python3 by
        name on the prelude's PATH runs both. A census run (no boundary) still
        starts every python3 of the gate by the pin: the planted python3 logs
        only the fixture's fakes (legs), no gate script or inline program. A
        symlink there to the pinned file, with no pyvenv.cfg around it, is the
        same interpreter with the same import path: the run attests, the
        report naming it. A caller's SOUNDNESS_PYTHON3 (the planted file
        itself) refuses the run with builtins, before any program: nothing
        runs, no record."""
        world, extra, base = self.world("host-boundary-pin-", 0o022, shared=False)
        extra["SOUNDNESS_X86_HOST"] = None
        log = base / "elan-python3.log"
        pth_log = base / "venv-pth.log"
        other = base / "otherpy"
        site = self.venv(other, shared_site=True)
        (site / "zz_probe.pth").write_text(self.PTH_MARKER.format(log=str(pth_log)))
        os.chmod(site / "zz_probe.pth", 0o666)
        elan_bin = world.home / ".elan" / "bin"
        planted = elan_bin / "python3"
        planted.write_text(self.LOGGING_PYTHON3.format(log=log, python=other / "bin" / "python3"))
        os.chmod(planted, 0o755)
        after_prelude = f"{world.bin}:{elan_bin}:{world.env()['PATH']}"
        self.assertEqual(shutil.which("python3", path=after_prelude), str(planted), "the positive control")
        subprocess.run(["python3", "-c", "pass"], env={"PATH": after_prelude, "HOME": str(world.home)}, cwd="/",
                       check=True, timeout=60)
        self.assertTrue(log.exists() and pth_log.exists(), "a leg's python3 by name runs both (positive control)")
        log.unlink()
        pth_log.unlink()
        pinned = self.pinned_python3(world)
        self.assertNotEqual(os.path.realpath(planted), pinned)
        result = world.run_gate("--attest", "--scope", "portable", umask=0o022, **extra)
        self.assertFalse(log.exists(), log.read_text() if log.exists() else "")
        self.assertFalse(pth_log.exists(), pth_log.read_text() if pth_log.exists() else "")
        self.assertEqual(result.returncode, 1, result.stdout[-3000:] + result.stderr[-2000:])
        self.assertIn(f"host_boundary: REFUSED {planted} ({self.LEG_PLACE}): is not the gate's pinned python3 "
                      f"{pinned} (it resolves to {planted})", result.stdout)
        self.assertIn(f"host_boundary: judged the gate's pinned python3 (SOUNDNESS_PYTHON3) {pinned}", result.stdout)
        self.assertIn("STOPPED at the first failure (preflight: host trust boundary): nothing else ran.",
                      result.stdout)
        self.assertEqual(world.workloads(), [], "no fixture tool ran")
        self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")
        # The census run: the planted python3 runs the fakes only.
        planted.write_text(self.LOGGING_PYTHON3.format(log=log, python=fixture.FIXTURE_PYTHON3))
        census = world.run_gate("--scope", "portable", umask=0o022, **extra)
        self.assertIn("gates:", census.stdout, census.stdout[-3000:] + census.stderr[-2000:])
        runs = [line.split("\t", 1)[1] for line in log.read_text().splitlines()] if log.exists() else []
        self.assertTrue(runs, "the fakes start python3 by name, as legs do (non-vacuity)")
        gate = [args for args in runs
                if not args.startswith("/") or Path(args.split(" ", 1)[0]).resolve().is_relative_to(world.cg.resolve())]
        self.assertEqual(gate, [], "no python3 the gate or its tools start is the planted one")
        log.unlink()
        planted.unlink()
        planted.symlink_to(pinned)
        attested = world.run_gate("--attest", "--scope", "portable", umask=0o022, **extra)
        self.assertEqual(attested.returncode, 0, attested.stdout[-3000:] + attested.stderr[-2000:])
        report = (fixture.logdir_of(attested) / "host-boundary.log").read_text()
        self.assertIn(f"host_boundary: judged {self.LEG_PLACE} {planted}", report)
        self.assertIn(f"host_boundary: judged the gate's pinned python3 (SOUNDNESS_PYTHON3) {pinned}", report)
        self.assertRegex(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"),
                         r"^refs/attest/soundness/[0-9a-f]{40}/")
        planted.unlink()
        planted.write_text(self.LOGGING_PYTHON3.format(log=log, python=fixture.FIXTURE_PYTHON3))
        os.chmod(planted, 0o755)
        caller = world.run_gate("--attest", "--scope", "portable", umask=0o022, SOUNDNESS_PYTHON3=str(planted),
                                **extra)
        self.assertEqual(caller.returncode, 1, caller.stdout[-3000:] + caller.stderr[-2000:])
        self.assertIn(f"SOUNDNESS_PYTHON3 is set by the caller (SOUNDNESS_PYTHON3={planted})", caller.stdout)
        self.assertIn("no attestation record", caller.stdout)
        self.assertNotIn("host_boundary:", caller.stdout, "refused before the boundary ran")
        self.assertEqual(world.workloads(), [])
        self.assertFalse(log.exists(), log.read_text() if log.exists() else "")

    def test_a_virtual_environments_python3_first_on_path_refuses_the_run(self):
        """(A, round 4) A virtual environment's bin directory first on the
        caller's PATH (an activated venv), its site-packages 0777 with a
        benign .pth another user could have put there. Its bin/python3 is a
        symlink to the base interpreter, so the round-3 pin (the realpath of
        sys.executable) was that base file, the boundary judged its import
        path, and the legs, running python3 by name, ran the environment's,
        0777 site-packages included: 8d3e1a608 attested with the fakes
        running the .pth; 8b127f2a4, whose boundary itself ran python3 by
        name, refused that directory, but only after its own startup had run
        the .pth. Now the boundary refuses the run naming the environment's
        pyvenv.cfg; the .pth never runs, no fixture tool runs, no record. The
        positive control: python3 by name on that PATH runs the .pth."""
        world, extra, base = self.world("host-boundary-venv-", 0o022, shared=False)
        extra["SOUNDNESS_X86_HOST"] = None
        pth_log = base / "venv-pth.log"
        venv = base / "leg-venv"
        site = self.venv(venv, shared_site=True)
        (site / "zz_probe.pth").write_text(self.PTH_MARKER.format(log=str(pth_log)))
        os.chmod(site / "zz_probe.pth", 0o666)
        path = f"{venv / 'bin'}:{world.env()['PATH']}"
        pinned = os.path.realpath(shutil.which("python3", path=path))
        self.assertEqual(pinned, os.path.realpath(fixture.FIXTURE_PYTHON3))
        subprocess.run(["python3", "-c", "pass"], env={"PATH": path, "HOME": str(world.home)}, cwd="/", check=True,
                       timeout=60)
        self.assertTrue(pth_log.exists(), "a leg's python3 by name runs the environment's .pth (positive control)")
        pth_log.unlink()
        result = world.run_gate("--attest", "--scope", "portable", umask=0o022, PATH=path, **extra)
        self.assertFalse(pth_log.exists(), pth_log.read_text() if pth_log.exists() else "")
        self.assertEqual(result.returncode, 1, result.stdout[-3000:] + result.stderr[-2000:])
        self.assertIn(f"host_boundary: REFUSED {venv / 'pyvenv.cfg'} ({self.LEG_PLACE}): is a virtual environment's "
                      f"configuration python3 reads at startup, and a leg runs the pinned interpreter as "
                      f"{venv / 'bin' / 'python3'} while the gate runs it as {pinned}", result.stdout)
        self.assertIn("STOPPED at the first failure (preflight: host trust boundary): nothing else ran.",
                      result.stdout)
        self.assertEqual(world.workloads(), [], "no fixture tool ran")
        self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")

    PLANTED_SCRIPT = '''# benign marker (X-HOST-P13, repair round 4 of OD-XHOST-GATE-CWD-20261025)
import sys
with open({log!r}, "a") as handle:
    handle.write("planted %s ran: argv=%r\\n" % ({name!r}, sys.argv[1:3]))
sys.exit(3)
'''

    def test_no_script_a_callers_trust_cg_dir_names_runs_before_the_boundary(self):
        """The round-3 verifier's probe_scrubbed_flag.py: with the
        gate-internal SOUNDNESS_ENV_SCRUBBED=1 exported by the caller (no
        scrub) and TRUST_CG_DIR naming a 0777 directory, the cache-base rule
        ran that directory's 0666 scripts/private_cache.py, and the boundary
        was its scripts/host_boundary.py, before anything was judged (at
        8b127f2a4 and 8d3e1a608). Both are now named by the gate's own
        directory, the candidate's scripts/ that holds the very file bash
        runs: no planted script runs, the boundary refuses the caller's
        directory as the candidate checkout, nothing else runs, no record."""
        world, extra, base = self.world("host-boundary-cgdir-", 0o022, shared=False)
        extra["SOUNDNESS_X86_HOST"] = None
        caller = base / "caller-cg"
        (caller / "scripts").mkdir(parents=True)
        os.chmod(caller, 0o777)
        os.chmod(caller / "scripts", 0o777)
        log = base / "planted-scripts.log"
        for name in ("private_cache.py", "host_boundary.py"):
            (caller / "scripts" / name).write_text(self.PLANTED_SCRIPT.format(log=str(log), name=name))
            os.chmod(caller / "scripts" / name, 0o666)
        result = world.run_gate("--attest", "--scope", "portable", umask=0o022, SOUNDNESS_ENV_SCRUBBED="1",
                                TRUST_CG_DIR=str(caller), **extra)
        self.assertFalse(log.exists(), log.read_text() if log.exists() else "")
        self.assertEqual(result.returncode, 1, result.stdout[-3000:] + result.stderr[-2000:])
        self.assertIn(f"host_boundary: REFUSED {caller}", result.stdout)
        self.assertIn("no attestation record", result.stdout)
        self.assertEqual(world.workloads(), [], "no fixture tool ran")
        self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")

    def test_an_attested_run_not_read_from_the_candidates_script_file_refuses_before_any_program(self):
        """(B) The repair round 2 verifiers' probe: `bash -s -- --attest <
        <candidate>/scripts/soundness_check.sh` started in a 0777 directory
        has no BASH_SOURCE[0], so $0 (`bash`) named the script, the script
        directory check judged the caller's directory (a `bash` file there
        made it pass), and the scrub ran that directory's 0666
        soundness_attestation.py before the boundary; `bash -c "$(cat ...)"
        <word>` did the same with any word. An --attest run read from
        standard input or a -c string, or sourced, and a file bash reads
        that is not the candidate's scripts/soundness_check.sh (`bash
        /dev/stdin`), now refuse with builtins before any program: no
        planted program runs, no fixture tool runs, no record. The control:
        the same script file run as a script from that directory attests."""
        world, extra, base = self.world("host-boundary-stdin-", 0o022, shared=False)
        caller = base / "caller-0777"
        caller.mkdir()
        os.chmod(caller, 0o777)
        log = base / "planted.log"
        planted = caller / "soundness_attestation.py"
        planted.write_text(self.PLANTED_TOOL.format(log=str(log)))
        os.chmod(planted, 0o666)
        for name in ("bash", "soundness_check.sh"):
            (caller / name).write_text("exit 0\n")
            os.chmod(caller / name, 0o666)
        (caller / "wrapper.sh").write_text(f'source {world.cg / "scripts" / "soundness_check.sh"} "$@"\n')
        script = world.cg / "scripts" / "soundness_check.sh"
        text = script.read_text()
        args = ("--attest", "--scope", "portable")
        cases = (
            ("bash -s", ["bash", "-s", "--", *args], text,
             "reads its commands from a -c string or from standard input"),
            # The script text is longer than one argument may be (Linux:
            # 128 KiB), so the -c string evaluates it whole from stdin.
            ("bash -c", ["bash", "-c", 'eval "$(cat)"', str(caller / "soundness_check.sh"), *args], text,
             "reads its commands from a -c string or from standard input"),
            ("sourced", ["bash", str(caller / "wrapper.sh"), *args], None,
             "bash names no such file here"),
            ("bash /dev/stdin", ["bash", "/dev/stdin", *args], text,
             "is not the candidate checkout's scripts/soundness_check.sh"),
        )
        world.write_fixture_env(world.env(SOUNDNESS_X86_HOST=None, **extra))
        env = self.gate_environment(world, SOUNDNESS_X86_HOST=None, **extra)
        for name, argv, stdin, refusal in cases:
            with self.subTest(start=name):
                world.log.write_text("")
                log.unlink(missing_ok=True)
                result = subprocess.run(argv, cwd=caller, env=env, input=stdin, capture_output=True, text=True,
                                        timeout=600, umask=0o022)
                self.assertFalse(log.exists(), log.read_text() if log.exists() else "")
                self.assertEqual(result.returncode, 1, result.stdout[-3000:] + result.stderr[-2000:])
                self.assertIn(refusal, result.stdout)
                self.assertIn("[FAIL] preflight: host trust boundary", result.stdout)
                self.assertIn("no attestation record", result.stdout)
                self.assertNotIn("host_boundary:", result.stdout, "refused before the boundary ran")
                self.assertEqual(world.workloads(), [])
                self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "")
        # The control: the same script file, run as a script from the same
        # directory, attests.
        control = subprocess.run(["bash", str(script), *args], cwd=caller, env=env, capture_output=True, text=True,
                                 timeout=600, umask=0o022)
        self.assertEqual(control.returncode, 0, control.stdout[-3000:] + control.stderr[-2000:])
        self.assertFalse(log.exists(), log.read_text() if log.exists() else "")
        self.assertRegex(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"),
                         r"^refs/attest/soundness/[0-9a-f]{40}/")


class GatePythonIsolationTests(unittest.TestCase):
    """OD-XHOST-GATE-CWD-20261025 and its repair round 2, held statically so
    a new site cannot regress: every python3 the gate scripts start, inline
    (`-c`, `-`, a program on stdin) or a script, carries -I among its leading
    options (the round-1 rule held inline runs only; a script run without -I
    imports from the user site-packages and runs its .pth files), so does
    every python3 argv the Python tools they start build, no script of theirs
    runs by its `#!/usr/bin/env python3` line, and every `cd` in the gate
    scripts ignores CDPATH (`CDPATH= cd`) or names a literal absolute
    directory. The scanner reads a python word by any spelling a shell
    script could use (python, python3, python3.12, an absolute path to one, a
    $PYTHON-like variable)."""

    # The attested gate, the scripts it starts and the landing paths that start it.
    GATE_SHELL_SCRIPTS = ("scripts/soundness_check.sh", "scripts/gate_env.sh", "scripts/trust_cargo.sh",
                          "scripts/soundness_remote.sh", "scripts/land_main.sh", "hooks/pre-push",
                          "scripts/check_fmt.sh", "scripts/check_tippy.sh")
    # Named on a code line of one of them, but not started by it.
    NAMED_NOT_STARTED = {"run_full_test_matrix.sh": "gate_env.sh's check names it in a message",
                         "check_linux_aarch64_bridge.py": "gate_env.sh's check names it in a message"}
    # Code lines that name python3 without starting it: (script, a substring
    # of the line) -> why. Each must still match (no stale entry).
    NOT_A_PYTHON_RUN = {
        ("scripts/soundness_check.sh", "share it with: python3 scripts/soundness_attestation.py push"):
            "a hint printed for the user to run by hand",
        ("scripts/soundness_remote.sh", "for tool in git python3; do"): "the remote probe's presence check",
        # Repair round 3: each gate script's pin point, a builtin PATH lookup.
        **{(name, "$(type -P python3"): "the pin point: a builtin PATH lookup, not a run"
           for name in ("scripts/soundness_check.sh", "scripts/gate_env.sh", "scripts/trust_cargo.sh",
                        "scripts/soundness_remote.sh", "scripts/land_main.sh", "hooks/pre-push",
                        "scripts/check_fmt.sh", "scripts/check_tippy.sh")},
    }
    # The python3 runs each script holds at repair round 3 (the scanner's
    # non-vacuity floor: a broken scanner finds fewer).
    KNOWN_RUNS = {"scripts/soundness_check.sh": 27, "scripts/gate_env.sh": 1, "scripts/trust_cargo.sh": 5,
                  "scripts/soundness_remote.sh": 2, "scripts/land_main.sh": 1, "hooks/pre-push": 2,
                  "scripts/check_fmt.sh": 1, "scripts/check_tippy.sh": 1}
    # The `cd` commands each script holds at repair round 2 (the same floor).
    KNOWN_CDS = {"scripts/soundness_check.sh": 6, "scripts/gate_env.sh": 1, "scripts/trust_cargo.sh": 1,
                 "scripts/soundness_remote.sh": 1, "scripts/land_main.sh": 5, "scripts/check_fmt.sh": 2,
                 "scripts/check_tippy.sh": 2}
    WORD_START = r"(?:^|(?<=[\s;|&(!`]))"
    PYTHON_WORD = re.compile(WORD_START + r"[\"']?(?:/[\w.+-]+)*/?(?:python(?:3(?:\.\d+)?)?|\$\{?\w*PYTHON\w*\}?)"
                             r"[\"']?(?=\s|$|[;|&)])")
    # A cluster of python3's flags that take no argument, holding I (`-I`,
    # `-IB`, `-BI`), optionally ending in the c or m that takes the program.
    ISOLATED_OPTION = re.compile(r"-[bBdEhiIOPqRsSuvVx]*I[bBdEhiIOPqRsSuvVx]*[cm]?")
    # Repair round 3: a python word that is an OPERAND, not a command: the
    # subject of `case`, an operand of a `[ ... ]` test (after `[`, `!`, a
    # unary test such as `-z`/`-f`/`-x`, or `=`/`!=`/`-ef`), or the value of
    # the boundary's `--python3` option. The text before the word ends so.
    OPERAND_CONTEXT = re.compile(r"(?:\bcase|\[|\[\s+!|\[\s+-[zfnxeL]|\[\s+!\s+-[zfnxeL]|!?=|-ef|--python3)\s+[\"']?$")
    # Each gate script resolves python3 ONCE, at its pin point (the one code
    # line holding this builtin PATH lookup), and starts it only by the
    # pinned path from there on.
    PIN_LOOKUP = "$(type -P python3"
    PINNED_WORD = '"$SOUNDNESS_PYTHON3"'
    # The python word after a pin point that is not the pinned path, with why.
    NOT_THE_PINNED_RUN = {
        ("scripts/soundness_check.sh", '"$SOUNDNESS_FOUND_PYTHON3" -I -S -c'):
            "the pin itself: the python3 PATH finds prints its canonical path (-I -S: no site directory)",
    }
    # The python words before a script's pin point, with why (none else).
    BEFORE_THE_PIN = {
        ("scripts/soundness_remote.sh", 'python3 -I -c "$private_cache_py" mkdir'):
            "REMOTE_SCRIPT: runs on the remote host, whose own gate pins its interpreter",
    }
    # The code line each pin point must precede: the call of the prelude that
    # puts $HOME/.elan/bin first on PATH.
    PRELUDE_CALLS = {"scripts/soundness_check.sh": "! gate_env_prelude --with-lean",
                     "scripts/gate_env.sh": "gate_env_prelude $_gate_env_prelude_args"}
    # Uses of sys.executable outside an argv list, per gate Python tool:
    # host_boundary.py judges it and compares the gate's pin with it, and
    # soundness_attestation.py reads it once to pin it (running_interpreter).
    EXECUTABLE_USES = {"host_boundary.py": 2, "soundness_attestation.py": 1}
    CD_WORD = re.compile(r"(?:^|(?<=[\s;|&(!]))(?:pushd|cd)(?=\s|$|;)")
    PY_ARGV = re.compile(r"\[\s*(?P<head>sys\.executable|[\"']python(?:3(?:\.\d+)?)?[\"'])\s*(?:,(?P<rest>[^\]]*))?\]")
    SCRIPT_ARGV = re.compile(r"\[\s*(?:str\()?[^\],]*\.py[\"']\)?\s*[,\]]")

    @staticmethod
    def code_line_items(text: str):
        """(line number, line) of each line that is not a comment."""
        for number, line in enumerate(text.splitlines(), 1):
            if not line.lstrip().startswith("#"):
                yield number, line

    @classmethod
    def python_words(cls, text: str) -> list[tuple[int, str, str, bool]]:
        """(line, text, word, isolated) of each python word on a code line of
        a shell script that is not an operand (OPERAND_CONTEXT): isolated
        when one of the option words that follow it, up to the first that is
        no option, is an -I cluster."""
        found = []
        for number, line in cls.code_line_items(text):
            for match in cls.PYTHON_WORD.finditer(line):
                if cls.OPERAND_CONTEXT.search(line[:match.start()]):
                    continue
                isolated = False
                for word in line[match.end():].split():
                    if not word.startswith("-") or word == "-":
                        break
                    if cls.ISOLATED_OPTION.fullmatch(word):
                        isolated = True
                        break
                found.append((number, line.strip(), match.group(0), isolated))
        return found

    @classmethod
    def python_runs(cls, text: str) -> list[tuple[int, str, bool]]:
        """(line, text, isolated) of each python word (python_words)."""
        return [(number, line, isolated) for number, line, _word, isolated in cls.python_words(text)]

    def pin_problems(self, name: str, text: str, used: set | None = None) -> list[str]:
        """Each way `text` (the gate script `name`) breaks the pin rule: not
        exactly one pin point; the pin point after the prelude call; a python
        word before it (BEFORE_THE_PIN aside) or after it that is not the
        pinned path (NOT_THE_PINNED_RUN aside). Lines that name python3
        without starting it (NOT_A_PYTHON_RUN) are skipped."""
        used = set() if used is None else used
        lines = list(self.code_line_items(text))
        pins = [number for number, line in lines if self.PIN_LOOKUP in line]
        if len(pins) != 1:
            return [f"{name}: {len(pins)} pin points (`{self.PIN_LOOKUP})` on a code line), not one"]
        pin, problems = pins[0], []
        prelude = self.PRELUDE_CALLS.get(name)
        if prelude is not None:
            calls = [number for number, line in lines if prelude in line]
            if len(calls) != 1 or calls[0] < pin:
                problems.append(f"{name}: the pin point (line {pin}) does not precede the prelude call {calls}")
        for number, line, word, _isolated in self.python_words(text):
            if number == pin or self.allowed(name, line):
                continue
            table = self.BEFORE_THE_PIN if number < pin else self.NOT_THE_PINNED_RUN
            exempt = [(script, needle) for script, needle in table if script == name and needle in line]
            if exempt:
                used.update(exempt)
            elif number < pin:
                problems.append(f"{name}:{number}: {word} runs before the pin point (line {pin}): {line}")
            elif word != self.PINNED_WORD:
                problems.append(f"{name}:{number}: {word} after the pin point (line {pin}) is not the pinned "
                                f"interpreter {self.PINNED_WORD}: {line}")
        return problems

    @classmethod
    def cd_runs(cls, text: str) -> list[tuple[int, str, bool]]:
        """(line, text, safe) of each cd/pushd on a code line: safe when
        written `CDPATH= cd` or when its first operand is a literal absolute
        directory (CDPATH is then never consulted)."""
        found = []
        for number, line in cls.code_line_items(text):
            for match in cls.CD_WORD.finditer(line):
                operands = [word for word in line[match.end():].split() if not word.startswith("-")]
                safe = line[:match.start()].endswith("CDPATH= ") or bool(operands and operands[0].startswith("/"))
                found.append((number, line.strip(), safe))
        return found

    @classmethod
    def python_argvs(cls, text: str) -> list[tuple[str, bool]]:
        """(argv text, isolated) of each `[sys.executable or "python3", ...]`."""
        found = []
        for match in cls.PY_ARGV.finditer(text):
            isolated = False
            for element in (match.group("rest") or "").split(","):
                literal = re.fullmatch(r"\s*[\"'](-[A-Za-z]*)[\"']\s*", element)
                if not literal:
                    break
                if cls.ISOLATED_OPTION.fullmatch(literal.group(1)):
                    isolated = True
                    break
            found.append((match.group(0), isolated))
        return found

    def allowed(self, name: str, line: str) -> bool:
        return any(script == name and needle in line for script, needle in self.NOT_A_PYTHON_RUN)

    def test_the_scanner_reads_each_form(self):
        sample = "\n".join((
            "x=\"$(printf '%s' \"$r\" | python3 -c 'import json')\"",                    # 1 inline, open
            "python3 - \"$a\" <<'EOF'",                                                   # 2 stdin, open
            "python3 -I -c 'pass'",                                                       # 3
            "  python3 -I - \"$a\" <<'EOF'",                                              # 4
            "python3 -IBc 'pass'",                                                        # 5
            "python3 -B \"$root/scripts/trust_toolchain.py\" --print json",               # 6 script, open
            "exec python3 -I \"$dir/soundness_attestation.py\" exec-scrubbed",            # 7
            "# python3 -c 'a comment'",                                                   # (comment)
            "python3.12 -c 'pass'",                                                       # 9 open
            "/usr/bin/python3 -c 'pass'",                                                 # 10 open
            "\"$PYTHON\" -c 'pass'",                                                      # 11 open
            "python3 -W ignore -I -c 'pass'",                                             # 12 open (-W's word)
            "python3 <<'EOF'",                                                            # 13 open
            "printf x | python3",                                                         # 14 open
            "python3 -m json.tool",                                                       # 15 open
            "python3 -BI script.py",                                                      # 16
            "env \"${clean_env[@]}\" python3 -I -B \"$t\" --print json",                   # 17
        ))
        self.assertEqual([(number, isolated) for number, _line, isolated in self.python_runs(sample)],
                         [(1, False), (2, False), (3, True), (4, True), (5, True), (6, False), (7, True),
                          (9, False), (10, False), (11, False), (12, False), (13, False), (14, False),
                          (15, False), (16, True), (17, True)])
        cds = "\n".join(("x=\"$(cd \"$d\" && pwd)\"", "CDPATH= cd -- \"$d\"", "cd /", "! cd /; then",
                         "(cd \"$w\" && ./x)", "CDPATH= cd -P -- \"$r\" || fail", "pushd \"$d\""))
        self.assertEqual([safe for _number, _line, safe in self.cd_runs(cds)],
                         [False, True, True, True, False, True, False])
        argvs = self.python_argvs('run([sys.executable, "-c", code])\nrun(["python3", "-I", "-c", c])\n'
                                  'run([sys.executable, "-B", str(script)])\nrun(["python3", "-", x])\n'
                                  'run([sys.executable, "-I", "-B", str(s)])\nrun([sys.executable])\n')
        self.assertEqual([isolated for _argv, isolated in argvs], [False, True, False, False, True, False])
        self.assertTrue(self.SCRIPT_ARGV.search('subprocess.run([str(SCRIPTS / "run_with_timeout.py"), "--chdir"])'))
        self.assertFalse(self.SCRIPT_ARGV.search('[sys.executable, "-I", str(SCRIPTS / "run_with_timeout.py")]'))
        # Repair round 3: operands are not runs, and the pin rule.
        operands = "\n".join(('case "$SOUNDNESS_PYTHON3" in', 'if [ -z "$SOUNDNESS_PYTHON3" ]; then',
                               '[ ! -x "$SOUNDNESS_PYTHON3" ] || x', '[ "$a" != "$SOUNDNESS_PYTHON3" ]',
                               'args=(--python3 "$SOUNDNESS_PYTHON3")', '"$SOUNDNESS_PYTHON3" -I x.py',
                               'run_bounded "$d" python3 x.py', 'case "$x" in python3) python3 -c 1 ;; esac'))
        self.assertEqual([(number, isolated) for number, _line, isolated in self.python_runs(operands)],
                         [(6, True), (7, False), (8, False), (8, False)])
        pinned = "\n".join(('python3 -I early.py',
                             'SOUNDNESS_PYTHON3="${SOUNDNESS_PYTHON3:-$(type -P python3 || true)}"',
                             '"$SOUNDNESS_PYTHON3" -I a.py', 'python3 -I b.py', '/usr/bin/python3 -I c.py',
                             '"$PYTHON" -I d.py', 'x="$(printf x | "$SOUNDNESS_PYTHON3" -I -c 1)"'))
        self.assertEqual([problem.split(": ", 1)[0] for problem in self.pin_problems("sample.sh", pinned)],
                         ["sample.sh:1", "sample.sh:4", "sample.sh:5", "sample.sh:6"])
        self.assertEqual(self.pin_problems("sample.sh", '"$SOUNDNESS_PYTHON3" -I a.py\n'),
                         ["sample.sh: 0 pin points (`$(type -P python3)` on a code line), not one"])

    def test_every_python3_the_gate_scripts_start_runs_isolated(self):
        unisolated, used = [], set()
        for name in self.GATE_SHELL_SCRIPTS:
            runs = []
            for number, line, isolated in self.python_runs((ROOT / name).read_text()):
                if self.allowed(name, line):
                    used |= {(script, needle) for script, needle in self.NOT_A_PYTHON_RUN
                             if script == name and needle in line}
                    continue
                runs.append((number, line, isolated))
            self.assertGreaterEqual(len(runs), self.KNOWN_RUNS.get(name, 0), (name, runs))
            unisolated += [f"{name}:{number}: {line}" for number, line, isolated in runs if not isolated]
        self.assertEqual(unisolated, [], "each python3 of the gate scripts needs -I")
        self.assertEqual(sorted(set(self.NOT_A_PYTHON_RUN) - used), [], "a stale NOT_A_PYTHON_RUN entry")

    def test_every_python3_after_the_pin_point_is_the_pinned_interpreter(self):
        """Repair round 3 of OD-XHOST-GATE-CWD-20261025: each gate script
        resolves python3 once, at its pin point, before anything changes PATH
        (in soundness_check.sh and gate_env.sh, before the prelude puts
        $HOME/.elan/bin first), and from there on starts python3 only by the
        pinned path, "$SOUNDNESS_PYTHON3": a bare `python3`, another spelling
        or another variable after the pin point fails, as does a run before
        it (the remote half of soundness_remote.sh, which runs on the remote
        host, aside)."""
        problems, used = [], set()
        for name in self.GATE_SHELL_SCRIPTS:
            problems += self.pin_problems(name, (ROOT / name).read_text(), used)
        self.assertEqual(problems, [], "each python3 of a gate script after its pin point is the pinned path")
        self.assertEqual(sorted((set(self.BEFORE_THE_PIN) | set(self.NOT_THE_PINNED_RUN)) - used), [],
                         "a stale BEFORE_THE_PIN or NOT_THE_PINNED_RUN entry")

    def test_no_gate_script_starts_a_python_script_by_its_interpreter_line(self):
        # A variable holding a .py path must not be a command's first word:
        # the script's `#!/usr/bin/env python3` would run it without -I.
        started = []
        for name in self.GATE_SHELL_SCRIPTS:
            text = (ROOT / name).read_text()
            variables = set(re.findall(r"^\s*(?:local\s+)?([A-Za-z_][A-Za-z0-9_]*)=\"[^\"]*\.py\"", text, re.M))
            for variable in variables:
                use = re.compile(r"(?:^|[;|&(]|\$\(|\b(?:then|do|else|exec|if|while|until)\s|!\s)\s*"
                                 r"\"\$\{?" + variable + r"\}?\"")
                started += [f"{name}:{number}: {line.strip()}" for number, line in self.code_line_items(text)
                            if use.search(line)]
            started += [f"{name}:{number}: {line.strip()}" for number, line in self.code_line_items(text)
                        if re.search(r"(?:^|[;|&(]|\$\()\s*\"?[^\s\"]*\.py\"?(?:\s|$)", line)
                        and not self.PYTHON_WORD.search(line)]
        self.assertEqual(started, [])

    def test_every_cd_of_the_gate_scripts_ignores_cdpath(self):
        unsafe = []
        for name in self.GATE_SHELL_SCRIPTS:
            runs = self.cd_runs((ROOT / name).read_text())
            self.assertGreaterEqual(len(runs), self.KNOWN_CDS.get(name, 0), (name, runs))
            unsafe += [f"{name}:{number}: {line}" for number, line, safe in runs if not safe]
        self.assertEqual(unsafe, [], "each cd of the gate scripts needs `CDPATH= cd` or a literal absolute directory")

    def test_the_gate_script_list_covers_every_shell_script_they_start(self):
        listed = {Path(name).name for name in self.GATE_SHELL_SCRIPTS}
        named = set()
        for name in self.GATE_SHELL_SCRIPTS:
            named |= {found for found in re.findall(r"\b([A-Za-z0-9_]+\.sh)\b",
                                                     "\n".join(line for _n, line in
                                                               self.code_line_items((ROOT / name).read_text())))
                      if (ROOT / "scripts" / found).is_file()}
        self.assertEqual(sorted(named - listed - set(self.NAMED_NOT_STARTED)), [])

    def gate_python_tools(self) -> set[str]:
        """The scripts/*.py the gate shell scripts name on a code line, and,
        transitively, every scripts/*.py a python3 argv of one of those
        tools names (the scripts they start)."""
        tools: set[str] = set()
        pending = []
        for name in self.GATE_SHELL_SCRIPTS:
            text = "\n".join(line for _n, line in self.code_line_items((ROOT / name).read_text()))
            pending += re.findall(r"\b([A-Za-z0-9_]+\.py)\b", text)
        while pending:
            tool = pending.pop()
            if tool in tools or tool in self.NAMED_NOT_STARTED or not (ROOT / "scripts" / tool).is_file():
                continue
            tools.add(tool)
            text = (ROOT / "scripts" / tool).read_text()
            for argv, _isolated in self.python_argvs(text):
                pending += re.findall(r"\b([A-Za-z0-9_]+\.py)\b", argv)
            # A resolver held in a variable and then started: `resolver = ...
            # / "trust_toolchain.py"` with `[sys.executable, ..., str(resolver)]`.
            pending += re.findall(r"^\s*\w+\s*=\s*[^\n]*[\"']([A-Za-z0-9_]+\.py)[\"']", text, re.M)
        return tools

    def test_the_python_tools_the_gate_starts_start_every_python3_isolated(self):
        tools = self.gate_python_tools()
        self.assertTrue({"soundness_attestation.py", "host_boundary.py", "private_cache.py", "trust_toolchain.py",
                         "run_with_timeout.py", "export_vt_tables.py", "check_x86_icmp_certificates.py"} <= tools,
                        tools)
        unisolated, by_name, by_path, executable_uses = [], [], [], {}
        for tool in sorted(tools):
            text = (ROOT / "scripts" / tool).read_text()
            argvs = self.python_argvs(text)
            unisolated += [f"scripts/{tool}: {argv}" for argv, isolated in argvs if not isolated]
            # Repair round 3: by sys.executable (the gate's pinned interpreter
            # that runs the tool), never a python3 looked up by name.
            by_name += [f"scripts/{tool}: {argv}" for argv, _isolated in argvs
                        if not argv.startswith("[sys.executable")]
            by_path += [f"scripts/{tool}: {match.group(0)}" for match in self.SCRIPT_ARGV.finditer(text)]
            # Every sys.executable is the head of such an argv, or one of the
            # known uses that start nothing.
            uses = text.count("sys.executable") - sum(argv.startswith("[sys.executable") for argv, _isolated in argvs)
            if uses:
                executable_uses[tool] = uses
        self.assertEqual(unisolated, [], "each python3 argv of the gate's Python tools needs -I")
        self.assertEqual(by_name, [], "each python3 argv of the gate's Python tools starts sys.executable")
        self.assertEqual(by_path, [], "no gate Python tool starts a script by its interpreter line")
        # host_boundary.py judges sys.executable and compares the gate's pin
        # with it; soundness_attestation.py reads it once to pin it (its
        # `sys.version` is not counted) and starts the anchored verifier
        # through an argv held in a list it builds.
        self.assertEqual(executable_uses, self.EXECUTABLE_USES, "a new use of sys.executable outside an argv list")


if __name__ == "__main__":
    unittest.main()
