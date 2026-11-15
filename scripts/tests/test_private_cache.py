"""scripts/private_cache.py: the private-cache rule the repository's scripts share.

trust-cg's own caches create every directory under `<cache>/trust-cg` 0700
and every file 0600 whatever the umask (trust_cg_process_env::private_fs).
X-HOST-P13's closure audit (2026-10-03) found three scripts that still created
`<cache>/trust-cg` with `mkdir -p` / `Path.mkdir`, i.e. 0775 under umask 0002,
after which AY's identity rule refused AY in every later process; its
verification then found the soundness gate's Clean lane and the remote x86-64
legs writing group-writable build trees under the same caches. These cases
pin the rule itself under several umasks and with an inherited default ACL,
and each script that writes under the cache, run under umask 0002 with a
fresh cache: soundness_check.sh (its pinned dependency checkouts, and a whole
attested run of the fixture: the Clean lane's build tree and the remote
clone), and check_x86_icmp_certificates.py (its AY build cache, warm and
cold). soundness_remote.sh's remote side is also held in
test_soundness_remote.py. The third closure audit (2026-10-15) found the
scripts executing through the path they were given after the rule judged its
canonical form; the cases with "link" in their names re-point a symlink in a
0777 directory after the check and require that only the checked canonical
paths run. Test rung, not proof.
"""

from __future__ import annotations

import contextlib
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
HELPER = ROOT / "scripts" / "private_cache.py"
sys.path.insert(0, str(Path(__file__).resolve().parent))
import soundness_fixture as fixture  # noqa: E402


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


PC = load("private_cache", HELPER)
GATE = load("check_x86_icmp_certificates", ROOT / "scripts" / "check_x86_icmp_certificates.py")
AY = "a" * 40
AY_TOOL = GATE.Tool("ay", AY, "0.27.0", ("-p", "ay", "--features", "cli"), ())


# The fixture's targo for the icmp gate's cold AY build: it checks it was
# started as build_tool starts it, in the export, and writes what Cargo would (a
# target tree and the `ay` binary, whose `--version` names the revision) with
# the modes the process umask gives. FIXTURE_LOOSEN names a directory it makes
# 0775 meanwhile (an ancestor loosened during the build).
FAKE_TARGO = r'''#!/bin/sh
[ "$1 $2" = "--unverified build" ] || { echo "fixture targo: unexpected: $*" >&2; exit 64; }
[ -f Cargo.toml ] && [ -f .cargo/config.toml ] || { echo "fixture targo: not in the export" >&2; exit 65; }
grep -q "BEGIN Trust lane config" .cargo/config.toml || { echo "fixture targo: source lane config removed" >&2; exit 66; }
if [ -n "${FIXTURE_LOOSEN:-}" ]; then chmod 0775 "$FIXTURE_LOOSEN" || exit 67; fi
release="$CARGO_TARGET_DIR/release"
mkdir -p "$release/deps" "$release/.fingerprint/ay-fixture" || exit 68
echo deps > "$release/deps/ay-fixture.d"
echo fingerprint > "$release/.fingerprint/ay-fixture/bin-ay"
printf '#!/bin/sh\necho "ay 0.27.0+build.1.%s@2026-10-03"\n' "$AY_SOURCE_GIT_COMMIT" > "$release/ay"
chmod +x "$release/ay"
'''


def UNGATED(tool, label: str, work: Path) -> list:
    """No admission wrapper: these cases run the cold build in process with a
    fixture targo; the heavy_gate wrapper itself is held by
    test_check_x86_icmp_certificates.py."""
    return []


def tool_identity(tool, payload: bytes, banner: str) -> dict:
    """A current cache receipt; privacy attacks vary its storage, not recipe."""
    return {
        "schema": tool.cache_schema, "rev": tool.rev, "version": tool.version,
        "sha256": hashlib.sha256(payload).hexdigest(), "banner": banner, "build_seconds": 1,
        "recipe": {
            "cargo_config": "export's own .cargo/config.toml",
            "command": ["--unverified", "build", "--release", "--locked", *tool.build_args],
            "unverified_export": GATE.unverified_tool_export(b'[workspace]\n', tool.package)[1],
        },
    }


def fake_ay_repository(base: Path) -> tuple[Path, str]:
    """A git repository standing in for AY: a `.cargo/config.toml` with a
    Trust-lane block (build_tool preserves it), sources, and an executable file
    (its archive mode shows `tar.umask`). Returns it and its HEAD."""
    repo = base / "ay-source"
    (repo / ".cargo").mkdir(parents=True)
    (repo / ".cargo" / "config.toml").write_text(
        "[build]\njobs = 1\n# \u2500\u2500 BEGIN Trust lane config (fixture)\n[unstable]\nfixture = true\n"
        "# \u2500\u2500 END Trust lane config\n")
    (repo / "Cargo.toml").write_text('[package]\nname = "ay"\nversion = "0.27.0"\n')
    (repo / "src").mkdir()
    (repo / "src" / "main.rs").write_text("fn main() {}\n")
    (repo / "run.sh").write_text("#!/bin/sh\n")
    os.chmod(repo / "run.sh", 0o755)
    git = ["git", "-C", str(repo), "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
           "-c", "commit.gpgSign=false"]
    subprocess.run(["git", "init", "-q", str(repo)], check=True)
    subprocess.run(git + ["add", "-A"], check=True)
    subprocess.run(git + ["commit", "-q", "-m", "fixture ay"], check=True)
    rev = subprocess.run(["git", "-C", str(repo), "rev-parse", "HEAD"], capture_output=True, text=True,
                         check=True).stdout.strip()
    return repo, rev


def open_entries(root: Path) -> list[str]:
    """Every non-symlink entry below `root` with a group or other bit."""
    return [f"{mode(path):04o} {path.relative_to(root)}" for path in root.rglob("*")
            if not path.is_symlink() and mode(path) & 0o077]


def mode(path: Path) -> int:
    return stat.S_IMODE(os.lstat(path).st_mode)


@contextlib.contextmanager
def umask(value: int):
    previous = os.umask(value)
    try:
        yield
    finally:
        os.umask(previous)


def private_tmp() -> tempfile.TemporaryDirectory:
    """A scratch directory whose every ancestor passes AY's rule (mkdtemp
    makes it 0700 under the system temporary directory)."""
    return tempfile.TemporaryDirectory(prefix="private-cache-")


class RuleTests(unittest.TestCase):
    def mkdir_cli(self, path: Path, mask: int) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, "-I", str(HELPER), "mkdir", str(path)], capture_output=True,
                              text=True, umask=mask)

    def test_every_created_directory_is_0700_whatever_the_umask(self):
        with private_tmp() as temporary:
            base = Path(temporary)
            control = base / "control" / "nested"
            subprocess.run(["mkdir", "-p", str(control)], check=True, umask=0o002)
            self.assertEqual(mode(control), 0o775, "the control must run under umask 0002")
            for mask in (0o002, 0o022, 0o077, 0o277, 0o477, 0o000):
                with self.subTest(umask=oct(mask)):
                    top = base / f"u{mask:o}"
                    tree = top / "cache" / "trust-cg" / "soundness-deps"
                    result = self.mkdir_cli(tree, mask)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    for created in (top, top / "cache", top / "cache" / "trust-cg", tree):
                        self.assertEqual(mode(created), 0o700, created)

    def test_an_existing_directory_is_never_changed(self):
        with private_tmp() as temporary:
            base = Path(temporary)
            for existing_mode in (0o775, 0o755, 0o500):
                with self.subTest(mode=oct(existing_mode)):
                    existing = base / f"existing-{existing_mode:o}"
                    existing.mkdir()
                    os.chmod(existing, existing_mode)
                    result = self.mkdir_cli(existing, 0o002)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(mode(existing), existing_mode)
            shared = base / "existing-775"
            result = self.mkdir_cli(shared / "trust-cg" / "ay-cli", 0o002)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(mode(shared), 0o775, "an existing ancestor is never changed")
            self.assertEqual(mode(shared / "trust-cg"), 0o700)
            self.assertEqual(mode(shared / "trust-cg" / "ay-cli"), 0o700)
            # A symlink to a directory is an existing directory, as for
            # `mkdir -p` and private_fs.
            link = base / "link"
            link.symlink_to(shared / "trust-cg")
            self.assertFalse(PC.create_private_dir_all(link))
            self.assertTrue(PC.create_private_dir_all(link / "below"))
            self.assertEqual(mode(shared / "trust-cg" / "below"), 0o700)

    def test_reports_whether_this_call_created_the_leaf(self):
        with private_tmp() as temporary:
            leaf = Path(temporary, "a", "b", "store")
            self.assertTrue(PC.create_private_dir_all(leaf))
            self.assertFalse(PC.create_private_dir_all(leaf))
            self.assertFalse(PC.create_private_dir_all(str(leaf) + "/"))

    def test_a_set_group_id_parent_does_not_pass_its_bit_on(self):
        with private_tmp() as temporary:
            shared = Path(temporary, "setgid")
            shared.mkdir()
            os.chmod(shared, 0o2770)
            if mode(shared) != 0o2770:
                self.skipTest("this file system does not keep the set-group-ID bit on a directory")
            below = shared / "x" / "y"
            self.assertEqual(self.mkdir_cli(below, 0o002).returncode, 0)
            self.assertEqual(mode(shared / "x"), 0o700)
            self.assertEqual(mode(below), 0o700)
            self.assertEqual(mode(shared), 0o2770, "an existing directory is never changed")

    def test_a_new_directory_that_cannot_be_made_private_is_an_error_and_removed(self):
        with private_tmp() as temporary:
            tree = Path(temporary, "a", "b")
            with umask(0o277), mock.patch.object(PC, "private_umask", contextlib.nullcontext), \
                    mock.patch.object(PC.os, "fchmod", side_effect=OSError(95, "Operation not supported")):
                with self.assertRaises(PC.NotPrivateError) as raised:
                    PC.create_private_dir_all(tree)
            self.assertIsNone(raised.exception.errno)
            self.assertIn("cannot make it 0700", str(raised.exception))
            self.assertFalse(Path(temporary, "a").exists(), "the unsettled directory is removed")
            # Without the injected failure the same creation succeeds.
            PC.create_private_dir_all(tree)
            self.assertEqual(mode(tree), 0o700)

    def test_a_file_in_the_way_is_refused_and_nothing_is_created(self):
        with private_tmp() as temporary:
            blocker = Path(temporary, "file")
            blocker.write_text("x")
            with self.assertRaises(OSError):
                PC.create_private_dir_all(blocker)
            with self.assertRaises(OSError):
                PC.create_private_dir_all(blocker / "below")
            self.assertEqual(self.mkdir_cli(blocker / "below", 0o002).returncode, 1)

    def test_files_are_0600_even_when_the_umask_clears_owner_bits(self):
        """`open(..., 0600)` can only clear bits of the requested mode, so
        under a umask that clears an owner bit (0277: 0400, 0477: 0200) the
        new file is not 0600 until create_private_file sets the mode on its
        descriptor; without that `fchmod` a lock file opened read-write is
        refused (EACCES) and a record is unreadable or unwritable. Pins the
        `fchmod` (X-HOST-P13 second audit: its mutant survived every suite)."""
        with private_tmp() as temporary:
            base = Path(temporary)
            for mask in (0o277, 0o477, 0o377, 0o002, 0o077):
                with self.subTest(umask=oct(mask)):
                    with umask(mask):
                        PC.write_private_file(base / f"record-{mask:o}.json", "{}\n")
                        os.close(PC.open_lock_file(base / f"held-{mask:o}.lock"))
                        os.close(PC.create_private_file(base / f"raw-{mask:o}"))
                    for name in (f"record-{mask:o}.json", f"held-{mask:o}.lock", f"raw-{mask:o}"):
                        self.assertEqual(mode(base / name), 0o600, name)
                    self.assertEqual((base / f"record-{mask:o}.json").read_text(), "{}\n")

    def test_files_are_created_exclusively_0600_and_locks_never_change(self):
        with private_tmp() as temporary, umask(0o002):
            base = Path(temporary)
            PC.write_private_file(base / "record.json", "{}\n")
            self.assertEqual(mode(base / "record.json"), 0o600)
            with self.assertRaises(FileExistsError):
                PC.create_private_file(base / "record.json")
            (base / "link").symlink_to(base / "elsewhere")
            with self.assertRaises(FileExistsError):
                PC.create_private_file(base / "link")
            self.assertFalse((base / "elsewhere").exists(), "never created through a symlink")
            os.close(PC.open_lock_file(base / "new.lock"))
            self.assertEqual(mode(base / "new.lock"), 0o600)
            (base / "old.lock").write_text("held")
            self.assertEqual(mode(base / "old.lock"), 0o664)
            os.close(PC.open_lock_file(base / "old.lock"))
            self.assertEqual(mode(base / "old.lock"), 0o664, "an existing lock is opened as it is")
            self.assertEqual((base / "old.lock").read_text(), "held", "and never truncated")

    def test_the_checks_are_the_private_fs_checks(self):
        with private_tmp() as temporary:
            base = Path(temporary)
            store = base / "parent" / "store"
            PC.create_private_dir_all(store)
            self.assertEqual(PC.canonical_owner_private_directory(store), os.path.realpath(store))
            for ancestor_mode in (0o777, 0o770, 0o775):
                os.chmod(base / "parent", ancestor_mode)
                with self.assertRaises(PermissionError) as raised:
                    PC.canonical_owner_private_directory(store)
                self.assertIn(f"mode {ancestor_mode:04o}", str(raised.exception))
                self.assertEqual(mode(base / "parent"), ancestor_mode, "never repaired")
            os.chmod(base / "parent", 0o1777)
            PC.canonical_owner_private_directory(store)
            os.chmod(store, 0o720)
            with self.assertRaises(PermissionError):
                PC.check_owner_private(store, True)
            os.chmod(store, 0o755)
            PC.check_owner_private(store, True)
            key = store / "key"
            PC.write_private_file(key, b"x")
            PC.check_owner_private(key, False)
            for file_mode in (0o640, 0o604, 0o620):
                os.chmod(key, file_mode)
                with self.assertRaises(PermissionError):
                    PC.check_owner_private(key, False)
            os.chmod(key, 0o500)
            PC.check_owner_private(key, False)
            (store / "alias").symlink_to(key)
            with self.assertRaises(PermissionError):
                PC.check_owner_private(store / "alias", False)

    def test_the_write_only_check_allows_read_and_execute_bits(self):
        """`check_owner_only_writable` refuses exactly what another user could
        change: a group/other write bit, another owner, a symlink. A 0555
        binary or a 0644 record in a 0755 directory passes; `check_owner_private`
        refuses a group-readable file and says so."""
        with private_tmp() as temporary:
            base = Path(temporary)
            slot = base / "slot"
            PC.create_private_dir_all(slot)
            entry = slot / "ay"
            PC.write_private_file(entry, b"x")
            for allowed in (0o555, 0o644, 0o500, 0o755):
                os.chmod(entry, allowed)
                PC.check_owner_only_writable(entry, False)
            os.chmod(slot, 0o755)
            PC.check_owner_only_writable(slot, True)
            for refused in (0o664, 0o646, 0o775, 0o757):
                with self.subTest(mode=oct(refused)):
                    os.chmod(entry, refused)
                    with self.assertRaises(PermissionError) as raised:
                        PC.check_owner_only_writable(entry, False)
                    self.assertIn(f"has mode {refused:04o}; another user could replace its contents",
                                  str(raised.exception))
            os.chmod(slot, 0o775)
            with self.assertRaises(PermissionError):
                PC.check_owner_only_writable(slot, True)
            os.chmod(slot, 0o700)
            os.chmod(entry, 0o640)
            with self.assertRaises(PermissionError) as raised:
                PC.check_owner_private(entry, False)
            self.assertIn("has mode 0640; another user could read it", str(raised.exception))
            (slot / "alias").symlink_to(entry)
            with self.assertRaises(PermissionError):
                PC.check_owner_only_writable(slot / "alias", False)
            (base / "alias-dir").symlink_to(slot)
            with self.assertRaises(PermissionError):
                PC.check_owner_only_writable(base / "alias-dir", True)

    def test_an_inherited_default_acl_is_removed_from_each_created_directory(self):
        """A default POSIX ACL overrides the umask for whatever is created
        below it, so git, tar and cargo running under umask 077 below a
        directory that inherited one still wrote group-writable entries. Each
        directory the helper creates drops the default ACL it inherited; an
        existing directory keeps its own."""
        setfacl = shutil.which("setfacl")
        if setfacl is None or not hasattr(os, "getxattr"):
            self.skipTest("no setfacl or no extended-attribute calls on this host")
        with private_tmp() as temporary:
            base = Path(temporary, "base")
            base.mkdir(mode=0o700)
            os.chmod(base, 0o700)
            acl = subprocess.run([setfacl, "-d", "-m", "u::rwx,g::rwx,o::rx", str(base)], capture_output=True,
                                 text=True)
            if acl.returncode != 0:
                self.skipTest(f"this file system keeps no default ACL: {acl.stderr.strip()}")
            control = base / "control"
            subprocess.run(["mkdir", str(control)], check=True, umask=0o077)
            self.assertEqual(mode(control), 0o775, "the control: the default ACL overrides umask 077")
            tree = base / "trust-cg" / "soundness-deps"
            result = self.mkdir_cli(tree, 0o002)
            self.assertEqual(result.returncode, 0, result.stderr)
            for created in (base / "trust-cg", tree):
                self.assertEqual(mode(created), 0o700, created)
                with self.assertRaises(OSError) as raised:
                    os.getxattr(created, PC.DEFAULT_ACL_ATTRIBUTE)
                self.assertIn(raised.exception.errno, PC.NO_DEFAULT_ACL_ERRNOS, created)
            self.assertTrue(os.getxattr(base, PC.DEFAULT_ACL_ATTRIBUTE), "an existing directory keeps its ACL")
            checkout = tree / "checkout"
            subprocess.run(["sh", "-c", 'mkdir -p "$1/src" && : > "$1/src/file"', "_", str(checkout)], check=True,
                           umask=0o077)
            for entry, expected in ((checkout, 0o700), (checkout / "src", 0o700), (checkout / "src" / "file", 0o600)):
                self.assertEqual(mode(entry), expected, entry)

    def test_the_cache_base_is_the_xdg_rule_trust_cg_resolves_by(self):
        """`user_cache_base` is trust_cg_process_env::private_fs::user_cache_base
        for scripts, row for row (the Rust table in private_fs.rs has the same
        rows and refusal texts): an absolute XDG_CACHE_HOME wins; an empty or
        relative one is ignored, as the XDG Base Directory specification
        requires; then an absolute HOME's .cache; else no cache. Nothing
        depends on the working directory."""
        refused_home = "HOME={} is not absolute and XDG_CACHE_HOME names no absolute directory"
        neither = "neither XDG_CACHE_HOME nor HOME names an absolute directory"
        rows = [
            ({"XDG_CACHE_HOME": "/xdg", "HOME": "/home/u"}, "/xdg"),
            ({"XDG_CACHE_HOME": "/xdg"}, "/xdg"),
            ({"XDG_CACHE_HOME": "", "HOME": "/home/u"}, "/home/u/.cache"),
            ({"XDG_CACHE_HOME": "relative", "HOME": "/home/u"}, "/home/u/.cache"),
            ({"XDG_CACHE_HOME": " /padded", "HOME": "/home/u"}, "/home/u/.cache"),
            ({"HOME": "/home/u"}, "/home/u/.cache"),
            ({"XDG_CACHE_HOME": "relative", "HOME": "relative-home"}, ValueError(refused_home.format("relative-home"))),
            ({"XDG_CACHE_HOME": "", "HOME": ""}, ValueError(refused_home.format(""))),
            ({"XDG_CACHE_HOME": "relative"}, ValueError(neither)),
            ({}, ValueError(neither)),
        ]
        with private_tmp() as temporary:
            for environ, expected in rows:
                with self.subTest(environ=environ):
                    if isinstance(expected, ValueError):
                        with self.assertRaises(ValueError) as raised:
                            PC.user_cache_base(environ)
                        self.assertEqual(str(raised.exception), str(expected))
                    else:
                        self.assertEqual(PC.user_cache_base(environ), expected)
                    cli = subprocess.run([sys.executable, "-I", str(HELPER), "cache-base"], capture_output=True,
                                         text=True, env=dict(environ, PATH=os.environ.get("PATH", "")),
                                         cwd=temporary)
                    if isinstance(expected, ValueError):
                        self.assertEqual(cli.returncode, 1)
                        self.assertEqual(cli.stderr.strip(), f"private_cache: no user cache: {expected}")
                    else:
                        self.assertEqual((cli.returncode, cli.stdout), (0, expected + "\n"), cli.stderr)

    def test_require_private_refuses_what_another_user_could_change(self):
        """`require_private` (the soundness gate's `require-private`): a
        directory by the ancestor rule, a file also by the owner-only-writable
        rule, a symlinked file never; refusals name the entry and its mode
        and change nothing."""
        with private_tmp() as temporary:
            base = Path(temporary)
            release = base / "deps" / "clean-x" / "target" / "release"
            PC.create_private_dir_all(release)
            binary = release / "clean"
            PC.write_private_file(binary, b"#!/bin/sh\n")
            os.chmod(binary, 0o755)
            self.assertEqual(PC.require_private(release), os.path.realpath(release))
            self.assertEqual(PC.require_private(binary), os.path.join(os.path.realpath(release), "clean"))
            cases = [
                (base / "deps", 0o775, release, "is not a trusted directory ancestor"),
                (base / "deps", 0o757, binary, "is not a trusted directory ancestor"),
                (release, 0o770, release, "has mode 0770; another user could replace its contents"),
                (release, 0o775, binary, "has mode 0775; another user could replace its contents"),
                (binary, 0o775, binary, "has mode 0775; another user could replace its contents"),
                (binary, 0o757, binary, "has mode 0757; another user could replace its contents"),
            ]
            for loosened, loose, checked, why in cases:
                with self.subTest(loosened=loosened.name, mode=oct(loose), checked=checked.name):
                    before = mode(loosened)
                    os.chmod(loosened, loose)
                    try:
                        with self.assertRaises(PermissionError) as raised:
                            PC.require_private(checked)
                        self.assertIn(why, str(raised.exception))
                        self.assertIn(f"{loose:04o}", str(raised.exception))
                        cli = subprocess.run([sys.executable, "-I", str(HELPER), "require-private", str(checked)],
                                             capture_output=True, text=True)
                        self.assertEqual(cli.returncode, 1)
                        self.assertIn(f"private_cache: refusing {checked}: ", cli.stderr)
                        self.assertIn(PC.PRIVATE_REMEDY, cli.stderr)
                        self.assertEqual(mode(loosened), loose, "never repaired")
                    finally:
                        os.chmod(loosened, before)
            # A sticky shared ancestor (as /tmp is) is allowed, as for AY.
            os.chmod(base / "deps", 0o1777)
            PC.require_private(binary)
            os.chmod(base / "deps", 0o700)
            alias = release / "alias"
            alias.symlink_to(binary)
            with self.assertRaises(PermissionError):
                PC.require_private(alias)
            self.assertEqual(subprocess.run([sys.executable, "-I", str(HELPER), "require-private", str(base / "gone")],
                                            capture_output=True, text=True).returncode, 1)
            ok = subprocess.run([sys.executable, "-I", str(HELPER), "require-private", str(release), str(binary)],
                                capture_output=True, text=True)
            # The canonical path of each, one per line: what the caller uses.
            canonical = os.path.realpath(release)
            self.assertEqual((ok.returncode, ok.stdout, ok.stderr),
                             (0, f"{canonical}\n{os.path.join(canonical, 'clean')}\n", ""))

    def test_require_private_checks_and_prints_the_canonical_path(self):
        """X-HOST-P13 third closure audit: the rule judges the CANONICAL path,
        and the soundness gate then ran Clean by the name it was given, which
        led there through `<shared 0777>/link`; another user re-pointed the
        link after the check. `require_private` returns (and the CLI prints)
        the canonical path, which names the very entries the checks examined:
        a file is checked by its name in the canonical directory. A real
        directory inside the open directory is refused, and so is a
        canonical path the one-per-line output cannot carry whole."""
        with private_tmp() as temporary:
            base = Path(os.path.realpath(temporary))
            release = base / "real" / "release"
            PC.create_private_dir_all(release)
            binary = release / "clean"
            PC.write_private_file(binary, b"#!/bin/sh\n")
            os.chmod(binary, 0o755)
            shared = base / "shared"
            shared.mkdir()
            os.chmod(shared, 0o777)
            link = shared / "link"
            link.symlink_to(base / "real")
            self.assertEqual(PC.require_private(link / "release" / "clean"), str(binary))
            self.assertEqual(PC.require_private(link / "release"), str(release))
            cli = subprocess.run([sys.executable, "-I", str(HELPER), "require-private",
                                  str(link / "release" / "clean")], capture_output=True, text=True)
            self.assertEqual((cli.returncode, cli.stdout, cli.stderr), (0, f"{binary}\n", ""))
            # A file is judged by its canonical name: the loose canonical file
            # is refused under that name, whatever name led to it.
            os.chmod(binary, 0o775)
            with self.assertRaises(PermissionError) as raised:
                PC.require_private(link / "release" / "clean")
            self.assertIn(f"{binary} has mode 0775", str(raised.exception))
            os.chmod(binary, 0o755)
            # The control: a real directory inside the open directory.
            direct = shared / "direct"
            PC.create_private_dir_all(direct)
            with self.assertRaises(PermissionError) as raised:
                PC.require_private(direct)
            self.assertIn(f"{shared} is not a trusted directory ancestor", str(raised.exception))
            # A canonical path the line protocol cannot carry whole.
            newline = base / "new\nline"
            PC.create_private_dir_all(newline)
            self.assertEqual(PC.require_private(newline), str(newline))
            cli = subprocess.run([sys.executable, "-I", str(HELPER), "require-private", str(newline)],
                                 capture_output=True, text=True)
            self.assertEqual((cli.returncode, cli.stdout), (1, ""))
            self.assertIn("its canonical path holds a newline", cli.stderr)

    def test_require_private_tree_judges_every_entry_of_the_tree(self):
        """X-HOST-P13 fourth closure audit: the soundness gate judged only its
        pinned Clean checkout's root, and another user rewrote a proof file
        Clean read in a `0775` subdirectory mid-run. `require_private_tree`
        (the gate's `require-private-tree`) judges the root as
        `require_private` does and then every entry below it: a directory or
        file another user could write, a symlink leading out of the tree and
        a FIFO are each refused by name with the remedy to remove the tree
        (an entry another user owns is refused too; this unprivileged test
        cannot create one); a symlink inside the tree is judged by its
        target. Nothing is changed, and the canonical root is returned."""
        with private_tmp() as temporary:
            base = Path(os.path.realpath(temporary))
            checkout = base / "deps" / "clean-x"
            proofs = checkout / "proofs"
            release = checkout / "target" / "release"
            for directory in (proofs, release):
                PC.create_private_dir_all(directory)
            proof = proofs / "lrat_checker_tree.lean"
            PC.write_private_file(proof, b"-- pinned\n")
            os.chmod(proof, 0o644)
            binary = release / "clean"
            PC.write_private_file(binary, b"#!/bin/sh\n")
            os.chmod(binary, 0o755)
            (checkout / "proofs-link").symlink_to(proofs)
            self.assertEqual(PC.require_private_tree(checkout), str(checkout))
            cases = [
                (proofs, 0o775, "has mode 0775; another user could replace its contents"),
                (proofs, 0o757, "has mode 0757; another user could replace its contents"),
                (proof, 0o664, "has mode 0664; another user could replace its contents"),
                (release, 0o770, "has mode 0770; another user could replace its contents"),
                (binary, 0o775, "has mode 0775; another user could replace its contents"),
                (checkout, 0o775, "has mode 0775; another user could replace its contents"),
                (base / "deps", 0o775, "is not a trusted directory ancestor"),
            ]
            for loosened, loose, why in cases:
                with self.subTest(loosened=loosened.name, mode=oct(loose)):
                    before = mode(loosened)
                    os.chmod(loosened, loose)
                    try:
                        with self.assertRaises(PermissionError) as raised:
                            PC.require_private_tree(checkout)
                        self.assertIn(f"{loosened} {why}" if "has mode" in why else why, str(raised.exception))
                        # An entry of the tree: remove the tree; a directory
                        # above it: make that directory private.
                        in_tree = "ancestor" not in why
                        self.assertEqual(isinstance(raised.exception, PC.UntrustedTreeError), in_tree)
                        cli = subprocess.run([sys.executable, "-I", str(HELPER), "require-private-tree",
                                              str(checkout)], capture_output=True, text=True)
                        self.assertEqual((cli.returncode, cli.stdout), (1, ""))
                        self.assertIn(f"private_cache: refusing {checkout}: ", cli.stderr)
                        self.assertIn(PC.TREE_REMEDY if in_tree else PC.PRIVATE_REMEDY, cli.stderr)
                        self.assertEqual(mode(loosened), loose, "never repaired")
                    finally:
                        os.chmod(loosened, before)
            outside = base / "outside.lean"
            PC.write_private_file(outside, b"-- elsewhere\n")
            escape = proofs / "escape.lean"
            escape.symlink_to(outside)
            with self.assertRaises(PermissionError) as raised:
                PC.require_private_tree(checkout)
            self.assertIn(f"{escape} is a symlink to {str(outside)!r}, whose resolution leaves the tree",
                          str(raised.exception))
            escape.unlink()
            fifo = proofs / "fifo"
            os.mkfifo(fifo, 0o600)
            with self.assertRaises(PermissionError) as raised:
                PC.require_private_tree(checkout)
            self.assertIn(f"{fifo} is neither a directory, a regular file nor a symlink", str(raised.exception))
            fifo.unlink()
            # The canonical root, through a symlink in a directory others can
            # write: the tree is judged and named where the link leads.
            shared = base / "shared"
            shared.mkdir()
            os.chmod(shared, 0o777)
            (shared / "link").symlink_to(checkout)
            self.assertEqual(PC.require_private_tree(shared / "link"), str(checkout))
            ok = subprocess.run([sys.executable, "-I", str(HELPER), "require-private-tree", str(shared / "link")],
                                capture_output=True, text=True)
            self.assertEqual((ok.returncode, ok.stdout, ok.stderr), (0, f"{checkout}\n", ""))

    def test_require_private_tree_refuses_an_acl_that_lets_another_user_write(self):
        """X-HOST-P13 round-4 verifier (acl_probe.py): a pinned checkout with
        a default ACL naming another uid kept mode 0700, so the mode-bit rule
        accepted it before the build, and what the build then created there
        under umask 077 took the ACL's grant until the check after the build
        refused it. `require_private_tree` now also refuses, by name and with
        the remedy to remove the tree, a default ACL of the root or of any
        directory below it that lets anyone but this user write what is
        created there (a named user, any group whoever its members are, or
        every user), read by scripts/host_boundary.py's ACL reader. A default
        ACL whose mask holds no write, or that grants only this user, passes.
        An access ACL that grants write shows in the group bits (its mask),
        which the mode rule already refuses."""
        setfacl = shutil.which("setfacl")
        if setfacl is None or not hasattr(os, "getxattr"):
            self.skipTest("no setfacl or no extended-attribute calls on this host")
        with private_tmp() as temporary:
            base = Path(os.path.realpath(temporary))
            checkout = base / "deps" / "clean-x"
            source = checkout / "src"
            PC.create_private_dir_all(source)
            PC.write_private_file(source / "lib.rs", b"// pinned\n")
            self.assertEqual(PC.require_private_tree(checkout), str(checkout))
            probe = subprocess.run([setfacl, "-d", "-m", "u:4242:rwx", str(checkout)], capture_output=True, text=True)
            if probe.returncode != 0:
                self.skipTest(f"setfacl failed: {probe.stderr}")
            subprocess.run([setfacl, "-k", str(checkout)], check=True)
            cases = [
                (checkout, "u:4242:rwx", f"{checkout}: its default ACL lets uid 4242 write what is created in it"),
                (source, "u:4242:w", f"{source}: its default ACL lets uid 4242 write what is created in it"),
                (source, "g::rwx", f"{source}: its default ACL lets gid {os.getegid()} write what is created in it, "
                                   "and no group may write here (the strict rule of trust-cg's caches)"),
                (source, "o::rwx", f"{source}: its default ACL lets every user write what is created in it"),
                (source, "u:4242:rwx,m::rx", None),
                (source, f"u:{os.geteuid()}:rwx", None),
            ]
            for directory, entries, why in cases:
                with self.subTest(directory=directory.name, acl=entries):
                    subprocess.run([setfacl, "-d", "-m", entries, str(directory)], check=True)
                    try:
                        self.assertEqual(mode(directory), 0o700, "the mode bits show nothing")
                        if why is None:
                            self.assertEqual(PC.require_private_tree(checkout), str(checkout))
                            continue
                        with self.assertRaises(PC.UntrustedTreeError) as raised:
                            PC.require_private_tree(checkout)
                        self.assertEqual(raised.exception.strerror, why)
                        cli = subprocess.run([sys.executable, "-I", "-B", str(HELPER), "require-private-tree",
                                              str(checkout)], capture_output=True, text=True)
                        self.assertEqual((cli.returncode, cli.stdout), (1, ""))
                        self.assertIn(f"private_cache: refusing {checkout}: {why}; {PC.TREE_REMEDY}", cli.stderr)
                    finally:
                        subprocess.run([setfacl, "-k", str(directory)], check=True)
            # What the probe then showed: an entry created under umask 077 in
            # such a directory takes the grant, and the mode rule sees it.
            subprocess.run([setfacl, "-d", "-m", "u:4242:rwx", str(source)], check=True)
            with umask(0o077):
                os.close(os.open(source / "build-script-build", os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o777))
            self.assertEqual(mode(source / "build-script-build") & 0o070, 0o070)
            self.assertEqual(mode(source), 0o700, "never changed")

    def test_a_symlink_is_judged_hop_by_hop_through_its_literal_target(self):
        """X-HOST-P13 fifth closure audit: a symlink was judged by where it
        resolved at check time, so a link whose literal path left the tree
        through a directory others can write, and came back inside, passed;
        re-pointing that outside hop afterwards made the same in-tree name
        read a file outside the tree. Every hop of the literal target is now
        walked and must stay inside the tree: what stays inside (a relative
        link such as AY's `crates/ay/LICENSE -> ../../LICENSE`, an absolute
        one spelled with the canonical root, a chain of in-tree links, a
        dangling in-tree name) passes; a link whose resolution leaves the
        tree at any hop is refused even when it ends inside, and so is a
        loop. Nothing is changed."""
        with private_tmp() as temporary:
            base = Path(os.path.realpath(temporary))
            checkout = base / "deps" / "clean-x"
            proofs = checkout / "proofs"
            crate = checkout / "crates" / "ay"
            for directory in (proofs, crate):
                PC.create_private_dir_all(directory)
            real = proofs / "real.lean"
            PC.write_private_file(real, b"-- pinned\n")
            PC.write_private_file(checkout / "LICENSE", b"license\n")
            (crate / "LICENSE").symlink_to("../../LICENSE")
            (proofs / "absolute.lean").symlink_to(real)
            (proofs / "first.lean").symlink_to("second.lean")
            (proofs / "second.lean").symlink_to("../proofs/real.lean")
            (checkout / "proofs-dir").symlink_to("proofs")
            (proofs / "through-dir.lean").symlink_to("../proofs-dir/real.lean")
            (proofs / "dangling.lean").symlink_to("not-yet.lean")
            self.assertEqual(PC.require_private_tree(checkout), str(checkout))

            shared = base / "shared"
            shared.mkdir()
            os.chmod(shared, 0o777)
            (shared / "hop").symlink_to(proofs)
            # An in-tree link to the root itself stays inside.
            (checkout / "root").symlink_to(".")
            self.assertEqual(PC.require_private_tree(checkout), str(checkout))
            outside = base / "outside.lean"
            PC.write_private_file(outside, b"-- elsewhere\n")
            # Each case: the links it adds, and the link the refusal names
            # (None: a chain whose every link is refused on its own).
            refused = [
                # The audit's case: absolute, out through the open directory
                # and back in; its realpath is inside the tree.
                ([(proofs / "checked.lean", str(shared / "hop" / "real.lean"))], proofs / "checked.lean"),
                # Out through the tree's parent and back in by name.
                ([(proofs / "back.lean", "../../clean-x/proofs/real.lean")], proofs / "back.lean"),
                # An in-tree link to the root, then `..` above it.
                ([(proofs / "above.lean", "../root/../clean-x/proofs/real.lean")], proofs / "above.lean"),
                # Inside first, then a link that leaves.
                ([(proofs / "chain-out.lean", "later"), (proofs / "later", str(outside))], None),
                ([(proofs / "loop-a", "loop-b"), (proofs / "loop-b", "loop-a")], None),
            ]
            for links, named in refused:
                with self.subTest(link=links[0][0].name):
                    for link, target in links:
                        link.symlink_to(target)
                    try:
                        if named is None:
                            for link, _ in links:
                                self.assertFalse(PC._symlink_stays_in_tree(str(checkout), str(link)), link)
                        with self.assertRaises(PC.UntrustedTreeError) as raised:
                            PC.require_private_tree(checkout)
                        if named is None:
                            self.assertIn("whose resolution leaves the tree", str(raised.exception))
                        else:
                            self.assertIn(f"{named} is a symlink to {os.readlink(named)!r}, whose resolution "
                                          "leaves the tree", str(raised.exception))
                            # Where it resolved at the check was inside the
                            # tree: the realpath rule this replaces passed it.
                            self.assertTrue(os.path.realpath(named).startswith(str(checkout) + os.sep), named)
                        cli = subprocess.run([sys.executable, "-I", str(HELPER), "require-private-tree",
                                              str(checkout)], capture_output=True, text=True)
                        self.assertEqual((cli.returncode, cli.stdout), (1, ""))
                        self.assertIn(PC.TREE_REMEDY, cli.stderr)
                    finally:
                        for link, _ in links:
                            link.unlink()
            self.assertEqual(PC.require_private_tree(checkout), str(checkout))
            self.assertEqual(mode(real), 0o600, "never changed")

    def test_the_source_runs_as_python3_dash_c(self):
        # soundness_remote.sh runs this source with `python3 -I -c` on the
        # x86-64 executor, which has no checkout of its own yet.
        with private_tmp() as temporary:
            tree = Path(temporary, "home", ".cache", "trust-cg", "soundness-remote", "incoming")
            result = subprocess.run([sys.executable, "-I", "-c", HELPER.read_text(), "mkdir", str(tree)],
                                    capture_output=True, text=True, umask=0o002)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(mode(tree.parent.parent), 0o700)
            self.assertEqual(mode(tree), 0o700)
            usage = subprocess.run([sys.executable, "-I", str(HELPER)], capture_output=True, text=True)
            self.assertEqual(usage.returncode, 2)


class SoundnessDependencyCheckoutTests(unittest.TestCase):
    def test_pinned_checkouts_under_umask_0002_keep_the_cache_private(self):
        """The audit's reproducer: `soundness_check.sh --attest
        --preflight-only` under umask 0002 with a fresh XDG_CACHE_HOME and
        SOUNDNESS_DEPS_DIR at its default made <cache>/trust-cg,
        soundness-deps and each pinned checkout 0775."""
        directory = fixture.FixtureDirectory("private-cache-deps-")
        self.addCleanup(directory.cleanup)
        world = fixture.Constellation(Path(directory.name))
        cache = Path(directory.name, "xdg-cache")
        cache.mkdir(mode=0o700)
        os.chmod(cache, 0o700)
        result = world.run_gate("--attest", "--preflight-only", umask=0o002, SOUNDNESS_DEPS_DIR=None,
                                XDG_CACHE_HOME=str(cache))
        self.assertEqual(result.returncode, 0, result.stdout[-3000:])
        deps = cache / "trust-cg" / "soundness-deps"
        checkouts = [deps / f"clean-{world.clean_rev}", deps / f"ay-{world.ay_rev}"]
        # The checkout is named by its canonical path (the one the rule judged).
        self.assertIn(f"pinned worktree {os.path.realpath(checkouts[0])}", result.stdout)
        for created in (cache / "trust-cg", deps, *checkouts):
            self.assertEqual(mode(created), 0o700, created)
        for checkout in checkouts:
            entries = list(checkout.rglob("*"))
            self.assertTrue(entries)
            for entry in entries:
                self.assertEqual(mode(entry) & 0o077, 0, entry)
        self.assertEqual(mode(cache), 0o700, "an existing directory is never changed")
        PC.canonical_owner_private_directory(deps)

    def private_cache_world(self, prefix: str) -> tuple[fixture.Constellation, Path]:
        directory = fixture.FixtureDirectory(prefix)
        self.addCleanup(directory.cleanup)
        world = fixture.Constellation(Path(directory.name))
        cache = Path(directory.name, "xdg-cache")
        cache.mkdir(mode=0o700)
        os.chmod(cache, 0o700)
        return world, cache

    def test_an_existing_directory_others_can_write_is_refused_before_anything_is_written(self):
        """X-HOST-P13 second audit: with a pre-existing world-writable
        <cache>/trust-cg and soundness-deps the attested gate checked Clean
        out, built it and ran every clean-check leg below them, green. The
        dependency directory is now held to the rule the icmp gate holds its
        AY cache to: refused by name with its mode and the remedy, before any
        checkout is written into it, and never changed. A <cache>/trust-cg
        every user can write is refused even earlier, at the host trust
        boundary, since another user could create the `.cargo` Cargo reads
        there (LD-75); nothing runs then."""
        world, cache = self.private_cache_world("private-cache-loose-")
        trust_cg = cache / "trust-cg"
        deps = trust_cg / "soundness-deps"
        for loose, at in ((0o777, trust_cg), (0o775, deps), (0o770, deps), (0o757, trust_cg), (0o775, trust_cg)):
            with self.subTest(mode=oct(loose), at=at.name):
                deps.mkdir(parents=True, exist_ok=True)
                os.chmod(trust_cg, 0o700)
                os.chmod(deps, 0o700)
                os.chmod(at, loose)
                result = world.run_gate("--attest", "--preflight-only", umask=0o002, SOUNDNESS_DEPS_DIR=None,
                                        XDG_CACHE_HOME=str(cache))
                self.assertNotEqual(result.returncode, 0, result.stdout[-3000:])
                named = os.path.realpath(at)
                if loose & 0o002:
                    self.assertIn(f"host_boundary: REFUSED {named} (Cargo's configuration search above the user "
                                  f"cache's trust-cg directory): writable by every user (mode {loose:04o})",
                                  result.stdout)
                    self.assertEqual(world.workloads(), [], "nothing ran after the boundary refused")
                else:
                    # Group-writable in this host's private group: the host
                    # boundary passes it, and the cache rule refuses it.
                    self.assertIn("refusing the candidate's clean checkout under", result.stdout)
                    self.assertIn(f"{named} is not a trusted directory ancestor (uid {os.geteuid()}, mode "
                                  f"{loose:04o})" if at == trust_cg else f"{named} has mode {loose:04o}", result.stdout)
                self.assertIn("chmod go-w", result.stdout)
                self.assertEqual(mode(at), loose, "never repaired")
                self.assertEqual(sorted(path.name for path in deps.iterdir()), [], "nothing written into it")

    def test_an_existing_checkout_others_can_write_is_refused(self):
        world, cache = self.private_cache_world("private-cache-loose-checkout-")
        first = world.run_gate("--attest", "--preflight-only", umask=0o002, SOUNDNESS_DEPS_DIR=None,
                               XDG_CACHE_HOME=str(cache))
        self.assertEqual(first.returncode, 0, first.stdout[-3000:])
        checkout = cache / "trust-cg" / "soundness-deps" / f"clean-{world.clean_rev}"
        os.chmod(checkout, 0o775)
        result = world.run_gate("--attest", "--preflight-only", umask=0o002, SOUNDNESS_DEPS_DIR=None,
                                XDG_CACHE_HOME=str(cache))
        self.assertNotEqual(result.returncode, 0, result.stdout[-3000:])
        canonical = os.path.realpath(checkout)
        self.assertIn(f"refusing {canonical}: {canonical} has mode 0775", result.stdout)
        self.assertEqual(mode(checkout), 0o775)

    def test_a_clean_binary_beneath_a_directory_others_can_write_is_never_run(self):
        """The binary the attestation's Clean legs run is built below the
        pinned checkout; a target directory an earlier build left
        group-writable (which the umask-077 build does not change) lets
        another user replace it between the build and the checks, or plant
        what the build reads. The whole checkout is judged before it is used
        (X-HOST-P13 fourth closure audit), so the gate refuses it at
        preflight: nothing is built and no Clean check runs."""
        world, cache = self.private_cache_world("private-cache-loose-target-")
        first = world.run_gate("--attest", "--preflight-only", umask=0o002, SOUNDNESS_DEPS_DIR=None,
                               XDG_CACHE_HOME=str(cache))
        self.assertEqual(first.returncode, 0, first.stdout[-3000:])
        release = cache / "trust-cg" / "soundness-deps" / f"clean-{world.clean_rev}" / "target" / "release"
        release.mkdir(parents=True)
        os.chmod(release.parent, 0o700)
        os.chmod(release, 0o775)
        result = world.run_gate("--attest", umask=0o002, SOUNDNESS_DEPS_DIR=None, XDG_CACHE_HOME=str(cache))
        self.assertNotEqual(result.returncode, 0, result.stdout[-3000:])
        self.assertRegex(result.stdout, r"preflight: clean checkout[^\n]*refusing the candidate's clean checkout "
                                        r"under [^\n]*" + re.escape(f"{os.path.realpath(release)} has mode 0775"))
        self.assertIn(PC.TREE_REMEDY, result.stdout)
        self.assertFalse((release / "clean").exists(), "nothing was built")
        self.assertEqual([line for line in world.workloads() if line.startswith("clean check")], [],
                         "no Clean check ran")
        self.assertEqual(mode(release), 0o775)

    def test_a_build_that_leaves_an_entry_others_can_write_runs_no_clean_check(self):
        """The tree the build wrote is judged again after the build, before
        the Clean binary runs: a build step that leaves a group-writable
        entry anywhere in the checkout (here the fake build loosens the
        proofs/ directory Clean then reads, which is no ancestor of the
        binary, so the binary's own check would pass) is refused by name and
        no Clean check runs."""
        world, cache = self.private_cache_world("private-cache-loosening-build-")
        anchor = "        target.chmod(0o777 & ~mask)\n"
        loosen = '        os.chmod(Path(os.environ["CARGO_TARGET_DIR"]).parent / "proofs", 0o775)\n'
        # Every copy of the fake tool: the Trust package's targo runs the build.
        for tool in (world.bin / "fake-tool", world.sysroot / "bin" / "targo", world.sysroot / "bin" / "trustc"):
            original = tool.read_text()
            self.assertEqual(original.count(anchor), 1, tool)
            tool.write_text(original.replace(anchor, anchor + loosen))
        result = world.run_gate("--attest", umask=0o002, SOUNDNESS_DEPS_DIR=None, XDG_CACHE_HOME=str(cache))
        self.assertNotEqual(result.returncode, 0, result.stdout[-3000:])
        self.assertIn("[PASS] preflight: clean checkout", result.stdout)
        checkout = cache / "trust-cg" / "soundness-deps" / f"clean-{world.clean_rev}"
        proofs = checkout / "proofs"
        self.assertRegex(result.stdout, r"Clean release binary matches checkout[^\n]*not run: private_cache: "
                                        r"refusing [^\n]*" + re.escape(f"{os.path.realpath(proofs)} has mode 0775"))
        self.assertTrue((checkout / "target" / "release" / "clean").is_file(), "the build ran")
        self.assertEqual([line for line in world.workloads() if line.startswith("clean check")], [],
                         "no Clean check ran")
        self.assertEqual(mode(proofs), 0o775)

    def test_a_default_acl_on_an_existing_checkout_is_refused_before_anything_is_built(self):
        """X-HOST-P13 round-4 verifier
        (test_v4_relative_roots.py::test_default_acl_on_an_existing_pinned_checkout):
        a pinned Clean checkout an earlier run left, given a default ACL
        naming another uid (its mode stays 0700), passed the attested
        preflight, and what the Clean build then created there under umask
        077 was writable by that uid until the check after the build. The
        check of the checkout before it is used (`require-private-tree`) now
        refuses it: the preflight row names the ACL and the remedy, nothing
        is built and no Clean check runs."""
        setfacl = shutil.which("setfacl")
        if setfacl is None or not hasattr(os, "getxattr"):
            self.skipTest("no setfacl or no extended-attribute calls on this host")
        world, cache = self.private_cache_world("private-cache-acl-checkout-")
        first = world.run_gate("--attest", "--preflight-only", umask=0o002, SOUNDNESS_DEPS_DIR=None,
                               XDG_CACHE_HOME=str(cache))
        self.assertEqual(first.returncode, 0, first.stdout[-3000:])
        checkout = cache / "trust-cg" / "soundness-deps" / f"clean-{world.clean_rev}"
        probe = subprocess.run([setfacl, "-d", "-m", "u:4242:rwx", str(checkout)], capture_output=True, text=True)
        if probe.returncode != 0:
            self.skipTest(f"setfacl failed: {probe.stderr}")
        self.assertEqual(mode(checkout), 0o700)
        result = world.run_gate("--attest", umask=0o002, SOUNDNESS_DEPS_DIR=None, XDG_CACHE_HOME=str(cache))
        self.assertNotEqual(result.returncode, 0, result.stdout[-3000:])
        canonical = os.path.realpath(checkout)
        self.assertRegex(result.stdout, r"\[FAIL\] preflight: clean checkout[^\n]*refusing the candidate's clean "
                                        r"checkout under [^\n]*" + re.escape(
                                            f"refusing {canonical}: {canonical}: its default ACL lets uid 4242 write "
                                            "what is created in it"))
        self.assertIn(PC.TREE_REMEDY, result.stdout)
        self.assertFalse((checkout / "target").exists(), "nothing was built")
        self.assertEqual([line for line in world.workloads() if line.startswith("clean check")], [],
                         "no Clean check ran")

    def test_a_checkout_with_a_loose_interior_is_refused_and_credits_nothing(self):
        """The fourth closure audit's reproducer: the pinned Clean checkout in
        the state a umask-0002 checkout reaches when its owner applies the
        printed root remedy (`chmod go-w`) to the named root only (root 0755,
        proofs/ 0775, its files 0664). Then the gate judged only the root and
        accepted it; a co-group writer rewrote a pinned proof that Clean
        rejects while the run's first Clean check ran and restored it after
        its own check, and the run recorded `132 total 132 passed` and an
        attestation. Now the preflight refuses the checkout, naming the
        loose directory and the remedy to remove it: no Clean check runs, the
        substitution never happens and no attestation is recorded."""
        world, cache = self.private_cache_world("private-cache-legacy-interior-")
        first = world.run_gate("--attest", "--preflight-only", umask=0o002, SOUNDNESS_DEPS_DIR=None,
                               XDG_CACHE_HOME=str(cache))
        self.assertEqual(first.returncode, 0, first.stdout[-3000:])
        checkout = cache / "trust-cg" / "soundness-deps" / f"clean-{world.clean_rev}"
        proofs = checkout / "proofs"
        os.chmod(checkout, 0o755)
        os.chmod(proofs, 0o775)
        for entry in proofs.iterdir():
            os.chmod(entry, 0o664)
        target = proofs / "lrat_checker_tree.lean"
        pinned = target.read_text()
        marker = Path(world.base, "attacker-acted")
        # The audit's attacker, inside the fake Clean: substitute the pinned
        # proof on the first Clean check of a pinned proof, and pass only the
        # substituted text.
        block = (
            'if name == "clean" and args[:1] == ["check"] and "soundness-deps" in args[-1]:\n'
            '    _t = Path(args[-1]).parent / "lrat_checker_tree.lean"\n'
            f'    _m = Path({str(marker)!r})\n'
            '    if not _m.exists():\n'
            '        _t.write_text("-- SUBSTITUTED by a co-group writer\\n")\n'
            '        _m.write_text("acted\\n")\n'
            '    if Path(args[-1]).name == "lrat_checker_tree.lean":\n'
            '        if "SUBSTITUTED" not in Path(args[-1]).read_text():\n'
            '            print("Checked 5 declarations\\n  4 passed, 1 failed"); sys.exit(1)\n'
            f'        Path(args[-1]).write_text({pinned!r})\n'
            '        print("Checked 5 declarations\\n  5 passed, 0 failed"); sys.exit(0)\n'
        )
        anchor = 'if name == "clean":'
        tool = world.bin / "fake-tool"
        original = tool.read_text()
        self.assertEqual(original.count(anchor), 1)
        tool.write_text(original.replace(anchor, block + anchor))
        result = world.run_gate("--attest", umask=0o002, SOUNDNESS_DEPS_DIR=None, XDG_CACHE_HOME=str(cache))
        self.assertNotEqual(result.returncode, 0, result.stdout[-3000:])
        self.assertRegex(result.stdout, r"\[FAIL\] preflight: clean checkout[^\n]*refusing the candidate's clean "
                                        r"checkout under [^\n]*" + re.escape(f"{os.path.realpath(proofs)} has mode 0775"))
        self.assertIn(PC.TREE_REMEDY, result.stdout)
        self.assertIn(f"worktree remove --force {os.path.realpath(checkout)}", result.stdout)
        self.assertEqual([line for line in world.workloads() if line.startswith("clean check")], [],
                         "no Clean check ran")
        self.assertFalse(marker.exists(), "the substitution never happened")
        self.assertEqual(target.read_text(), pinned)
        self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "",
                         "no attestation is recorded")
        self.assertEqual((mode(checkout), mode(proofs), mode(target)), (0o755, 0o775, 0o664), "never repaired")

    # The fifth closure audit's attacker for trust-cg's own proofs, inside the
    # fake tool: on the first Clean check of a trust-cg proof it rewrites
    # sentinel_decide_spec in the candidate's WORKING TREE; Clean then judges
    # the content it is handed, wherever it was read from, and accepts only
    # the substitute. The fake lake writes an .olean where it builds and
    # records that directory.
    CANDIDATE_ATTACK = (
        'if name == "clean" and args[:1] == ["check"] and Path(args[-1]).stem in {stems!r}:\n'
        '    _t = Path({working!r})\n'
        '    _m = Path({marker!r})\n'
        '    if not _m.exists():\n'
        '        _t.write_text("-- SUBSTITUTED by a co-group writer\\n")\n'
        '        _m.write_text("acted\\n")\n'
        '    if Path(args[-1]).stem == "sentinel_decide_spec" and "SUBSTITUTED" not in Path(args[-1]).read_text():\n'
        '        print("Checked 5 declarations\\n  4 passed, 1 failed"); sys.exit(1)\n'
        'if name == "lake" and args[:1] == ["build"]:\n'
        '    Path(".lake/build/lib").mkdir(parents=True, exist_ok=True)\n'
        '    Path(".lake/build/lib/Trust.olean").write_text("olean\\n")\n'
        '    Path({lake_dir!r}).write_text(os.getcwd())\n'
    )

    def attacked_world(self, prefix: str) -> tuple[fixture.Constellation, Path, Path, Path]:
        """A fixture world whose fake tool carries `CANDIDATE_ATTACK`; returns
        it, its cache, the attacker's marker and the file the fake lake names
        its build directory in."""
        world, cache = self.private_cache_world(prefix)
        stems = fixture.bash_array((world.cg / "scripts" / "soundness_check.sh").read_text(), "TRUST_CG_LEAN")
        marker = Path(world.base, "attacker-acted")
        lake_dir = Path(world.base, "lake-dir")
        block = self.CANDIDATE_ATTACK.format(stems=stems, marker=str(marker), lake_dir=str(lake_dir),
                                             working=str(world.cg / "proofs" / "sentinel_decide_spec.lean"))
        anchor = 'if name == "lake":'
        tool = world.bin / "fake-tool"
        original = tool.read_text()
        self.assertEqual(original.count(anchor), 1)
        tool.write_text(original.replace(anchor, block + anchor))
        return world, cache, marker, lake_dir

    def test_an_attested_run_checks_the_candidates_own_proofs_only_in_a_private_export(self):
        """X-HOST-P13 fifth closure audit: the attested gate had Clean check
        trust-cg's own proofs/*.lean in the candidate checkout itself, which no
        rule judges (this host's is 0775, proofs/ 0775). A co-group writer who
        rewrote a proof Clean rejects during the run's first Clean check of
        one, and restored it after its own check, turned a failing proof into
        `132 total 132 passed` and two attestation refs. Every check of the
        candidate's own proofs (the inventory, the Clean checks, the lake
        build and its ratchets) now reads a private export of exactly the
        attested commit below the run's log directory, every entry owner-only
        and lake's output too (lake builds under umask 077): the rewrite of the
        working tree reaches no check, the committed proof fails as committed,
        and nothing is recorded."""
        world, cache, marker, lake_dir = self.attacked_world("private-cache-candidate-proofs-")
        head = world.head()
        working = world.cg / "proofs" / "sentinel_decide_spec.lean"
        result = world.run_gate("--attest", "--keep-going", umask=0o002, SOUNDNESS_DEPS_DIR=None,
                                XDG_CACHE_HOME=str(cache))
        self.assertNotEqual(result.returncode, 0, result.stdout[-3000:])
        self.assertTrue(marker.exists(), "the co-group writer acted")
        self.assertIn("SUBSTITUTED", working.read_text(), "the working tree was rewritten")
        self.assertRegex(result.stdout, r"\[FAIL\] clean-check trust-cg proofs/sentinel_decide_spec[^\n]*4 passed, "
                                        r"1 failed")
        logdir = fixture.logdir_of(result)
        self.assertIsNotNone(logdir)
        export = Path(os.path.realpath(logdir / "candidate-proofs"))
        self.assertRegex(result.stdout, r"\[PASS\] trust-cg proofs/\*\.lean inventory[^\n]*"
                         + re.escape(f"a private export of {head} ({export})"))
        stems = fixture.bash_array((world.cg / "scripts" / "soundness_check.sh").read_text(), "TRUST_CG_LEAN")
        checked = [line.split()[-1] for line in world.workloads()
                   if line.startswith("clean check ") and Path(line.split()[-1]).stem in stems]
        self.assertEqual(checked, [str(export / "proofs" / f"{stem}.lean") for stem in stems])
        self.assertEqual(lake_dir.read_text(), str(export / "formal" / "lean"), "lake built in the export")
        self.assertIn("[PASS] formal/lean lake build", result.stdout)
        self.assertIn("[PASS] formal/lean sorry-count", result.stdout)
        self.assertEqual((export / "proofs" / "sentinel_decide_spec.lean").read_text(), "-- fixture\n",
                         "the export holds the committed proof")
        self.assertEqual(open_entries(export), [], "every entry of the export, lake's output included, is private")
        self.assertEqual(mode(export / "formal" / "lean" / ".lake" / "build" / "lib" / "Trust.olean"), 0o600)
        self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "",
                         "no attestation is recorded")

    def test_a_proof_export_that_cannot_be_made_private_runs_no_proof_check(self):
        """The export is refused, never used, when it cannot be made
        private: here the run's TMPDIR (an ancestor of its log directory,
        where the export is made) is group-writable. The inventory, every
        Clean check of a trust-cg proof and the lake build then record FAIL
        naming the refusal and the remedy, none of them runs, and nothing is
        recorded."""
        world, cache, marker, lake_dir = self.attacked_world("private-cache-open-export-")
        os.chmod(world.tmp, 0o775)
        result = world.run_gate("--attest", "--keep-going", umask=0o002, SOUNDNESS_DEPS_DIR=None,
                                XDG_CACHE_HOME=str(cache))
        self.assertNotEqual(result.returncode, 0, result.stdout[-3000:])
        refusal = (f"not run: the export of {world.head()} is not private: private_cache: refusing ")
        tmp = re.escape(f"{os.path.realpath(world.tmp)} is not a trusted directory ancestor")
        stems = fixture.bash_array((world.cg / "scripts" / "soundness_check.sh").read_text(), "TRUST_CG_LEAN")
        for leg in ["trust-cg proofs/*.lean inventory", *(f"clean-check trust-cg proofs/{stem}" for stem in stems),
                    "formal/lean lake build"]:
            self.assertRegex(result.stdout, re.escape(f"[FAIL] {leg}") + r"[^\n]*" + re.escape(refusal)
                             + r"[^\n]*" + tmp + r"[^\n]*point TMPDIR at a directory only you can write")
        self.assertEqual([line for line in world.workloads() if line.startswith("clean check ")
                          and Path(line.split()[-1]).stem in stems], [], "no trust-cg proof was checked")
        self.assertNotIn("lake build", world.workloads())
        self.assertFalse(marker.exists() or lake_dir.exists())
        self.assertEqual(fixture.git(world.cg, "for-each-ref", "--format=%(refname)", "refs/attest/"), "",
                         "no attestation is recorded")
        self.assertEqual(mode(world.tmp), 0o775, "never repaired")

    def test_a_relative_or_empty_xdg_cache_home_is_ignored(self):
        """The dependency directory's default follows the one cache-base rule
        trust-cg's own caches use: an empty or relative XDG_CACHE_HOME is
        ignored (XDG Base Directory specification), so the checkouts land in
        $HOME/.cache, never below the working directory."""
        world, _cache = self.private_cache_world("private-cache-relative-")
        os.chmod(world.home, 0o700)
        for xdg in ("", "relative-cache"):
            with self.subTest(xdg=xdg):
                result = world.run_gate("--attest", "--preflight-only", umask=0o002, SOUNDNESS_DEPS_DIR=None,
                                        XDG_CACHE_HOME=xdg)
                self.assertEqual(result.returncode, 0, result.stdout[-3000:])
                deps = world.home / ".cache" / "trust-cg" / "soundness-deps"
                checkout = os.path.realpath(deps / ("clean-" + world.clean_rev))
                self.assertIn(f"pinned worktree {checkout}", result.stdout)
                self.assertFalse((world.cg / "relative-cache").exists())
                self.assertFalse((world.cg / "trust-cg").exists())

    def test_a_cache_reached_through_a_link_others_can_repoint_runs_only_the_clean_it_checked(self):
        """X-HOST-P13 third closure audit's reproducer: XDG_CACHE_HOME names
        `<shared 0777>/link`, a symlink to a private directory. The rule
        judged the canonical paths, but the attested gate kept the alias, so
        when the first genuine Clean run stood in for another user and
        re-pointed the link at a copy of the cache whose `clean` is another
        program, 13 of the 14 clean-check legs ran that program and the run
        wrote its attestation record. The gate now uses the canonical paths
        its checks judged: every Clean leg runs the checked binary, and the
        re-pointed link changes nothing. The control: the same cache as a real
        directory inside the open directory is refused at preflight."""
        directory = fixture.FixtureDirectory("private-cache-alias-")
        self.addCleanup(directory.cleanup)
        base = Path(os.path.realpath(directory.name))
        world = fixture.Constellation(base)
        real = base / "xdg-real"
        real.mkdir(mode=0o700)
        os.chmod(real, 0o700)
        shared = base / "shared"
        shared.mkdir()
        os.chmod(shared, 0o777)
        link = shared / "link"
        link.symlink_to(real)
        evil = base / "xdg-evil"
        marker = base / "swapped"
        # The fixture's tool, wrapped: its first run as `clean` re-points the
        # link (atomically, as another user could) at a copy of the cache
        # whose release `clean` logs EVIL-clean and prints a passing summary.
        evil_clean = ("#!/usr/bin/env python3\nimport sys\n"
                      f"open({str(world.log)!r}, 'a').write('EVIL-clean ' + ' '.join(sys.argv) + '\\n')\n"
                      "print('Checked 5 declarations\\n  5 passed, 0 failed')\n")
        swap = (
            f"if name == 'clean' and not os.path.exists({str(marker)!r}):\n"
            f"    import shutil as _shutil\n"
            f"    open({str(marker)!r}, 'w').close()\n"
            f"    open({str(world.log)!r}, 'a').write('GENUINE-clean ran as ' + sys.argv[0] + '\\n')\n"
            f"    _shutil.copytree({str(real)!r}, {str(evil)!r}, symlinks=True)\n"
            f"    for _path in Path({str(evil)!r}).rglob('clean'):\n"
            f"        if _path.parent.name == 'release' and _path.is_file():\n"
            f"            _path.unlink()\n"
            f"            _path.write_text({evil_clean!r})\n"
            f"            _path.chmod(0o700)\n"
            f"    os.symlink({str(evil)!r}, {str(shared / '.link-new')!r})\n"
            f"    os.replace({str(shared / '.link-new')!r}, {str(link)!r})\n"
        )
        original = (world.bin / "fake-tool").read_text()
        anchor = 'if name == "clean":'
        self.assertEqual(original.count(anchor), 1)
        tool = base / "repointing-tool"
        tool.write_text(original.replace(anchor, swap + anchor))
        tool.chmod(0o755)
        result = world.run_gate("--attest", umask=0o002, SOUNDNESS_DEPS_DIR=None, XDG_CACHE_HOME=str(link),
                                FIXTURE_TOOL=str(tool))
        workloads = world.workloads()
        self.assertTrue([line for line in workloads if line.startswith("GENUINE-clean")], "the link was re-pointed")
        self.assertEqual(os.readlink(link), str(evil))
        self.assertEqual([line for line in workloads if line.startswith("EVIL-clean")], [],
                         "a Clean the gate never checked ran after the link was re-pointed")
        checkout = real / "trust-cg" / "soundness-deps" / f"clean-{world.clean_rev}"
        self.assertIn(f"pinned worktree {checkout}", result.stdout)
        self.assertRegex(result.stdout, r"\[PASS\] Clean release binary matches checkout +"
                                        + re.escape(f"{checkout}/target/release/clean"))
        checks = [line for line in workloads if line.startswith("clean check ")]
        self.assertEqual(len(checks), 14, workloads)
        self.assertEqual(result.returncode, 0, result.stdout[-4000:] + result.stderr[-2000:])

        # The control: a real cache directory inside the open directory.
        direct = shared / "xdg-direct"
        direct.mkdir(mode=0o700)
        os.chmod(direct, 0o700)
        refused = world.run_gate("--attest", "--preflight-only", umask=0o002, SOUNDNESS_DEPS_DIR=None,
                                 XDG_CACHE_HOME=str(direct))
        self.assertNotEqual(refused.returncode, 0, refused.stdout[-3000:])
        # Since LD-75 the host trust boundary refuses it first: another user
        # could create the `.cargo` Cargo reads in the open directory.
        self.assertIn(f"host_boundary: REFUSED {shared} (Cargo's configuration search above the user cache's "
                      "trust-cg directory): writable by every user (mode 0777)", refused.stdout)

    def test_every_clean_lane_command_runs_under_the_private_umask(self):
        """The Clean lane's commands all start through run_clean_bounded,
        the one place that runs in the Clean checkout, under umask 077. The
        fixture's `clean check` writes nothing, so this pins the routing of
        that command; the run below shows the Cargo lane's effect."""
        text = (ROOT / "scripts" / "soundness_check.sh").read_text()
        self.assertEqual(re.findall(r'run_bounded "\$CLEAN_DIR"[^\n]*', text), ['run_bounded "$CLEAN_DIR" "$@")'])
        self.assertIn('(umask 077 && run_bounded "$CLEAN_DIR" "$@")', text)
        self.assertIn('run_clean_bounded "$CLEAN_BIN" check "$file"', text)

    def test_an_attested_run_under_umask_0002_leaves_nothing_open_under_either_cache(self):
        """The X-HOST-P13 verification's reproducers: under the caller's umask
        0002 the Clean lane wrote its pinned checkout's target/ group-writable,
        and the x86-64 legs wrote the remote clone (their build tree, Python
        caches and the record's git objects) under the remote login umask. A
        whole attested run of the fixture under umask 0002, with a fresh
        XDG_CACHE_HOME and a fresh remote HOME (the fake ssh keeps the umask):
        no non-symlink entry under <cache>/trust-cg or under the remote's
        ~/.cache/trust-cg has a group or other bit."""
        directory = fixture.FixtureDirectory("private-cache-run-")
        self.addCleanup(directory.cleanup)
        world = fixture.Constellation(Path(directory.name))
        cache = Path(directory.name, "xdg-cache")
        cache.mkdir(mode=0o700)
        os.chmod(cache, 0o700)
        result = world.run_gate("--attest", "--scope", "full", umask=0o002,
                                SOUNDNESS_DEPS_DIR=None, XDG_CACHE_HOME=str(cache))
        self.assertEqual(result.returncode, 0, result.stdout[-4000:] + result.stderr[-2000:])
        clean_release = cache / "trust-cg" / "soundness-deps" / f"clean-{world.clean_rev}" / "target" / "release"
        self.assertTrue((clean_release / "clean").is_file(), "the Clean lane built in the pinned checkout")
        self.assertFalse((clean_release / "clean").is_symlink())
        self.assertEqual(mode(clean_release), 0o700)
        self.assertEqual(mode(clean_release / "clean"), 0o700, "built under umask 077")
        self.assertIn("Clean release binary matches checkout", result.stdout)
        remote_cache = world.remote_home / ".cache" / "trust-cg"
        clone = remote_cache / "soundness-remote" / "trust-cg"
        prefix = "fixture-x86-bytecode "
        witnesses = [json.loads(line[len(prefix):]) for line in world.workloads() if line.startswith(prefix)]
        run_logs = fixture.logdir_of(result)
        remote_log = run_logs / "remote" / "remote-run.log" if run_logs else None
        remote_diagnostic = remote_log.read_text(errors="replace") if remote_log and remote_log.is_file() else ""
        self.assertEqual(len(witnesses), 1, "the real remote fixture must execute exactly once:\n"
                         + result.stdout[-4000:] + result.stderr[-2000:] + remote_diagnostic[-4000:]
                         + "\nworkloads:\n" + "\n".join(world.workloads()))
        witness = witnesses[0]
        source = clone / "scripts" / "soundness_attestation.py"
        self.assertEqual(witness["repo"], str(clone.resolve()))
        self.assertEqual(witness["source"], str(source.resolve()))
        self.assertEqual(witness["source_sha256"], hashlib.sha256(source.read_bytes()).hexdigest())
        cache_dir = clone / "scripts" / "__pycache__"
        cache_entries = sorted(path.name for path in cache_dir.iterdir()) if cache_dir.is_dir() else []
        artifact_diagnostic = ("the remote fixture's actual bytecode must remain in its clone:\n"
                               + json.dumps(witness, sort_keys=True)
                               + f"\nreturned path exists: {Path(witness['bytecode']).exists()}"
                               + f"\nclone cache entries: {cache_entries}\n" + remote_diagnostic[-4000:])
        bytecode = list(cache_dir.glob("soundness_attestation.*.pyc"))
        self.assertTrue(bytecode, artifact_diagnostic)
        self.assertIn(Path(witness["bytecode"]), [artifact.resolve() for artifact in bytecode])
        self.assertEqual(Path(witness["bytecode"]).stat().st_size, witness["bytes"])
        for artifact in bytecode:
            self.assertTrue(artifact.is_file(), artifact)
            self.assertGreater(artifact.stat().st_size, 16, artifact)
        self.assertTrue(list((clone / ".git" / "refs" / "attest").rglob("*")), "and the record")
        for root in (cache / "trust-cg", remote_cache):
            with self.subTest(root=root):
                self.assertEqual(open_entries(root), [])


class IcmpAyCacheTests(unittest.TestCase):
    def test_the_cache_is_private_under_umask_0002_even_when_the_build_cannot_start(self):
        """The audit's reproducer: `ay-path --ay-source <absent>` (now `tools-path`) under umask
        0002 left <cache>/trust-cg and ay-cli 0775 and the lock 0664 before
        it failed on the missing source."""
        with private_tmp() as temporary, umask(0o002):
            cache = Path(temporary, "xdg", "trust-cg", "ay-cli")
            with self.assertRaises(GATE.MissingInput) as raised:
                GATE.obtain_ay(AY, "0.27.0", cache, Path(temporary, "no-repo"), False, UNGATED)
            self.assertEqual(raised.exception.code, "ay-source-missing")
            for created in (Path(temporary, "xdg"), cache.parent, cache):
                self.assertEqual(mode(created), 0o700, created)
            self.assertEqual(mode(cache / f"{AY}.lock"), 0o600)

    def test_the_default_cache_dir_follows_the_one_cache_base_rule(self):
        """The gate's default --cache-dir is `user_cache_base`'s: an empty or
        relative XDG_CACHE_HOME is ignored, never resolved against the working
        directory; with no absolute base at all the gate fails closed."""
        rows = [({"XDG_CACHE_HOME": "/xdg", "HOME": "/home/u"}, "/xdg/trust-cg/ay-cli"),
                ({"XDG_CACHE_HOME": "relative", "HOME": "/home/u"}, "/home/u/.cache/trust-cg/ay-cli"),
                ({"XDG_CACHE_HOME": "", "HOME": "/home/u"}, "/home/u/.cache/trust-cg/ay-cli")]
        for environ, expected in rows:
            with self.subTest(environ=environ), mock.patch.dict(os.environ, environ, clear=True):
                self.assertEqual(GATE.default_cache_dir(), Path(expected))
        with mock.patch.dict(os.environ, {"XDG_CACHE_HOME": "relative", "HOME": "relative-home"}, clear=True), \
                mock.patch.object(GATE, "log") as logged:
            self.assertEqual(GATE.main(["tools-path"]), GATE.EXIT_FAIL)
        self.assertIn("HOME=relative-home is not absolute", logged.call_args.args[0])

    def warm_slot(self, cache: Path, payload: bytes = b"built bytes") -> Path:
        return self.warm_tool_slot(cache, AY_TOOL, payload, f"ay 0.27.0+build.0.{AY}@fixture")

    def test_a_slot_another_user_could_write_is_refused_never_repaired(self):
        """The skeptic's plant: a binary and an identity record naming its
        digest, in a slot created group-writable. The record sits beside the
        binary, so it vouches for nothing there."""
        with private_tmp() as temporary:
            cache = Path(os.path.realpath(temporary), "ay-cli")
            slot = self.warm_slot(cache, b"#!/bin/sh\necho planted\n")
            self.assertEqual(GATE.obtain_ay(AY, "0.27.0", cache, None, False, UNGATED)["cache"], "warm")
            for path, loose in ((slot, 0o775), (slot / "ay", 0o775), (slot / "identity.json", 0o664)):
                with self.subTest(path=path.name):
                    original = mode(path)
                    os.chmod(path, loose)
                    with self.assertRaises(GATE.Finding) as raised:
                        GATE.obtain_ay(AY, "0.27.0", cache, None, False, UNGATED)
                    self.assertEqual(raised.exception.code, "ay-cache-not-private")
                    self.assertIn(f"delete {slot} to rebuild", raised.exception.message)
                    self.assertEqual(mode(path), loose, "never repaired")
                    os.chmod(path, original)
            os.chmod(cache, 0o775)
            with self.assertRaises(GATE.Finding) as raised:
                GATE.obtain_ay(AY, "0.27.0", cache, None, False, UNGATED)
            self.assertEqual(raised.exception.code, "ay-cache-not-private")
            self.assertEqual(mode(cache), 0o775)

    def test_a_slot_an_earlier_script_built_under_umask_0022_is_used_as_it_is(self):
        """280ea37bf made the cache with `mkdir(parents=True)`, the slot with
        `slot.mkdir()`, the binary 0555 and the record with `write_text`:
        under umask 0022 that is 0755, 0755, 0555 and 0644. This fixture keeps
        those modes with a current exact-command/export receipt and cache key.
        No other user can write any of it, so it is used (warm) under any
        umask and nothing is changed. The same slot built under umask 0002
        (0775 slot, 0664 record) is refused, with the remedy."""
        with private_tmp() as temporary:
            cache = Path(os.path.realpath(temporary), "xdg", "trust-cg", "ay-cli")
            slot = cache / AY_TOOL.cache_key
            payload = b"#!/bin/sh\necho built by 280ea37bf\n"
            identity = tool_identity(AY_TOOL, payload, f"ay 0.27.0+build.0.{AY}@fixture")
            with umask(0o022):
                slot.mkdir(parents=True)
                (slot / "ay").write_bytes(payload)
                os.chmod(slot / "ay", 0o555)
                (slot / "identity.json").write_text(json.dumps(identity))
                (cache / f"{AY}.lock").write_text("")
            entries = (Path(temporary, "xdg"), cache.parent, cache, slot, slot / "ay", slot / "identity.json",
                       cache / f"{AY}.lock")
            before = {path: mode(path) for path in entries}
            self.assertEqual([before[slot], before[slot / "ay"], before[slot / "identity.json"]],
                             [0o755, 0o555, 0o644])
            for mask in (0o002, 0o022, 0o077):
                with self.subTest(umask=oct(mask)), umask(mask):
                    self.assertEqual(GATE.obtain_ay(AY, "0.27.0", cache, None, False, UNGATED)["cache"], "warm")
                    self.assertEqual({path: mode(path) for path in entries}, before, "nothing is changed")
            os.chmod(slot, 0o775)
            os.chmod(slot / "identity.json", 0o664)
            with self.assertRaises(GATE.Finding) as raised:
                GATE.obtain_ay(AY, "0.27.0", cache, None, False, UNGATED)
            self.assertEqual(raised.exception.code, "ay-cache-not-private")
            self.assertIn(f"{slot} has mode 0775; another user could replace its contents", raised.exception.message)
            self.assertIn(f"delete {slot} to rebuild", raised.exception.message)

    def warm_tool_slot(self, cache: Path, tool, payload: bytes, banner: str) -> Path:
        slot = cache / tool.cache_key
        PC.create_private_dir_all(slot)
        (slot / tool.package).write_bytes(payload)
        os.chmod(slot / tool.package, 0o500)
        identity = tool_identity(tool, payload, banner)
        PC.write_private_file(slot / "identity.json", json.dumps(identity))
        return slot

    def test_a_cache_reached_through_a_link_others_can_repoint_runs_the_slots_it_checked(self):
        """X-HOST-P13 third closure audit: obtain_ay admitted a warm slot by
        the canonical ancestry of its cache directory, and obtain_tools then
        handed on `cache_dir / slot / package`, the alias. With the caches
        reached through `<shared 0777>/link`, re-pointing the link after
        admission ran a planted AY. obtain_build now names everything below
        the canonical cache directory and returns that binary as `path`, which
        obtain_tools hands on, so the planted tools never run. The control:
        the same slot directly inside the open directory is refused."""
        with private_tmp() as temporary:
            base = Path(os.path.realpath(temporary))
            real, evil = base / "real", base / "evil"
            shared = base / "shared"
            shared.mkdir()
            os.chmod(shared, 0o777)
            link = shared / "link"
            link.symlink_to(real)
            ay = AY_TOOL
            clean = GATE.Tool("clean", "c" * 40, "0.9.0", ("-p", "clean"), ())
            for root, word in ((real, "genuine"), (evil, "PLANTED")):
                self.warm_tool_slot(root / "ay-cli", ay, f"#!/bin/sh\necho {word}-ay\n".encode(),
                                    f"ay 0.27.0+build.0.{AY}@fixture")
                self.warm_tool_slot(root / "clean-cli", clean, f"#!/bin/sh\necho {word}-clean\n".encode(),
                                    "clean 0.9.0")
            args = mock.Mock(cache_dir=link / "ay-cli", clean_cache_dir=link / "clean-cli", ay_source=None,
                             clean_source=None, keep_build=False)
            report: dict = {}
            with mock.patch.object(GATE, "heavy_gate_admission", return_value=UNGATED), \
                    mock.patch.object(GATE, "log"):
                tools, missing = GATE.obtain_tools(args, {"ay": ay, "clean": clean}, report)
            self.assertEqual(missing, [])
            for tool in (ay, clean):
                checked = real / f"{tool.package}-cli" / tool.cache_key / tool.package
                self.assertEqual(tools[tool.package], checked)
                self.assertEqual(report[tool.package]["path"], str(checked))
            # Another user re-points the link after admission.
            os.symlink(evil, shared / ".link-new")
            os.replace(shared / ".link-new", link)
            for package in ("ay", "clean"):
                ran = subprocess.run([str(tools[package])], capture_output=True, text=True)
                self.assertEqual(ran.stdout.strip(), f"genuine-{package}", package)
            # The control: the slot directly inside the open directory.
            direct = shared / "direct-ay-cli"
            self.warm_tool_slot(direct, ay, b"#!/bin/sh\necho genuine-ay\n", f"ay 0.27.0+build.0.{AY}@fixture")
            with self.assertRaises(GATE.Finding) as raised:
                GATE.obtain_ay(AY, "0.27.0", direct, None, False, UNGATED)
            self.assertEqual(raised.exception.code, "ay-cache-not-private")
            self.assertIn(f"{shared} is not a trusted directory ancestor", raised.exception.message)

    def test_a_slot_named_through_an_alias_is_refused(self):
        """`require_private_slot` holds only a slot named below its canonical
        cache directory: the entries it checks are then the ones the ancestor
        rule vouched for."""
        with private_tmp() as temporary:
            base = Path(os.path.realpath(temporary))
            slot = self.warm_slot(base / "real" / "ay-cli")
            (base / "alias").symlink_to(base / "real")
            aliased = base / "alias" / "ay-cli" / AY_TOOL.cache_key
            with self.assertRaises(GATE.Finding) as raised:
                GATE.require_private_slot(aliased, aliased / "ay", aliased / "identity.json")
            self.assertEqual(raised.exception.code, "ay-cache-not-private")
            self.assertIn(f"is not named by its canonical cache directory {slot.parent}", raised.exception.message)
            GATE.require_private_slot(slot, slot / "ay", slot / "identity.json")

    def test_a_symlinked_slot_is_refused(self):
        with private_tmp() as temporary:
            cache = Path(temporary, "ay-cli")
            real = self.warm_slot(Path(temporary, "elsewhere"))
            PC.create_private_dir_all(cache)
            (cache / AY_TOOL.cache_key).symlink_to(real)
            with self.assertRaises(GATE.Finding) as raised:
                GATE.obtain_ay(AY, "0.27.0", cache, None, False, UNGATED)
            self.assertEqual(raised.exception.code, "ay-cache-not-private")
            self.assertIn("symlinks are refused", raised.exception.message)

    def test_a_cache_below_a_group_writable_ancestor_is_refused_before_anything_is_written(self):
        with private_tmp() as temporary:
            shared = Path(temporary, "shared")
            shared.mkdir()
            os.chmod(shared, 0o775)
            cache = shared / "trust-cg" / "ay-cli"
            with self.assertRaises(GATE.Finding) as raised:
                GATE.obtain_ay(AY, "0.27.0", cache, Path(temporary, "no-repo"), False, UNGATED)
            self.assertEqual(raised.exception.code, "ay-cache-not-private")
            self.assertIn(f"{shared} is not a trusted directory ancestor", raised.exception.message)
            self.assertIn("chmod go-w", raised.exception.message)
            self.assertEqual(list(cache.iterdir()), [], "no lock and no build in a refused cache")
            self.assertEqual(mode(shared), 0o775)


class IcmpColdBuildTests(unittest.TestCase):
    """The cold path (`build_tool`, for AY), run in process under umask 0002 with a
    fixture AY repository and a fixture targo that writes its target tree with
    the umask's modes (the X-HOST-P13 verification found no test reaching it).
    The real build was run once by hand (CHANGELOG, "Measured")."""

    def setUp(self):
        temporary = private_tmp()
        self.addCleanup(temporary.cleanup)
        base = Path(temporary.name)
        self.repo, self.rev = fake_ay_repository(base)
        self.tool = AY_TOOL._replace(rev=self.rev)
        self.targo = base / "bin" / "targo"
        self.targo.parent.mkdir()
        self.targo.write_text(FAKE_TARGO)
        os.chmod(self.targo, 0o755)
        self.xdg = base / "xdg"
        self.cache = self.xdg / "trust-cg" / "ay-cli"

    def obtain(self, keep_build: bool, **environment: str) -> dict:
        with umask(0o002), mock.patch.object(GATE, "resolve_targo", return_value=self.targo), \
                mock.patch.dict(os.environ, environment):
            return GATE.obtain_ay(self.rev, "0.27.0", self.cache, self.repo, keep_build, UNGATED)

    def test_a_cold_build_under_umask_0002_writes_only_private_entries(self):
        """Everything the build writes under the cache (the work directory,
        the export, the build log, Cargo's target tree) has no group or other
        bit; the slot is exactly 0700 although the cache directory is
        set-group-ID, the binary 0500 and the record and lock 0600. The next
        call is warm."""
        PC.create_private_dir_all(self.cache)
        os.chmod(self.cache, 0o2700)
        setgid = mode(self.cache) == 0o2700
        if not setgid:
            os.chmod(self.cache, 0o700)
        identity = self.obtain(keep_build=True)
        self.assertEqual(identity["cache"], "cold")
        slot = self.cache / self.tool.cache_key
        self.assertEqual(mode(slot), 0o700, "exactly 0700: no set-group-ID bit from the cache directory")
        self.assertEqual(mode(slot / "ay"), 0o500)
        self.assertEqual(mode(slot / "identity.json"), 0o600)
        self.assertEqual(mode(self.cache / f"{self.rev}.lock"), 0o600)
        self.assertEqual(identity["sha256"], hashlib.sha256((slot / "ay").read_bytes()).hexdigest())
        self.assertEqual(identity["banner"], f"ay 0.27.0+build.1.{self.rev}@2026-10-03")
        self.assertEqual(identity["schema"], self.tool.cache_schema)
        self.assertEqual(identity["recipe"]["command"],
                         ["--unverified", "build", "--release", "--locked", *self.tool.build_args])
        self.assertEqual(identity["recipe"]["unverified_export"],
                         GATE.unverified_tool_export((self.repo / "Cargo.toml").read_bytes(), "ay")[1])
        self.assertEqual(identity["recipe"]["cargo_config"], "export's own .cargo/config.toml")
        kept = [path for path in self.cache.iterdir() if path.name.startswith("build-")]
        self.assertEqual(len(kept), 1, kept)
        written = {path.relative_to(kept[0]).as_posix() for path in kept[0].rglob("*")}
        for witness in ("src", "src/run.sh", "src/.cargo/config.toml", "build.log", "target/release/deps/ay-fixture.d",
                        "target/release/.fingerprint/ay-fixture/bin-ay", "target/release/ay"):
            self.assertIn(witness, written)
        self.assertEqual((kept[0] / "src/.cargo/config.toml").read_bytes(),
                         (self.repo / ".cargo/config.toml").read_bytes())
        self.assertEqual(mode(kept[0] / "src" / "run.sh"), 0o700, "the export's executable keeps owner bits only")
        self.assertEqual(open_entries(kept[0]), [])
        self.assertEqual(open_entries(self.xdg), [])
        warm = self.obtain(keep_build=False)
        self.assertEqual((warm["cache"], warm["sha256"]), ("warm", identity["sha256"]))
        if not setgid:
            self.skipTest("this file system keeps no set-group-ID bit on a directory (the rest passed)")

    def test_without_keep_build_only_the_slot_and_its_lock_remain(self):
        self.assertEqual(self.obtain(keep_build=False)["cache"], "cold")
        self.assertEqual(sorted(path.name for path in self.cache.iterdir()),
                         sorted([self.tool.cache_key, f"{self.rev}.lock"]))
        self.assertEqual(open_entries(self.xdg), [])

    def test_an_ancestor_loosened_during_the_build_is_refused_after_it(self):
        """The slot is checked again once it is written: a cache directory
        whose ancestor became group-writable while AY built (here the fixture
        targo loosens it) is refused, never repaired, and the slot is used
        once the owner fixes the ancestor."""
        with self.assertRaises(GATE.Finding) as raised:
            self.obtain(keep_build=False, FIXTURE_LOOSEN=str(self.xdg))
        self.assertEqual(raised.exception.code, "ay-cache-not-private")
        self.assertIn(f"{self.xdg} is not a trusted directory ancestor", raised.exception.message)
        self.assertIn("chmod go-w", raised.exception.message)
        self.assertEqual(mode(self.xdg), 0o775, "never repaired")
        os.chmod(self.xdg, 0o700)
        self.assertEqual(self.obtain(keep_build=False)["cache"], "warm")


class ExportCommitTests(unittest.TestCase):
    """`export-commit`, the attested gate's export of the commit's own
    proofs. X-HOST-P13 sixth closure audit: `git archive` applied the smudge
    filters and attributes of the user's global git configuration (0664 on
    the audited host), so the export held a substitute proof while the
    candidate stayed clean. The export now reads the commit, its trees and
    its blobs from the object store by hash, under no system or global
    configuration and no attributes, and reads its files back against their
    blob hashes."""

    def setUp(self):
        self.base = Path(tempfile.mkdtemp(prefix="private-cache-export-"))
        os.chmod(self.base, 0o700)
        self.addCleanup(shutil.rmtree, self.base, True)
        self.global_config = self.base / "gitconfig"
        self.global_config.write_text("[user]\n\tname = Fixture\n\temail = fixture@example.invalid\n"
                                      "[commit]\n\tgpgSign = false\n")
        self.env = dict(os.environ, GIT_CONFIG_GLOBAL=str(self.global_config), GIT_CONFIG_NOSYSTEM="1")
        self.repo = self.base / "repo"
        self.git("init", "-q", str(self.repo), cwd=self.base)
        files = {"proofs/spec.lean": "-- committed spec\n", "proofs/nested/inner.lean": "-- inner\n",
                 "formal/lean/lakefile.lean": "-- committed lake\n", "formal/lean/run.sh": "#!/bin/sh\n",
                 "formal/other.txt": "not exported\n", "README": "outside\n",
                 ".gitattributes": "proofs/*.lean filter=local\n"}
        for name, text in files.items():
            path = self.repo / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        os.chmod(self.repo / "formal/lean/run.sh", 0o755)
        self.git("add", "-A")
        self.git("commit", "-qm", "fixture")
        self.commit = self.git("rev-parse", "HEAD").strip()

    def git(self, *args: str, cwd: Path | None = None, env: dict | None = None) -> str:
        return subprocess.run(["git", *args], cwd=cwd or self.repo, env=env or self.env, capture_output=True,
                              text=True, check=True).stdout

    def export(self, destination: Path, env: dict | None = None) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, "-I", str(HELPER), "export-commit", str(self.repo), self.commit,
                               str(destination), "proofs", "formal/lean"], capture_output=True, text=True,
                              env=env or self.env, umask=0o002)

    def expected(self) -> dict:
        """relative path -> blob, None for a directory, from `git ls-tree`."""
        listed = {}
        for line in self.git("ls-tree", "-r", "-t", self.commit, "--", "proofs", "formal/lean").splitlines():
            meta, name = line.split("\t", 1)
            kind, oid = meta.split()[1:]
            listed[name] = oid if kind == "blob" else None
        listed["formal"] = None
        return listed

    def test_the_export_is_the_committed_bytes_whatever_the_configuration_says(self):
        attributes = self.base / "attributes"
        attributes.write_text("proofs/spec.lean filter=cogroup\nformal/lean/lakefile.lean filter=cogroup\n")
        with open(self.global_config, "a") as config:
            config.write('[filter "cogroup"]\n\tsmudge = sed s/committed/SUBSTITUTED/\n'
                         f"[core]\n\tattributesFile = {attributes}\n")
        self.git("config", "filter.local.smudge", "sed s/committed/LOCAL/")
        archived = subprocess.run(["git", "-C", str(self.repo), "archive", self.commit, "--", "proofs",
                                   "formal/lean"], capture_output=True, env=self.env, check=True).stdout
        # The in-tree attributes win for proofs/*.lean (the repository's own
        # filter); the global attributes file reaches the lakefile.
        self.assertIn(b"-- LOCAL spec", archived, "`git archive` applies the repository's filter")
        self.assertIn(b"-- SUBSTITUTED lake", archived, "`git archive` applies the global filter")
        destination = self.base / "logs" / "candidate-proofs"
        (self.base / "logs").mkdir(mode=0o700)
        result = self.export(destination)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), os.path.realpath(destination))
        found = {str(path.relative_to(destination)): path for path in destination.rglob("*")}
        self.assertEqual(set(found), set(self.expected()))
        for name, blob in self.expected().items():
            if blob is None:
                self.assertEqual(mode(found[name]), 0o700, name)
                continue
            self.assertEqual(found[name].read_bytes(), self.git("cat-file", "blob", blob).encode(), name)
        self.assertEqual(mode(found["proofs/spec.lean"]), 0o600)
        self.assertEqual(mode(found["formal/lean/run.sh"]), 0o700)
        self.assertEqual(mode(destination), 0o700)
        self.assertNotIn("README", found)

    def test_an_object_that_does_not_hash_to_its_name_is_refused(self):
        blob = self.git("rev-parse", f"{self.commit}:proofs/spec.lean").strip()
        loose = self.repo / ".git" / "objects" / blob[:2] / blob[2:]
        self.assertTrue(loose.is_file())
        import zlib
        data = b"-- SUBSTITUTED in the object store\n"
        staged = loose.parent / "staged"
        staged.write_bytes(zlib.compress(b"blob %d\0" % len(data) + data))
        os.replace(staged, loose)
        self.assertEqual(self.git("cat-file", "blob", blob), data.decode(), "the store now serves other bytes")
        result = self.export(self.base / "candidate-proofs")
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn(f"object {blob} read from the object store does not hash to its name", result.stderr)

    def test_the_read_back_refuses_a_changed_missing_or_extra_entry(self):
        destination = self.base / "candidate-proofs"
        self.assertEqual(self.export(destination).returncode, 0)
        expected = self.expected()
        PC.verify_export(str(destination), expected, "sha1")
        spec = destination / "proofs" / "spec.lean"
        original = spec.read_bytes()
        spec.write_bytes(b"-- changed after it was written\n")
        with self.assertRaisesRegex(PC.ExportError, r"proofs/spec\.lean as written does not hash to its blob"):
            PC.verify_export(str(destination), expected, "sha1")
        spec.write_bytes(original)
        os.chmod(spec, 0o644)
        with self.assertRaisesRegex(PC.ExportError, r"not an owner-only regular file"):
            PC.verify_export(str(destination), expected, "sha1")
        os.chmod(spec, 0o600)
        (destination / "proofs" / "extra.lean").write_text("-- extra\n")
        with self.assertRaisesRegex(PC.ExportError, r"extra \['proofs/extra\.lean'\]"):
            PC.verify_export(str(destination), expected, "sha1")
        (destination / "proofs" / "extra.lean").unlink()
        spec.unlink()
        with self.assertRaisesRegex(PC.ExportError, r"missing \['proofs/spec\.lean'\]"):
            PC.verify_export(str(destination), expected, "sha1")

    def test_a_symlink_entry_and_an_existing_destination_are_refused(self):
        existing = self.base / "exists"
        existing.mkdir()
        result = self.export(existing)
        self.assertEqual(result.returncode, 1)
        self.assertIn(f"{existing} already exists", result.stderr)
        os.symlink("spec.lean", self.repo / "proofs" / "alias.lean")
        self.git("add", "-A")
        self.git("commit", "-qm", "a symlink")
        self.commit = self.git("rev-parse", "HEAD").strip()
        result = self.export(self.base / "with-link")
        self.assertEqual(result.returncode, 1)
        self.assertIn("proofs/alias.lean has mode 120000 (only regular files and directories are exported)",
                      result.stderr)


if __name__ == "__main__":
    unittest.main()
