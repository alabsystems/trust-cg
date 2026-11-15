#!/usr/bin/env python3
"""Record the Git dependency identities a Cargo build resolves on this host.

For every Git source in a Cargo.lock (the TrustIr, Clean and AY companions and
any other Git dependency) this records the source URL, the requested reference,
the pinned 40-hex revision, the packages resolved from it, the Cargo Git
database directory Cargo uses for that URL and whether the revision resolves to
a commit there, and the checkout directory Cargo builds from: the commit its
HEAD names, git's list of its modified, untracked and ignored files, and a
SHA-256 over its tree. It also records the SHA-256 of the Cargo.lock bytes.

Cargo keeps a Git dependency's objects in $CARGO_HOME/git/db/<ident> and builds
from $CARGO_HOME/git/checkouts/<ident>/<short-id>. <ident> is the last path
segment of the canonical URL and a hash of that URL; IDENT_SCHEME is the hash
Cargo 1.85 and later compute. A database under the same name with another
suffix (an older Cargo's hash, or another URL) is listed as other_databases and
never consulted. <short-id> is the revision's shortest unique abbreviation of at
least seven digits in that database; when no such directory exists, a sole
directory abbreviating the revision (a configured core.abbrev lengthens it) is
recorded instead, and every candidate is listed.

TREE_SCHEME walks the checkout without following symlinks, skips every entry
named .git and the top-level .cargo-ok marker Cargo writes, sorts entries by
relative path bytes, and hashes one record per regular file or symlink: its
kind (f regular, x owner-executable, l symlink), the SHA-256 of its content or
link text, and its path, NUL-terminated. Empty directories are not recorded,
as Git does not track them.

This is identity recording. A revision that resolves locally lets
`cargo --locked --offline` start without a fetch; it says nothing about whether
the revision is audited, published, tested or correct. Git's status check is
stat-based; the tree SHA-256 is what binds the bytes.

Exit status: 0 when every identity was recorded (with --require-offline, also
when every pinned revision resolves locally and no finished checkout differs
from it); 1 otherwise; 2 when the lockfile cannot be read.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import struct
import subprocess
import sys
from typing import Mapping, Optional, Sequence
from urllib.parse import parse_qsl, urlsplit


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "trust-cg-dependency-identity-v1"
TREE_SCHEME = "trust-cg-tree-sha256-v1"
IDENT_SCHEME = (
    "cargo>=1.85 git ident: <last canonical URL segment>-<hex(le64(3*h0 + h1))>, "
    "(h0, h1) = SipHash-1-3-128 with zero keys over the canonical URL bytes and 0xff"
)
FULL_REVISION = re.compile(r"[0-9a-f]{40}\Z")
IDENT_SUFFIX = re.compile(r"-[0-9a-f]{16}\Z")
LOCK_HEADER = re.compile(r"^\[\[?[^\]]+\]\]?\s*$")
LOCK_FIELD = re.compile(r'^(name|version|source) = "([^"]*)"\s*$')
CARGO_MARKER = ".cargo-ok"
MARKER_STATUS = {f"?? {CARGO_MARKER}", f"!! {CARGO_MARKER}"}
GIT_TIMEOUT_SECONDS = 120
CHUNK = 1 << 20
MASK = (1 << 64) - 1


# Cargo's git directory naming (cargo::sources::git::source::ident, CanonicalUrl
# and util::hex::short_hash on rustc-stable-hash's StableSipHasher128).

def _rotl(value: int, bits: int) -> int:
    return ((value << bits) | (value >> (64 - bits))) & MASK


def _sip_round(v0: int, v1: int, v2: int, v3: int) -> tuple[int, int, int, int]:
    v0 = (v0 + v1) & MASK
    v1 = _rotl(v1, 13) ^ v0
    v0 = _rotl(v0, 32)
    v2 = (v2 + v3) & MASK
    v3 = _rotl(v3, 16) ^ v2
    v0 = (v0 + v3) & MASK
    v3 = _rotl(v3, 21) ^ v0
    v2 = (v2 + v1) & MASK
    v1 = _rotl(v1, 17) ^ v2
    v2 = _rotl(v2, 32)
    return v0, v1, v2, v3


def siphash13_128(data: bytes) -> tuple[int, int]:
    """SipHash-1-3 with 128-bit output and zero keys."""
    v0, v1 = 0x736F6D6570736575, 0x646F72616E646F6D ^ 0xEE
    v2, v3 = 0x6C7967656E657261, 0x7465646279746573
    whole = len(data) - len(data) % 8
    for offset in range(0, whole, 8):
        (word,) = struct.unpack_from("<Q", data, offset)
        v3 ^= word
        v0, v1, v2, v3 = _sip_round(v0, v1, v2, v3)
        v0 ^= word
    last = (len(data) & 0xFF) << 56
    for index, byte in enumerate(data[whole:]):
        last |= byte << (8 * index)
    v3 ^= last
    v0, v1, v2, v3 = _sip_round(v0, v1, v2, v3)
    v0 ^= last
    v2 ^= 0xEE
    for _ in range(3):
        v0, v1, v2, v3 = _sip_round(v0, v1, v2, v3)
    first = v0 ^ v1 ^ v2 ^ v3
    v1 ^= 0xDD
    for _ in range(3):
        v0, v1, v2, v3 = _sip_round(v0, v1, v2, v3)
    return first, v0 ^ v1 ^ v2 ^ v3


def cargo_short_hash(text: str) -> str:
    """Cargo's short_hash of a hashed str: its bytes, then the 0xff terminator."""
    first, second = siphash13_128(text.encode("utf-8") + b"\xff")
    return struct.pack("<Q", (3 * first + second) & MASK).hex()


def canonical_url(url: str) -> str:
    """Cargo's CanonicalUrl text for a Git source URL (query and fragment removed)."""
    parts = urlsplit(url)
    if not parts.scheme or not parts.netloc:
        raise ValueError(f"not an absolute URL with a host: {url!r}")
    scheme = parts.scheme.lower()
    userinfo, at, hostport = parts.netloc.rpartition("@")
    netloc = f"{userinfo}{at}{hostport.lower()}"
    path = parts.path
    if path.endswith("/"):
        path = path[:-1]
    if (parts.hostname or "") == "github.com":
        scheme, path = "https", path.lower()
    if path.endswith(".git"):
        path = path[:-4]
    return f"{scheme}://{netloc}{path}"


def cargo_git_ident(url: str) -> str:
    """The <ident> directory name Cargo uses for a Git source URL."""
    canonical = canonical_url(url)
    name = urlsplit(canonical).path.rsplit("/", 1)[-1] or "_empty"
    return f"{name}-{cargo_short_hash(canonical)}"


# Cargo.lock parsing.

def describe_git_source(source: str) -> tuple[dict, list[str]]:
    """Split a lock `git+URL?query#revision` source into its recorded parts."""
    base, _, revision = source[len("git+"):].partition("#")
    url, _, query = base.partition("?")
    problems = []
    if FULL_REVISION.match(revision) is None:
        problems.append(f"{url}: pinned revision {revision!r} is not a full 40-hex commit")
    return {
        "source": source, "url": url, "reference": dict(parse_qsl(query, keep_blank_values=True)),
        "revision": revision,
    }, problems


def parse_lock_git_sources(text: str, label: str = "Cargo.lock") -> tuple[list[dict], list[str]]:
    """Group the lock's Git-sourced packages by exact source string, in file order."""
    sources: dict[str, dict] = {}
    errors: list[str] = []

    def finish(package: Optional[dict]) -> None:
        if package is None or not package.get("source", "").startswith("git+"):
            return
        entry = sources.get(package["source"])
        if entry is None:
            entry, problems = describe_git_source(package["source"])
            entry.update({"lock_line": package["source_line"], "packages": []})
            errors.extend(f"{label}:{package['source_line']}: {problem}" for problem in problems)
            sources[package["source"]] = entry
        entry["packages"].append(f"{package.get('name', '?')} {package.get('version', '?')}")

    package: Optional[dict] = None
    for number, line in enumerate(text.splitlines(), 1):
        if LOCK_HEADER.match(line):
            finish(package)
            package = {} if line.strip() == "[[package]]" else None
            continue
        field = LOCK_FIELD.match(line)
        if package is None or field is None:
            continue
        key, value = field.groups()
        if key in package:
            errors.append(f"{label}:{number}: duplicate {key} field in one package")
        package[key] = value
        if key == "source":
            package["source_line"] = number
    finish(package)
    return list(sources.values()), errors


# Local Cargo state.

def git_environment(base: Optional[Mapping[str, str]] = None) -> dict:
    """Drop every GIT_* variable so an inherited GIT_DIR cannot redirect a query."""
    return {
        name: value for name, value in (os.environ if base is None else base).items()
        if not name.startswith("GIT_")
    }


def run_git(git: str, git_dir: Path, *arguments: str, work_tree: Optional[Path] = None) -> tuple[int, str, str]:
    """Run git against an explicit repository; failures are data, not exceptions."""
    command = [git, "--no-optional-locks", f"--git-dir={git_dir}"]
    if work_tree is not None:
        command.append(f"--work-tree={work_tree}")
    try:
        result = subprocess.run(
            [*command, *arguments], cwd=str(work_tree or git_dir.parent), capture_output=True,
            timeout=GIT_TIMEOUT_SECONDS, check=False, env=git_environment(),
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        return 125, "", str(error)
    return (
        result.returncode, result.stdout.decode("utf-8", errors="replace"),
        result.stderr.decode("utf-8", errors="replace").strip(),
    )


def resolve_commit(git: str, git_dir: Path, revision: str) -> tuple[bool, str]:
    code, stdout, stderr = run_git(git, git_dir, "rev-parse", "--verify", "--quiet", f"{revision}^{{commit}}")
    if code == 0 and stdout.strip() == revision:
        return True, "resolves"
    if code == 1 and not stderr:
        return False, "absent"
    return False, f"git exited {code}: {stderr or stdout.strip()}"


def home_directory(environment: Mapping[str, str]) -> Path:
    """The home directory Rust's `std::env::home_dir` gives Cargo: HOME when it
    is set and not empty, else the user's password-database entry. (Python's
    `Path.home()` differs: it returns an empty HOME as the current directory.)"""
    home = environment.get("HOME")
    if home:
        return Path(home)
    import pwd

    return Path(pwd.getpwuid(os.getuid()).pw_dir)


def cargo_home_from(environment: Mapping[str, str], cwd: Path = ROOT) -> tuple[Path, str]:
    """Cargo's home for a command started in cwd, resolved as Cargo does
    (`home::cargo_home_with_cwd`): a non-empty CARGO_HOME, else
    `home_directory()/.cargo`, either joined to cwd when relative. This is
    the one resolver the dependency record and the Cargo config audit share."""
    configured = environment.get("CARGO_HOME")
    if configured:
        path = Path(configured)
        return (path if path.is_absolute() else cwd / path), "CARGO_HOME"
    home = home_directory(environment)
    return (home if home.is_absolute() else cwd / home) / ".cargo", "default"


def tree_sha256(root: Path) -> tuple[str, int, int]:
    """Return (TREE_SCHEME digest, file count, content bytes) for a checkout."""
    entries: list[tuple[bytes, str, str]] = []
    pending = [(str(root), b"")]
    while pending:
        directory, prefix = pending.pop()
        with os.scandir(directory) as listing:
            for entry in listing:
                if entry.name == ".git" or (not prefix and entry.name == CARGO_MARKER):
                    continue
                relative = prefix + os.fsencode(entry.name)
                mode = entry.stat(follow_symlinks=False).st_mode
                if stat.S_ISLNK(mode):
                    entries.append((relative, "l", entry.path))
                elif stat.S_ISDIR(mode):
                    pending.append((entry.path, relative + b"/"))
                elif stat.S_ISREG(mode):
                    entries.append((relative, "x" if mode & stat.S_IXUSR else "f", entry.path))
                else:
                    raise OSError(f"unsupported file kind in dependency tree: {entry.path}")
    entries.sort(key=lambda row: row[0])
    tree = hashlib.sha256(TREE_SCHEME.encode("ascii") + b"\0")
    total = 0
    for relative, kind, path in entries:
        digest = hashlib.sha256()
        if kind == "l":
            digest.update(os.readlink(os.fsencode(path)))
        else:
            before = os.lstat(path)
            with open(path, "rb") as source:
                for chunk in iter(lambda: source.read(CHUNK), b""):
                    digest.update(chunk)
            after = os.lstat(path)
            if (before.st_size, before.st_mtime_ns, before.st_ino) != (after.st_size, after.st_mtime_ns, after.st_ino):
                raise OSError(f"dependency tree file changed during hashing: {path}")
            total += after.st_size
        tree.update(kind.encode("ascii") + b" " + digest.hexdigest().encode("ascii") + b" " + relative + b"\0")
    return tree.hexdigest(), len(entries), total


def locate_checkout(checkouts: Path, revision: str, short_id: Optional[str]) -> tuple[Optional[Path], list[str]]:
    """The checkout Cargo uses, plus every present directory abbreviating the revision."""
    candidates = sorted(
        entry.name for entry in (checkouts.iterdir() if checkouts.is_dir() else ())
        if entry.is_dir() and len(entry.name) >= 7 and revision.startswith(entry.name)
    )
    if short_id is not None and (checkouts / short_id).is_dir():
        return checkouts / short_id, candidates
    # A configured core.abbrev can lengthen Cargo's abbreviation, and without
    # the database none can be computed; a sole candidate is still recorded.
    if len(candidates) == 1:
        return checkouts / candidates[0], candidates
    return (None if short_id is None else checkouts / short_id), candidates


def describe_checkout(git: str, path: Optional[Path], revision: str, hash_trees: bool) -> dict:
    record: dict = {
        "path": None if path is None else str(path), "present": False, "cargo_ok": False,
        "head": None, "head_matches": False, "modifications": None,
        "tree_sha256": None, "files": None, "bytes": None, "errors": [],
    }
    if path is None or not path.is_dir():
        return record
    record["present"] = True
    record["cargo_ok"] = (path / CARGO_MARKER).is_file()
    code, stdout, stderr = run_git(git, path / ".git", "rev-parse", "--verify", "--quiet", "HEAD^{commit}")
    if code == 0:
        record["head"] = stdout.strip()
        record["head_matches"] = record["head"] == revision
    else:
        record["errors"].append(f"checkout HEAD is unreadable (git exited {code}: {stderr})")
    code, stdout, stderr = run_git(
        git, path / ".git", "status", "--porcelain=v1", "--untracked-files=all", "--ignored=matching",
        work_tree=path,
    )
    if code == 0:
        record["modifications"] = [line for line in stdout.splitlines() if line and line not in MARKER_STATUS]
    else:
        record["errors"].append(f"checkout status is unreadable (git exited {code}: {stderr})")
    if hash_trees:
        try:
            record["tree_sha256"], record["files"], record["bytes"] = tree_sha256(path)
        except OSError as error:
            record["errors"].append(f"checkout tree could not be hashed: {error}")
    return record


def describe_local(source: dict, cargo_home: Path, git: Optional[str], hash_trees: bool) -> None:
    """Attach the Cargo Git database and checkout state of one lock source."""
    database: dict = {
        "path": None, "present": False, "revision_resolves": False, "detail": None,
        "short_id": None, "other_databases": [],
    }
    source["database"] = database
    source["checkout"] = describe_checkout(git or "git", None, source["revision"], False)
    try:
        ident = cargo_git_ident(source["url"])
    except ValueError as error:
        database["detail"] = str(error)
        return
    name = ident[: -len("-0123456789abcdef")]
    databases = cargo_home / "git" / "db"
    path = databases / ident
    database.update({"path": str(path), "present": path.is_dir()})
    if databases.is_dir():
        database["other_databases"] = sorted(
            entry.name for entry in databases.iterdir()
            if entry.name != ident and entry.name.startswith(f"{name}-")
            and IDENT_SUFFIX.search(entry.name[len(name):]) is not None
        )
    revision = source["revision"]
    if git is None:
        database["detail"] = "git executable not found"
    elif FULL_REVISION.match(revision) is None:
        database["detail"] = "the lock pins no full revision"
    elif not database["present"]:
        database["detail"] = "database directory is absent"
    else:
        database["revision_resolves"], database["detail"] = resolve_commit(git, path, revision)
        if database["revision_resolves"]:
            code, stdout, stderr = run_git(git, path, "rev-parse", "--verify", "--short=7", revision)
            if code == 0 and revision.startswith(stdout.strip()) and len(stdout.strip()) >= 7:
                database["short_id"] = stdout.strip()
            else:
                database["detail"] = f"revision resolves but its abbreviation is unreadable: {stderr}"
                database["revision_resolves"] = False
    checkout, candidates = locate_checkout(
        cargo_home / "git" / "checkouts" / ident, revision, database["short_id"],
    )
    source["checkout"] = describe_checkout(git or "git", checkout if git else None, revision, hash_trees)
    source["checkout"]["candidates"] = candidates


def collect(
    lock_path: Path, cargo_home: Path, *, git: str = "git", hash_trees: bool = True,
    cargo_home_source: str = "argument",
) -> dict:
    """Record every Git source of a lockfile against a Cargo home."""
    executable = shutil.which(git)
    identity: dict = {
        "schema": SCHEMA,
        "scope": "dependency identity recording; not audit, publication or correctness evidence",
        "lockfile": str(lock_path), "lockfile_sha256": None,
        "cargo_home": str(cargo_home), "cargo_home_source": cargo_home_source,
        "ident_scheme": IDENT_SCHEME, "tree_scheme": TREE_SCHEME if hash_trees else None,
        "git": executable, "sources": [], "errors": [], "offline_ready": False,
    }
    if executable is None:
        identity["errors"].append(f"git executable {git!r} not found; no revision can be resolved")
    try:
        data = lock_path.read_bytes()
    except OSError as error:
        identity["errors"].append(f"cannot read {lock_path}: {error}")
        return identity
    identity["lockfile_sha256"] = hashlib.sha256(data).hexdigest()
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        identity["errors"].append(f"{lock_path} is not UTF-8: {error}")
        return identity
    sources, errors = parse_lock_git_sources(text, lock_path.name)
    identity["errors"].extend(errors)
    for source in sources:
        describe_local(source, cargo_home, executable, hash_trees)
        identity["sources"].append(source)
    identity["offline_ready"] = not offline_problems(identity)
    return identity


def offline_problems(identity: Mapping) -> list[str]:
    """Why a --locked --offline build could not use exactly the pinned revisions."""
    problems = [str(error) for error in identity.get("errors", [])]
    if identity.get("lockfile_sha256") is None and not problems:
        problems.append("the lockfile was not read")
    for source in identity.get("sources", []):
        label = f"{source.get('url')} {str(source.get('revision'))[:12]}"
        database = source.get("database") or {}
        if not database.get("revision_resolves"):
            problems.append(
                f"{label}: pinned revision does not resolve in the local Cargo Git database "
                f"{database.get('path')} ({database.get('detail')})"
            )
        checkout = source.get("checkout") or {}
        # Cargo discards and re-extracts a checkout that lacks its marker, so
        # only a finished checkout is what a build would compile.
        if checkout.get("present") and checkout.get("cargo_ok"):
            if not checkout.get("head_matches"):
                problems.append(f"{label}: checkout {checkout.get('path')} HEAD {checkout.get('head')} is not the pinned revision")
            if checkout.get("modifications"):
                problems.append(
                    f"{label}: checkout {checkout.get('path')} differs from its HEAD "
                    f"({len(checkout['modifications'])} entries, first: {checkout['modifications'][0]})"
                )
            problems.extend(f"{label}: {error}" for error in checkout.get("errors", []))
    return problems


def identity_changes(before: Mapping, after: Mapping) -> list[str]:
    """Differences between two records of one run that mean the build used other bytes.

    A record that cannot show the bytes are unchanged counts as a change: a
    present checkout hashed before the run but not after, and a finished
    checkout that appeared during the run (Cargo extracted it) whose HEAD,
    status or, when trees are hashed, tree SHA-256 does not bind it to the pin.
    """
    changes = []
    if before.get("lockfile_sha256") != after.get("lockfile_sha256"):
        changes.append("Cargo.lock bytes changed")

    def keyed(identity: Mapping) -> dict:
        return {(str(row.get("url")), str(row.get("revision"))): row for row in identity.get("sources", [])}

    first, last = keyed(before), keyed(after)
    hashed = bool(after.get("tree_scheme"))
    for key in sorted(set(first) ^ set(last)):
        changes.append(f"git source {key[0]} {key[1][:12]} recorded only {'before' if key in first else 'after'} the run")
    for key in sorted(set(first) & set(last)):
        label = f"{key[0]} {key[1][:12]}"
        early, late = first[key].get("checkout") or {}, last[key].get("checkout") or {}
        if early.get("tree_sha256") and late.get("tree_sha256") and early["tree_sha256"] != late["tree_sha256"]:
            changes.append(f"checkout tree of {label} changed during the run")
        if early.get("present") and late.get("present") and early.get("path") != late.get("path"):
            changes.append(f"checkout of {label} moved during the run")
        if early.get("present") and not late.get("present"):
            changes.append(f"checkout of {label} disappeared during the run")
        if early.get("tree_sha256") and late.get("present") and not late.get("tree_sha256"):
            changes.append(
                f"checkout tree of {label} was not re-hashed after the run: {'; '.join(late.get('errors') or []) or 'no hash'}"
            )
        if late.get("present") and late.get("cargo_ok") and not (early.get("present") and early.get("cargo_ok")):
            reasons = []
            if not late.get("head_matches"):
                reasons.append(f"HEAD {late.get('head')} is not the pinned revision")
            if late.get("modifications") is None or late.get("modifications"):
                reasons.append(f"status {'unreadable' if late.get('modifications') is None else late['modifications'][:3]}")
            if hashed and not late.get("tree_sha256") and not early.get("tree_sha256"):
                reasons.append("tree not hashed")
            reasons.extend(late.get("errors") or [])
            if reasons:
                changes.append(
                    f"checkout of {label} extracted during the run is not bound to the pin: {'; '.join(map(str, reasons))}"
                )
    return changes


def summary_lines(identity: Mapping) -> list[str]:
    lines = [
        f"lockfile {identity['lockfile']} sha256 {identity['lockfile_sha256']}",
        f"cargo home {identity['cargo_home']} ({identity['cargo_home_source']})",
    ]
    for source in identity["sources"]:
        database, checkout = source["database"], source["checkout"]
        state = "resolves" if database["revision_resolves"] else f"MISSING ({database['detail']})"
        lines.append(f"{source['url']} {source['revision']}: {state} in {database['path']}")
        if checkout["present"]:
            tree = checkout["tree_sha256"] or "not hashed"
            lines.append(
                f"  checkout {checkout['path']} head {checkout['head']} tree {tree} "
                f"({checkout['files']} files) modifications {len(checkout['modifications'] or [])}"
            )
        else:
            lines.append("  no extracted checkout")
    lines.extend(f"error: {error}" for error in identity["errors"])
    return lines


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0], allow_abbrev=False)
    parser.add_argument("--lock", type=Path, default=ROOT / "Cargo.lock", help="lockfile to record (default: this checkout's Cargo.lock)")
    parser.add_argument("--cargo-home", type=Path, help="Cargo home (default: $CARGO_HOME, else $HOME/.cargo)")
    parser.add_argument("--git", default="git", help="git executable used to query the Cargo Git databases")
    parser.add_argument("--no-tree-hash", action="store_true", help="skip the checkout tree SHA-256 (recording only)")
    parser.add_argument("--json", action="store_true", help="print the identity record as JSON")
    parser.add_argument(
        "--require-offline", action="store_true",
        help="exit 1 unless every pinned revision resolves locally and no finished checkout differs from it",
    )
    args = parser.parse_args(argv)
    if args.cargo_home is None:
        cargo_home, origin = cargo_home_from(os.environ, Path.cwd())
    else:
        cargo_home, origin = args.cargo_home.absolute(), "argument"
    identity = collect(args.lock, cargo_home, git=args.git, hash_trees=not args.no_tree_hash, cargo_home_source=origin)
    print(json.dumps(identity, indent=2) if args.json else "\n".join(summary_lines(identity)))
    if identity["lockfile_sha256"] is None:
        return 2
    problems = offline_problems(identity)
    if args.require_offline:
        for problem in problems:
            print(f"--require-offline: {problem}", file=sys.stderr)
    return 1 if identity["errors"] or (args.require_offline and problems) else 0


if __name__ == "__main__":
    raise SystemExit(main())
