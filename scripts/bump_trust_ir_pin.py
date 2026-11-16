#!/usr/bin/env python3
"""Atomically move TrustCG's existing TrustIR/Clean/AY source cohort.

Usage: python3 scripts/bump_trust_ir_pin.py <40-hex-TrustIR-revision> \
           --targo /absolute/path/to/targo [--ay-revision <40-hex-AY-revision>] \
           [--ay-version 0.28.0] \
           [--ir-version 0.15.0] \
           [--clean-version 0.9.2] \
           [--admit-ir-package <trust-ir-NAME> ...] [--admit-ay-package <ay-NAME> ...] \
           [--admit-dropped-package <NAME> ...] \
           [--admit-registry-package <nix@0.29.0|cfg_aliases@0.2.1|cfg_aliases@0.2.2|wait-timeout@0.2.1> ...]

This narrowly owns four manifests, three independent locks and both cache
salts in one source file. AY stays unchanged unless explicitly selected.
It does not stage Git changes, refresh a soundness
attestation, or qualify upstream source. The caller must separately qualify the
immutable target and authenticate its explicitly selected Targo executable.
Metadata/update are noncompiling commands; the mandatory Rust guards use the
explicit unverified compilation lane, without a stock Cargo fallback. Eight
guards close the transaction, each receipt held to its exact reviewed test
names (`rust_guard_transcript.py`), and a red one rolls every file back: the
dependency-authority guard (the moved pins agree everywhere), then the two
inventories derived from TrustIR source, re-derived against the target
(trust-cg-verify `tests/fsym_ub_map.rs`, which reads the interpreter at the
locked revision, and trust-cg-lower `tests/trust_ir_construct_inventory.rs`,
whose exhaustive census and re-driven refusals run against it), then the
three CONFORMANCE FIXTURE guards (LD-84) — the corpus
census, trust-cg-codegen `tests/trust_ir_corpus_roundtrip.rs`, over the
TARGET revision's conformance corpus, and the vendored container fixtures
(`tests/fixtures/trust_ir_binary_container/`, whose `conformance/` goldens and
JSON twins the codegen target requires byte-identical to that corpus's
top-level ones, `compat_v22_composition.tmbc` excepted) through trust-cg-codegen
and trust-cg-cli `tests/trust_ir_binary_container.rs`; a red one names what
to update for the target — then, last, the MUST-REFUSE CORPUS guard (KIND 4,
2026-09-24) — trust-cg-codegen's `tests/must_refuse_corpus.rs`, which drives
every row of the TARGET revision's must-refuse corpus (`trust-ir-conformance`,
feature `must-refuse`) through this backend's real admission paths and fails
by name on a row the new pin adds that this backend still compiles. A TrustIR
pin bump is therefore not complete until every guard is green; the
transaction cannot leave a moved pin whose corpus this backend does not
refuse, or whose census or vendored fixtures are still the old pin's. The
inventories, the census and the vendored fixtures are updated for the target
before the transaction runs (their files are not owned, so they may be
uncommitted); each guard source must be byte-identical before and after its
own run, and the vendored fixture tree through the end of the transaction.

Only source moves within the existing package cohort are supported. Adding or
removing packages, changing third-party resolution, or changing package
versions requires a separately reviewed migration, not an automatic resolver
expansion. The reviewed `--ir-version 0.15.0` migration admits only the
0.14.0 to 0.15.0 TrustIR version move, authenticated at the requested immutable
target, with the same package roster and source-qualified external graph.
It retains all eight mandatory Rust guards and the original rollback contract.
The reviewed `--clean-version 0.9.2` migration admits only the 0.9.1 to 0.9.2
Clean version move co-owned by that immutable TrustIR target. It rewrites only
the direct Clean requirements and source-qualified Clean cohort identities;
the package roster, third-party graph, eight guards and rollback stay exact.
The reviewed `--ay-version 0.28.0` migration requires an explicit
AY revision, immutable TrustIR/Clean co-ownership at the selected version,
the same package roster and complete source-qualified non-AY graph checks.
AY0.28's actual required ay-sys macOS policy dependency retains its independent
excluded workspace/version0.13 owner and sole libc edge. A foreign same-source
package or a module-wide name census cannot stand in for that exact route.
Explicit named registry intake is limited to nix0.29.0, its cfg_aliases0.2.1
build dependency and wait-timeout0.2.1. The selected immutable AY request and
lock checksums plus actual archive manifests own every newly selected edge;
prior registry nodes and every other external edge remain exact. Only a newly
introduced node may receive a Cargo precise-version constraint. These are
source-graph checks, without installed policy, resource or proof authority.
No version is inferred from a remote tip. The reviewed workspace widening is
`--admit-ir-package NAME`: the caller
NAMES a new TrustIR workspace crate, and it joins the cohort only when the
fetched target defines it as a `crates/NAME` member at the cohort version, an
already-admitted TrustIR package declares it as a non-dev dependency, and its
own non-dev dependencies are TrustIR workspace paths inside the widened cohort
(so no registry, Git or third-party package can enter with it). Each lock must
then gain it exactly where a requiring package is resolved, and its lock edges
must stay inside the cohort; an unnamed new package still refuses the move. An
AY move requires immutable TrustIR and Clean co-ownership of the explicit
target. Its one reviewed widening is `--admit-ay-package NAME`, only with an
AY move: the caller NAMES a new AY workspace package, and it joins the AY
cohort only when the fetched AY target defines it as a member at the cohort
version and a package already in the AY cohort declares it as a non-dev
dependency there; each lock may then gain it only where such a requirer is
resolved, at the cohort version and the target revision, and its own lock
edges are held to its immutable manifest like every AY row's (so a
third-party package can enter only if the lock already resolves it). The one
reviewed narrowing is `--admit-dropped-package NAME` (LD-PIN2A43-1): the caller
NAMES a third-party registry package a current lock resolves, and where the
target's resolution drops it (Clean `d618ceed7` stops enabling Tokio's macros,
so `tokio-macros` leaves), its row and the edges to it may vanish and nothing
else may change; a named package that leaves no lock refuses the move. Any
failed installed transaction restores all eight files.

Immutable GitHub authorities are fetched through Agh's owner-routed client,
with complete main ancestry in a private blobless Git store. Native Agh cat
bytes are authenticated against the selected tree's Git blob identity before
decoding, with Git lazy fetching disabled. An explicit --authority-cache
NAME=/absolute/source/repo can instead borrow source Git objects after fresh
Agh admission and exact remote commit authentication. Every consumed commit,
tree and blob is hash-checked back to that identity; no index, build artifact
or cached verdict is read. Missing/refused Agh operations have no direct Git,
anonymous or offline fallback and cannot install a pin. All Rust guards remain
mandatory for either source transport.

Before publishing a mutually dependent certificate rule, an explicit
--stage-qualification-ir-source /absolute/repo with --qualification-receipt
/absolute/receipt.json stages the SAME manifest/lock transaction against an
immutable local IR commit. This is untrusted candidate source DATA, not remote
authority: Clean and AY still require normal authenticated source, the complete
selected IR tree and commit ancestry must exist, and every consumed object is
hash-checked. Its resolver commands are offline: provision missing candidate
objects through the maintained explicit local source-DATA transport first.
This mode exits 3 after locked graph checks, without the eight
Rust guards, adoption or publication. Its receipt retains original bytes for
restoration. Restore those bytes and run the ordinary transaction after the IR
commit is published; this mode never turns a local object into published input.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
from dataclasses import dataclass, field
import fcntl
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
sys.path.insert(0, str(Path(__file__).resolve().parent))
import ay_exec_policy_owner as exec_policy
import ay_registry_source_owner as registry_owner
# Prefer the standard parser. Maintenance must not require installing another
# runtime when this host already has a TOML 1.0 parser (including pip's copy).
try:
    import tomllib
except ModuleNotFoundError:
    try:
        import tomli as tomllib
    except ModuleNotFoundError:
        try:
            from pip._vendor import tomli as tomllib
        except (ImportError, ModuleNotFoundError) as error:
            raise SystemExit("REFUSED: no installed TOML parser (tomllib or tomli)") from error
from typing import Iterator

from rust_guard_transcript import GUARD_TEST_NAMES, validate_rust_test_transcript


IR_URL = "https://github.com/alabsystems/trust-ir.git"
CLEAN_URL = "https://github.com/alabsystems/clean.git"
AY_URL = "https://github.com/alabsystems/ay.git"
AUTHORITY_REF = "refs/agh/compiler-pin-source"
REGISTRY = "registry+https://github.com/rust-lang/crates.io-index"
LOCKS = (
    "Cargo.lock",
    "crates/rustc-codegen-trust-cg/Cargo.lock",
    "fuzz/Cargo.lock",
)
MANIFESTS = ("Cargo.toml", "crates/rustc-codegen-trust-cg/Cargo.toml")
REGALLOC = "crates/trust-cg-regalloc/Cargo.toml"
VERIFY = "crates/trust-cg-verify/Cargo.toml"
CACHE = "crates/trust-cg-codegen/src/compile_artifact_cache_profile.rs"
OWNED = (*MANIFESTS, REGALLOC, VERIFY, *LOCKS, CACHE)
GUARD = "crates/trust-cg-test/tests/dependency_authority.rs"
CORPUS_GUARD = "crates/trust-cg-codegen/tests/must_refuse_corpus.rs"
# (guard source, package, integration target): the inventories derived from
# TrustIR source. Running them against the moved pin is the re-derivation.
INVENTORY_GUARDS = (
    ("crates/trust-cg-verify/tests/fsym_layout.rs", "trust-cg-verify", "fsym_layout"),
    ("crates/trust-cg-verify/tests/fsym_ub_map.rs", "trust-cg-verify", "fsym_ub_map"),
    ("crates/trust-cg-lower/tests/trust_ir_construct_inventory.rs", "trust-cg-lower",
     "trust_ir_construct_inventory"),
)
# The conformance data this backend keeps in step with the pin by hand, in run
# order: (guard source, package, integration target, what a red run asks the
# mover to update for the target). The census reads the target's corpus; the
# two container targets read the copy vendored under VENDORED_FIXTURES.
FIXTURE_GUARDS = (
    ("crates/trust-cg-codegen/tests/trust_ir_corpus_roundtrip.rs", "trust-cg-codegen",
     "trust_ir_corpus_roundtrip",
     "the corpus census in crates/trust-cg-codegen/tests/trust_ir_corpus_roundtrip.rs "
     "(CENSUS, TEMPLATE_FILES and the named-exception tables), measured on the target corpus"),
    ("crates/trust-cg-codegen/tests/trust_ir_binary_container.rs", "trust-cg-codegen",
     "trust_ir_binary_container",
     "the vendored fixtures: re-vendor tests/fixtures/trust_ir_binary_container/conformance "
     "from the target's crates/trust-ir-conformance/tests/fixtures and record it in its "
     "SOURCE.txt, then CONFORMANCE_FIXTURE_COUNT and NEWEST_MODULE_VERSION in "
     "crates/trust-cg-codegen/tests/trust_ir_binary_container.rs"),
    ("crates/trust-cg-cli/tests/trust_ir_binary_container.rs", "trust-cg-cli",
     "trust_ir_binary_container",
     "the re-vendored fixtures' verdicts in crates/trust-cg-cli/tests/"
     "trust_ir_binary_container.rs (COMPILING_FIXTURES, NAMED_REFUSALS); "
     "re-vendor tests/fixtures/trust_ir_binary_container/conformance first if it is stale"),
)
VENDORED_FIXTURES = "tests/fixtures/trust_ir_binary_container"
CACHE_NAME = "COMPILE_ARTIFACT_DEFAULT_TRUST_IR_IDENTITY"
AY_CACHE_NAME = "COMPILE_ARTIFACT_DEFAULT_AY_IDENTITY"
AY_VERSION_MIGRATION = ("0.27.0", "0.28.0")
CLEAN_VERSION_MIGRATION = ("0.9.1", "0.9.2")
IR_VERSION_MIGRATION = ("0.14.0", "0.15.0")
SHA = re.compile(r"[0-9a-f]{40}\Z")


class Refusal(Exception):
    """The requested transaction is unsupported or failed closed."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Refusal(message)


def exact_sha(value: str) -> str:
    require(isinstance(value, str) and SHA.fullmatch(value) is not None,
            "revision must be exactly 40 lowercase hexadecimal characters")
    return value


def checked_git_blob(data: bytes, expected: str) -> bytes:
    """Authenticate exact transport bytes before any decoding or parsing."""
    require(isinstance(data, bytes) and len(data) <= 32 * 1024 * 1024,
            "immutable blob transport must return bounded raw bytes")
    require(SHA.fullmatch(expected) is not None, "invalid immutable blob identity")
    header = b"blob " + str(len(data)).encode("ascii") + b"\0"
    require(hashlib.sha1(header + data).hexdigest() == expected,
            "immutable blob bytes do not match authenticated Git tree")
    return data


def source(url: str, revision: str) -> str:
    return f"git+{url}?rev={revision}#{revision}"


def family(name: str, prefix: str) -> bool:
    return name == prefix or name.startswith(prefix + "-")


def document(data: bytes, label: str) -> dict:
    try:
        return tomllib.loads(data.decode("utf-8"))
    except (UnicodeError, tomllib.TOMLDecodeError) as error:
        raise Refusal(f"{label}: invalid TOML: {error}") from error


def pin(dependency: dict, url: str, label: str) -> str:
    require(isinstance(dependency, dict), f"{label}: expected a dependency table")
    require(dependency.get("git") == url, f"{label}: unexpected repository authority")
    require(not {"path", "branch", "tag"}.intersection(dependency),
            f"{label}: mixed or mutable source selectors are forbidden")
    return exact_sha(dependency.get("rev", ""))


def dependency(doc: dict, workspace: bool, name: str, label: str) -> dict:
    table = doc.get("workspace", {}) if workspace else doc
    value = table.get("dependencies", {}).get(name)
    require(isinstance(value, dict), f"{label}: missing {name} dependency")
    return value


def safe_file(root: Path, relative: str) -> Path:
    path = root
    for component in Path(relative).parts:
        path /= component
        require(not path.is_symlink(), f"symlink in controlled path: {relative}")
    require(path.is_file(), f"missing regular file: {relative}")
    info = path.stat()
    require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
            f"controlled file is not a singly linked regular file: {relative}")
    return path


def guard_tree(root: Path, relative: str) -> dict[str, bytes]:
    """Every file of a guard's data directory, by path: no link, no other entry kind."""
    base = root
    for component in Path(relative).parts:
        base /= component
        require(not base.is_symlink(), f"symlink in guard data path: {relative}")
    require(base.is_dir(), f"missing guard data directory: {relative}")

    def unreadable(error: OSError) -> None:
        raise Refusal(f"unreadable guard data under {relative}: {error}")

    files = {}
    for directory, subdirectories, names in os.walk(base, onerror=unreadable):
        subdirectories.sort()
        for name in subdirectories:
            require(not (Path(directory) / name).is_symlink(),
                    f"symlink in guard data: {relative}")
        for name in sorted(names):
            path = (Path(directory) / name).relative_to(root).as_posix()
            files[path] = safe_file(root, path).read_bytes()
    require(bool(files), f"empty guard data directory: {relative}")
    return files


@dataclass(frozen=True)
class Snapshot:
    data: bytes
    mode: int


def snapshot(root: Path) -> dict[str, Snapshot]:
    return {
        relative: Snapshot(path.read_bytes(), stat.S_IMODE(path.stat().st_mode))
        for relative in OWNED
        for path in [safe_file(root, relative)]
    }


def unchanged(root: Path, expected: dict[str, Snapshot]) -> None:
    require(snapshot(root) == expected,
            "controlled source changed while the transaction was preparing")


def install(root: Path, relative: str, data: bytes, mode: int, *, recovery: bool = False) -> None:
    if recovery:
        # A failed resolver may have removed a lock, replaced it with a link,
        # or left a hard link. Replace that directory entry without following
        # it; never follow a changed parent into somebody else's directory.
        path = root
        for component in Path(relative).parts[:-1]:
            path /= component
            require(not path.is_symlink() and path.is_dir(),
                    f"unsafe restoration parent: {relative}")
        path /= Path(relative).name
        require(not path.is_dir() or path.is_symlink(), f"restoration target became a directory: {relative}")
    else:
        path = safe_file(root, relative)
    # Keep staging in the same validated parent, making replacement atomic for
    # each file. The transaction-level rollback covers the complete owned set.
    descriptor, temporary = tempfile.mkstemp(prefix=".compiler-pin-", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as output:
            output.write(data)
            output.flush()
            os.fchmod(output.fileno(), mode)
            os.fsync(output.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def restore(root: Path, before: dict[str, Snapshot]) -> None:
    errors = []
    for relative, saved in before.items():
        try:
            install(root, relative, saved.data, saved.mode, recovery=True)
        except BaseException as error:
            errors.append(f"{relative}: {type(error).__name__}: {error}")
    if errors:
        raise Refusal("ROLLBACK INCOMPLETE; preserve this checkout for recovery: "
                      + "; ".join(errors))
    unchanged(root, before)


def resource_fds(env: dict[str, str]) -> tuple[int, ...]:
    """Preserve only advertised live transport descriptions, never grant authority.

    The native owners still authenticate GNU/SDK/CPU custody. A Python launch
    must not silently close its caller's actual descriptions or pass unrelated
    descriptors. Malformed or closed locators refuse before running a row.
    """
    descriptors: set[int] = set()

    def add(word: str, name: str) -> None:
        if not re.fullmatch(r"[1-9][0-9]{0,9}", word) or int(word) < 3:
            raise Refusal(f"inherited resources: malformed {name} descriptor")
        descriptor = int(word)
        try:
            os.fstat(descriptor)
        except (OSError, OverflowError) as error:
            raise Refusal(f"inherited resources: {name} descriptor is not live") from error
        descriptors.add(descriptor)

    for name in ("ATERM_SDK_LEASE_V3", "ATERM_WORKLOAD_HOST_STORE_FD_V1",
                 "TRUST_CPU_IMPLICIT_FD"):
        if name in env:
            add(env[name], name)
    fixed_name = "TRUST_FIXED_ADMISSION_FD_V1"
    if fixed_name in env:
        if env[fixed_name] == "requires-live-ancestor-v1":
            # The native nested owner deliberately advertises no direct FD.
            # Preserve its opaque locator; Targo authenticates the ancestor.
            require(bool(env.get("TRUST_FIXED_CLAIM_HANDOFF_V1")),
                    "inherited resources: fixed marker needs its original ancestor advertisement")
        else:
            add(env[fixed_name], fixed_name)
    for name in ("ATERM_WORKLOAD_CPU_FDS_V1", "BUILD_SLOT_FENCE_FDS"):
        if name in env:
            words = env[name].split(",")
            if not 1 <= len(words) <= 128 or len(set(words)) != len(words):
                raise Refusal(f"inherited resources: malformed {name} descriptor set")
            for word in words:
                add(word, name)
    # FIFO/path and native handoff advertisements are deliberately left intact
    # for the maintained GNU importer. Only its numeric pipe transport needs
    # descriptor inheritance at this Python boundary.
    for name in ("CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"):
        # GNU uses the last auth advertisement, even when it disables the
        # jobserver or selects a non-pipe style. Legacy fds is only a fallback,
        # matching the maintained GNU importer; never revive an obsolete pipe.
        value = ""
        for spelling in ("auth", "fds"):
            advertisements = re.findall(
                rf"(?:^|\s)--jobserver-{spelling}=([^\s]*)", env.get(name, ""))
            if advertisements:
                value = advertisements[-1]
                break
        pair = re.fullmatch(r"([0-9]+),([0-9]+)", value)
        if pair:
            add(pair[1], name)
            add(pair[2], name)
    return tuple(sorted(descriptors))


class Commands:
    """Explicit subprocess lanes, with interrupted children stopped before rollback."""

    def __init__(self, root: Path, targo: Path, source_caches: dict[str, Path] | None = None,
                 *, guard_admission: str = "native-worker"):
        self.root = root
        self.targo = targo
        self.source_caches = source_caches or {}
        require(guard_admission in {"ordinary", "native-worker", "original-fixed-v1"},
                "unknown guard admission interface")
        self.guard_admission = guard_admission
        self.git = shutil.which("git")
        self.agh = shutil.which("agh")
        require(self.git is not None, "Git is required; no authority was changed")

    def run(self, argv: list[str], *, cwd: Path, capture: bool = False,
            git: bool = False, allowed: tuple[int, ...] = (0,),
            discard_stdout: bool = False, binary: bool = False, raw: bool = False,
            capture_status: bool = False,
            env: dict[str, str] | None = None) -> str | bytes | tuple[int, str | bytes, str | bytes]:
        binary = binary or raw
        environment = dict(os.environ)
        if env is not None:
            environment.update(env)
        if git:
            # Ambient Git routing must not substitute a sibling object database,
            # index, replacement object or injected configuration for the target.
            for key in list(environment):
                if key.startswith("GIT_CONFIG") or key in {
                    "GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE", "GIT_COMMON_DIR",
                    "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES",
                    "GIT_NAMESPACE", "GIT_REPLACE_REF_BASE", "GIT_GRAFT_FILE",
                    "GIT_SHALLOW_FILE", "GIT_TEMPLATE_DIR", "GIT_DEFAULT_HASH",
                    "GIT_DEFAULT_REF_FORMAT",
                }:
                    del environment[key]
            # Clearing an override restores the default user config. Disable
            # that too; NO_REPLACE alone does not disable legacy graft files.
            environment["GIT_CONFIG_GLOBAL"] = os.devnull
            environment["GIT_CONFIG_NOSYSTEM"] = "1"
            environment["GIT_NO_REPLACE_OBJECTS"] = "1"
            environment["GIT_TERMINAL_PROMPT"] = "0"
            environment["GIT_NO_LAZY_FETCH"] = "1"
            environment["GIT_OPTIONAL_LOCKS"] = "0"
        stderr = {"stderr": subprocess.PIPE} if capture_status else {}
        child = subprocess.Popen(
            argv, cwd=cwd, env=environment, text=not binary,
            stdout=subprocess.PIPE if capture else subprocess.DEVNULL if discard_stdout else None,
            start_new_session=True,
            pass_fds=resource_fds(environment), **stderr,
        )
        try:
            output, diagnostics = child.communicate()
        except BaseException:
            # SIGINT/SIGTERM must not leave a resolver rewriting a lock after
            # the parent restored it. SIGKILL/power loss cannot be transactional.
            try:
                os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait(timeout=5)
            raise
        if capture_status and diagnostics:
            if isinstance(diagnostics, bytes):
                sys.stderr.buffer.write(diagnostics)
            else:
                sys.stderr.write(diagnostics)
        if capture and not git and not binary and child.returncode not in allowed and output:
            print(output, end="" if output.endswith("\n") else "\n", flush=True)
        require(child.returncode in allowed,
                f"command failed ({child.returncode}): {' '.join(argv)}")
        output = output or (b"" if binary else "")
        if capture_status:
            return child.returncode, output, diagnostics or (b"" if binary else "")
        return output

    def git_bytes(self, args: list[str], *, cwd: Path) -> bytes:
        output = self.run([self.git, *args], cwd=cwd, capture=True, git=True, binary=True)
        require(isinstance(output, bytes), "Git did not return raw immutable object bytes")
        return output

    def git_run(self, args: list[str], *, cwd: Path | None = None,
                allowed: tuple[int, ...] = (0,)) -> str:
        return self.run([self.git, *args], cwd=cwd or self.root,
                        capture=True, git=True, allowed=allowed)

    def fetch_github(self, directory: Path, url: str, revision: str) -> None:
        repository = re.fullmatch(
            r"https://github\.com/([A-Za-z0-9_.-]+)/([A-Za-z0-9_.-]+)\.git", url)
        require(repository is not None
                and all(part not in {".", ".."} for part in repository.groups()),
                "immutable authority must name a canonical GitHub repository")
        require(self.agh is not None, "Agh is required for owner-routed GitHub reads; no direct Git fallback")
        exact_sha(revision)
        self.run([self.agh, "repo", "fetch-main", "/".join(repository.groups()), str(directory),
                  "--blobless"],
                 cwd=directory, capture=True, git=True)

    def frontend(self, args: list[str]) -> None:
        # Metadata's potentially large JSON is not an authority receipt. Keep
        # update diagnostics and every named Rust test/result in the caller's
        # retained stdout/stderr; never replace the guard transcript with a tail.
        self.run([str(self.targo), *args], cwd=self.root,
                 discard_stdout=args[0] == "metadata")

    def _test_guard_transport(self, args: list[str]) -> str:
        """Select a serial interface, never reinterpret a modern admission refusal."""
        if self.guard_admission == "ordinary":
            # Deliberately selected before discovery, never after a native
            # refusal. Normal Targo execution retains its own admission.
            return "ordinary"
        configured = [*args[:2], "--config", "build.test-jobs=1", *args[2:]]
        fixed = self.guard_admission == "original-fixed-v1"
        probe = ([str(self.targo), "--resource-capabilities", "--fixed-admission-v1"]
                 if fixed else [str(self.targo), "--resource-capabilities", "--", *configured])
        response = self.run(
            probe,
            cwd=self.root, capture=True, allowed=(0, 1, 2),
            capture_status=True,
        )
        require(isinstance(response, tuple) and len(response) == 3,
                "Targo capability response has no exit status")
        code, text, diagnostics = response
        require(type(code) is int and isinstance(text, str) and isinstance(diagnostics, str)
                and len(text) + len(diagnostics) <= 65536,
                "Targo capability response is malformed")
        if fixed:
            require(code == 0, "original fixed discovery refused; no other interface retry")
        if code != 0:
            # The held older Trust frontend has no native test-graph protocol.
            # Only its exact unknown-option response selects the legacy interface;
            # every recognized native refusal remains a refusal, never a fallback.
            error_text = text + "\n" + diagnostics
            require("error: unexpected argument '--resource-capabilities' found" in error_text
                    and "Usage: targo" in error_text,
                    "Targo capability probe refused; no legacy fallback")
            version = self.run([str(self.targo), "--unverified", "--version"],
                               cwd=self.root, capture=True)
            require(isinstance(version, str) and version.startswith("targo "),
                    "legacy test interface requires the branded Trust frontend")
            return "legacy"
        try:
            # Stdout is the machine protocol. Keep lane warnings on stderr
            # visible without interpreting them as capability data.
            capability = json.loads(text)
        except (ValueError, TypeError) as error:
            raise Refusal(f"Targo capability JSON refused: {error}") from error
        if fixed:
            require(isinstance(capability, dict)
                    and type(capability.get("version")) is int
                    and capability == {"version": 1, "fixed_admission": "original-fixed-v1"},
                    "Targo does not advertise the selected original fixed interface")
            # Discovery is not admission or SDK readiness. Actual execution
            # retains/authenticates the original fixed owner and its GNU bridge.
            return "original-fixed"
        # Invocation-discovery v2 and configured-cohort v3 both advertise
        # Targo-owned test budgets. Select that CLI; actual execution still
        # authenticates CPU/fd/cohort custody and may refuse. A v2 reply is
        # not evidence of a v3 paired-compiler/cohort check.
        require(isinstance(capability, dict) and type(capability.get("version")) is int
                and capability["version"] in {2, 3}
                and capability.get("cpu_workers") is True
                and capability.get("supports_invocation") is True,
                "Targo does not admit this native test invocation; no legacy fallback")
        return "native"

    def rust_guard(self, args: list[str], expected: tuple[str, ...]) -> None:
        require(args[:2] == ["--unverified", "test"] and "--" not in args,
                "Rust guards require the unverified test lane without manual libtest arguments")
        try:
            transport = self._test_guard_transport(args)
            require(transport in {"ordinary", "native", "legacy", "original-fixed"}, "unknown Targo test transport")
            configured = ([*args[:2], "--config", "build.test-jobs=1", *args[2:]]
                          if transport in {"ordinary", "native", "original-fixed"}
                          else [*args, "--", "--test-threads=1"])
            # Match TY's explicit ordinary contract: the same configured
            # command, with libtest bounded directly and parent CPU/fd policy
            # inherited unchanged. This grants no worker or SDK readiness.
            execution = {"env": {"RUST_TEST_THREADS": "1"}} if transport == "ordinary" else {}
            output = self.run([str(self.targo), *configured], cwd=self.root, capture=True, **execution)
        except UnicodeError as error:
            raise Refusal(f"Rust guard transcript could not be decoded: {error}") from error
        try:
            if isinstance(output, str):
                print(output, end="" if output.endswith("\n") else "\n", flush=True)
            validate_rust_test_transcript(output, expected)
        except UnicodeError as error:
            raise Refusal(f"Rust guard transcript could not be decoded: {error}") from error
        except ValueError as error:
            raise Refusal(f"Rust guard transcript refused: {error}") from error


def clean_owned(commands: Commands) -> None:
    commands.git_run(["ls-files", "--error-unmatch", "--", *OWNED])
    status = commands.git_run(
        ["status", "--porcelain=v1", "--untracked-files=all", "--", *OWNED])
    require(not status, "owned pin files are dirty; commit or resolve them before retrying")


@contextmanager
def exclusive(commands: Commands) -> Iterator[None]:
    raw = commands.git_run(["rev-parse", "--git-path", "compiler-pin-transaction.lock"]).strip()
    require(bool(raw), "Git did not resolve the transaction lock path")
    path = Path(raw)
    if not path.is_absolute():
        path = commands.root / path
    require(all(not parent.is_symlink() for parent in path.parents),
            "symlink in transaction lock parent path")
    descriptor = os.open(path, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
    try:
        lock_info = os.fstat(descriptor)
        require(stat.S_ISREG(lock_info.st_mode) and lock_info.st_nlink == 1,
                "transaction lock is not a singly linked regular file")
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise Refusal("another compiler-pin transaction owns this checkout") from error
        yield
    finally:
        os.close(descriptor)


class Authority:
    """A private authenticated object view; never an ambient worktree/index."""

    def __init__(self, commands: Commands, directory: Path, url: str, revision: str):
        self.commands = commands
        self.directory = directory
        self.revision = exact_sha(revision)
        self.repository = url.removeprefix("https://github.com/").removesuffix(".git")
        require(url in {IR_URL, CLEAN_URL, AY_URL},
                "no routed authority repository for immutable source URL")
        directory.mkdir()
        commands.git_run(["init", "--bare", "--quiet", "--template=", "--object-format=sha1"], cwd=directory)
        rewrites = commands.git_run(
            ["config", "--get-regexp", r"^url\..*\.insteadof$"],
            cwd=directory, allowed=(0, 1))
        for line in rewrites.splitlines():
            fields = line.split(None, 1)
            require(len(fields) == 2 and not url.startswith(fields[1]),
                    f"Git URL rewrite would replace immutable remote {url}")
        require(url in (IR_URL, CLEAN_URL, AY_URL),
                "no routed authority repository for immutable source URL")
        self.cached_tree = None
        cache = getattr(commands, "source_caches", {}).get(url)
        if cache is not None:
            # A cache is not authority: authenticate the exact commit through
            # Agh now, then hash-check every commit/tree/blob used below.
            require(commands.agh is not None, "Agh is required for source-cache authentication")
            slug = url.removeprefix("https://github.com/").removesuffix(".git")
            commands.run([commands.agh, "repo", "check-local", slug, str(cache)],
                         cwd=directory, capture=True, git=True)
            remote = commands.run([commands.agh, "rev", slug + "@" + revision,
                                   "--jq", ".sha"], cwd=directory, capture=True, git=True)
            require(remote.strip() == revision, "Agh resolved a different source-cache commit")
            objects = commands.git_run(["-C", str(cache), "rev-parse", "--path-format=absolute",
                                        "--git-path", "objects"], cwd=directory).strip()
            require(Path(objects).is_absolute() and Path(objects).is_dir()
                    and not any(c in objects for c in "\r\n\0"), "invalid source object directory")
            (directory / "objects/info/alternates").write_text(objects + "\n")
            commit = self.verified_object("commit", revision)
            tree = re.match(rb"tree ([0-9a-f]{40})\n", commit)
            require(tree is not None, "cached commit has no canonical root tree")
            self.cached_tree = tree[1].decode("ascii")
            commands.git_run(["update-ref", AUTHORITY_REF, revision], cwd=directory)
        else:
            commands.fetch_github(directory, url, self.revision)
        actual = commands.git_run(["rev-parse", "--verify", self.revision + "^{commit}"],
                                  cwd=directory).strip()
        require(actual == revision, f"remote resolved a different commit for {url}")
        if cache is None:
            commands.git_run(["merge-base", "--is-ancestor", self.revision,
                              "refs/agh/fetched-main"], cwd=directory)

    def verified_object(self, kind: str, oid: str) -> bytes:
        raw = self.commands.git_bytes(["cat-file", kind, oid], cwd=self.directory)
        header = f"{kind} {len(raw)}\0".encode("ascii")
        require(hashlib.sha1(header + raw).hexdigest() == oid,
                f"source cache {kind} object does not match its immutable identity: {oid}")
        return raw

    def cached_blob(self, relative: str) -> bytes | None:
        tree = self.cached_tree
        parts = relative.encode("ascii").split(b"/")
        for index, part in enumerate(parts):
            raw = self.verified_object("tree", tree)
            entries, at = [], 0
            while at < len(raw):
                space, zero = raw.find(b" ", at), raw.find(b"\0", at)
                require(at < space < zero and zero + 21 <= len(raw), "malformed cached tree")
                mode, name = raw[at:space], raw[space + 1:zero]
                oid = raw[zero + 1:zero + 21].hex()
                if name == part:
                    entries.append((mode, oid))
                at = zero + 21
            if not entries:
                return None
            require(len(entries) == 1, f"ambiguous cached manifest path: {relative}")
            mode, oid = entries[0]
            if index + 1 == len(parts):
                require(mode in (b"100644", b"100755"),
                        f"immutable manifest is not a regular blob: {relative}")
                return self.verified_object("blob", oid)
            require(mode == b"40000", f"non-tree ancestor of immutable manifest: {relative}")
            tree = oid
        raise Refusal("empty immutable manifest path")

    def read_optional(self, relative: str) -> dict | None:
        require(isinstance(relative, str) and bool(relative)
                and re.fullmatch(r"[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)*", relative) is not None
                and not any(part in (".", "..") for part in relative.split("/")),
                "unsafe immutable object path")
        if PurePosixPath(relative).name == "Cargo.toml":
            alternate = str(PurePosixPath(relative).with_name("Targo.toml"))
            require(self.read_optional(alternate) is None,
                    f"unsupported immutable Targo manifest precedence: {alternate}")
        if self.cached_tree is not None:
            raw = self.cached_blob(relative)
            return None if raw is None else document(raw, f"{self.revision}:{relative}")
        tree = self.commands.git_run(["ls-tree", "-z", self.revision, "--", relative],
                                     cwd=self.directory)
        entries = [entry for entry in tree.split("\0") if entry]
        if not entries:
            return None
        require(len(entries) == 1, f"ambiguous immutable manifest: {relative}")
        header, separator, path = entries[0].partition("\t")
        fields = header.split()
        require(separator and path == relative and len(fields) == 3
                and fields[0] in ("100644", "100755") and fields[1] == "blob"
                and SHA.fullmatch(fields[2]) is not None,
                f"immutable manifest is not a regular blob: {relative}")
        data = self.commands.run(
            [self.commands.agh, "cat", f"{self.repository}@{self.revision}:{relative}"],
            cwd=self.directory, capture=True, git=True, raw=True)
        return document(checked_git_blob(data, fields[2]), f"{self.revision}:{relative}")

    def read(self, relative: str) -> dict:
        value = self.read_optional(relative)
        require(value is not None, f"missing immutable manifest: {relative}")
        return value


class QualificationIrSource(Authority):
    """Immutable local IR DATA only; deliberately no remote-authority operation."""

    def __init__(self, commands: Commands, directory: Path, source_repo: Path, revision: str):
        require(source_repo.is_absolute() and source_repo.is_dir(),
                "qualification IR source needs an existing absolute repository")
        self.commands = commands
        self.directory = directory
        self.revision = exact_sha(revision)
        self.repository = IR_URL.removeprefix("https://github.com/").removesuffix(".git")
        directory.mkdir()
        commands.git_run(["init", "--bare", "--quiet", "--template=", "--object-format=sha1"],
                         cwd=directory)
        objects = commands.git_run(["-C", str(source_repo), "rev-parse", "--path-format=absolute",
                                    "--git-path", "objects"], cwd=directory).strip()
        require(Path(objects).is_absolute() and Path(objects).is_dir()
                and not any(c in objects for c in "\r\n\0"),
                "invalid qualification IR object directory")
        (directory / "objects/info/alternates").write_text(objects + "\n")
        commit = self.verified_object("commit", revision)
        tree = re.match(rb"tree ([0-9a-f]{40})\n", commit)
        require(tree is not None, "qualification IR commit has no canonical root tree")
        self.cached_tree = tree[1].decode("ascii")
        self.require_complete_source()

    def require_complete_source(self) -> None:
        # Selected source is required, not all unrelated historical blobs.
        # Traversing commits separately still refuses missing ancestry metadata.
        self.commands.git_run(["rev-list", "--count", self.revision], cwd=self.directory)
        objects = self.commands.git_run(
            ["rev-list", "--objects", "--no-object-names", "--missing=print", self.cached_tree],
            cwd=self.directory).splitlines()
        require(bool(objects) and all(SHA.fullmatch(oid) is not None for oid in objects),
                "qualification IR selected source closure is incomplete")
        self.verified_object("tree", self.cached_tree)


def packages(data: bytes, label: str) -> list[dict]:
    rows = document(data, label).get("package")
    require(isinstance(rows, list) and bool(rows) and all(isinstance(row, dict) for row in rows),
            f"{label}: missing package cohort")
    keys = [(row.get("name"), row.get("version"), row.get("source")) for row in rows]
    require(all(isinstance(name, str) and isinstance(version, str)
                and (identity is None or isinstance(identity, str)) for name, version, identity in keys),
            f"{label}: invalid package identity")
    require(len(set(keys)) == len(keys), f"{label}: duplicate package identity")
    return rows


def cohort(rows: list[dict], prefix: str, url: str, revision: str | None = None) -> dict[str, str]:
    vendor = None
    if prefix == "ay":
        owners = [row for row in rows if family(row.get("name", ""), "ay")]
        if owners:
            match = re.fullmatch(r"git\+" + re.escape(url) + r"\?rev=([0-9a-f]{40})#\1",
                                 owners[0].get("source", ""))
            if match is not None:
                try:
                    vendor = exec_policy.locked_identity(rows, match[1], owners[0].get("version"))
                except exec_policy.OwnerError as error:
                    raise Refusal(str(error)) from error
    for row in rows:
        identity = row.get("source", "")
        require(not (isinstance(identity, str) and identity.startswith(f"git+{url}"))
                or family(row.get("name", ""), prefix) or exec_policy.identity(row) == vendor,
                f"unexpected package name from {prefix} repository authority")
    selected = [row for row in rows if family(row.get("name", ""), prefix)]
    require(bool(selected), f"missing {prefix} package cohort")
    result = {}
    sources = set()
    for row in selected:
        name, version, identity = row["name"], row.get("version"), row.get("source", "")
        require(name not in result, f"split or duplicate {name} package")
        require(isinstance(version, str), f"{name}: missing version")
        match = re.fullmatch(r"git\+" + re.escape(url) + r"\?rev=([0-9a-f]{40})#\1", identity)
        require(match is not None, f"{name}: source is not an exact canonical Git identity")
        require(revision is None or match[1] == revision, f"{name}: wrong dependency revision")
        result[name] = version
        sources.add(identity)
    require(len(sources) == 1, f"split {prefix} source cohort")
    return result


@dataclass(frozen=True)
class Current:
    ir: str
    clean: str
    ay: str
    ay_version: str
    ir_packages: dict[str, str]
    clean_packages: dict[str, str]
    ay_packages: dict[str, str]


def current(root: Path, files: dict[str, Snapshot]) -> Current:
    manifest = document(files[MANIFESTS[0]].data, MANIFESTS[0])
    ir = pin(dependency(manifest, True, "trust-ir", MANIFESTS[0]), IR_URL, "trust-ir")
    require(pin(dependency(manifest, True, "trust-ir-build", MANIFESTS[0]), IR_URL,
                "trust-ir-build") == ir, "root TrustIR manifests disagree")
    # The must-refuse corpus runner: dev-only, same revision by construction.
    require(pin(dependency(manifest, True, "trust-ir-conformance", MANIFESTS[0]), IR_URL,
                "trust-ir-conformance") == ir, "root TrustIR manifests disagree")
    bridge = document(files[MANIFESTS[1]].data, MANIFESTS[1])
    require(pin(dependency(bridge, False, "trust-ir", MANIFESTS[1]), IR_URL,
                "bridge trust-ir") == ir, "bridge TrustIR manifest disagrees")
    # The bridge's test-only validator (WS7.3-pre, `tests/mir_lane_valid_trust_ir.rs`):
    # a dev-dependency, but its lock row resolves trust-ir, so a move that left it
    # behind would put two trust-ir graphs in the bridge lock.
    require(pin(bridge.get("dev-dependencies", {}).get("trust-ir-build"), IR_URL,
                "bridge trust-ir-build") == ir, "bridge TrustIR manifest disagrees")
    regalloc = document(files[REGALLOC].data, REGALLOC)
    ay_dep = dependency(regalloc, False, "ay-pb", REGALLOC)
    ay = pin(ay_dep, AY_URL, "ay-pb")
    ay_version = ay_dep.get("version")
    require(isinstance(ay_version, str), "AY version authority is missing")
    for name, features in (("ay-pb", []), ("ay-sat", ["raw-pointer-bcp"])):
        dep = dependency(regalloc, False, name, REGALLOC)
        require(pin(dep, AY_URL, name) == ay and dep.get("version") == ay_version,
                "AY manifest pins/versions disagree")
        require(dep.get("optional") is True and dep.get("default-features") is False
                and dep.get("features", []) == features,
                f"{name}: AY allocator optionality/features changed")
    require(regalloc.get("features", {}).get("default") == []
            and regalloc.get("features", {}).get("ay-regalloc") ==
            ["dep:ay-pb", "dep:ay-sat", "dep:trust-cg-process-env"],
            "AY allocator feature activation changed")
    all_ir, all_clean, all_ay = {}, {}, {}
    clean = None
    for lock in LOCKS:
        rows = packages(files[lock].data, lock)
        ir_rows = cohort(rows, "trust-ir", IR_URL, ir)
        clean_rows = cohort(rows, "clean", CLEAN_URL, clean)
        if clean is None:
            clean_row = next(row for row in rows if family(row["name"], "clean"))
            clean = clean_row["source"].split("#", 1)[1]
        require({"trust-ir", "trust-ir-build", "trust-ir-giveback"} <= ir_rows.keys(),
                f"{lock}: missing the supported TrustIR core/build/giveback cohort")
        for combined, incoming in [(all_ir, ir_rows), (all_clean, clean_rows)]:
            for name, version in incoming.items():
                require(name not in combined or combined[name] == version,
                        f"{name}: package versions differ across locks")
                combined[name] = version
        if lock != "fuzz/Cargo.lock" or any(family(row["name"], "ay")
                                            or row.get("source", "").startswith("git+" + AY_URL)
                                            for row in rows):
            ay_rows = cohort(rows, "ay", AY_URL, ay)
            for version in ay_rows.values():
                require(version == ay_version, f"{lock}: AY version drift")
            all_ay.update(ay_rows)
    verify = document(files[VERIFY].data, VERIFY)
    for name in ("clean-kernel", "clean-olean", "clean-verify"):
        dep = dependency(verify, False, name, VERIFY)
        require(pin(dep, CLEAN_URL, f"{VERIFY}: {name}") == clean,
                f"{VERIFY}: {name} disagrees with the locked Clean authority")
        require("version" not in dep or dep["version"] in set(all_clean.values()),
                f"{VERIFY}: {name} version disagrees with the locked Clean authority")
        require(dep.get("optional") is True,
                f"{VERIFY}: {name} must remain optional")
    require(dependency(verify, False, "clean-olean", VERIFY).get("default-features") is False,
            "original CIC replay must keep Clean olean default features disabled")
    require(verify.get("features", {}).get("original-i128-cic") ==
            ["dep:clean-kernel", "dep:clean-olean"],
            "original CIC replay feature activation changed")
    require(verify.get("features", {}).get("core-byte-replay") ==
            ["dep:clean-kernel", "dep:clean-verify", "dep:trust-ir-build"],
            "canonical byte replay feature activation changed")
    cache = files[CACHE].data.decode()
    require(cache.count(f"pub const {CACHE_NAME}") == 1, "compile cache authority is ambiguous")
    pattern = rf'pub const {CACHE_NAME}: &str =\s*"trust_ir:{ir}";'
    require(len(re.findall(pattern, cache)) == 1, "compile cache identity disagrees with TrustIR")
    require(cache.count(f"pub const {AY_CACHE_NAME}") == 1
            and len(re.findall(rf'pub const {AY_CACHE_NAME}: &str =\s*"ay:{ay}";', cache)) == 1,
            "compile cache identity disagrees with AY")
    return Current(ir, clean, ay, ay_version, all_ir, all_clean, all_ay)


@dataclass(frozen=True)
class AyTarget:
    revision: str
    version: str
    declarations: dict[str, dict[str, list[dict]]]
    required: dict[str, set[str]]
    exec_policy: bool = False
    registry_owners: dict[tuple[str, str], registry_owner.Owner] | None = None


@dataclass(frozen=True)
class Target:
    clean: str
    ay: AyTarget | None
    # Newly admitted TrustIR package -> the existing cohort packages whose
    # immutable target manifests require it (see admit_ir_packages).
    admitted: dict[str, frozenset[str]]
    # Newly admitted AY package -> the existing AY cohort packages whose
    # immutable target manifests require it (see admit_ay_packages).
    admitted_ay: dict[str, frozenset[str]] = field(default_factory=dict)
    qualification_ir_tree: str | None = None
    clean_version: str | None = None


def selected_clean_version(state: Current, requested: str | None) -> str:
    versions = set(state.clean_packages.values())
    require(len(versions) == 1, "current Clean package versions disagree")
    current_version = next(iter(versions))
    if requested is None:
        return current_version
    require(requested == current_version or
            (current_version, requested) == CLEAN_VERSION_MIGRATION,
            "unsupported Clean package-version migration")
    return requested


def selected_ir_version(state: Current, requested: str | None) -> str:
    versions = set(state.ir_packages.values())
    require(len(versions) == 1, "current TrustIR package versions disagree")
    current_version = next(iter(versions))
    if requested is None:
        return current_version
    require(requested == current_version or
            (current_version, requested) == IR_VERSION_MIGRATION,
            "unsupported TrustIR package-version migration")
    return requested


def mentions_ay(alias: str, dep) -> bool:
    return family(alias, "ay") or (isinstance(dep, dict) and (
        family(str(dep.get("package", "")), "ay")
        or AY_URL.removesuffix(".git") in str(dep.get("git", ""))))


def ay_dependencies(table: dict, expected: set[str], revision: str, version: str, label: str) -> None:
    require(isinstance(table, dict), f"{label}: malformed AY dependency table")
    selected = {alias: dep for alias, dep in table.items() if mentions_ay(alias, dep)}
    require(selected.keys() == expected, f"{label}: unsupported target AY cohort")
    for alias, dep in selected.items():
        require(isinstance(dep, dict) and dep.get("package", alias) == alias,
                f"{label}: renamed AY package authority")
        require(pin(dep, AY_URL, alias) == revision and dep.get("version") == version,
                f"{label}: changes requested AY authority/version; select a coherent --ay-revision")


def dependency_tables(doc: dict):
    targets = doc.get("target", {})
    require(isinstance(targets, dict) and all(isinstance(value, dict) for value in targets.values()),
            "malformed target dependency tables")
    for container in [doc, *targets.values()]:
        for section in ("dependencies", "build-dependencies", "dev-dependencies"):
            table = container.get(section, {})
            require(isinstance(table, dict), "malformed dependency table")
            yield container is doc, section, table


def admit_ir_packages(ir: Authority, state: Current, names: tuple[str, ...], *,
                      ir_version: str | None = None) -> dict[str, frozenset[str]]:
    """Admit explicitly NAMED new TrustIR workspace crates, bound to the fetched target.

    A name joins the cohort only when the immutable target (1) lists
    `crates/NAME` as a workspace member whose manifest defines NAME at the
    cohort version, (2) declares it as a non-dev dependency of a package the
    cohort already admits, and (3) gives it no non-dev dependency other than a
    TrustIR workspace path inside the widened cohort. Anything else refuses.
    """
    require(len(set(names)) == len(names), "duplicate --admit-ir-package name")
    if not names:
        return {}
    version = selected_ir_version(state, ir_version)
    workspace = ir.read("Cargo.toml").get("workspace", {})
    require(isinstance(workspace, dict), "malformed target TrustIR workspace")
    members = workspace.get("members", [])
    workspace_deps = workspace.get("dependencies", {})
    require(isinstance(members, list) and isinstance(workspace_deps, dict),
            "malformed target TrustIR workspace members/dependencies")
    widened = set(state.ir_packages) | set(names)

    def workspace_path(alias: str, raw, label: str) -> str:
        """The TrustIR package a non-dev edge names; only an in-workspace path is admitted."""
        require(isinstance(raw, dict), f"{label}: {alias} must be a TrustIR workspace path")
        if raw.get("workspace") is True:
            require(set(raw) <= {"workspace", "optional", "features", "default-features"},
                    f"{label}: mixed workspace dependency selectors for {alias}")
            raw = workspace_deps.get(alias)
            require(isinstance(raw, dict) and raw.get("path") == f"crates/{alias}",
                    f"{label}: {alias} is not a TrustIR workspace path")
        else:
            require(raw.get("path") == f"../{alias}",
                    f"{label}: {alias} is not a TrustIR workspace path")
        require(set(raw) <= {"path", "version", "optional", "features", "default-features"}
                and "package" not in raw,
                f"{label}: unsupported selector on TrustIR path dependency {alias}")
        return alias

    def requires(doc: dict, name: str) -> bool:
        return any(section != "dev-dependencies" and name in table
                   for _, section, table in dependency_tables(doc))

    admitted = {}
    for name in names:
        require(isinstance(name, str) and family(name, "trust-ir") and name != "trust-ir",
                f"{name}: only a named trust-ir-* package can be admitted")
        require(name not in state.ir_packages, f"{name}: already in the TrustIR cohort")
        require(f"crates/{name}" in members, f"{name}: not a member of the target TrustIR workspace")
        label = f"{ir.revision}:crates/{name}/Cargo.toml"
        doc = ir.read(f"crates/{name}/Cargo.toml")
        package = doc.get("package", {})
        require(isinstance(package, dict) and package.get("name") == name
                and package.get("version") in (version, {"workspace": True}),
                f"{name}: target does not define it at the cohort version")
        for _, section, table in dependency_tables(doc):
            if section == "dev-dependencies":
                continue
            for alias, raw in table.items():
                require(workspace_path(alias, raw, label) in widened,
                        f"{label}: {alias} is outside the admitted TrustIR cohort")
        required_by = frozenset(member for member in state.ir_packages
                                if requires(ir.read(f"crates/{member}/Cargo.toml"), name))
        require(bool(required_by), f"{name}: no admitted TrustIR package requires it")
        admitted[name] = required_by
    return admitted


def admit_ay_packages(authority: AyTarget | None, state: Current,
                      names: tuple[str, ...]) -> dict[str, frozenset[str]]:
    """Admit explicitly NAMED new AY workspace packages, bound to the fetched AY target.

    Only with an AY move. A name joins the AY cohort only when the immutable
    AY target (1) defines it as a workspace member (validate_ay_target read
    every member's manifest at the cohort version) and (2) declares it as a
    non-dev dependency of a package already in the AY cohort. Its own edges
    are held to that manifest per lock by validate_graph.
    """
    require(len(set(names)) == len(names), "duplicate --admit-ay-package name")
    if not names:
        return {}
    require(authority is not None, "--admit-ay-package needs an AY move (--ay-revision)")
    admitted = {}
    for name in names:
        require(isinstance(name, str) and family(name, "ay") and name != "ay",
                f"{name}: only a named ay-* package can be admitted")
        require(name not in state.ay_packages, f"{name}: already in the AY cohort")
        require(name in authority.declarations,
                f"{name}: not a member of the target AY workspace")
        required_by = frozenset(member for member in state.ay_packages
                                if name in authority.declarations.get(member, {}))
        require(bool(required_by), f"{name}: no AY cohort package requires it")
        admitted[name] = required_by
    return admitted


def selected_ay_version(state: Current, requested: str | None) -> str:
    if requested is None:
        return state.ay_version
    require(requested == state.ay_version
            or (state.ay_version, requested) == AY_VERSION_MIGRATION,
            "unsupported AY package-version migration")
    require(requested == AY_VERSION_MIGRATION[1], "unsupported explicit AY target version")
    return requested


def target_cohort(commands: Commands, directory: Path, state: Current, revision: str,
                  ay_revision: str | None = None, admit: tuple[str, ...] = (),
                  admit_ay: tuple[str, ...] = (), ay_version: str | None = None,
                  admit_registry: tuple[str, ...] = (),
                  qualification_ir_source: Path | None = None,
                  clean_version: str | None = None, *,
                  ir_version: str | None = None) -> Target:
    require(ay_version is None or ay_revision is not None,
            "--ay-version requires an explicit --ay-revision")
    ay_version = selected_ay_version(state, ay_version)
    clean_version = selected_clean_version(state, clean_version)
    selected_ir = selected_ir_version(state, ir_version)
    ay_revision = state.ay if ay_revision is None else exact_sha(ay_revision)
    require(not admit_registry or ay_revision != state.ay,
            "named registry source admission requires an explicit AY move")
    ir = (Authority(commands, directory / "trust-ir", IR_URL, revision)
          if qualification_ir_source is None else
          QualificationIrSource(commands, directory / "trust-ir", qualification_ir_source, revision))
    ir_workspace = ir.read("Cargo.toml").get("workspace", {}).get("package", {})
    require(selected_ir == ir_workspace.get("version"),
            "TrustIR package version move is unsupported without matching explicit selection")
    admitted = admit_ir_packages(ir, state, tuple(admit), ir_version=ir_version)
    clean_revisions = set()
    for relative in ["crates/trust-ir/Cargo.toml", "crates/trust-ir-build/Cargo.toml"]:
        manifest = ir.read(relative)
        for section in ["dependencies", "dev-dependencies"]:
            for name, dep in manifest.get(section, {}).items():
                if family(name, "clean"):
                    require(name in {"clean-kernel", "clean-mathverse", "clean-olean", "clean-verify"},
                            f"unsupported TrustIR-owned Clean dependency: {name}")
                    clean_revisions.add(pin(dep, CLEAN_URL, f"{relative}: {name}"))
                    require(dep.get("version") == clean_version,
                            f"{relative}: Clean version differs from explicit selection")
    require(len(clean_revisions) == 1, "target TrustIR must own exactly one Clean revision")
    clean_revision = next(iter(clean_revisions))
    clean = Authority(commands, directory / "clean", CLEAN_URL, clean_revision)
    clean_root = clean.read("Cargo.toml").get("workspace", {})
    require(clean_root.get("package", {}).get("version") == clean_version,
            "Clean package version move is unsupported without matching explicit selection")
    ay_dependencies(clean_root.get("dependencies", {}),
                    {"ay", "ay-core", "ay-dpll", "ay-proof", "ay-frontend", "ay-translate", "ay-lean-bridge"},
                    ay_revision, ay_version, "target Clean")
    ay_target = None
    if ay_revision != state.ay:
        adapter = ir.read("crates/trust-ir-ay/Cargo.toml")
        ay_dependencies(adapter.get("dependencies", {}), {"ay", "ay-proof"},
                        ay_revision, ay_version, "target TrustIR AY adapter")
        for primary, section, table in dependency_tables(adapter):
            if not primary or section != "dependencies":
                require(not any(mentions_ay(alias, dep) for alias, dep in table.items()),
                        "unsupported target TrustIR adapter AY declaration")
        ay_target = validate_ay_target(Authority(commands, directory / "ay", AY_URL, ay_revision),
                                       state, ay_version, admit_registry,
                                       frozenset(state.ay_packages) | frozenset(admit_ay),
                                       clean_authority=clean, clean_revision=clean_revision)
    # Every admitted package is checked against a manifest in the fetched object,
    # not inferred from a same-named sibling or from package-version coincidence.
    for authority, expected in [(ir, dict.fromkeys(state.ir_packages, selected_ir)),
                                (clean, dict.fromkeys(state.clean_packages, clean_version))]:
        for name, version in expected.items():
            package = authority.read(f"crates/{name}/Cargo.toml").get("package", {})
            require(package.get("name") == name, f"target does not define admitted package {name}")
            require(package.get("version") in (version, {"workspace": True}),
                    f"{name}: target package version is unsupported")
    if isinstance(ir, QualificationIrSource):
        ir.require_complete_source()
    return Target(clean_revision, ay_target, admitted,
                  admit_ay_packages(ay_target, state, tuple(admit_ay)),
                  ir.cached_tree if qualification_ir_source is not None else None,
                  clean_version)


def unused_vendor_declaration(authority: Authority, excludes: list[str], package: str,
                              resolved: str, optional: bool, *, unselected: bool = False) -> str:
    """Check an excluded optional declaration, never admit its selected graph.

    AY's CLI-only vendor can be declared by an unselected workspace member or
    with its CLI feature off. Discovery requires its explicit separate owner;
    it does not activate or admit that owner into the selected lock graph.
    """
    require((optional or unselected) and not family(package, "ay"),
            f"unreviewed required vendor dependency: {package}")
    require(resolved in excludes and resolved.startswith("vendor/")
            and all(part not in ("", ".", "..") for part in resolved.split("/")),
            f"vendor dependency is not an explicit excluded root: {package}")
    # Authority.read also checks exact regular Git mode and Targo precedence.
    doc = authority.read(resolved + "/Cargo.toml")
    owner = doc.get("package")
    require(isinstance(owner, dict) and owner.get("name") == package
            and "workspace" not in owner and isinstance(doc.get("workspace"), dict),
            f"vendor package has no matching explicit workspace owner: {package}")
    version = owner.get("version")
    require(isinstance(version, str)
            and re.fullmatch(r"(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*)", version) is not None,
            f"vendor package needs an explicit stable version: {package}")
    return version


def validate_ay_target(authority: Authority, state: Current,
                       version: str | None = None,
                       admit_registry: tuple[str, ...] = (),
                       selected_packages: frozenset[str] | None = None, *,
                       clean_authority: Authority | None = None,
                       clean_revision: str | None = None) -> AyTarget:
    """Admit only existing AY packages actually defined by the fetched workspace.

    AY's theory crates do not follow crates/<package-name>; inspect its literal
    member paths, never a mutable sibling or guessed same-name path.
    """
    version = state.ay_version if version is None else version
    selected_packages = (frozenset(state.ay_packages) if selected_packages is None
                         else selected_packages)
    root = authority.read("Cargo.toml")
    workspace = root.get("workspace", {})
    require(not {"package", "project"}.intersection(root) and isinstance(workspace, dict),
            "unsupported AY root package ownership")
    workspace_package = workspace.get("package", {})
    require(isinstance(workspace_package, dict), "malformed AY workspace package")
    require(workspace_package.get("version") == version,
            "AY package version move is unsupported")
    members = workspace.get("members")
    literal = lambda path: isinstance(path, str) and re.fullmatch(r"[A-Za-z0-9_-]+(?:/[A-Za-z0-9_-]+)*", path)
    require(isinstance(members, list) and bool(members)
            and all(literal(path) for path in members) and len(set(members)) == len(members),
            "AY workspace requires unique literal member paths")
    excludes = workspace.get("exclude", [])
    require(isinstance(excludes, list) and all(literal(path) for path in excludes)
            and len(set(excludes)) == len(excludes),
            "unsupported AY workspace exclusions")
    defaults = workspace.get("default-members", members)
    require(isinstance(defaults, list) and all(literal(path) for path in defaults)
            and len(set(defaults)) == len(defaults) and set(defaults) <= set(members),
            "unsupported AY workspace default members")
    found = {}
    ancestors = {}
    for member in members:
        require(not any(member == path or member.startswith(path + "/") for path in excludes),
                "AY member is excluded from the immutable workspace")
        doc = authority.read(member + "/Cargo.toml")
        package = doc.get("package", {})
        require(isinstance(package, dict) and "project" not in doc, "malformed/legacy AY member package")
        name = package.get("name")
        require(isinstance(name, str) and bool(name) and name not in found and "workspace" not in doc
                and "workspace" not in package, "ambiguous AY workspace package ownership")
        for parent in PurePosixPath(member).parents:
            if str(parent) == ".":
                continue
            relative = str(parent) + "/Cargo.toml"
            if relative not in ancestors:
                ancestors[relative] = authority.read_optional(relative)
            ancestor = ancestors[relative]
            if ancestor is not None:
                owners = [ancestor[key] for key in ("package", "project") if key in ancestor]
                require(len(owners) <= 1 and all(isinstance(owner, dict) for owner in owners),
                        "malformed/ambiguous AY ancestor package")
                require("workspace" not in ancestor and all("workspace" not in owner for owner in owners),
                        "AY member crosses nested/redirected workspace ownership")
        found[name] = (member, doc)
    for name in state.ay_packages:
        require(name in found and found[name][1]["package"].get("version") in (version, {"workspace": True}),
                f"{name}: target AY package missing or version changed")

    workspace_deps = workspace.get("dependencies", {})
    require(isinstance(workspace_deps, dict), "malformed AY workspace dependencies")
    has_exec_policy = False
    selected_members = {member for name, (member, _) in found.items()
                        if name in selected_packages}

    def declaration(alias, raw, member, primary=False, section=None, macos=False):
        nonlocal has_exec_policy
        raw = {"version": raw} if isinstance(raw, str) else raw
        require(isinstance(raw, dict), f"{member}: malformed dependency {alias}")
        inherited = raw.get("workspace") is True
        require("workspace" not in raw or (inherited and member is not None
                and set(raw) <= {"workspace", "optional", "features", "default-features"}),
                f"{member}: mixed workspace dependency selectors")
        dep = workspace_deps.get(alias) if inherited else raw
        dep = {"version": dep} if isinstance(dep, str) else dep
        require(isinstance(dep, dict), f"{member}: unresolved workspace dependency {alias}")
        optional = raw.get("optional", False)
        require(isinstance(optional, bool), f"{member}: malformed optional dependency")
        package = dep.get("package", alias)
        require(isinstance(package, str) and bool(package), "malformed dependency package name")
        if "path" in dep:
            path = dep["path"]
            require(isinstance(path, str) and bool(path) and not PurePosixPath(path).is_absolute()
                    and "\\" not in path and not {"git", "rev", "branch", "tag", "registry", "registry-index"}.intersection(dep),
                    f"{member}: mixed/invalid dependency path")
            components = path.split("/")
            ascent = 0
            while ascent < len(components) and components[ascent] == "..":
                ascent += 1
            base = [] if inherited or member is None else member.split("/")
            require(ascent <= len(base) and bool(components[ascent:])
                    and all(literal(part) and "/" not in part for part in components[ascent:]),
                    f"{member}: unsupported noncanonical dependency path")
            # Do not normalize away symlink/nonexistent path components such as
            # redirect/../sat. Only bounded leading ascent plus literals is used.
            resolved = "/".join(base[:len(base) - ascent] + components[ascent:])
            if package not in found and not family(package, "ay"):
                # Workspace templates and unselected members participate in
                # ownership discovery without selecting their dependency graph.
                # Transitive dependency test suites are not selected by this
                # consumer either. A required non-dev use from any selected
                # (including newly admitted) member still refuses; all foreign
                # locked rows still fail cohort(), even if discovered here.
                if package == exec_policy.NAME:
                    require(member == "crates/ay-sys" and alias == exec_policy.NAME
                            and not primary and macos and section == "dependencies",
                            "exec-policy needs the actual ay-sys macOS dependency")
                    try:
                        vendor_version = exec_policy.immutable_version(
                            authority, excludes, package, resolved, optional)
                    except exec_policy.OwnerError as error:
                        raise Refusal(str(error)) from error
                    has_exec_policy = True
                else:
                    vendor_version = unused_vendor_declaration(
                        authority, excludes, package, resolved, optional,
                        unselected=member is None or member not in selected_members
                                   or section == "dev-dependencies")
                if "version" in dep:
                    require(matches_version(dep["version"], vendor_version),
                            f"{package}: vendor path/version disagree")
                return package, {"git": AY_URL, "rev": authority.revision,
                                 "version": "=" + vendor_version}, optional
            require(package in found and resolved == found[package][0],
                    f"{member}: path dependency is not the declared AY member {package}")
            require(family(package, "ay"), "foreign package under AY path authority")
            package_version = found[package][1]["package"].get("version")
            package_version = version if package_version == {"workspace": True} else package_version
            require(isinstance(package_version, str), f"{package}: missing member version")
            if "version" in dep:
                require(matches_version(dep["version"], package_version), f"{package}: member path/version disagree")
            dep = {"git": AY_URL, "rev": authority.revision, "version": "=" + package_version}
        elif mentions_ay(alias, dep):
            raise Refusal(f"{member}: AY dependency is not an owning-workspace path")
        elif "git" in dep:
            require(isinstance(dep["git"], str) and not {"branch", "tag", "registry", "registry-index"}.intersection(dep),
                    f"{member}: unsupported Git dependency source")
            exact_sha(dep.get("rev", ""))
        else:
            require(not {"rev", "branch", "tag", "registry", "registry-index"}.intersection(dep)
                    and isinstance(dep.get("version"), str), f"{member}: unsupported registry authority")
        return package, dep, optional

    # All declarations participate in workspace discovery, even dev/optional
    # edges and packages not selected in these three locks. A hidden implicit
    # path member is unsupported, not silently granted root inheritance.
    for alias, raw in workspace_deps.items():
        declaration(alias, raw, None)
    declarations, required = {}, {}
    for name, (member, doc) in found.items():
        declarations[name], required[name] = {}, set()
        for primary, section, table in dependency_tables(doc):
            for alias, raw in table.items():
                macos = table is doc.get("target", {}).get('cfg(target_os = "macos")', {}).get("dependencies")
                package, dep, optional = declaration(alias, raw, member, primary, section, macos)
                if section != "dev-dependencies":
                    declarations[name].setdefault(package, []).append(dep)
                    if primary and not optional:
                        required[name].add(package)
    require(not has_exec_policy or version == "0.28.0",
            "independent exec-policy source owner requires the reviewed AY 0.28.0 cohort")
    if has_exec_policy:
        required["ay-sys"].add(exec_policy.NAME)
    registry_owners = None
    if admit_registry:
        try:
            registry_owners = registry_owner.from_ay(authority, admit_registry,
                Path(os.environ.get("CARGO_HOME", str(Path.home() / ".cargo"))),
                clean_authority=clean_authority, clean_revision=clean_revision)
        except registry_owner.OwnerError as error:
            raise Refusal(str(error)) from error
    return AyTarget(authority.revision, version, declarations, required, has_exec_policy,
                    registry_owners)


def rewritten(files: dict[str, Snapshot], old: str, new: str,
              old_ay: str, new_ay: str, old_clean: str, new_clean: str,
              old_ay_version: str | None = None, new_ay_version: str | None = None, *,
              old_clean_version: str | None = None,
              new_clean_version: str | None = None,
              old_ir_version: str | None = None,
              new_ir_version: str | None = None) -> dict[str, bytes]:
    require((old_ay_version is None) == (new_ay_version is None),
            "AY version rewrite requires both old and new identities")
    require((old_clean_version is None) == (new_clean_version is None),
            "Clean version rewrite requires both old and new identities")
    require((old_ir_version is None) == (new_ir_version is None),
            "TrustIR version rewrite requires both old and new identities")
    result = {}
    for relative, names in [(MANIFESTS[0], ("trust-ir", "trust-ir-build", "trust-ir-conformance")),
                            (MANIFESTS[1], ("trust-ir", "trust-ir-build")), (REGALLOC, ("ay-pb", "ay-sat")),
                            (VERIFY, ("clean-kernel", "clean-olean", "clean-verify"))]:
        text = files[relative].data.decode()
        previous, following = ((old_ay, new_ay) if relative == REGALLOC else
                               (old_clean, new_clean) if relative == VERIFY else (old, new))
        for name in names:
            pattern = rf'(?m)^{re.escape(name)}\s*=\s*\{{[^\n}}]*\}}[^\n]*$'
            lines = list(re.finditer(pattern, text))
            require(len(lines) == 1, f"{relative}: {name} must have one inline declaration")
            line = lines[0]
            updated, count = re.subn(rf'\brev\s*=\s*"{previous}"', f'rev = "{following}"', line[0])
            require(count == 1, f"{relative}: ambiguous {name} revision")
            if (relative in MANIFESTS and old_ir_version is not None
                    and old_ir_version != new_ir_version):
                parsed = document(("[dependencies]\n" + updated + "\n").encode(), relative)
                if "version" in parsed["dependencies"][name]:
                    updated, count = re.subn(rf'\bversion\s*=\s*"{re.escape(old_ir_version)}"',
                                             f'version = "{new_ir_version}"', updated)
                    require(count == 1, f"{relative}: ambiguous {name} TrustIR version")
            if relative == REGALLOC and old_ay_version is not None:
                updated, count = re.subn(rf'\bversion\s*=\s*"{re.escape(old_ay_version)}"',
                                         f'version = "{new_ay_version}"', updated)
                require(count == 1, f"{relative}: ambiguous {name} version")
            if relative == VERIFY and old_clean_version is not None:
                parsed = document(("[dependencies]\n" + updated + "\n").encode(), relative)
                if "version" in parsed["dependencies"][name]:
                    updated, count = re.subn(rf'\bversion\s*=\s*"{re.escape(old_clean_version)}"',
                                             f'version = "{new_clean_version}"', updated)
                    require(count == 1, f"{relative}: ambiguous {name} Clean version")
            text = text[:line.start()] + updated + text[line.end():]
        result[relative] = text.encode()
    text = files[CACHE].data.decode()
    pattern = rf'(pub const {CACHE_NAME}: &str =\s*"trust_ir:){old}(";)'
    text, count = re.subn(pattern, lambda match: match[1] + new + match[2], text)
    require(count == 1, "compile cache identity is ambiguous")
    pattern = rf'(pub const {AY_CACHE_NAME}: &str =\s*"ay:){old_ay}(";)'
    text, count = re.subn(pattern, lambda match: match[1] + new_ay + match[2], text)
    require(count == 1, "AY compile cache identity is ambiguous")
    result[CACHE] = text.encode()
    return result


def package_index(rows: list[dict]) -> dict[str, list[dict]]:
    result = {}
    for row in rows:
        result.setdefault(row["name"], []).append(row)
    return result


def resolve_edge(raw: str, index: dict[str, list[dict]], label: str) -> dict:
    require(isinstance(raw, str), f"{label}: non-string dependency")
    match = re.fullmatch(r"([^ ()]+)(?: ([^ ()]+))?(?: \(([^()]+)\))?", raw)
    require(match is not None, f"{label}: malformed dependency identity")

    def source_matches(resolved):
        requested = match[3]
        if requested is None or resolved == requested:
            return True
        # Cargo's dependency disambiguator omits the precise Git fragment;
        # the selected package row retains it. Resolve that spelling to one
        # FULL row identity, never erase the commit from graph comparisons.
        # Explicit fragments, registry sources and differing rev queries do
        # not receive this abbreviation rule. Multiple matches still refuse.
        if not isinstance(resolved, str) or not requested.startswith("git+") or "#" in requested:
            return False
        base, separator, precise = resolved.rpartition("#")
        return base == requested and bool(separator) and SHA.fullmatch(precise) is not None

    selected = [row for row in index.get(match[1], [])
                if (match[2] is None or row["version"] == match[2])
                and source_matches(row.get("source"))]
    require(len(selected) == 1, f"{label}: unresolved/ambiguous dependency {raw}")
    return selected[0]


def matches_version(requirement: str, version: str) -> bool:
    # Bounded stable-numeric caret/exact admission shared with the Clean/TY
    # updaters, not a second general resolver. Other syntax fails closed.
    numeric = r"(0|[1-9][0-9]*)(?:\.(0|[1-9][0-9]*))?(?:\.(0|[1-9][0-9]*))?"
    requested = re.fullmatch(r"([=^]?)" + numeric, requirement) if isinstance(requirement, str) else None
    selected = re.fullmatch(numeric, version) if isinstance(version, str) else None
    require(requested is not None and selected is not None
            and all(part is not None for part in selected.groups()),
            f"unsupported version requirement/identity: {requirement!r} / {version!r}")
    parts = tuple(int(part) for part in requested.groups()[1:] if part is not None)
    lower = parts + (0,) * (3 - len(parts))
    actual = tuple(int(part) for part in selected.groups())
    if requested[1] == "=":
        require(len(parts) == 3, "partial exact version requirement is unsupported")
        return actual == lower
    pivot = next((index for index, value in enumerate(parts) if value), len(parts) - 1)
    upper = lower[:pivot] + (lower[pivot] + 1,) + (0,) * (2 - pivot)
    return lower <= actual < upper


def validate_graph(before: bytes, after: bytes, label: str, state: Current,
                   ir: str, clean: str, ay: str, authority: AyTarget | None = None,
                   admitted: dict[str, frozenset[str]] | None = None,
                   admitted_ay: dict[str, frozenset[str]] | None = None,
                   dropped: frozenset[str] = frozenset(), *,
                   clean_version: str | None = None,
                   ir_version: str | None = None) -> frozenset[str]:
    admitted = admitted or {}
    admitted_ay = admitted_ay or {}
    old_rows, new_rows = packages(before, label), packages(after, label)
    # A named third-party package may LEAVE this lock (--admit-dropped-package):
    # its row and every edge to it vanish, and nothing else may change.
    gone = frozenset(name for name in dropped
                     if any(row["name"] == name for row in old_rows)
                     and not any(row["name"] == name for row in new_rows))
    old_ir = cohort(old_rows, "trust-ir", IR_URL, state.ir)
    # An admitted package is gained exactly where a package requiring it is
    # resolved; every requirer is some lock's cohort member, so each admission
    # lands in at least one lock.
    gained = {name for name, required_by in admitted.items() if required_by & old_ir.keys()}
    ir_cohort_version = selected_ir_version(state, ir_version)
    expected = dict.fromkeys({*old_ir, *gained}, ir_cohort_version)
    require(cohort(new_rows, "trust-ir", IR_URL, ir) == expected,
            f"{label}: adding/removing/versioning the trust-ir cohort is unsupported"
            + (f" (admitted: {', '.join(sorted(admitted))})" if admitted else ""))
    clean_version = selected_clean_version(state, clean_version)
    old_clean = cohort(old_rows, "clean", CLEAN_URL, state.clean)
    require(dict.fromkeys(old_clean, clean_version)
            == cohort(new_rows, "clean", CLEAN_URL, clean),
            f"{label}: adding/removing/versioning the clean cohort is unsupported")
    ay_present = lambda rows: any(family(row["name"], "ay")
                                 or row.get("source", "").startswith("git+" + AY_URL) for row in rows)
    ay_version = state.ay_version if authority is None else authority.version
    if ay_version != state.ay_version:
        require((state.ay_version, ay_version) == AY_VERSION_MIGRATION,
                "unsupported AY package-version migration")
    try:
        old_vendor = exec_policy.locked_identity(old_rows, state.ay, state.ay_version)
        new_vendor = exec_policy.locked_identity(new_rows, ay, ay_version)
    except exec_policy.OwnerError as error:
        raise Refusal(f"{label}: {error}") from error
    require(old_vendor is None or new_vendor is not None,
            f"{label}: independent exec-policy owner cannot silently leave")
    if authority is not None:
        selected_owner = any(row["name"] == "ay-sys"
                             and row.get("source") == source(AY_URL, ay) for row in new_rows)
        require(bool(new_vendor) == (authority.exec_policy and selected_owner),
                f"{label}: independent exec-policy owner disagrees with immutable required edge")
    gained_ay: set[str] = set()
    if ay_present(old_rows) or ay_present(new_rows):
        old_ay = cohort(old_rows, "ay", AY_URL, state.ay)
        new_ay = cohort(new_rows, "ay", AY_URL, ay)
        # An admitted AY package may be gained only where a package requiring
        # it is resolved, and only at the cohort version.
        gained_ay = {name for name, required_by in admitted_ay.items()
                     if name in new_ay and required_by & old_ay.keys()}
        require(new_ay == dict.fromkeys({*old_ay, *gained_ay}, ay_version),
                f"{label}: adding/removing/versioning the AY cohort is unsupported"
                + (f" (admitted: {', '.join(sorted(admitted_ay))})" if admitted_ay else ""))
    replacements = {source(IR_URL, state.ir): source(IR_URL, ir),
                    source(CLEAN_URL, state.clean): source(CLEAN_URL, clean),
                    source(AY_URL, state.ay): source(AY_URL, ay)}
    old_index, new_index = package_index(old_rows), package_index(new_rows)
    try:
        gained_registry = registry_owner.validate_gain(old_rows, new_rows,
            None if authority is None else authority.registry_owners,
            lambda raw: resolve_edge(raw, new_index, label), matches_version)
    except registry_owner.OwnerError as error:
        raise Refusal(f"{label}: {error}") from error

    def identity(row, remap):
        original = row.get("source", "")
        if remap and family(row["name"], "trust-ir") and original == source(IR_URL, state.ir):
            return row["name"], ir_cohort_version, source(IR_URL, ir)
        if remap and family(row["name"], "clean") and original == source(CLEAN_URL, state.clean):
            return row["name"], clean_version, source(CLEAN_URL, clean)
        if remap and exec_policy.identity(row) == old_vendor:
            return exec_policy.NAME, exec_policy.VERSION, source(AY_URL, ay)
        if remap and family(row["name"], "ay") and original == source(AY_URL, state.ay):
            return row["name"], ay_version, source(AY_URL, ay)
        return row["name"], row["version"], replacements.get(original, original) if remap else original

    def edges(row, index, remap):
        raw = row.get("dependencies", [])
        require(isinstance(raw, list), f"{label}: malformed dependency array")
        selected = [identity(resolve_edge(edge, index, label), remap) for edge in raw]
        require(len(set(selected)) == len(selected), f"{label}: duplicate dependency identity")
        return sorted(selected)

    # Resolve each edge against one package index per lock. Only that identity
    # may be source-remapped; notes/checksums/metadata never carry this authority.
    def external_rows(rows, index, remap):
        result = []
        for row in rows:
            if any(family(row["name"], prefix) for prefix in ("trust-ir", "clean")):
                continue
            if row["name"] in gone:
                continue
            vendor = old_vendor if rows is old_rows else new_vendor
            if exec_policy.identity(row) == vendor:
                continue
            if rows is new_rows and registry_owner.identity(row) in gained_registry:
                continue
            if row["name"] in gained_ay:
                # Only in the new lock; its edges are bound to its immutable
                # manifest below, like every AY row's.
                continue
            saved = dict(row)
            if ay != state.ay and family(row["name"], "ay"):
                saved["version"] = identity(row, remap)[1]
                saved["source"] = identity(row, remap)[2]
                saved.pop("dependencies", None)
                edges(row, index, remap)  # Still reject malformed/dangling old edges.
            else:
                saved["dependencies"] = [edge for edge in edges(row, index, remap)
                                         if edge[0] not in gone]
            result.append(saved)
        return sorted(result, key=lambda row: (row["name"], row["version"], row.get("source", "")))

    old_external = external_rows(old_rows, old_index, True)
    new_external = external_rows(new_rows, new_index, False)
    # Name exact changed identities/edges before rollback. A refusal must be
    # actionable without rerunning resolution outside this atomic owner.
    external_delta = {
        "removed_or_changed": [row for row in old_external if row not in new_external],
        "added_or_changed": [row for row in new_external if row not in old_external],
    }
    require(old_external == new_external,
            f"{label}: resolver changed a package outside the admitted source cohort"
            + (f" (admitted drops: {', '.join(sorted(dropped))})" if dropped else "")
            + ": " + json.dumps(external_delta, sort_keys=True))
    # A gained package's own edges stay inside the widened TrustIR cohort.
    for row in new_rows:
        if row["name"] in gained:
            for name, _, identity_source in edges(row, new_index, False):
                require(name in expected and identity_source == source(IR_URL, ir),
                        f"{label}: admitted {row['name']} depends outside the TrustIR cohort: {name}")
    old_doc, new_doc = document(before, label), document(after, label)
    old_doc.pop("package")
    new_doc.pop("package")
    require(old_doc == new_doc, f"{label}: unsupported lock metadata change")
    if ay != state.ay:
        require(authority is not None and authority.revision == ay, "missing/wrong immutable AY graph authority")
        for row in new_rows:
            if not family(row["name"], "ay"):
                continue
            name = row["name"]
            require(name in authority.declarations and name in authority.required,
                    f"{name}: missing admitted AY manifest")
            selected = edges(row, new_index, False)
            require(authority.required[name] <= {edge[0] for edge in selected},
                    f"{name}: missing required target dependency")
            for package, version, identity_source in selected:
                declarations = authority.declarations[name].get(package, [])
                require(bool(declarations), f"{name}: dependency absent from immutable target: {package}")
                # A lock edge cannot identify which alias/platform supplied it.
                # All declarations for that package must admit the selection.
                for dep in declarations:
                    expected = source(dep["git"], dep["rev"]) if "git" in dep else REGISTRY
                    require(identity_source == expected, f"{name}: dependency source differs from immutable target: {package}")
                    if "version" in dep:
                        require(matches_version(dep["version"], version),
                                f"{name}: dependency version violates immutable target: {package}")
    return gone


def validate_installed(root: Path, before: dict[str, Snapshot], staged: dict[str, bytes],
                       state: Current, revision: str, clean: str, ay: str,
                       authority: AyTarget | None = None,
                       admitted: dict[str, frozenset[str]] | None = None,
                       admitted_ay: dict[str, frozenset[str]] | None = None,
                       dropped: frozenset[str] = frozenset(), *,
                       clean_version: str | None = None,
                       ir_version: str | None = None) -> None:
    after = snapshot(root)
    for relative in OWNED:
        require(after[relative].mode == before[relative].mode, f"{relative}: file mode changed")
    for relative, data in staged.items():
        require(after[relative].data == data, f"{relative}: resolver/guard changed staged source")
    new_state = current(root, after)
    require(new_state.ir == revision and new_state.clean == clean and new_state.ay == ay,
            "installed dependency authority disagrees with immutable target")
    require(new_state.ay_version == (state.ay_version if authority is None else authority.version),
            "installed AY package version disagrees with immutable target")
    require(set(new_state.clean_packages.values()) == {selected_clean_version(state, clean_version)},
            "installed Clean package version disagrees with immutable target")
    require(set(new_state.ir_packages.values()) == {selected_ir_version(state, ir_version)},
            "installed TrustIR package version disagrees with immutable target")
    left: set[str] = set()
    for lock in LOCKS:
        left |= validate_graph(before[lock].data, after[lock].data, lock, state, revision,
                               clean, ay, authority, admitted, admitted_ay, dropped,
                               clean_version=clean_version, ir_version=ir_version)
    for name in sorted(dropped - left):
        raise Refusal(f"--admit-dropped-package {name}: the move drops it from no lock")


def admit_dropped_packages(before: dict[str, Snapshot], names: tuple[str, ...]) -> frozenset[str]:
    """--admit-dropped-package: a NAMED third-party package may leave the locks.

    Only a registry package some current lock resolves qualifies (never a
    trust-ir, clean or AY cohort member, never a git or path package). The
    graph check then lets its row and the edges to it vanish where the
    resolver drops it, and nothing else; a removal adds no code to any build.
    """
    require(len(set(names)) == len(names), "duplicate --admit-dropped-package name")
    for name in names:
        require(not any(family(name, prefix) for prefix in ("trust-ir", "clean", "ay")),
                f"--admit-dropped-package {name}: only a third-party package may be dropped")
        rows = [row for lock in LOCKS for row in packages(before[lock].data, lock)
                if row["name"] == name]
        require(bool(rows), f"--admit-dropped-package {name}: no current lock resolves it")
        require(all(row.get("source") == REGISTRY for row in rows),
                f"--admit-dropped-package {name}: only a registry package may be dropped")
    return frozenset(names)


def transaction(root: Path, revision: str, commands: Commands,
                ay_revision: str | None = None, admit: tuple[str, ...] = (),
                admit_ay: tuple[str, ...] = (), drop: tuple[str, ...] = (),
                ay_version: str | None = None, admit_registry: tuple[str, ...] = (), *,
                qualification_ir_source: Path | None = None,
                qualification_receipt: Path | None = None,
                clean_version: str | None = None,
                ir_version: str | None = None) -> None:
    exact_sha(revision)
    if ay_revision is not None:
        exact_sha(ay_revision)
    require(ay_version is None or ay_revision is not None,
            "--ay-version requires an explicit --ay-revision")
    require((qualification_ir_source is None) == (qualification_receipt is None),
            "qualification source and receipt must be explicitly selected together")
    if qualification_receipt is not None:
        require(qualification_receipt.is_absolute() and not qualification_receipt.exists(),
                "qualification receipt needs a fresh absolute path")
    with exclusive(commands):
        clean_owned(commands)
        before = snapshot(root)
        dropped = admit_dropped_packages(before, tuple(drop))
        guard = safe_file(root, GUARD).read_bytes()
        corpus_guard = safe_file(root, CORPUS_GUARD).read_bytes()
        inventory_guards = {relative: safe_file(root, relative).read_bytes()
                            for relative, _, _ in INVENTORY_GUARDS}
        fixture_guards = {relative: safe_file(root, relative).read_bytes()
                          for relative, _, _, _ in FIXTURE_GUARDS}
        vendored = guard_tree(root, VENDORED_FIXTURES)
        state = current(root, before)
        ay_revision = state.ay if ay_revision is None else ay_revision
        selected_version = selected_ay_version(state, ay_version)
        selected_ir = selected_ir_version(state, ir_version)
        with tempfile.TemporaryDirectory(prefix="trust-cg-pin-authority-") as temporary:
            target = target_cohort(commands, Path(temporary), state, revision, ay_revision,
                                   tuple(admit), tuple(admit_ay), ay_version, admit_registry,
                                   qualification_ir_source=qualification_ir_source,
                                   clean_version=clean_version,
                                   ir_version=ir_version)
        clean = target.clean
        require(target.ay is None and selected_version == state.ay_version
                or target.ay is not None
                and (target.ay.revision, target.ay.version) == (ay_revision, selected_version),
                "immutable AY target disagrees with explicit revision/version")
        staged = rewritten(before, state.ir, revision, state.ay, ay_revision, state.clean, clean,
                           state.ay_version, selected_version,
                           old_clean_version=next(iter(set(state.clean_packages.values()))),
                           new_clean_version=selected_clean_version(state, clean_version),
                           old_ir_version=next(iter(set(state.ir_packages.values()))),
                           new_ir_version=selected_ir)
        clean_owned(commands)
        unchanged(root, before)
        backup = Path(tempfile.mkdtemp(prefix="trust-cg-pin-recovery-"))
        retain_backup = False
        try:
            for relative, saved in before.items():
                path = backup / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                with path.open("wb") as output:
                    output.write(saved.data)
                    output.flush()
                    os.fchmod(output.fileno(), saved.mode)
                    os.fsync(output.fileno())
            for relative, data in staged.items():
                install(root, relative, data, before[relative].mode)
            offline = ["--offline"] if qualification_ir_source is not None else []
            for lock in LOCKS:
                manifest = str(root / Path(lock).with_name("Cargo.toml"))
                commands.frontend(["metadata", "--format-version", "1", "--manifest-path", manifest,
                                   *offline])
                commands.frontend(["update", "--manifest-path", manifest, "-p",
                                   f"trust-ir@{selected_ir}", "--precise", revision,
                                   *offline])
                if target.ay is not None and target.ay.registry_owners:
                    try:
                        constraints = registry_owner.resolution_constraints(
                            packages(before[lock].data, lock),
                            packages(safe_file(root, lock).read_bytes(), lock),
                            target.ay.registry_owners, matches_version)
                    except registry_owner.OwnerError as error:
                        raise Refusal(str(error)) from error
                    for name, previous, wanted in constraints:
                        commands.frontend(["update", "--manifest-path", manifest, "-p",
                                           name + "@" + previous, "--precise", wanted, *offline])
            validate_installed(root, before, staged, state, revision, clean, ay_revision,
                               target.ay, target.admitted, target.admitted_ay, dropped,
                               clean_version=clean_version, ir_version=ir_version)
            gained_registry = set()
            for lock in LOCKS:
                old_ids = {registry_owner.identity(row) for row in packages(before[lock].data, lock)}
                gained_registry |= {row["name"] + "@" + row["version"]
                    for row in packages(safe_file(root, lock).read_bytes(), lock)
                    if row.get("source") == REGISTRY and registry_owner.identity(row) not in old_ids}
            require(set(admit_registry) <= gained_registry,
                    "named registry source admission gains its package in no lock")
            for lock in LOCKS:
                manifest = str(root / Path(lock).with_name("Cargo.toml"))
                commands.frontend(["metadata", "--locked", "--format-version", "1",
                                   "--manifest-path", manifest, *offline])
            if qualification_receipt is not None:
                require(target.qualification_ir_tree is not None,
                        "qualification stage has no immutable IR tree")
                require(safe_file(root, GUARD).read_bytes() == guard
                        and safe_file(root, CORPUS_GUARD).read_bytes() == corpus_guard
                        and all(safe_file(root, path).read_bytes() == data
                                for path, data in {**inventory_guards, **fixture_guards}.items())
                        and guard_tree(root, VENDORED_FIXTURES) == vendored,
                        "qualification preparation changed a guard or its fixture inputs")
                qualification_receipt.parent.mkdir(parents=True, exist_ok=True)
                originals = qualification_receipt.parent / (qualification_receipt.name + ".originals")
                originals.mkdir()
                after = snapshot(root)
                for relative, saved in before.items():
                    path = originals / relative
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(saved.data)
                    path.chmod(saved.mode)
                qualification_receipt.write_text(json.dumps({
                    "schema": "trust-cg.qualification-source-stage.v1",
                    "source_role": "untrusted-candidate-data",
                    "publication_authority": False,
                    "rust_guards": "NOT RUN", "upstream_qualification": "NOT JUDGED",
                    "ir_commit": revision, "ir_tree": target.qualification_ir_tree,
                    "clean_commit": clean, "ay_commit": ay_revision,
                    "originals": str(originals),
                    "files": {path: {
                        "before_sha256": hashlib.sha256(before[path].data).hexdigest(),
                        "after_sha256": hashlib.sha256(saved.data).hexdigest(),
                        "mode": saved.mode,
                    } for path, saved in after.items()},
                }, indent=2) + "\n")
                print("QUALIFICATION ONLY: staged immutable local IR source and locked graph; "
                      "Rust guards NOT RUN, adoption/publication NOT JUDGED. Restore original "
                      "bytes and run the ordinary authenticated transaction before landing.")
                return
            require(safe_file(root, GUARD).read_bytes() == guard, "independent Rust guard changed")
            # Compilation uses the repository default or build-slot's admitted
            # CARGO_BUILD_JOBS, like every later guard. Runtime order stays serial.
            commands.rust_guard(["--unverified", "test", "--locked", "-p", "trust-cg-test",
                               "--test", "dependency_authority"],
                               GUARD_TEST_NAMES["trust-cg-test", "dependency_authority"])
            require(safe_file(root, GUARD).read_bytes() == guard, "independent Rust guard changed")
            # The TrustIR-derived inventories, re-derived against the moved pin.
            for relative, package, target_name in INVENTORY_GUARDS:
                require(safe_file(root, relative).read_bytes() == inventory_guards[relative],
                        "TrustIR-derived inventory guard changed")
                commands.rust_guard(["--unverified", "test", "--locked", "-p", package,
                                    "--test", target_name],
                                   GUARD_TEST_NAMES[package, target_name])
                require(safe_file(root, relative).read_bytes() == inventory_guards[relative],
                        "TrustIR-derived inventory guard changed")
            # The conformance fixture guards (LD-84): the
            # census over the target corpus, then the vendored fixtures. They
            # run before the must-refuse corpus guard, which stays last. A red
            # one rolls the move back like every guard; its refusal also names
            # the data a pin move leaves stale, the cause of LD-77 and LD-81.
            for relative, package, target_name, update in FIXTURE_GUARDS:
                require(safe_file(root, relative).read_bytes() == fixture_guards[relative],
                        "conformance fixture guard changed")
                require(guard_tree(root, VENDORED_FIXTURES) == vendored,
                        "vendored conformance fixtures changed")
                try:
                    commands.rust_guard(["--unverified", "test", "--locked", "-p", package,
                                        "--test", target_name],
                                       GUARD_TEST_NAMES[package, target_name])
                except Refusal as error:
                    raise Refusal(f"{package} --test {target_name} is red at the target: "
                                  f"{error}; update {update}, then re-run the transaction") from error
                require(safe_file(root, relative).read_bytes() == fixture_guards[relative],
                        "conformance fixture guard changed")
                require(guard_tree(root, VENDORED_FIXTURES) == vendored,
                        "vendored conformance fixtures changed")
            # The must-refuse corpus guard: the TARGET revision's corpus, through
            # this backend's real admission paths (see the module docstring). A
            # row the new pin adds that this backend compiles fails here by name
            # and rolls the move back.
            require(safe_file(root, CORPUS_GUARD).read_bytes() == corpus_guard,
                    "must-refuse corpus guard changed")
            commands.rust_guard(["--unverified", "test", "--locked", "-p", "trust-cg-codegen",
                                "--test", "must_refuse_corpus"],
                               GUARD_TEST_NAMES["trust-cg-codegen", "must_refuse_corpus"])
            require(safe_file(root, CORPUS_GUARD).read_bytes() == corpus_guard,
                    "must-refuse corpus guard changed")
            require(guard_tree(root, VENDORED_FIXTURES) == vendored,
                    "vendored conformance fixtures changed")
            validate_installed(root, before, staged, state, revision, clean, ay_revision,
                               target.ay, target.admitted, target.admitted_ay, dropped,
                               clean_version=clean_version, ir_version=ir_version)
        except BaseException as error:
            try:
                restore(root, before)
            except BaseException as recovery:
                retain_backup = True
                raise Refusal(f"{recovery}; original-byte recovery files: {backup}; "
                              f"original failure: {type(error).__name__}: {error}") from error
            print("Pin transaction failed; restored all eight original files and modes.", file=sys.stderr)
            raise
        finally:
            if not retain_backup:
                shutil.rmtree(backup)
    admitted = "".join(f"; admitted {name}"
                       for name in sorted({*target.admitted, *target.admitted_ay}))
    admitted += "".join(f"; dropped {name}" for name in sorted(dropped))
    print(f"Updated TrustIR to {revision}; Clean source {clean}; AY {ay_revision}{admitted}. "
          "All eight files, the Rust authority guard, the TrustIR-derived inventories, the "
          "corpus census, the vendored container fixtures and the must-refuse corpus guard "
          "agree. "
          "Git index untouched; upstream qualification and soundness attestation remain "
          "separate.")


def selected_targo(raw: str) -> Path:
    path = Path(raw)
    require(path.is_absolute() and path.name == "targo", "--targo must be an absolute path named targo")
    require(path.is_file() and os.access(path, os.X_OK), "selected Targo is not an executable file")
    require(path.resolve().name == "targo", "selected Targo resolves to a different executable name")
    return path.resolve()


def interrupted(signum, _frame):
    raise InterruptedError(f"compiler-pin transaction interrupted by signal {signum}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("revision")
    parser.add_argument("--ay-revision", help="explicit coordinated AY source move")
    parser.add_argument("--ay-version", choices=[AY_VERSION_MIGRATION[1]],
                        help="explicit reviewed 0.27.0 to 0.28.0 package-version migration")
    parser.add_argument("--clean-version", choices=[CLEAN_VERSION_MIGRATION[1]],
                        help="explicit reviewed 0.9.1 to 0.9.2 package-version migration")
    parser.add_argument("--ir-version", choices=[IR_VERSION_MIGRATION[1]],
                        help="explicit reviewed 0.14.0 to 0.15.0 package-version migration")
    parser.add_argument("--targo", required=True, help="explicit operational frontend selection, not proof authority")
    parser.add_argument("--guard-admission", choices=("ordinary", "native-worker", "original-fixed-v1"),
                        default="native-worker",
                        help="explicit supported test interface; ordinary uses normal execution, not optional worker discovery")
    parser.add_argument("--authority-cache", action="append", default=[], metavar="NAME=/ABS/PATH",
                        help="source Git cache for trust-ir, clean or ay; fresh Agh authentication required")
    parser.add_argument("--stage-qualification-ir-source", type=Path,
                        help="stage local immutable IR DATA only; exits 3, no adoption/publication")
    parser.add_argument("--qualification-receipt", type=Path,
                        help="fresh absolute receipt retaining original files for qualification-only staging")
    parser.add_argument("--admit-ir-package", action="append", default=[], metavar="NAME",
                        help="explicitly admit one new trust-ir-* workspace crate the target requires")
    parser.add_argument("--admit-ay-package", action="append", default=[], metavar="NAME",
                        help="with --ay-revision, explicitly admit one new ay-* workspace package "
                             "an AY cohort package requires at the target")
    parser.add_argument("--admit-dropped-package", action="append", default=[], metavar="NAME",
                        help="explicitly admit one third-party registry package the target's "
                             "resolution drops from the locks (its row and the edges to it only)")
    parser.add_argument("--admit-registry-package", action="append", default=[],
                        choices=[registry_owner.SELECTION, registry_owner.REUSED_SELECTION,
                                 registry_owner.CLEAN_REUSED_SELECTION, registry_owner.WAIT_SELECTION],
                        help="explicit checksum-bound registry source required by the actual AY system owner")
    args = parser.parse_args(argv)
    previous = signal.signal(signal.SIGTERM, interrupted)
    try:
        root = Path(__file__).resolve().parent.parent
        revision = exact_sha(args.revision)
        caches = {}
        for entry in args.authority_cache:
            name, separator, path = entry.partition("=")
            urls = {"trust-ir": IR_URL, "clean": CLEAN_URL, "ay": AY_URL}
            require(separator and name in urls and urls[name] not in caches,
                    "authority cache must name one unique trust-ir, clean or ay source")
            cache = Path(path)
            require(cache.is_absolute() and cache.is_dir(), "authority cache needs an existing absolute directory")
            caches[urls[name]] = cache
        require(args.stage_qualification_ir_source is None or IR_URL not in caches,
                "qualification IR DATA cannot also be selected as an authenticated authority cache")
        transaction(root, revision, Commands(root, selected_targo(args.targo), caches,
                                            guard_admission=args.guard_admission), args.ay_revision,
                    tuple(args.admit_ir_package), tuple(args.admit_ay_package),
                    tuple(args.admit_dropped_package), args.ay_version,
                    tuple(args.admit_registry_package),
                    qualification_ir_source=args.stage_qualification_ir_source,
                    qualification_receipt=args.qualification_receipt,
                    clean_version=args.clean_version, ir_version=args.ir_version)
        return 3 if args.stage_qualification_ir_source is not None else 0
    except (Refusal, OSError, KeyboardInterrupt) as error:
        print(f"REFUSED: {error}", file=sys.stderr)
        return 1
    finally:
        signal.signal(signal.SIGTERM, previous)


if __name__ == "__main__":
    raise SystemExit(main())
