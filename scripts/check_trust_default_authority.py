#!/usr/bin/env python3
"""Fail-closed preflight for any future Trust-verified repository default.

An upstream toolchain is an honest, unverified default and passes unless
``--require-verified-default`` is requested. This checker does not turn
verification on; it prevents configuration text from claiming authority that
the installed toolchain cannot supply. A ``channel = "trust"`` pin is read in
one of two ways, decided by the Cargo configuration alone:

* Trust toolchain SELECTION: the Cargo configuration carries no Trust flag at
  all (no ``-Z trust-*`` option in any string and any spelling rustc accepts,
  so neither a policy nor an activation nor an off-switch). The pin then only
  chooses the compiler; each invocation's lane is chosen by ``targo``
  (``targo --unverified`` makes no proof claim, ``targo trust`` authenticates
  its own verdict), so the repository makes no verified-default claim. The
  checker requires the configuration not to route around ``trustc`` (no rustc
  wrapper or path, no ambient override or Trust flag, no rustc argfile whose
  flags it cannot read, no ``TRUST_NO_VERIFY`` transport) and the ``PATH``
  ``trustc``/``targo`` to be
  one branded package: ``binary: trustc``, a 40-hex commit, the package's own
  sysroot, and a ``targo`` that accepts ``--unverified`` (upstream cargo
  rejects it). atpkg launcher shims are followed to the package files they
  exec (``scripts/trust_toolchain.py``). ``--require-verified-default`` still
  applies the whole contract below, which a selection does not satisfy.
* Verified-default CLAIM: any Trust flag in the Cargo configuration. It is
  accepted only when its policy is strict or certify, no unit is switched off,
  and the installed Trust toolchain is one recorded, read-only sysroot whose
  identity equals a committed identity lock (the contract below).

Installed-toolchain contract
----------------------------

Identity comes from the compiler, never from a path label: ``-Vv`` must report
a canonical 40-hex ``commit-hash`` and ``binary: trustc``, the branded driver
that ``scripts/run_full_test_matrix.sh --check-rustc-backend-env`` and
``scripts/check_linux_aarch64_bridge.py`` also require. Labels are only checked
against that identity.

Recorded sysroot: ``TRUST_SEALED_SYSROOT`` must name an existing directory that
is not itself a symlink and that the compiler's ``--print sysroot`` resolves to
identically. It binds to the reported commit-hash in one of two ways:

* its basename is ``trust-<prefix>``, where ``<prefix>`` is at least
  ``SEAL_PREFIX_MIN_HEX`` lowercase hex digits and a prefix of the reported
  commit-hash. Trust's ``scripts/promote-toolchain.sh`` names seals
  ``trust-<8-hex short hash>``; a full 40-hex name also binds; or
* it carries a ``PROVENANCE`` record whose ``reported_commit`` equals the
  reported commit-hash and whose ``seal_name`` is such a ``trust-<prefix>``,
  as when a promoted seal is laid out under another name (the atpkg store's
  ``trust/<build>``).

A ``PROVENANCE`` record, whenever present, must not contradict the compiler:
``reported_commit`` and ``seal_name`` must bind as above, ``provenance_class``
must be ``BUILD-STAMPED-CLEAN`` with no dirty-provenance waiver, and every
recorded ``artifact_driver_sha256`` and ``artifact_bin_<tool>_sha256`` must
equal the file in the tree. A key repeated with a different value is voided.

Immutability: no symlink or unreadable directory anywhere in the sealed tree,
no directory or file with any write bit (directories 0o555, files 0o444 or
0o555), and neither the sysroot nor a rustup link may resolve into a mutable
``build/host/stage2``. Write bits are a local permission state, not
authentication.

Two resolution models are accepted:

* ``pack``: ``trustc`` or ``targo`` is on ``PATH``. Both must resolve to
  executable files in one ``bin/`` directory whose parent is the reported
  sysroot and the sealed root. This is how the matrix and bridge runners
  resolve Trust. A rustup ``trust`` toolchain may also exist, but only when it
  resolves to the same sealed root; a divergent link is rejected because a
  rustup-proxied ``cargo`` would then build with another compiler.
* ``linked``: neither pack tool is on ``PATH``; ``rustup which --toolchain
  trust rustc`` resolves to ``bin/rustc`` in the sealed root and
  ``$RUSTUP_HOME/toolchains/trust`` resolves to the sealed root. That
  ``bin/rustc`` must itself report ``binary: trustc``. A driver that brands
  itself from ``argv[0]`` therefore qualifies only through the ``pack`` model
  (in the atpkg pack inspected on 2026-09-18, ``bin/rustc`` and ``bin/trustc``
  are one hard-linked file and ``rustc -Vv`` reports ``binary: rustc``).

Host/target coherence: the required target is ``--required-target`` or, by
default, the running machine's triple. It must be one of ``PRIMARY_TARGETS``
and equal the running machine; the reported host must equal it; and the sealed
tree must ship ``lib/rustlib/<target>/lib/libstd-*``.

CG backend expectation: the diagnostics record any ``librustc_codegen_trust*``
dylib in ``lib/rustlib/<host>/codegen-backends/`` and any trust-cg bridge
dylib (``librustc_codegen_trust_cg``) under ``lib/``. Finding neither is a
failure only under ``--require-verified-default``. The canaries emit metadata
only and select no backend, so this is a presence check, not a backend test.

Committed identity: ``trust_toolchain_identity.lock`` at the repository root
must be a regular file whose lines are ``identity = <host> <commit-hash>
<sysroot-tree-sha256>``, at most one per primary target. The line for the
reported host must equal the reported commit-hash and ``sysroot_tree_digest``
of the sealed tree (SHA-256 over every entry's relative path, kind, executable
bit and content SHA-256). Ruling OD-01 (docs/decision-record.md): the lock
names an atpkg-published, sealed Trust package (read-only, with PROVENANCE),
never a tree-built or writable one. None exists yet, so no lock is committed
and a Trust claim fails closed. The
lock pins content; it is not a signature, and nothing here verifies a signed
package manifest or who produced the tree.

Behavior: two metadata-only canaries run with no flags. A trivial crate must
compile, and a division crate must be rejected with Trust verification failure
evidence. They exercise the installed compiler's no-flag default, not a
workspace's per-unit policy. They run only after every identity check above
passes, except under ``--inspect``.

``--inspect`` resolves the installed toolchain and prints the diagnostics as
JSON regardless of the repository channel, running the canaries whenever a
compiler resolved. On a stock channel without ``--require-verified-default``
the verdict stays PASS and installed findings print as INFO lines; with it,
every finding is a FAIL. A default invocation on a stock channel resolves
nothing and runs no compiler.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import re
import shutil
import stat
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable, Mapping, Optional, Sequence

sys.path.insert(0, os.fspath(Path(__file__).resolve().parent))
from trust_toolchain import launcher_target, without_untracked_controls  # noqa: E402


CHANNEL_RE = re.compile(r'^\s*channel\s*=\s*["\']([^"\']+)["\']\s*$', re.MULTILINE)
MUTABLE_STAGE2_RE = re.compile(r'(?:^|/)build/host/stage2(?:/|$)')
COMMIT_HASH_RE = re.compile(r'^[0-9a-f]{40}$')
SHA256_RE = re.compile(r'^[0-9a-f]{64}$')
# Trust's promote layout names a seal trust-<short> with an 8-hex short hash;
# a shorter label binds too little of the identity to be accepted.
SEAL_PREFIX_MIN_HEX = 8
SEAL_NAME_RE = re.compile(r'^trust-([0-9a-f]{%d,40})$' % SEAL_PREFIX_MIN_HEX)
PROVENANCE_NAME = "PROVENANCE"
PROVENANCE_FIELD_RE = re.compile(r'^([A-Za-z_][A-Za-z0-9_]*)=(.*)$')
CLEAN_PROVENANCE_CLASS = "BUILD-STAMPED-CLEAN"
ARTIFACT_BIN_KEY_RE = re.compile(r'^artifact_bin_([A-Za-z0-9_]+)_sha256$')
# A verified default is qualified on the host that runs it.
PRIMARY_TARGETS = ("aarch64-unknown-linux-gnu", "aarch64-apple-darwin")
PACK_TOOLS = ("trustc", "targo")
TRUST_BACKEND_PREFIX = "librustc_codegen_trust"
BRIDGE_DYLIB_RE = re.compile(r'^librustc_codegen_trust_cg(?:-[^/]+)?\.(?:dylib|so)$')
IDENTITY_LOCK_NAME = "trust_toolchain_identity.lock"
IDENTITY_LINE_RE = re.compile(r'^identity\s*=\s*(\S+)\s+(\S+)\s+(\S+)$')
TREE_DIGEST_DOMAIN = b"trust-cg sealed sysroot tree v1\0"
WRITE_BITS = stat.S_IWUSR | stat.S_IWGRP | stat.S_IWOTH
RUSTC_OVERRIDE_RE = re.compile(
    r'^\s*(?:(?:build|env)\s*\.\s*)?'
    r'(?:rustc-wrapper|rustc-workspace-wrapper|rustc|RUSTC|RUSTC_WRAPPER|'
    r'RUSTC_WORKSPACE_WRAPPER|CARGO_BUILD_RUSTC|CARGO_BUILD_RUSTC_WRAPPER|'
    r'CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER)\s*=',
    re.MULTILINE,
)
AMBIENT_RUSTC_OVERRIDES = {
    "RUSTC",
    "RUSTC_WRAPPER",
    "RUSTC_WORKSPACE_WRAPPER",
    "CARGO_BUILD_RUSTC",
    "CARGO_BUILD_RUSTC_WRAPPER",
    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
}
# rustc reads `-Z` through getopts and folds `-` to `_` in the option name, so
# one option has many spellings. `-Ztrust_verify=off`, `-Z trust_verify=off`,
# `--Z trust-verify=off`, `--Z=trust-verify=off` and a grouped short-flag
# prefix such as `-OZtrust-verify=off` all switch verification off exactly as
# `-Ztrust-verify=off` does (measured 2026-09-28, trustc 321aaeda7). Each is
# canonicalised to `-Ztrust-<name>[=<value>]`. The grouped prefix is matched on
# any letters, which can only over-report (a `-C` or `-o` value that begins
# with `Z`) in this fail-closed preflight, never miss a `-Z`.
Z_SHORT_OPTION_RE = re.compile(r'^-(?!-)[A-Za-z]*?Z(.*)$', re.DOTALL)
Z_LONG_OPTION_RE = re.compile(r'^--Z(=.*)?$', re.DOTALL)
# `TRUST_NO_VERIFY=1` in a compiler's environment switches verification off,
# silently (measured 2026-09-28, trustc 321aaeda7: the refutation canary
# compiles with no Trust note at all). Cargo's `[env]` table reaches rustc, so
# a configuration that names it, or an ambient value, is an off-switch.
NO_VERIFY_TRANSPORT = "TRUST_NO_VERIFY"
NO_VERIFY_TRANSPORT_RE = re.compile(r'(?<![A-Za-z0-9_])TRUST_NO_VERIFY(?![A-Za-z0-9_])')


@dataclass(frozen=True)
class ResolvedToolchain:
    """What resolution found; ``model`` is ``"pack"``, ``"linked"`` or ``None``.

    ``rustc`` is the resolved compiler driver: ``trustc`` under the pack model,
    rustup's ``rustc`` under the linked model. ``build_tool`` is ``targo`` under
    the pack model only. ``rustup_link`` is ``$RUSTUP_HOME/toolchains/trust``
    when present (required by the linked model, coherence-checked by the pack
    model). ``sealed_root`` is the recorded ``TRUST_SEALED_SYSROOT``. ``note``
    says why nothing resolved.
    """

    rustc: Optional[Path]
    sysroot: Optional[Path]
    rustup_link: Optional[Path]
    sealed_root: Optional[Path]
    host: Optional[str]
    commit_hash: Optional[str]
    model: Optional[str] = "linked"
    build_tool: Optional[Path] = None
    binary: Optional[str] = None
    note: Optional[str] = None


@dataclass(frozen=True)
class LockedIdentity:
    host: str
    commit_hash: str
    tree_sha256: str


@dataclass
class Report:
    """``issues`` decide the verdict; ``informational`` findings never do.

    ``selection`` describes the Trust package a toolchain selection resolved.
    """

    issues: list
    informational: list
    diagnostics: Optional[dict]
    selection: Optional[dict] = None


class _Detect:
    """Sentinel type: detect the running machine's host triple."""


DETECT = _Detect()


def toolchain_channel(text: str) -> Optional[str]:
    match = CHANNEL_RE.search(text)
    return match.group(1) if match else None


def _toml_strings_and_normalized(text: str) -> tuple[list[str], str, list[str]]:
    """Lex enough Cargo TOML to decode strings and erase comments.

    Trust flags are collected from every string, rather than from a short list
    of table layouts. That is deliberately fail-closed: Cargo accepts flags in
    target, build, and ``[env]`` tables, including dotted and quoted keys.
    Multiline strings are not useful Cargo flag values and are rejected instead
    of being incompletely audited.
    """
    strings: list[str] = []
    normalized: list[str] = []
    issues: list[str] = []
    index = 0
    while index < len(text):
        char = text[index]
        if char == "#":
            newline = text.find("\n", index)
            if newline < 0:
                break
            normalized.append("\n")
            index = newline + 1
            continue
        if char not in {'"', "'"}:
            normalized.append(char)
            index += 1
            continue

        quote = char
        if text.startswith(quote * 3, index):
            issues.append("verified Cargo configuration cannot use multiline strings")
            closing = text.find(quote * 3, index + 3)
            if closing < 0:
                return strings, "".join(normalized), issues
            index = closing + 3
            continue

        end = index + 1
        escaped = False
        while end < len(text):
            current = text[end]
            if quote == '"' and current == "\\" and not escaped:
                escaped = True
                end += 1
                continue
            if current == quote and not escaped:
                break
            escaped = False
            if current == "\n":
                issues.append("verified Cargo configuration contains an unterminated string")
                return strings, "".join(normalized), issues
            end += 1
        if end >= len(text):
            issues.append("verified Cargo configuration contains an unterminated string")
            return strings, "".join(normalized), issues

        token = text[index : end + 1]
        try:
            if quote == '"':
                # JSON and TOML share the single-line basic-string escapes used
                # by Cargo. Expand TOML's eight-hex-digit form before JSON.
                token = re.sub(
                    r"\\U([0-9A-Fa-f]{8})",
                    lambda match: "\\u" + match.group(1)[4:]
                    if int(match.group(1), 16) <= 0xFFFF
                    else chr(int(match.group(1), 16)),
                    token,
                )
                value = json.loads(token)
            else:
                value = token[1:-1]
        except (ValueError, json.JSONDecodeError):
            issues.append("verified Cargo configuration contains an unauditable string escape")
            value = token[1:-1]
        strings.append(value)
        # Decoding quoted keys closes Unicode-escape evasions in names such as
        # ``RUSTC_WRAPPER``. Escaping a quote may only create a conservative
        # false positive in this fail-closed authority preflight.
        normalized.append(value)
        index = end + 1
    return strings, "".join(normalized), issues


def _flag_tokens(values: Iterable[str]) -> list:
    tokens = []
    for value in values:
        tokens.extend(value.replace("\x1f", " ").split())
    return tokens


def _canonical_z_option(value: str) -> Optional[str]:
    """``-Ztrust-<name>[=<value>]`` for a ``-Z`` value naming a Trust option."""
    name, separator, setting = value.partition("=")
    name = name.replace("_", "-")
    if not name.startswith("trust-"):
        return None
    return f"-Z{name}{separator}{setting}"


def _canonical_trust_flags(values: Iterable[str]) -> Iterable[str]:
    """Yield every Trust ``-Z`` option in ``values`` in its canonical spelling."""
    tokens = _flag_tokens(values)
    index = 0
    while index < len(tokens):
        token = tokens[index]
        index += 1
        long_form = Z_LONG_OPTION_RE.match(token)
        short_form = None if long_form else Z_SHORT_OPTION_RE.match(token)
        if long_form is not None:
            attached = long_form.group(1)[1:] if long_form.group(1) is not None else None
        elif short_form is not None:
            attached = short_form.group(1) or None
        else:
            continue
        if attached is not None:
            canonical = _canonical_z_option(attached)
        elif index < len(tokens):
            # The value is the next argument. It is consumed only when it names
            # a Trust option; otherwise it is scanned again as a flag itself.
            canonical = _canonical_z_option(tokens[index])
            if canonical is not None:
                index += 1
        else:
            canonical = None
        if canonical is not None:
            yield canonical


def _argfile_references(values: Iterable[str]) -> Iterable[str]:
    """Yield ``@path`` arguments: rustc expands them into flags this check cannot read."""
    return (token for token in _flag_tokens(values) if token.startswith("@"))


def _ambient_flag_values(environment: Mapping[str, str]) -> list:
    return [
        value
        for key, value in environment.items()
        if value
        and (
            key in {"RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTFLAGS"}
            or (key.startswith("CARGO_") and key.endswith(("_RUSTFLAGS", "_RUSTDOCFLAGS")))
        )
    ]


def _hidden_off_switch_issues(
    subject: str,
    strings: Sequence[str],
    normalized: str,
    environment: Optional[Mapping[str, str]],
) -> list:
    """Flags and transports that switch verification off without a ``-Z`` spelling."""
    issues = []
    if any(True for _ in _argfile_references(strings)):
        issues.append(
            f"{subject} cannot pass a rustc argfile (@path) in Cargo configuration; "
            "its flags cannot be audited"
        )
    if NO_VERIFY_TRANSPORT_RE.search(normalized):
        issues.append(
            f"{subject} cannot set {NO_VERIFY_TRANSPORT}, the compiler's inherited "
            "verification off-switch"
        )
    if environment is not None:
        if any(True for _ in _argfile_references(_ambient_flag_values(environment))):
            issues.append(f"{subject} cannot inherit a rustc argfile (@path) in ambient compiler flags")
        if environment.get(NO_VERIFY_TRANSPORT):
            issues.append(
                f"{subject} cannot inherit {NO_VERIFY_TRANSPORT}, the compiler's inherited "
                "verification off-switch"
            )
    return issues


def configured_flags(config_text: str) -> Iterable[str]:
    """Yield canonical Trust flags from all decoded Cargo string values."""
    strings, _, _ = _toml_strings_and_normalized(config_text)
    yield from _canonical_trust_flags(strings)


def configures_trust_flags(config_text: str) -> bool:
    """Whether any decoded Cargo string carries a Trust flag (a claim)."""
    return any(True for _ in configured_flags(config_text))


def selection_config_issues(
    config_text: str, environment: Optional[Mapping[str, str]] = None
) -> list[str]:
    """Judge a flag-free Cargo configuration under a Trust toolchain selection."""
    strings, normalized, issues = _toml_strings_and_normalized(config_text)
    issues = list(issues)
    if RUSTC_OVERRIDE_RE.search(normalized):
        issues.append("Trust toolchain selection cannot use a rustc wrapper or alternate rustc path")
    if environment is not None:
        overrides = sorted(key for key in AMBIENT_RUSTC_OVERRIDES if environment.get(key))
        if overrides:
            issues.append(
                "Trust toolchain selection cannot inherit an ambient rustc override: "
                + ", ".join(overrides)
            )
        if list(_canonical_trust_flags(_ambient_flag_values(environment))):
            issues.append("Trust toolchain selection cannot inherit ambient Trust compiler flags")
    issues += _hidden_off_switch_issues(
        "Trust toolchain selection", strings, normalized, environment
    )
    return issues


def selected_package(root: Path, environment: Mapping[str, str]) -> tuple:
    """Resolve the PATH Trust package a toolchain selection runs; ``(record, issues)``."""
    path_value = environment.get("PATH", "")
    found = {name: shutil.which(name, path=path_value) for name in PACK_TOOLS}
    missing = [name for name, path in found.items() if path is None]
    if missing:
        return None, [
            "Trust toolchain selection needs the installed package's "
            + " and ".join(missing)
            + " on PATH; there is no stock fallback"
        ]
    compiler = _resolved_tool(found["trustc"])
    build_tool = _resolved_tool(found["targo"])
    assert compiler is not None and build_tool is not None
    launchers = None
    shim_compiler, shim_build_tool = launcher_target(compiler), launcher_target(build_tool)
    if shim_compiler is not None or shim_build_tool is not None:
        if shim_compiler is None or shim_build_tool is None:
            return None, [
                "PATH trustc and targo must both be atpkg launcher shims or both be package "
                f"files: {compiler} vs {build_tool}"
            ]
        launchers = {"trustc": os.fspath(compiler), "targo": os.fspath(build_tool)}
        compiler = _resolved_tool(os.fspath(shim_compiler))
        build_tool = _resolved_tool(os.fspath(shim_build_tool))
        assert compiler is not None and build_tool is not None
    issues = []
    if not _is_executable_file(compiler) or not _is_executable_file(build_tool):
        issues.append(f"PATH Trust package tools are not executable files: {compiler}, {build_tool}")
        return None, issues
    if compiler.parent != build_tool.parent:
        issues.append(
            "PATH trustc and targo must resolve to the same installed package: "
            f"{compiler} vs {build_tool}"
        )
    if compiler.name != "trustc":
        issues.append(f"Trust toolchain selection must run the branded trustc, not {compiler.name}")
    identity = _compiler_identity(compiler, root, environment)
    if identity.get("binary") != "trustc":
        issues.append(
            "Trust compiler is not the branded trustc driver: "
            f"binary {identity.get('binary') or 'unreported'}"
        )
    commit_hash = identity.get("commit_hash")
    if commit_hash is None or COMMIT_HASH_RE.fullmatch(commit_hash) is None:
        issues.append("Trust compiler did not report a canonical 40-hex commit-hash")
    sysroot = identity.get("sysroot")
    try:
        sysroot_path = Path(sysroot).resolve(strict=True) if sysroot else None
    except OSError:
        sysroot_path = None
    if sysroot_path is None or sysroot_path != compiler.parent.parent:
        issues.append(
            "Trust compiler/sysroot package mismatch: trustc is not the bin/trustc of its "
            f"reported sysroot ({compiler} vs {sysroot})"
        )
    # `targo --unverified --version` is the one discriminator between targo and
    # upstream cargo shipped under its name (upstream rejects the flag).
    try:
        targo_version = _run(
            [os.fspath(build_tool), "--unverified", "--version"],
            root,
            _identity_probe_environment(environment),
        )
    except RuntimeError as error:
        targo_version = ""
        issues.append(f"PATH targo is not targo (it rejected --unverified): {error}")
    else:
        if not targo_version.startswith("targo "):
            issues.append(f"PATH targo did not identify as targo: {targo_version!r}")
    record = {
        "compiler": os.fspath(compiler),
        "build_tool": os.fspath(build_tool),
        "launchers": launchers,
        "commit_hash": commit_hash,
        "host": identity.get("host"),
        "sysroot": sysroot,
        "targo_version": targo_version,
    }
    return (None if issues else record), issues


def policy_issues(
    toolchain_text: str,
    config_text: str,
    environment: Optional[Mapping[str, str]] = None,
) -> list[str]:
    if toolchain_channel(toolchain_text) != "trust":
        return []

    strings, normalized, lexical_issues = _toml_strings_and_normalized(config_text)
    issues = list(lexical_issues)
    if RUSTC_OVERRIDE_RE.search(normalized):
        issues.append("verified default cannot use a rustc wrapper or alternate rustc path")
    flags = list(_canonical_trust_flags(strings))
    policies = [flag for flag in flags if flag.startswith("-Ztrust-policy")]
    if not policies:
        issues.append("verified default must explicitly select strict or certify policy")
    elif len(policies) > 1:
        issues.append("multiple Trust policies make the authority claim ambiguous")
    for policy in policies:
        if policy not in {"-Ztrust-policy=strict", "-Ztrust-policy=certify"}:
            issues.append(f"Trust policy is not strict or certify: {policy}")
    for activation in (flag for flag in flags if flag.startswith("-Ztrust-verify")):
        if activation != "-Ztrust-verify=on":
            issues.append("at least one host, target, or rustdoc unit disables verification")

    if environment is not None:
        overrides = sorted(key for key in AMBIENT_RUSTC_OVERRIDES if environment.get(key))
        if overrides:
            issues.append(
                "verified default cannot inherit an ambient rustc override: "
                + ", ".join(overrides)
            )
        if list(_canonical_trust_flags(_ambient_flag_values(environment))):
            issues.append("verified default cannot inherit ambient Trust compiler flags")
    issues += _hidden_off_switch_issues("verified default", strings, normalized, environment)
    return issues


def _is_read_only(path: Path) -> bool:
    return path.exists() and path.stat().st_mode & WRITE_BITS == 0


def _sealed_tree_issues(root: Path) -> list[str]:
    """Reject one mutable or symlinked artifact anywhere below ``root``."""
    issues = []
    if not _is_read_only(root):
        issues.append("sealed sysroot root retains write bits")

    first_symlink = None
    first_writable = None
    # os.walk skips a directory it cannot list unless told, and a directory
    # that can be listed but not searched makes every lstat below it fail
    # (EACCES). Either leaves a subtree unaudited, which must fail, not crash.
    unreadable: list = []
    walk = os.walk(
        root, followlinks=False, onerror=lambda error: unreadable.append(error.filename)
    )
    for directory, dirnames, filenames in walk:
        parent = Path(directory)
        for name in list(dirnames) + filenames:
            candidate = parent / name
            try:
                # os.lstat raises on EACCES on every Python; pathlib's
                # predicates swallow it on newer ones.
                mode = os.lstat(candidate).st_mode
            except OSError:
                unreadable.append(os.fspath(parent))
                if name in dirnames:
                    dirnames.remove(name)
                continue
            if stat.S_ISLNK(mode):
                first_symlink = first_symlink or candidate
                if name in dirnames:
                    dirnames.remove(name)
            elif mode & WRITE_BITS:
                first_writable = first_writable or candidate
    if first_symlink is not None:
        issues.append(f"sealed sysroot contains a symlinked artifact: {first_symlink}")
    if first_writable is not None:
        issues.append(f"sealed sysroot contains a writable artifact: {first_writable}")
    if unreadable:
        issues.append(f"sealed sysroot contains an unreadable directory: {unreadable[0]}")
    return issues


def _is_executable_file(path: Optional[Path]) -> bool:
    return path is not None and path.is_file() and os.access(path, os.X_OK)


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _raise(error: OSError) -> None:
    raise error


def sysroot_tree_digest(root: Path) -> str:
    """Hash the tree below ``root`` into one content identity.

    Each entry contributes its kind and relative POSIX path; a file adds its
    executable bit and content SHA-256, a symlink its target. Records are
    length-prefixed and hashed in sorted path order, so the digest does not
    depend on enumeration order, timestamps, ownership or write bits (the
    immutability checks judge those separately). An unreadable directory
    raises ``OSError`` rather than being skipped.
    """
    records = []
    for directory, dirnames, filenames in os.walk(root, followlinks=False, onerror=_raise):
        parent = Path(directory)
        for name in dirnames + filenames:
            path = parent / name
            relative = os.fsencode(path.relative_to(root).as_posix())
            mode = os.lstat(path).st_mode
            if stat.S_ISLNK(mode):
                record = b"l\0" + relative + b"\0" + os.fsencode(os.readlink(path))
            elif stat.S_ISDIR(mode):
                record = b"d\0" + relative
            elif stat.S_ISREG(mode):
                executable = b"x" if mode & 0o111 else b"-"
                record = b"f\0" + relative + b"\0" + executable + b"\0"
                record += _file_sha256(path).encode("ascii")
            else:
                record = b"o\0" + relative
            records.append((relative, record))
    digest = hashlib.sha256(TREE_DIGEST_DOMAIN)
    for _, record in sorted(records):
        digest.update(len(record).to_bytes(8, "big") + record)
    return digest.hexdigest()


def _provenance_fields(path: Path) -> Optional[dict]:
    """Parse ``key=value`` lines, or return ``None`` when unreadable.

    Comments and lines that are not ``key=value`` (such as promote's
    ``build_stamp:`` copies) are ignored. A key repeated with a different value
    is voided to the empty string, so one record cannot say two things.
    """
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return None
    fields: dict = {}
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        match = PROVENANCE_FIELD_RE.match(line)
        if match is None:
            continue
        key, value = match.group(1), match.group(2).strip()
        if key in fields and fields[key] != value:
            fields[key] = ""
        else:
            fields.setdefault(key, value)
    return fields


def read_provenance(sealed: Path) -> tuple:
    """Return ``(fields, issues)``; ``fields`` is ``None`` when no record is usable."""
    path = sealed / PROVENANCE_NAME
    try:
        present = path.exists() or path.is_symlink()
        regular = present and not path.is_symlink() and path.is_file()
    except OSError as error:
        return None, [f"sealed sysroot {PROVENANCE_NAME} could not be inspected: {error}"]
    if not present:
        return None, []
    if not regular:
        return None, [f"sealed sysroot {PROVENANCE_NAME} is not a regular file: {path}"]
    fields = _provenance_fields(path)
    if fields is None:
        return None, [f"sealed sysroot {PROVENANCE_NAME} is unreadable: {path}"]
    return fields, []


def _seal_name_binds(name: str, commit_hash: str) -> bool:
    match = SEAL_NAME_RE.fullmatch(name)
    return match is not None and commit_hash.startswith(match.group(1))


def seal_binding(
    sealed: Path, commit_hash: str, provenance: Optional[Mapping[str, str]]
) -> tuple:
    """Bind the sealed directory to the reported commit-hash.

    Returns ``("name", [])`` when the basename is ``trust-<prefix>`` of the
    hash, ``("provenance", [])`` when a ``PROVENANCE`` record binds
    ``seal_name`` and ``reported_commit`` to it, and ``(None, issues)``
    otherwise.
    """
    if _seal_name_binds(sealed.name, commit_hash):
        return "name", []
    if (
        provenance is not None
        and provenance.get("reported_commit") == commit_hash
        and _seal_name_binds(provenance.get("seal_name", ""), commit_hash)
    ):
        return "provenance", []
    return None, [
        f"sealed sysroot {sealed.name} is neither named trust-<prefix of {commit_hash}> "
        f"(at least {SEAL_PREFIX_MIN_HEX} hex digits) nor bound to it by a "
        f"{PROVENANCE_NAME} record"
    ]


def _recorded_artifact_issue(path: Path, recorded: str, label: str) -> Optional[str]:
    if recorded == "-":
        if path.exists() or path.is_symlink():
            return f"sealed sysroot {label} was absent at seal time but is present: {path}"
        return None
    if SHA256_RE.fullmatch(recorded) is None:
        return (
            f"sealed sysroot {PROVENANCE_NAME} records a malformed {label} digest: "
            f"{recorded or 'empty'}"
        )
    if path.is_symlink() or not path.is_file():
        return f"sealed sysroot {label} recorded in {PROVENANCE_NAME} is missing: {path}"
    try:
        actual = _file_sha256(path)
    except OSError as error:
        return f"sealed sysroot {label} is unreadable: {error}"
    if actual != recorded:
        return f"sealed sysroot {label} does not match its {PROVENANCE_NAME} digest: {path}"
    return None


def provenance_issues(
    sealed: Path, commit_hash: str, provenance: Optional[Mapping[str, str]]
) -> list:
    """Reject a ``PROVENANCE`` record that contradicts the compiler or the tree."""
    if provenance is None:
        return []
    issues = []
    reported = provenance.get("reported_commit")
    if reported != commit_hash:
        issues.append(
            f"sealed sysroot {PROVENANCE_NAME} reported_commit {reported or 'absent'} "
            f"is not the compiler commit-hash {commit_hash}"
        )
    seal_name = provenance.get("seal_name") or ""
    if not _seal_name_binds(seal_name, commit_hash):
        issues.append(
            f"sealed sysroot {PROVENANCE_NAME} seal_name {seal_name or 'absent'} "
            f"is not trust-<prefix of {commit_hash}>"
        )
    provenance_class = provenance.get("provenance_class")
    if provenance_class != CLEAN_PROVENANCE_CLASS:
        issues.append(
            f"sealed sysroot provenance_class is {provenance_class or 'absent'}; only "
            f"{CLEAN_PROVENANCE_CLASS} ties the commit-hash to the compiled source"
        )
    if "dirty_provenance_waived" in provenance:
        issues.append(f"sealed sysroot {PROVENANCE_NAME} waives dirty build provenance")
    if "artifact_driver_name" in provenance or "artifact_driver_sha256" in provenance:
        name = provenance.get("artifact_driver_name", "")
        if not name or "/" in name or name in {".", ".."}:
            issues.append(
                f"sealed sysroot {PROVENANCE_NAME} names no single compiler driver "
                "for its artifact_driver_sha256"
            )
        else:
            issue = _recorded_artifact_issue(
                sealed / "lib" / name,
                provenance.get("artifact_driver_sha256", ""),
                "compiler driver",
            )
            if issue is not None:
                issues.append(issue)
    for key in sorted(provenance):
        match = ARTIFACT_BIN_KEY_RE.fullmatch(key)
        if match is None:
            continue
        tool = match.group(1)
        issue = _recorded_artifact_issue(sealed / "bin" / tool, provenance[key], f"bin/{tool}")
        if issue is not None:
            issues.append(issue)
    return issues


def _glibc_detected() -> bool:
    try:
        if os.confstr("CS_GNU_LIBC_VERSION"):
            return True
    except (AttributeError, ValueError, OSError):
        pass
    return platform.libc_ver()[0] == "glibc"


def running_host_triple(
    system: Optional[str] = None,
    machine: Optional[str] = None,
    glibc: Optional[bool] = None,
) -> Optional[str]:
    """Map the running machine to a primary target triple, or ``None``.

    Only the primary targets are recognized. Any other platform, architecture
    (including x86_64 under Rosetta) or a non-glibc Linux yields ``None`` and
    fails host coherence.
    """
    system = sys.platform if system is None else system
    machine = platform.machine() if machine is None else machine
    if machine.lower() not in {"arm64", "aarch64"}:
        return None
    if system == "darwin":
        return "aarch64-apple-darwin"
    if system.startswith("linux"):
        glibc = _glibc_detected() if glibc is None else glibc
        return "aarch64-unknown-linux-gnu" if glibc else None
    return None


def _libstd(sealed: Path, target: str) -> Optional[Path]:
    """Return the first ``libstd-*`` for ``target``; an unreadable dir has none."""
    try:
        found = sorted((sealed / "lib" / "rustlib" / target / "lib").glob("libstd-*"))
    except OSError:
        return None
    return found[0] if found else None


def host_issues(
    sealed: Path,
    host: Optional[str],
    required_target: Optional[str],
    machine_host: Optional[str],
) -> list:
    """Require the reported host to be the required, running primary target."""
    issues = []
    required = required_target or machine_host
    if required is None:
        issues.append(
            "running machine is not a primary-target host "
            f"({', '.join(PRIMARY_TARGETS)}) and no required target was named"
        )
    else:
        if required not in PRIMARY_TARGETS:
            issues.append(
                f"required target {required} is not a repository primary target "
                f"({', '.join(PRIMARY_TARGETS)})"
            )
        if machine_host != required:
            issues.append(
                f"required target {required} is not the running machine host "
                f"{machine_host or 'unrecognized'}"
            )
    if not host:
        issues.append("Trust compiler did not report a host triple")
    elif required is not None and host != required:
        issues.append(f"Trust compiler host {host} does not equal the required target {required}")
    target = required or host
    if target and _libstd(sealed, target) is None:
        issues.append(f"sealed sysroot has no std artifact for {target}")
    return issues


def _dylib_suffixes(host: Optional[str]) -> tuple:
    if host and host.endswith("-apple-darwin"):
        return (".dylib",)
    if host and "-linux-" in host:
        return (".so",)
    return (".dylib", ".so")


def _entries(directory: Path) -> list:
    """List a directory; an unlistable one contributes nothing (never a pass)."""
    try:
        return sorted(directory.iterdir()) if directory.is_dir() else []
    except OSError:
        return []


def _probe(predicate: Callable[[], bool]) -> bool:
    """Evaluate a filesystem predicate; one that cannot be answered is false.

    Callers use this only where false is the fail-closed answer (an artifact
    that cannot be inspected is not counted as present).
    """
    try:
        return predicate()
    except OSError:
        return False


def cg_backend_expectation(sealed: Path, host: Optional[str]) -> dict:
    """Locate the CG backend expectation without judging it."""
    suffixes = _dylib_suffixes(host)
    backends_dir = None
    trust_backends: list = []
    search = [sealed / "lib"]
    if host:
        candidate = sealed / "lib" / "rustlib" / host / "codegen-backends"
        if _probe(lambda: candidate.is_dir() and not candidate.is_symlink()):
            backends_dir = candidate
            trust_backends = [
                os.fspath(path)
                for path in _entries(candidate)
                if path.name.startswith(TRUST_BACKEND_PREFIX)
                and path.suffix in suffixes
                and _probe(path.is_file)
            ]
        search.insert(0, sealed / "lib" / "rustlib" / host / "lib")
    bridge_dylibs: list = []
    for directory in search:
        bridge_dylibs.extend(
            os.fspath(path)
            for path in _entries(directory)
            if BRIDGE_DYLIB_RE.fullmatch(path.name)
            and path.suffix in suffixes
            and _probe(path.is_file)
        )
    return {
        "codegen_backends_dir": None if backends_dir is None else os.fspath(backends_dir),
        "trust_backends": trust_backends,
        "bridge_dylibs": bridge_dylibs,
        "satisfied": bool(trust_backends or bridge_dylibs),
    }


def resolved_issues(
    resolved: ResolvedToolchain,
    *,
    machine_host: Optional[str],
    required_target: Optional[str] = None,
    require_cg_backend: bool = False,
) -> list:
    """Judge the resolved compiler, sealed tree, host and CG expectation.

    The committed identity lock and the behavioral canaries are judged
    separately by ``installed_report``.
    """
    issues = []
    if resolved.model == "pack":
        if not _is_executable_file(resolved.rustc):
            issues.append("PATH did not resolve an executable Trust trustc")
        if not _is_executable_file(resolved.build_tool):
            issues.append("PATH did not resolve an executable Trust targo")
    elif resolved.model == "linked":
        if not _is_executable_file(resolved.rustc):
            issues.append("rustup did not resolve an executable Trust rustc")
        if resolved.rustup_link is None or not resolved.rustup_link.exists():
            issues.append("rustup Trust toolchain link is missing")
    else:
        issues.append(
            "no Trust compiler resolved: neither trustc/targo on PATH nor "
            f"rustup which --toolchain trust rustc ({resolved.note or 'no detail'})"
        )
    if resolved.sysroot is None or not resolved.sysroot.is_dir():
        issues.append("Trust compiler did not resolve an existing sysroot")
    if resolved.sealed_root is None or not resolved.sealed_root.is_dir():
        issues.append("TRUST_SEALED_SYSROOT does not name an existing directory")
    if resolved.commit_hash is None or COMMIT_HASH_RE.fullmatch(resolved.commit_hash) is None:
        issues.append("Trust compiler did not report a canonical 40-hex commit-hash")

    if issues:
        return issues

    assert resolved.rustc is not None
    assert resolved.sysroot is not None
    assert resolved.sealed_root is not None
    assert resolved.commit_hash is not None

    rustc = resolved.rustc.resolve()
    sysroot = resolved.sysroot.resolve()
    sealed = resolved.sealed_root.resolve()
    linked = None
    if resolved.rustup_link is not None and (
        resolved.rustup_link.exists() or resolved.rustup_link.is_symlink()
    ):
        linked = resolved.rustup_link.resolve()

    if resolved.binary != "trustc":
        issues.append(
            "Trust compiler is not the branded trustc driver: "
            f"binary {resolved.binary or 'unreported'}"
        )
    if MUTABLE_STAGE2_RE.search(os.fspath(sysroot)) or (
        linked is not None and MUTABLE_STAGE2_RE.search(os.fspath(linked))
    ):
        issues.append("Trust toolchain resolves into mutable build/host/stage2")
    if resolved.sealed_root.is_symlink():
        issues.append("TRUST_SEALED_SYSROOT itself must be a versioned directory, not a symlink")
    provenance, provenance_read_issues = read_provenance(sealed)
    issues.extend(provenance_read_issues)
    issues.extend(seal_binding(sealed, resolved.commit_hash, provenance)[1])
    issues.extend(provenance_issues(sealed, resolved.commit_hash, provenance))
    if sysroot != sealed:
        issues.append("compiler sysroot and TRUST_SEALED_SYSROOT do not resolve identically")

    if resolved.model == "pack":
        assert resolved.build_tool is not None
        build_tool = resolved.build_tool.resolve()
        if rustc.parent != build_tool.parent:
            issues.append("PATH trustc and targo must resolve to the same installed package")
        if rustc.parent.parent != sysroot:
            issues.append(
                "Trust compiler/sysroot package mismatch: PATH trustc is not the "
                f"bin/trustc of its reported sysroot ({rustc} vs {sysroot})"
            )
        if rustc != (sealed / "bin" / "trustc").resolve():
            issues.append("resolved trustc is not the compiler inside the sealed sysroot")
        if build_tool != (sealed / "bin" / "targo").resolve():
            issues.append("resolved targo is not the build tool inside the sealed sysroot")
        if linked is not None and linked != sealed:
            issues.append(
                "rustup trust toolchain diverges from the PATH Trust package: "
                f"{resolved.rustup_link} -> {linked}"
            )
    else:
        if linked != sealed:
            issues.append(
                "rustup link, compiler sysroot, and TRUST_SEALED_SYSROOT do not resolve identically"
            )
        if rustc != (sealed / "bin" / "rustc").resolve():
            issues.append("resolved rustc is not the compiler inside the sealed sysroot")

    # Walk only a tree the compiler actually uses; a mismatch already failed.
    if sysroot == sealed:
        issues.extend(_sealed_tree_issues(sealed))
    issues.extend(host_issues(sealed, resolved.host, required_target, machine_host))
    if require_cg_backend and not cg_backend_expectation(sealed, resolved.host)["satisfied"]:
        issues.append(
            "sealed sysroot ships no CG backend: no "
            f"{TRUST_BACKEND_PREFIX}* dylib in lib/rustlib/{resolved.host}/codegen-backends/ "
            "and no librustc_codegen_trust_cg bridge dylib"
        )
    return issues


def read_identity_lock(path: Path) -> tuple:
    """Return ``(entries by host, issues)``; any issue voids every entry."""
    if path.is_symlink():
        return {}, [f"Trust toolchain identity lock must not be a symlink: {path}"]
    if not path.exists():
        return {}, [
            f"no committed Trust toolchain identity lock ({path.name}); naming the "
            "qualified Trust build needs a sealed, atpkg-published package (ruling OD-01, "
            "docs/decision-record.md)"
        ]
    if not path.is_file():
        return {}, [f"Trust toolchain identity lock is not a regular file: {path}"]
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as error:
        return {}, [f"Trust toolchain identity lock is unreadable: {error}"]
    entries: dict = {}
    issues = []
    for number, raw in enumerate(text.splitlines(), start=1):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        match = IDENTITY_LINE_RE.fullmatch(line)
        if match is None:
            issues.append(
                f"{path.name}:{number}: expected identity = <host> <commit-hash> <tree-sha256>"
            )
            continue
        host, commit_hash, tree_sha256 = match.groups()
        if host not in PRIMARY_TARGETS:
            issues.append(f"{path.name}:{number}: {host} is not a repository primary target")
        if COMMIT_HASH_RE.fullmatch(commit_hash) is None:
            issues.append(f"{path.name}:{number}: commit-hash is not canonical 40-hex")
        if SHA256_RE.fullmatch(tree_sha256) is None:
            issues.append(f"{path.name}:{number}: sysroot tree digest is not 64-hex SHA-256")
        if host in entries:
            issues.append(f"{path.name}:{number}: {host} is pinned more than once")
        entries[host] = LockedIdentity(host, commit_hash, tree_sha256)
    if not entries and not issues:
        issues.append(f"Trust toolchain identity lock names no identity: {path}")
    return ({} if issues else entries), issues


def identity_lock_issues(
    lock_path: Path,
    host: Optional[str],
    commit_hash: Optional[str],
    tree_digest: Callable[[], Optional[str]],
) -> list:
    """Compare the reported identity and sealed tree digest with the lock."""
    entries, issues = read_identity_lock(lock_path)
    if issues:
        return issues
    entry = entries.get(host or "")
    if entry is None:
        return [f"Trust toolchain identity lock pins no identity for host {host or 'unreported'}"]
    if entry.commit_hash != commit_hash:
        issues.append(
            f"Trust compiler commit-hash {commit_hash or 'unreported'} is not the locked "
            f"{entry.commit_hash} for {entry.host}"
        )
    digest = tree_digest()
    if digest is None:
        issues.append(
            "sealed sysroot tree digest was not computed: the sealed tree is not the "
            "compiler sysroot or failed the immutability checks"
        )
    elif digest != entry.tree_sha256:
        issues.append(
            f"sealed sysroot tree digest {digest} is not the locked {entry.tree_sha256} "
            f"for {entry.host}"
        )
    return issues


def _sealed_tree_for_digest(resolved: ResolvedToolchain) -> Optional[Path]:
    """Return the sealed root only when it is the compiler's immutable sysroot."""
    if resolved.sealed_root is None or resolved.sysroot is None:
        return None
    if resolved.sealed_root.is_symlink() or not resolved.sealed_root.is_dir():
        return None
    sealed = resolved.sealed_root.resolve()
    if not resolved.sysroot.is_dir() or resolved.sysroot.resolve() != sealed:
        return None
    if _sealed_tree_issues(sealed):
        return None
    return sealed


def describe_installed(
    resolved: ResolvedToolchain,
    machine_host: Optional[str],
    required_target: Optional[str],
    lock_path: Path,
) -> dict:
    """Diagnostic fields for ``--inspect``; every value is JSON-serializable."""

    def text(path: Optional[Path]) -> Optional[str]:
        return None if path is None else os.fspath(path)

    sealed = resolved.sealed_root
    binding = None
    provenance_summary = None
    libstd = None
    expectation = None
    if sealed is not None and sealed.is_dir():
        expectation = cg_backend_expectation(sealed, resolved.host)
        resolved_sealed = sealed.resolve()
        provenance, _ = read_provenance(resolved_sealed)
        if provenance is not None:
            provenance_summary = {
                key: provenance.get(key)
                for key in ("provenance_class", "seal_name", "reported_commit", "sealed_at")
            }
        if resolved.commit_hash and COMMIT_HASH_RE.fullmatch(resolved.commit_hash):
            binding = seal_binding(resolved_sealed, resolved.commit_hash, provenance)[0]
        target = required_target or machine_host or resolved.host
        if target:
            libstd = _libstd(resolved_sealed, target)
    link = None
    if resolved.rustup_link is not None:
        link = {
            "path": text(resolved.rustup_link),
            "resolves_to": text(resolved.rustup_link.resolve())
            if resolved.rustup_link.exists()
            else None,
        }
    entries, lock_issues = read_identity_lock(lock_path)
    locked = entries.get(resolved.host or "")
    return {
        "model": resolved.model,
        "resolution_note": resolved.note,
        "compiler": text(resolved.rustc),
        "build_tool": text(resolved.build_tool),
        "binary": resolved.binary,
        "commit_hash": resolved.commit_hash,
        "host": resolved.host,
        "required_target": required_target or machine_host,
        "machine_host": machine_host,
        "primary_targets": list(PRIMARY_TARGETS),
        "sysroot": text(resolved.sysroot),
        "rustup_link": link,
        "sealed_root": text(sealed),
        "seal_binding": binding,
        "provenance": provenance_summary,
        "libstd": text(libstd),
        "cg_backend": expectation,
        "identity_lock": {
            "path": os.fspath(lock_path),
            "issues": lock_issues,
            "locked_commit_hash": None if locked is None else locked.commit_hash,
            "locked_tree_sha256": None if locked is None else locked.tree_sha256,
        },
    }


def behavioral_issues(rustc: Path, environment: Optional[Mapping[str, str]] = None) -> list:
    """Prove the installed compiler's no-flag defaults with red/green crates."""
    positive = "pub fn identity(x: u64) -> u64 { x }\n"
    refutation = "pub fn divide(x: i32, y: i32) -> i32 { x / y }\n"
    results = {}
    env = None if environment is None else dict(environment)
    with tempfile.TemporaryDirectory(prefix="trust-default-authority-") as temporary:
        directory = Path(temporary)
        for name, source in (("positive", positive), ("refutation", refutation)):
            source_path = directory / f"{name}.rs"
            source_path.write_text(source, encoding="utf-8")
            command = [
                os.fspath(rustc),
                "--crate-name",
                f"trust_default_{name}",
                "--crate-type",
                "lib",
                "--edition=2021",
                "--emit",
                "metadata",
                "-o",
                os.fspath(directory / f"{name}.rmeta"),
                os.fspath(source_path),
            ]
            try:
                results[name] = subprocess.run(
                    command,
                    cwd=os.fspath(directory),
                    env=env,
                    check=False,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    timeout=60,
                )
            except subprocess.TimeoutExpired:
                return [f"Trust compiler behavioral {name} canary timed out"]
            except OSError as error:
                return [f"Trust compiler behavioral {name} canary could not run: {error}"]

    positive_result = results["positive"]
    negative_result = results["refutation"]
    issues = []
    if positive_result.returncode != 0:
        issues.append("Trust compiler rejected the trivial positive default canary")
    evidence = negative_result.stdout + negative_result.stderr
    refutation_evidence = re.search(r'\b[1-9][0-9]* failed\b|\bFAILED\b|counterexample', evidence)
    if negative_result.returncode == 0:
        issues.append("Trust compiler accepted the deliberate default refutation")
    if "Trust verification:" not in evidence or refutation_evidence is None:
        issues.append("deliberate refutation lacked Trust verification failure evidence")
    return issues


def _run(command: Sequence[str], cwd: Path, environment: Optional[Mapping[str, str]] = None) -> str:
    try:
        completed = subprocess.run(
            command,
            cwd=os.fspath(cwd),
            env=None if environment is None else dict(environment),
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise RuntimeError(f"{' '.join(command)} could not run: {error}") from error
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        raise RuntimeError(f"{' '.join(command)} failed: {detail}")
    return completed.stdout.strip()


def _resolved_tool(found: Optional[str]) -> Optional[Path]:
    if found is None:
        return None
    try:
        return Path(found).resolve(strict=True)
    except OSError:
        return Path(found)


def _identity_probe_environment(environment: Optional[Mapping[str, str]]) -> dict:
    """The probe environment for identity questions (``-Vv``, ``--print sysroot``).

    trustc refuses to run at all, even ``-Vv``, under any TRUST_CG_*/TCG_*
    control; a gate may export those for its test binaries. They do not change
    what the compiler is, so identity probes run without them. Behavioral
    canaries keep the caller's environment.
    """
    return without_untracked_controls(os.environ if environment is None else environment)


def _compiler_identity(
    compiler: Path, cwd: Path, environment: Optional[Mapping[str, str]]
) -> dict:
    identity: dict = {"sysroot": None, "host": None, "commit_hash": None, "binary": None}
    environment = _identity_probe_environment(environment)
    try:
        identity["sysroot"] = _run([os.fspath(compiler), "--print", "sysroot"], cwd, environment)
        verbose = _run([os.fspath(compiler), "-Vv"], cwd, environment)
    except RuntimeError:
        return identity
    for line in verbose.splitlines():
        for key, prefix in (
            ("host", "host: "),
            ("commit_hash", "commit-hash: "),
            ("binary", "binary: "),
        ):
            if line.startswith(prefix):
                identity[key] = line[len(prefix) :].strip()
    return identity


def resolve_installed(
    root: Path, environment: Optional[Mapping[str, str]] = None
) -> ResolvedToolchain:
    """Resolve the installed Trust toolchain by the pack model, then rustup.

    ``environment`` supplies ``PATH``, ``RUSTUP_HOME`` and
    ``TRUST_SEALED_SYSROOT`` and is the environment every probe runs in; it
    defaults to the process environment. An empty ``PATH`` resolves nothing.
    """
    env = os.environ if environment is None else environment
    path_value = env.get("PATH", "")
    rustup_home = Path(env.get("RUSTUP_HOME") or (Path.home() / ".rustup"))
    link = rustup_home / "toolchains" / "trust"
    present_link = link if (link.exists() or link.is_symlink()) else None
    sealed_value = env.get("TRUST_SEALED_SYSROOT")
    sealed_root = Path(sealed_value) if sealed_value else None

    tools = {name: shutil.which(name, path=path_value) for name in PACK_TOOLS}
    if any(tools.values()):
        compiler = _resolved_tool(tools["trustc"])
        identity = _compiler_identity(compiler, root, env) if compiler is not None else {}
        sysroot = identity.get("sysroot")
        return ResolvedToolchain(
            rustc=compiler,
            sysroot=Path(sysroot) if sysroot else None,
            rustup_link=present_link,
            sealed_root=sealed_root,
            host=identity.get("host"),
            commit_hash=identity.get("commit_hash"),
            model="pack",
            build_tool=_resolved_tool(tools["targo"]),
            binary=identity.get("binary"),
        )

    rustup = shutil.which("rustup", path=path_value)
    if rustup is None:
        return ResolvedToolchain(
            None, None, present_link, sealed_root, None, None, model=None,
            note="rustup is not on PATH",
        )
    try:
        rustc = Path(_run([rustup, "which", "--toolchain", "trust", "rustc"], root, env))
    except RuntimeError as error:
        return ResolvedToolchain(
            None, None, present_link, sealed_root, None, None, model=None, note=str(error)
        )
    identity = _compiler_identity(rustc, root, env)
    sysroot = identity.get("sysroot")
    return ResolvedToolchain(
        rustc=rustc,
        sysroot=Path(sysroot) if sysroot else None,
        rustup_link=link,
        sealed_root=sealed_root,
        host=identity.get("host"),
        commit_hash=identity.get("commit_hash"),
        model="linked",
        binary=identity.get("binary"),
    )


def installed_report(
    root: Path,
    environment: Mapping[str, str],
    *,
    machine_host: Optional[str],
    required_target: Optional[str],
    require_cg_backend: bool,
    inspect: bool,
) -> tuple:
    """Resolve, judge and describe the installed toolchain.

    The behavioral canaries run only when every identity check and the
    committed lock pass, or under ``inspect`` whenever a compiler resolved.
    """
    resolved = resolve_installed(root, environment)
    lock_path = root / IDENTITY_LOCK_NAME
    issues = resolved_issues(
        resolved,
        machine_host=machine_host,
        required_target=required_target,
        require_cg_backend=require_cg_backend,
    )
    digest_cache: dict = {}

    def tree_digest() -> Optional[str]:
        if "value" not in digest_cache:
            sealed = _sealed_tree_for_digest(resolved)
            try:
                digest_cache["value"] = None if sealed is None else sysroot_tree_digest(sealed)
            except OSError:
                digest_cache["value"] = None
        return digest_cache["value"]

    issues.extend(
        identity_lock_issues(lock_path, resolved.host, resolved.commit_hash, tree_digest)
    )
    diagnostics = describe_installed(resolved, machine_host, required_target, lock_path)
    if inspect:
        diagnostics["sysroot_tree_sha256"] = tree_digest()
    diagnostics["behavioral_canaries"] = "not run"
    if _is_executable_file(resolved.rustc) and (not issues or inspect):
        assert resolved.rustc is not None
        behavioral = behavioral_issues(resolved.rustc, environment)
        diagnostics["behavioral_canaries"] = behavioral or "pass"
        issues.extend(behavioral)
    return diagnostics, issues


def evaluate(
    root: Path,
    require_verified_default: bool,
    inspect: bool = False,
    environment: Optional[Mapping[str, str]] = None,
    machine_host: object = DETECT,
    required_target: Optional[str] = None,
) -> Report:
    env = dict(os.environ if environment is None else environment)
    host = running_host_triple() if isinstance(machine_host, _Detect) else machine_host
    toolchain_path = root / "rust-toolchain.toml"
    config_paths = (root / ".cargo" / "config.toml", root / ".cargo" / "config")
    structural_issues = []
    if toolchain_path.is_symlink():
        structural_issues.append("rust-toolchain.toml must not be a symlink")
    existing_configs = [path for path in config_paths if path.exists() or path.is_symlink()]
    if len(existing_configs) > 1:
        structural_issues.append(
            "both .cargo/config.toml and legacy .cargo/config exist; precedence is ambiguous"
        )
    if any(path.is_symlink() for path in existing_configs):
        structural_issues.append("verified Cargo configuration must not be a symlink")
    toolchain_text = toolchain_path.read_text(encoding="utf-8") if toolchain_path.exists() else ""
    config_text = "\n".join(
        path.read_text(encoding="utf-8") for path in existing_configs if path.is_file()
    )
    channel = toolchain_channel(toolchain_text)
    options = {
        "machine_host": host,
        "required_target": required_target,
        "require_cg_backend": require_verified_default,
        "inspect": inspect,
    }
    if channel != "trust":
        issues = (
            [f"verified default required, but repository channel is {channel or 'unpinned'}"]
            if require_verified_default
            else []
        )
        if not (require_verified_default or inspect):
            return Report(issues, [], None)
        diagnostics, installed = installed_report(root, env, **options)
        shown = diagnostics if inspect else None
        if require_verified_default:
            return Report(issues + installed, [], shown)
        return Report([], installed, shown)

    if not configures_trust_flags(config_text) and not require_verified_default:
        # A Trust toolchain selection: no configuration text claims authority,
        # so the verified-default contract is diagnostic here, as on a stock
        # channel, while the selected package itself must be coherent.
        issues = structural_issues + selection_config_issues(config_text, env)
        selection, package_issues = selected_package(root, env)
        issues += package_issues
        if not inspect:
            return Report(issues, [], None, selection)
        diagnostics, installed = installed_report(root, env, **options)
        return Report(issues, installed, diagnostics, selection)

    issues = structural_issues + policy_issues(toolchain_text, config_text, env)
    if issues and not inspect:
        return Report(issues, [], None)
    diagnostics, installed = installed_report(root, env, **options)
    return Report(issues + installed, [], diagnostics if inspect else None)


def check(
    root: Path,
    require_verified_default: bool,
    inspect: bool = False,
    environment: Optional[Mapping[str, str]] = None,
    machine_host: object = DETECT,
    required_target: Optional[str] = None,
) -> list:
    return evaluate(
        root, require_verified_default, inspect, environment, machine_host, required_target
    ).issues


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--require-verified-default", action="store_true")
    parser.add_argument(
        "--inspect",
        action="store_true",
        help="print installed Trust toolchain diagnostics regardless of the repository channel",
    )
    parser.add_argument(
        "--required-target",
        choices=PRIMARY_TARGETS,
        default=None,
        help="primary target the installed Trust host must equal (default: the running machine)",
    )
    args = parser.parse_args(argv)
    report = evaluate(
        args.root.resolve(),
        args.require_verified_default,
        inspect=args.inspect,
        required_target=args.required_target,
    )
    if report.diagnostics is not None:
        print("INSPECT: installed Trust toolchain diagnostics")
        print(json.dumps(report.diagnostics, indent=2, sort_keys=True))
    for note in report.informational:
        print(f"INFO: installed Trust toolchain would not qualify: {note}")
    if report.issues:
        for issue in report.issues:
            print(f"FAIL: {issue}", file=sys.stderr)
        return 1
    if report.selection is not None:
        print(
            "INFO: repository selects the Trust toolchain "
            f"{report.selection['commit_hash']} ({report.selection['compiler']}); "
            "targo chooses each invocation's lane and no verified-default claim is made"
        )
    print("PASS: repository default makes no uncertified Trust authority claim")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
