#!/usr/bin/env python3
"""Fail-closed preflight for any future Trust-verified repository default.

An upstream toolchain is an honest, unverified default and passes unless
``--require-verified-default`` is requested. A ``channel = "trust"`` claim is
accepted only when its policy is strict, no unit is switched off, and rustup
resolves to one explicitly named, read-only sysroot rather than an x.py build
tree. This checker does not turn verification on; it prevents configuration
text from claiming authority that the installed toolchain cannot supply.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Optional, Sequence


CHANNEL_RE = re.compile(r'^\s*channel\s*=\s*["\']([^"\']+)["\']\s*$', re.MULTILINE)
MUTABLE_STAGE2_RE = re.compile(r'(?:^|/)build/host/stage2(?:/|$)')
COMMIT_HASH_RE = re.compile(r'^[0-9a-f]{40}$')
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


@dataclass(frozen=True)
class ResolvedToolchain:
    rustc: Optional[Path]
    sysroot: Optional[Path]
    rustup_link: Optional[Path]
    sealed_root: Optional[Path]
    host: Optional[str]
    commit_hash: Optional[str]


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


def _canonical_trust_flags(values: Iterable[str]) -> Iterable[str]:
    tokens = []
    for value in values:
        tokens.extend(value.replace("\x1f", " ").split())
    index = 0
    while index < len(tokens):
        token = tokens[index]
        if token == "-Z" and index + 1 < len(tokens):
            value = tokens[index + 1]
            if value.startswith("trust-"):
                yield f"-Z{value}"
                index += 2
                continue
        if token.startswith("-Ztrust-"):
            yield token
        index += 1


def configured_flags(config_text: str) -> Iterable[str]:
    """Yield canonical Trust flags from all decoded Cargo string values."""
    strings, _, _ = _toml_strings_and_normalized(config_text)
    yield from _canonical_trust_flags(strings)


def policy_issues(
    toolchain_text: str,
    config_text: str,
    environment: Optional[dict[str, str]] = None,
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
        flag_values = [
            value
            for key, value in environment.items()
            if value
            and (
                key in {"RUSTFLAGS", "RUSTDOCFLAGS", "CARGO_ENCODED_RUSTFLAGS"}
                or (key.startswith("CARGO_") and key.endswith(("_RUSTFLAGS", "_RUSTDOCFLAGS")))
            )
        ]
        if list(_canonical_trust_flags(flag_values)):
            issues.append("verified default cannot inherit ambient Trust compiler flags")
    return issues


def _is_read_only(path: Path) -> bool:
    write_bits = stat.S_IWUSR | stat.S_IWGRP | stat.S_IWOTH
    return path.exists() and path.stat().st_mode & write_bits == 0


def _sealed_tree_issues(root: Path) -> list[str]:
    """Reject one mutable or symlinked artifact anywhere below ``root``."""
    issues = []
    if not _is_read_only(root):
        issues.append("sealed sysroot root retains write bits")

    first_symlink = None
    first_writable = None
    for directory, dirnames, filenames in os.walk(root, followlinks=False):
        parent = Path(directory)
        for name in list(dirnames):
            candidate = parent / name
            if candidate.is_symlink():
                first_symlink = first_symlink or candidate
                dirnames.remove(name)
            elif not _is_read_only(candidate):
                first_writable = first_writable or candidate
        for name in filenames:
            candidate = parent / name
            if candidate.is_symlink():
                first_symlink = first_symlink or candidate
            elif not _is_read_only(candidate):
                first_writable = first_writable or candidate
    if first_symlink is not None:
        issues.append(f"sealed sysroot contains a symlinked artifact: {first_symlink}")
    if first_writable is not None:
        issues.append(f"sealed sysroot contains a writable artifact: {first_writable}")
    return issues


def resolved_issues(resolved: ResolvedToolchain) -> list[str]:
    issues = []
    if resolved.rustc is None or not resolved.rustc.is_file() or not os.access(resolved.rustc, os.X_OK):
        issues.append("rustup did not resolve an executable Trust rustc")
    if resolved.sysroot is None or not resolved.sysroot.is_dir():
        issues.append("Trust rustc did not resolve an existing sysroot")
    if resolved.rustup_link is None or not resolved.rustup_link.exists():
        issues.append("rustup Trust toolchain link is missing")
    if resolved.sealed_root is None or not resolved.sealed_root.is_dir():
        issues.append("TRUST_SEALED_SYSROOT does not name an existing directory")
    if resolved.commit_hash is None or COMMIT_HASH_RE.fullmatch(resolved.commit_hash) is None:
        issues.append("Trust rustc did not report a canonical 40-hex commit-hash")

    if issues:
        return issues

    assert resolved.rustc is not None
    assert resolved.sysroot is not None
    assert resolved.rustup_link is not None
    assert resolved.sealed_root is not None
    assert resolved.commit_hash is not None

    rustc = resolved.rustc.resolve()
    sysroot = resolved.sysroot.resolve()
    linked = resolved.rustup_link.resolve()
    sealed = resolved.sealed_root.resolve()

    if MUTABLE_STAGE2_RE.search(os.fspath(linked)) or MUTABLE_STAGE2_RE.search(os.fspath(sysroot)):
        issues.append("Trust toolchain resolves into mutable build/host/stage2")
    if resolved.sealed_root.is_symlink():
        issues.append("TRUST_SEALED_SYSROOT itself must be a versioned directory, not a symlink")
    expected_name = f"trust-{resolved.commit_hash}"
    if sealed.name != expected_name:
        issues.append(
            f"sealed sysroot directory must be named {expected_name}, got {sealed.name}"
        )
    if linked != sealed or sysroot != sealed:
        issues.append("rustup link, rustc sysroot, and TRUST_SEALED_SYSROOT do not resolve identically")
    if rustc != (sealed / "bin" / "rustc").resolve():
        issues.append("resolved rustc is not the compiler inside the sealed sysroot")
    issues.extend(_sealed_tree_issues(sealed))
    if not resolved.host:
        issues.append("Trust rustc did not report a host triple")
    elif not any((sealed / "lib" / "rustlib" / resolved.host / "lib").glob("libstd-*")):
        issues.append("sealed sysroot has no std artifact for the reported host")
    return issues


def behavioral_issues(rustc: Path) -> list[str]:
    """Prove the installed compiler's no-flag defaults with red/green crates."""
    positive = "pub fn identity(x: u64) -> u64 { x }\n"
    refutation = "pub fn divide(x: i32, y: i32) -> i32 { x / y }\n"
    results = {}
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
                    check=False,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    timeout=60,
                )
            except subprocess.TimeoutExpired:
                return [f"Trust compiler behavioral {name} canary timed out"]

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


def _run(command: Sequence[str], cwd: Path) -> str:
    completed = subprocess.run(
        command,
        cwd=os.fspath(cwd),
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        raise RuntimeError(f"{' '.join(command)} failed: {detail}")
    return completed.stdout.strip()


def resolve_installed(root: Path) -> ResolvedToolchain:
    rustup = shutil.which("rustup")
    if rustup is None:
        return ResolvedToolchain(None, None, None, None, None, None)
    try:
        rustc = Path(_run([rustup, "which", "--toolchain", "trust", "rustc"], root))
        sysroot = Path(_run([os.fspath(rustc), "--print", "sysroot"], root))
        verbose = _run([os.fspath(rustc), "-Vv"], root)
    except RuntimeError:
        return ResolvedToolchain(None, None, None, None, None, None)

    host = None
    commit_hash = None
    for line in verbose.splitlines():
        if line.startswith("host: "):
            host = line[len("host: ") :].strip()
        elif line.startswith("commit-hash: "):
            commit_hash = line[len("commit-hash: ") :].strip()
    rustup_home = Path(os.environ.get("RUSTUP_HOME", os.fspath(Path.home() / ".rustup")))
    sealed = os.environ.get("TRUST_SEALED_SYSROOT")
    return ResolvedToolchain(
        rustc=rustc,
        sysroot=sysroot,
        rustup_link=rustup_home / "toolchains" / "trust",
        sealed_root=Path(sealed) if sealed else None,
        host=host,
        commit_hash=commit_hash,
    )


def check(root: Path, require_verified_default: bool) -> list[str]:
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
    if channel != "trust":
        if require_verified_default:
            return [f"verified default required, but repository channel is {channel or 'unpinned'}"]
        return []
    issues = structural_issues + policy_issues(toolchain_text, config_text, dict(os.environ))
    if issues:
        return issues
    resolved = resolve_installed(root)
    issues = resolved_issues(resolved)
    if issues:
        return issues
    assert resolved.rustc is not None
    return behavioral_issues(resolved.rustc)


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--require-verified-default", action="store_true")
    args = parser.parse_args(argv)
    issues = check(args.root.resolve(), args.require_verified_default)
    if issues:
        for issue in issues:
            print(f"FAIL: {issue}", file=sys.stderr)
        return 1
    print("PASS: repository default makes no uncertified Trust authority claim")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
