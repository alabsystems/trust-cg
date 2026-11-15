#!/usr/bin/env python3
"""Assemble a local Trust overlay toolchain: an installed pack plus a newer AY and Clean.

    scripts/assemble_trust_overlay.py \\
        --pack "$HOME/Library/Application Support/aterm/pkg/store/trust/9192" \\
        --ay <ay-checkout>/target/release/ay --ay-src <ay-checkout> \\
        --clean <clean-checkout>/target/release/clean --clean-src <clean-checkout> \\
        --out "$HOME/.local/share/trust-overlays/<name>"

The overlay is a copy-on-write clone of the pack (APFS `clonefile` on macOS,
`cp --reflink=auto` on Linux) whose `bin/ay` and `bin/clean` are replaced by
the given binaries, plus `overlay.json`, a manifest naming both digests and
their source commits. It is NOT a published pack: the package manager neither
installs nor attests it, and the pack's `trustc` still bundles the pack's own
AY libraries. Point `TRUST_TARGO` at its `bin/targo` for
`scripts/trust_cargo.sh`; trust-cg-verify's `build.rs` then records the
overlay's AY, binds the overlay's Clean digest, and names the manifest in
verdict provenance.

`--pack` may also be a WRAPPER SYSROOT (`--pack-kind wrapper-sysroot`): a
sysroot with `lib/rustlib` and no `targo`, whose `bin/trustc` is a shell
wrapper that runs another `trustc` with `--sysroot` hard-coded to the sysroot
itself in one `sysroot=` assignment. The x86_64 Darwin rustc bridge is built
against such a sysroot (`RUSTC=<sysroot>/bin/trustc`, driven by another
`targo`), because the published pack there has no `rustc-dev`. The overlay
rewrites that one assignment to name the overlay, so `$RUSTC --print sysroot`
(what trust-cg-verify's `build.rs` records) is the overlay; the manifest
records the wrapper's digest before and after, and the compiler it runs is
the one `-vV` reports. Use the overlay with `RUSTC=<overlay>/bin/trustc`.

Refusals (exit 2, nothing is left at `--out`):

* `--out` already exists, or an input is a symlink or not an executable file;
* the pack has no `bin/trustc`, `bin/targo` or `lib/rustlib` (a wrapper
  sysroot: no `bin/trustc` or `lib/rustlib`);
* a wrapper sysroot's `bin/trustc` is a symlink or not UTF-8 text, has no or
  several `sysroot=` assignments, assigns another directory, or names the
  sysroot's path anywhere else (the rewritten wrapper would still reach the
  original);
* the AY banner is not a numbered, clean build of `--ay-src`'s HEAD: the
  banner is parsed with the rules of `ay_identity_banner.rs`, and its
  `build.increment` must be non-zero and equal `git rev-list --count HEAD`
  (a `git archive` export reports build 0, commit `unknown`);
* either source checkout has tracked modifications, or lacks a commit named
  by `--require-ay-ancestor` / `--require-clean-ancestor`;
* the Clean binary does not fully verify the known-good control proof that
  trust-cg's checker probe uses (for example it was built without the
  `carcara-verify` feature). trust-cg never falls back from an overlay's
  Clean to another checker, so such an overlay could verify nothing;
* the assembled `bin/trustc --print sysroot` does not name the overlay.

What the manifest does not establish: `clean --version` reports no commit, so
the Clean `source.commit` is the checkout HEAD the assembler was given
(`binding` says so); both binaries are built unverified; and nothing here is
signed yet (`signatures` is empty and reserved for that).
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shlex
import shutil
import subprocess
import sys
import tempfile

SCHEMA = "trust-cg.trust-overlay.v1"
MANIFEST = "overlay.json"
PROBE_TIMEOUT_SECONDS = 120

# `--pack-kind`: an installed pack (with its own targo), or a wrapper sysroot.
PACK_KIND_INSTALLED = "installed"
PACK_KIND_WRAPPER = "wrapper-sysroot"

# A wrapper sysroot's one hard-coded sysroot assignment, optionally quoted.
WRAPPER_SYSROOT_ASSIGNMENT = re.compile(r"""^sysroot=(?P<quote>['"]?)(?P<path>[^'"\n]*)(?P=quote)[ \t]*$""")

# The control pair of trust-cg-verify's checker probe
# (obligation_cert_store.rs CHECKER_PROBE_SMT2 / CHECKER_PROBE_ALETHE).
CONTROL_SMT2 = "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n"
CONTROL_ALETHE = "(assume t0 p)\n(assume t1 (not p))\n(step t2 (cl) :rule resolution :premises (t1 t0))\n"

README = """This directory is a LOCAL OVERLAY toolchain, not a published Trust pack.

It is a copy-on-write clone of the installed pack named in overlay.json, whose
bin/ay and bin/clean were replaced by locally built binaries (from a wrapper
sysroot, bin/trustc's one `sysroot=` assignment was also rewritten to name
this directory). The package manager does not install, update or attest it. overlay.json names both
binaries' SHA-256 digests and source commits; trust-cg-verify's build.rs
refuses the overlay if either file no longer matches it.

Assembled by trust-cg scripts/assemble_trust_overlay.py.
"""


class Refusal(Exception):
    """A named reason the overlay was not assembled."""


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def scrubbed_env() -> dict[str, str]:
    """trustc refuses to run while TRUST_CG_/TCG_ variables are set."""
    env = {
        key: value
        for key, value in os.environ.items()
        if not key.startswith(("TRUST_CG_", "TCG_")) and key != "RUSTUP_TOOLCHAIN"
    }
    return env


def run(command: list[str], *, cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            command,
            cwd=cwd,
            env=scrubbed_env(),
            stdin=subprocess.DEVNULL,
            capture_output=True,
            text=True,
            timeout=PROBE_TIMEOUT_SECONDS,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise Refusal(f"`{' '.join(command)}` could not run: {error}") from error


def git(checkout: Path, *arguments: str) -> str:
    result = run(["git", "-C", str(checkout), *arguments])
    if result.returncode != 0:
        raise Refusal(
            f"`git -C {checkout} {' '.join(arguments)}` failed: {result.stderr.strip()}"
        )
    return result.stdout.strip()


# --- AY banner: the rules of crates/trust-cg-verify/src/ay_identity_banner.rs ---

HEX40 = re.compile(r"[0-9a-f]{40}")
PLAIN = re.compile(r"[A-Za-z0-9._+-]+")


def parse_ay_banner(text: str) -> dict[str, str]:
    fields: dict[str, str] = {}
    for line in text.splitlines():
        line = line.strip()
        for name in ("build.version", "build.increment", "build.commit", "build.stamp"):
            prefix = name + "="
            if line.startswith(prefix):
                if name in fields:
                    raise Refusal(f"AY banner: `{prefix}` occurs more than once")
                fields[name] = line[len(prefix):]
    for name in ("build.version", "build.increment", "build.commit", "build.stamp"):
        if name not in fields:
            raise Refusal(f"AY banner: no `{name}=` line (not an AY build banner)")
    version = fields["build.version"]
    increment = fields["build.increment"]
    commit = fields["build.commit"]
    if "dirty" in commit:
        raise Refusal(f"AY banner: build.commit={commit} is a DIRTY build")
    if not HEX40.fullmatch(commit):
        raise Refusal(
            f"AY banner: build.commit={commit!r} is not a 40-character lowercase hex commit "
            "(a `git archive` export reports `unknown`)"
        )
    if not PLAIN.fullmatch(version):
        raise Refusal(f"AY banner: build.version={version!r} is malformed")
    if not increment.isdigit() or not increment.isascii():
        raise Refusal(f"AY banner: build.increment={increment!r} is not a decimal build number")
    if int(increment) == 0:
        raise Refusal(
            "AY banner: build.increment=0 is an unnumbered build (built without git history, "
            "e.g. from a `git archive` export); build AY from a real git checkout"
        )
    expected = f"{version}+build.{increment}.{commit}@"
    if not fields["build.stamp"].startswith(expected):
        raise Refusal(
            f"AY banner: build.stamp={fields['build.stamp']!r} disagrees with "
            f"version/increment/commit (expected prefix {expected!r})"
        )
    return {"version": version, "increment": increment, "commit": commit}


# --- inputs ---


def executable_input(path: Path, role: str) -> Path:
    if path.is_symlink():
        raise Refusal(f"--{role} {path} is a symlink; name the built file itself")
    if not path.is_file():
        raise Refusal(f"--{role} {path} is not a file")
    if not os.access(path, os.X_OK):
        raise Refusal(f"--{role} {path} is not executable")
    return path.resolve()


def source_checkout(checkout: Path, role: str, required: list[str]) -> dict[str, object]:
    if not checkout.is_dir():
        raise Refusal(f"--{role}-src {checkout} is not a directory")
    head = git(checkout, "rev-parse", "HEAD")
    if git(checkout, "status", "--porcelain", "--untracked-files=no"):
        raise Refusal(f"--{role}-src {checkout} has tracked modifications; a dirty tree has no source identity")
    ancestors = []
    for revision in required:
        resolved = run(["git", "-C", str(checkout), "rev-parse", "--verify", "--quiet", f"{revision}^{{commit}}"])
        if resolved.returncode != 0:
            raise Refusal(f"--{role}-src HEAD {head} does not contain required commit {revision} (unknown here)")
        full = resolved.stdout.strip()
        result = run(["git", "-C", str(checkout), "merge-base", "--is-ancestor", full, head])
        if result.returncode != 0:
            raise Refusal(f"--{role}-src HEAD {head} does not contain required commit {full}")
        ancestors.append(full)
    return {
        "checkout": str(checkout.resolve()),
        "commit": head,
        "rev_list_count": int(git(checkout, "rev-list", "--count", head)),
        "tracked_tree_clean": True,
        "required_ancestors": ancestors,
    }


def ay_identity(ay: Path, checkout: Path, required: list[str]) -> dict[str, object]:
    result = run([str(ay), "--version"])
    if result.returncode != 0:
        raise Refusal(f"`{ay} --version` exited {result.returncode}: {result.stderr.strip()}")
    banner = parse_ay_banner(result.stdout + "\n" + result.stderr)
    source = source_checkout(checkout, "ay", required)
    if banner["commit"] != source["commit"]:
        raise Refusal(
            f"AY banner commit {banner['commit']} is not --ay-src HEAD {source['commit']}"
        )
    if int(banner["increment"]) != source["rev_list_count"]:
        raise Refusal(
            f"AY banner build {banner['increment']} is not `git rev-list --count` "
            f"{source['rev_list_count']} of {source['commit']}"
        )
    return {
        "path": "bin/ay",
        "sha256": sha256_file(ay),
        "version": banner["version"],
        "increment": banner["increment"],
        "commit": banner["commit"],
        "banner": [line for line in result.stdout.splitlines() if line.strip()],
        "source": {**source, "binding": "banner build.commit and build.increment, checked against the checkout"},
    }


def clean_alethe_fully_verified(stdout: str) -> bool:
    """obligation_cert_store.rs clean_alethe_stdout_is_fully_verified."""
    lines = [line.strip().lower() for line in stdout.splitlines()]
    return (
        "external certificate verification: passed" in lines
        and "type: alethe smt proof" in lines
        and "proof status: fully verified" in lines
        and not any("failed" in line or "holey" in line or "incomplete" in line for line in lines)
    )


def clean_control_probe(clean: Path) -> str:
    with tempfile.TemporaryDirectory(prefix="trust-overlay-probe-") as scratch:
        cert = Path(scratch) / "cert.json"
        cert.write_text(
            json.dumps(
                {
                    "type": "alethe_certificate",
                    "version": "1.0",
                    "problem": CONTROL_SMT2,
                    "proof": CONTROL_ALETHE,
                }
            )
        )
        result = run([str(clean), "cert", "verify-external", str(cert), "--verbose"])
    if result.returncode == 0 and clean_alethe_fully_verified(result.stdout):
        return "fully verified"
    transcript = " | ".join(
        line.strip() for line in (result.stdout + "\n" + result.stderr).splitlines() if line.strip()
    )[:400]
    hint = (
        " (built WITHOUT the carcara-verify feature)"
        if "carcara-verify feature required" in transcript
        else ""
    )
    raise Refusal(
        f"{clean} did not fully verify trust-cg's control proof{hint}; trust-cg would refuse "
        f"this overlay's checker (exit {result.returncode}: {transcript or '<no output>'})"
    )


def clean_identity(clean: Path, checkout: Path, required: list[str]) -> dict[str, object]:
    version = run([str(clean), "--version"])
    probe = clean_control_probe(clean)
    source = source_checkout(checkout, "clean", required)
    embedded = source["commit"].encode() in clean.read_bytes()
    return {
        "path": "bin/clean",
        "sha256": sha256_file(clean),
        "version_output": (version.stdout + version.stderr).strip(),
        "control_probe": probe,
        "source": {
            **source,
            "binding": (
                "commit string embedded in the binary"
                if embedded
                else "asserted: --clean-src HEAD at assembly time (clean --version reports no commit)"
            ),
        },
    }


# --- assembly ---


def clone_tree(source: Path, destination: Path) -> str:
    system = platform.system()
    if system == "Darwin":
        command = ["cp", "-c", "-R", str(source), str(destination)]
        method = "apfs-clonefile"
    elif system == "Linux":
        command = ["cp", "-a", "--reflink=auto", str(source), str(destination)]
        method = "reflink-auto"
    else:
        shutil.copytree(source, destination, symlinks=True)
        return "copy"
    result = subprocess.run(command, capture_output=True, text=True, check=False)
    if result.returncode != 0:
        raise Refusal(f"`{' '.join(command)}` failed: {result.stderr.strip()}")
    return method


def replace_binary(overlay: Path, relative: str, source: Path, expected_sha256: str) -> None:
    """Replace with a fresh file (new inode and mtime, never a link or a preserved mtime:
    build.rs re-records through cargo's mtime-based rerun-if-changed)."""
    target = overlay / relative
    if target.exists() or target.is_symlink():
        target.unlink()
    shutil.copyfile(source, target)
    os.chmod(target, 0o755)
    if sha256_file(target) != expected_sha256:
        raise Refusal(f"{target} changed while it was copied")


def wrapper_sysroot_assignment(pack: Path) -> tuple[str, int, str]:
    """A wrapper sysroot's `bin/trustc` text, the index of its one line
    assigning `sysroot=` the wrapper sysroot itself, and the path it names."""
    wrapper = pack / "bin" / "trustc"
    if wrapper.is_symlink():
        raise Refusal(f"--pack {pack}: bin/trustc is a symlink, not a wrapper script")
    try:
        text = wrapper.read_bytes().decode("utf-8")
    except UnicodeDecodeError:
        raise Refusal(f"--pack {pack}: bin/trustc is not a text wrapper script (a compiler binary?)") from None
    lines = text.splitlines(keepends=True)
    assignments = [
        index
        for index, line in enumerate(lines)
        if WRAPPER_SYSROOT_ASSIGNMENT.match(line.rstrip("\r\n"))
    ]
    if len(assignments) != 1:
        raise Refusal(
            f"--pack {pack}: bin/trustc has {len(assignments)} `sysroot=` assignments; "
            "a wrapper sysroot's has exactly one"
        )
    match = WRAPPER_SYSROOT_ASSIGNMENT.match(lines[assignments[0]].rstrip("\r\n"))
    assert match is not None
    named = match.group("path")
    if not named or Path(named).resolve() != pack:
        raise Refusal(
            f"--pack {pack}: bin/trustc assigns sysroot={named!r}, not the wrapper sysroot itself"
        )
    for spelling in {named, str(pack)}:
        if text.count(spelling) != (1 if spelling == named else 0):
            raise Refusal(
                f"--pack {pack}: bin/trustc names {spelling} outside its `sysroot=` assignment; "
                "the rewritten wrapper would still reach the original"
            )
    return text, assignments[0], named


def rewrite_wrapper(partial: Path, final: Path, text: str, index: int) -> None:
    """Point the cloned wrapper's one `sysroot=` assignment at the overlay's
    final path (a fresh file, like `replace_binary`)."""
    target = partial / "bin" / "trustc"
    if target.read_bytes() != text.encode("utf-8"):
        raise Refusal(f"{target} changed while the wrapper sysroot was cloned")
    lines = text.splitlines(keepends=True)
    ending = lines[index][len(lines[index].rstrip("\r\n")):]
    lines[index] = f"sysroot={shlex.quote(str(final))}{ending}"
    target.unlink()
    target.write_text("".join(lines))
    os.chmod(target, 0o755)


def trustc_facts(trustc: Path) -> tuple[str, dict[str, str]]:
    sysroot = run([str(trustc), "--print", "sysroot"])
    if sysroot.returncode != 0:
        raise Refusal(f"`{trustc} --print sysroot` failed: {sysroot.stderr.strip()}")
    version = run([str(trustc), "-vV"])
    if version.returncode != 0:
        raise Refusal(f"`{trustc} -vV` failed: {version.stderr.strip()}")
    facts = {}
    for line in version.stdout.splitlines():
        if ": " in line:
            key, value = line.split(": ", 1)
            facts[key.strip()] = value.strip()
        elif line.strip():
            facts.setdefault("banner", line.strip())
    return sysroot.stdout.strip(), facts


def assemble(arguments: argparse.Namespace) -> dict[str, object]:
    out = Path(arguments.out).absolute()
    if out.exists() or out.is_symlink():
        raise Refusal(f"--out {out} already exists; an overlay is assembled once, never updated")
    if not out.parent.is_dir():
        raise Refusal(f"--out parent {out.parent} does not exist")
    pack = Path(arguments.pack).resolve()
    kind = arguments.pack_kind
    if kind == PACK_KIND_WRAPPER:
        for relative in ("bin/trustc", "lib/rustlib"):
            if not (pack / relative).exists():
                raise Refusal(f"--pack {pack} has no {relative} (not a wrapper sysroot)")
    else:
        for relative in ("bin/trustc", "bin/targo", "lib/rustlib"):
            if not (pack / relative).exists():
                raise Refusal(f"--pack {pack} has no {relative} (not a Trust toolchain pack)")
    if (pack / MANIFEST).exists():
        raise Refusal(f"--pack {pack} is itself an overlay; assemble from an installed pack")
    wrapper = wrapper_sysroot_assignment(pack) if kind == PACK_KIND_WRAPPER else None
    ay = executable_input(Path(arguments.ay), "ay")
    clean = executable_input(Path(arguments.clean), "clean")
    ay_record = ay_identity(ay, Path(arguments.ay_src), arguments.require_ay_ancestor)
    clean_record = clean_identity(clean, Path(arguments.clean_src), arguments.require_clean_ancestor)
    if arguments.ay_build_command:
        ay_record["build_command"] = arguments.ay_build_command
    if arguments.clean_build_command:
        clean_record["build_command"] = arguments.clean_build_command

    partial = out.parent / f".{out.name}.partial-{os.getpid()}"
    try:
        method = clone_tree(pack, partial)
        replace_binary(partial, "bin/ay", ay, ay_record["sha256"])
        replace_binary(partial, "bin/clean", clean, clean_record["sha256"])
        if wrapper is not None:
            rewrite_wrapper(partial, out, wrapper[0], wrapper[1])
        os.chmod(partial, 0o700)
        os.rename(partial, out)
    except BaseException:
        shutil.rmtree(partial, ignore_errors=True)
        raise
    try:
        sysroot, trustc = trustc_facts(out / "bin" / "trustc")
        if Path(sysroot).resolve() != out.resolve():
            raise Refusal(f"{out}/bin/trustc --print sysroot names {sysroot}, not the overlay")
        manifest = {
            "schema": SCHEMA,
            "not_a_published_pack": True,
            "name": out.name,
            "created_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "host": {"system": platform.system(), "machine": platform.machine()},
            "pack": {
                "path": str(pack),
                "kind": kind,
                "store_id": pack.name,
                "clone_method": method,
                "trustc": trustc,
            },
            "ay": ay_record,
            "clean": clean_record,
            "signatures": [],
        }
        if wrapper is not None:
            manifest["pack"]["wrapper"] = {
                "path": "bin/trustc",
                "original_sha256": hashlib.sha256(wrapper[0].encode("utf-8")).hexdigest(),
                "sha256": sha256_file(out / "bin" / "trustc"),
                "sysroot_assignment": {"original": wrapper[2], "overlay": str(out)},
                "binding": "the one `sysroot=` assignment rewritten; the compiler it runs is `trustc` above (`-vV`)",
            }
        (out / MANIFEST).write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        (out / "OVERLAY-README.txt").write_text(README)
    except BaseException:
        shutil.rmtree(out, ignore_errors=True)
        raise
    return manifest


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument(
        "--pack",
        required=True,
        help="installed Trust pack directory (store/trust/<id>), or a wrapper sysroot (--pack-kind)",
    )
    parser.add_argument(
        "--pack-kind",
        choices=(PACK_KIND_INSTALLED, PACK_KIND_WRAPPER),
        default=PACK_KIND_INSTALLED,
        help="`wrapper-sysroot`: --pack is a sysroot whose bin/trustc is a shell wrapper with "
        "its --sysroot hard-coded in one `sysroot=` assignment (no targo)",
    )
    parser.add_argument("--ay", required=True, help="the built ay binary")
    parser.add_argument("--ay-src", required=True, help="the git checkout the ay binary was built from")
    parser.add_argument("--clean", required=True, help="the built clean binary (with carcara-verify)")
    parser.add_argument("--clean-src", required=True, help="the git checkout the clean binary was built from")
    parser.add_argument("--out", required=True, help="new overlay directory (must not exist)")
    parser.add_argument("--require-ay-ancestor", action="append", default=[], metavar="REV")
    parser.add_argument("--require-clean-ancestor", action="append", default=[], metavar="REV")
    parser.add_argument("--ay-build-command", help="label: how the ay binary was built")
    parser.add_argument("--clean-build-command", help="label: how the clean binary was built")
    arguments = parser.parse_args(argv)
    try:
        manifest = assemble(arguments)
    except Refusal as refusal:
        print(f"assemble_trust_overlay: refused: {refusal}", file=sys.stderr)
        return 2
    out = Path(arguments.out).absolute()
    print(f"assemble_trust_overlay: {out} (not a published pack)")
    print(f"  manifest sha256 {sha256_file(out / MANIFEST)}")
    print(f"  ay    {manifest['ay']['sha256']} build {manifest['ay']['increment']} commit {manifest['ay']['commit']}")
    print(f"  clean {manifest['clean']['sha256']} commit {manifest['clean']['source']['commit']}")
    if arguments.pack_kind == PACK_KIND_WRAPPER:
        print(f"  use: RUSTC={out}/bin/trustc <targo> --unverified build ...")
    else:
        print(f"  use: TRUST_TARGO={out}/bin/targo scripts/trust_cargo.sh test ...")
    return 0


if __name__ == "__main__":
    sys.exit(main())
