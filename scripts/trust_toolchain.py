#!/usr/bin/env python3
"""Resolve the installed Trust compiler that the rustc bridge is pinned to.

`crates/rustc-codegen-trust-cg/rust-toolchain.toml` pins `channel = "trust"`.
The backend links that compiler's rustc_private crates, so it can only be
built by and loaded into the same Trust compiler. Release and benchmark helpers
that build or load the backend resolve the compiler here, with the same package
rules as `scripts/check_linux_aarch64_bridge.py` and
`scripts/run_full_test_matrix.sh --check-rustc-backend-env`:

* `trustc` and `targo` come from one installed package: the PATH pair (or the
  explicit `--driver` file and the `targo` beside it) resolve into the same
  directory, and `trustc --print sysroot` is that package's root;
* `trustc -vV` reports exactly one branded `binary: trustc`, one 40-hex
  `commit-hash`, and one `host`;
* the sysroot carries the host `rustc_middle` and `rustc_codegen_ssa` private
  crates (purpose `bridge`, the default).

Purpose `workspace` (`--purpose workspace`) resolves the package for the root
workspace's own Cargo verbs, its formatter and its linter (`trust_cargo.sh`,
`check_fmt.sh`, `check_tippy.sh`). None of them builds against rustc_private
(the bridge is a separate workspace), so the private-crate rule is the one rule
it does not apply; every other rule above still holds. A package without
rustc-dev, such as the cross-built x86_64-apple-darwin pack, resolves for
`workspace` and is refused for `bridge`.

The bridge pin must be exactly `trust`. The retired stock `nightly-2026-04-20`
lane, any other stock channel, an unbranded driver (including the pack's own
`rustc` alias) and a toolchain without a commit identity (such as a local
rustup `trust` link reporting `commit-hash: unknown`) are refused. There is no
rustup, bare `rustc` or silent PATH fallback. A launcher shim is not a package,
but aterm's atpkg installs one on PATH for every tool: a small `#!/bin/sh` file
whose last command is `exec '<absolute file>' "$@"` and which contains no
other `exec`, except the exact build-admission tail described by
`launcher_target`. Most are that one command; aterm's `targo` and
`targo-tippy` shims (aterm 8d02fb9be, atpkg
`build_cache.rs`) first run a block of shell builtins that may put
`--config build.build-dir=...` in front of "$@". When the PATH `trustc` and
`targo` are both launcher shims, each is followed to the file its final exec
names, and those files must then pass every package rule above; the two must
both be shims or both be package files, and must exec one package. Following
a shim with a prelude is sound because no gate runs the shim. It is only read
here, never run, and only locates the package. Every consumer of `resolve`
drives the resolved package files (`compiler`, `targo`, `build_command`)
directly. A gate that asks a Trust tool anything else (a `targo metadata`
census, a `trustc -vV` host triple or `--print sysroot`, the
`targo --unverified --version` discriminator) runs the package file as well,
the one `resolve` names or the one `launcher_target` reads out of the shim,
never the PATH name. A prelude runs only when the shim itself is executed, so
it cannot change what is selected, what a gate builds with, or what a gate
measures. A new gate keeps that rule: it runs a resolved file, never a bare
`trustc` or `targo`. Any other wrapper (a second `exec`, an `exec` that is not
the last command, a relative or unquoted target, a non-`#!/bin/sh`
interpreter) is refused; name the package compiler with
`--driver <sysroot>/bin/trustc`.

Every consumer drives the resolved compiler in its explicit UNVERIFIED lane:
`-Ztrust-verify=off` for direct compiles and `targo --unverified` for builds.
That lane is diagnostic. It makes no Trust-verified-compilation claim, and
resolving it does not satisfy `check_trust_default_authority.py
--require-verified-default` (L12). Backend proof gates are unaffected: the
`TCG_*` codegen controls a helper sets or leaves unset keep their meaning.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from typing import Callable, Mapping, Optional, Sequence


ROOT = Path(__file__).resolve().parents[1]
PIN_RELATIVE = Path("crates/rustc-codegen-trust-cg/rust-toolchain.toml")
PIN = ROOT / PIN_RELATIVE
SCHEMA = "trust-cg-trust-toolchain-v1"
REQUIRED_CHANNEL = "trust"
RETIRED_CHANNEL = "nightly-2026-04-20"
PRIVATE_CRATES = ("rustc_middle", "rustc_codegen_ssa")
# What the resolved package is for: `bridge` needs the private crates the
# backend links; `workspace` (root workspace verbs, formatter, linter) does not.
PURPOSES = ("bridge", "workspace")
UNVERIFIED_COMPILER_FLAGS = ("-Ztrust-verify=off",)
LANE = "unverified"
LANE_LABEL = (
    "diagnostic: explicit unverified Trust lane (-Ztrust-verify=off for direct "
    "compiles, targo --unverified for builds); no Trust-verified compilation claim"
)
PROBE_TIMEOUT_SECONDS = 60
# atpkg launcher shims are small: aterm's build-dir `targo` shim is about
# 2.7 KB. The cap bounds what is read and leaves that block room to grow;
# anything larger is not that shape.
LAUNCHER_SHIM_MAX_BYTES = 16 * 1024
LAUNCHER_SHIM_EXEC_RE = re.compile(r"exec '([^'\n]+)' \"\$@\"")
LAUNCHER_SHIM_EXEC_WORD_RE = re.compile(r"\bexec\b")
# A command line ending in one of these continues into the next line.
LAUNCHER_SHIM_CONTINUATIONS = ("\\", "|", "&&")
# atpkg's BUILD-ADMIT shim_hop: the helper receives the same literal package
# target as the final exec. Read this protocol; never execute its helper.
LAUNCHER_ADMISSION_HOP_RE = re.compile(
    r"\[ -x '([^'\n]+)' \] && exec '\1' __build_admit --shim "
    r'(?:targo|targo-tippy) "\$__atb_h" "\$__atb_p" "\$@"'
)
LAUNCHER_ADMISSION_PLACEMENT = (
    'if [ -n "$__atb" ]; then if [ -n "$__atb_D" ] && [ -n "$__atb_e" ]; '
    'then __atb_h=env; else __atb_h=config; fi; fi'
)
LAUNCHER_ADMISSION_REFUSAL = (
    "printf '%s\\n' 'atpkg: the cache registrar is unavailable; "
    "run aterm pkg repair; no build started' >&2"
)

Runner = Callable[[Sequence[str]], str]


class ToolchainError(RuntimeError):
    """The pinned Trust compiler cannot be resolved; nothing may be measured."""


def target_arguments(identity: Mapping[str, object], target: str) -> list[str]:
    """Preserve native Trust configuration; name only a cross target explicitly."""
    host = identity.get("host")
    if not isinstance(host, str) or not host or not isinstance(target, str) or not target:
        raise ToolchainError("target arguments need a resolved compiler host and target")
    return [] if target == host else ["--target", target]


# trustc refuses to run at all, even `-vV`, while any variable with one of these
# prefixes is set ("an untracked Trust semantic/codegen control").
UNTRACKED_CONTROL_PREFIXES = ("TRUST_CG_", "TCG_")


def without_untracked_controls(environment: Mapping[str, str]) -> dict:
    """`environment` minus the TRUST_CG_*/TCG_* controls a Trust compiler refuses.

    For identity probes (`-vV`, `--print sysroot`, `targo --unverified
    --version`): they ask what the compiler is, which those controls do not
    change, so a gate that exports them for its test binaries can still probe.
    """
    return {
        key: value for key, value in environment.items()
        if not key.startswith(UNTRACKED_CONTROL_PREFIXES)
    }


def _probe_environment() -> dict:
    """The process environment minus the controls a Trust compiler refuses."""
    return without_untracked_controls(os.environ)


def _probe(command: Sequence[str], *, environment: Optional[dict] = None,
           cwd: Optional[Path] = None, subtree: bool = False) -> str:
    try:
        if subtree:
            # Targo's scheduled query has a compiler child. Own the new group
            # and stop it before deleting its temporary source on any failure.
            child = subprocess.Popen(list(command), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                     text=True, env=environment, cwd=cwd, start_new_session=True)
            try:
                output, diagnostics = child.communicate(timeout=PROBE_TIMEOUT_SECONDS)
            except BaseException:
                try:
                    os.killpg(child.pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
                try:
                    child.communicate(timeout=5)
                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(child.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    child.communicate()
                raise
            result = subprocess.CompletedProcess(command, child.returncode, output, diagnostics)
        else:
            result = subprocess.run(
                list(command), capture_output=True, text=True,
                env=_probe_environment() if environment is None else environment, cwd=cwd,
                timeout=PROBE_TIMEOUT_SECONDS, check=False,
            )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise ToolchainError(f"probe {list(command)!r} failed: {error}") from error
    if result.returncode != 0:
        raise ToolchainError(
            f"probe {list(command)!r} exited {result.returncode}: {result.stderr.strip()}"
        )
    return result.stdout


def scheduled_sysroot_query(compiler: Path, targo: Path, runner: Runner) -> str:
    """Ask the exact compiler through Targo's ordinary scheduled rustc unit.

    Older Trust admits the bounded argv at native entry but still requires a
    captured GNU scheduler at worker entry. Targo already owns that transport.
    The empty standalone package has no dependency or build script, and the
    sole extra rustc option prints metadata before analysis or code generation.
    No scheduler advertisement, descriptor or resource credit is constructed.
    """
    with tempfile.TemporaryDirectory(prefix="trust-cg-sysroot-query-") as temporary:
        root = Path(temporary).resolve()
        (root / "src").mkdir()
        (root / "src/lib.rs").write_text("", encoding="utf-8")
        (root / "Cargo.toml").write_text(
            '[package]\nname="trust-cg-toolchain-sysroot-query"\n'
            'version="0.0.0"\nedition="2021"\n[workspace]\n', encoding="utf-8",
        )
        environment = _probe_environment()
        # These would replace the selected compiler or wrap its answer. They
        # are compilation controls, not scheduler/SDK/host custody. Retain all
        # custody variables, including broken advertisements so Targo refuses.
        for key in ("RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
                    "CARGO_BUILD_RUSTC", "CARGO_BUILD_RUSTC_WRAPPER",
                    "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER", "CARGO_TARGET_DIR",
                    "CARGO_BUILD_TARGET_DIR", "RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS",
                    "CARGO_BUILD_RUSTFLAGS", "RUSTUP_TOOLCHAIN"):
            environment.pop(key, None)
        environment["RUSTC"] = str(compiler)
        # There is no registry dependency. Use a private empty Cargo home so
        # user Cargo configuration cannot substitute a wrapper for this query.
        environment["CARGO_HOME"] = str(root / "cargo-home")
        command = [str(targo), "--unverified", "rustc", "--offline",
                   "--manifest-path", str(root / "Cargo.toml"),
                   "--target-dir", str(root / "target"),
                   "--config", "build.rustc=" + json.dumps(str(compiler)),
                   "--config", 'build.rustc-wrapper=""',
                   "--config", 'build.rustc-workspace-wrapper=""',
                   "--lib", "--", "--print=sysroot"]
        if runner is _probe:
            return _probe(command, environment=environment, cwd=root, subtree=True)
        return runner(command)


def _toolchain_table(text: str) -> dict:
    """Read `[toolchain]` string keys without requiring Python 3.11 tomllib."""
    try:
        import tomllib  # type: ignore[import-not-found]
    except ModuleNotFoundError:
        tomllib = None
    if tomllib is not None:
        try:
            table = tomllib.loads(text).get("toolchain")
        except tomllib.TOMLDecodeError as error:
            raise ToolchainError(f"bridge toolchain pin is not valid TOML: {error}") from error
        if not isinstance(table, dict):
            raise ToolchainError("bridge toolchain pin has no [toolchain] table")
        return table
    table: dict = {}
    section = None
    for raw in text.splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        if line.startswith("[") and line.endswith("]"):
            section = line[1:-1].strip()
            continue
        if section != "toolchain" or "=" not in line:
            continue
        key, value = (part.strip() for part in line.split("=", 1))
        if key in table:
            raise ToolchainError(f"bridge toolchain pin repeats toolchain.{key}")
        match = re.fullmatch(r'"([^"\\]*)"', value)
        table[key] = match.group(1) if match else value
    if section is None and not table:
        raise ToolchainError("bridge toolchain pin has no [toolchain] table")
    return table


def require_trust_pin(pin: Path = PIN) -> str:
    """Return the bridge channel, refusing everything except `trust`."""
    try:
        text = Path(pin).read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as error:
        raise ToolchainError(f"cannot read the bridge toolchain pin {pin}: {error}") from error
    channel = _toolchain_table(text).get("channel")
    if channel != REQUIRED_CHANNEL:
        retired = " (the retired stock nightly lane)" if channel == RETIRED_CHANNEL else ""
        raise ToolchainError(
            f"bridge toolchain pin {pin} must be channel = \"{REQUIRED_CHANNEL}\", found "
            f"{channel!r}{retired}; a backend built against the Trust compiler cannot be "
            f"loaded into a stock compiler, so no stock or nightly lane is resolved"
        )
    return channel


def _single(identity: str, field: str) -> Optional[str]:
    values = re.findall(rf"^{re.escape(field)}: (.*)$", identity, re.MULTILINE)
    return values[0].strip() if len(values) == 1 else None


def _executable_file(path: Path, what: str) -> Path:
    try:
        resolved = path.resolve(strict=True)
    except OSError as error:
        raise ToolchainError(f"{what} does not exist: {path} ({error})") from error
    if not resolved.is_file() or not os.access(resolved, os.X_OK):
        raise ToolchainError(f"{what} is not an executable file: {resolved}")
    return resolved


def launcher_target(path: Path) -> Optional[Path]:
    """Return the absolute file an atpkg launcher shim execs, else None.

    The atpkg shape: a `#!/bin/sh` file of at most `LAUNCHER_SHIM_MAX_BYTES`
    whose last command (comments and blank lines aside) is
    `exec '<absolute path>' "$@"`, on a line of its own that no earlier line
    continues into (a trailing `\\`, `|`, `||` or `&&`), in a file with no
    here-document and no other `exec`, apart from atpkg's exact BUILD-ADMIT
    tail. That tail assigns the same literal target, selects the placement,
    conditionally execs one absolute helper with the fixed admission protocol,
    then refuses with exit 75 if no helper ran. A changed target, protocol,
    refusal or any other exec refuses the file. Commands before that exec
    (aterm's build-dir prelude, which may put `--config ...` in front of "$@") are allowed; see
    the module docstring for why that cannot change what is selected. This is
    a line-level reading, not a shell parser; anything it does not recognize
    is not a shim.
    """
    try:
        if path.stat().st_size > LAUNCHER_SHIM_MAX_BYTES:
            return None
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return None
    lines = text.splitlines()
    if not lines or lines[0].strip() != "#!/bin/sh":
        return None
    commands = [
        line.strip() for line in lines[1:]
        if line.strip() and not line.strip().startswith("#")
    ]
    if not commands:
        return None
    *prelude, last = commands
    match = LAUNCHER_SHIM_EXEC_RE.fullmatch(last)
    if match is None:
        return None
    if len(prelude) >= 6:
        assignment, placement, select, dispatch, refusal, exit_line = prelude[-6:]
        hop = LAUNCHER_ADMISSION_HOP_RE.fullmatch(dispatch)
        if (assignment == f"__atb_p='{match.group(1)}'"
                and placement == "__atb_h=-"
                and select == LAUNCHER_ADMISSION_PLACEMENT
                and hop is not None and Path(hop.group(1)).is_absolute()
                and refusal == LAUNCHER_ADMISSION_REFUSAL and exit_line == "exit 75"):
            prelude = prelude[:-6]
    if any(LAUNCHER_SHIM_EXEC_WORD_RE.search(line) or "<<" in line for line in prelude):
        return None
    if prelude and prelude[-1].endswith(LAUNCHER_SHIM_CONTINUATIONS):
        return None
    target = Path(match.group(1))
    return target if target.is_absolute() else None


# The `bin/` files that decide what a build with a Trust sysroot runs: `trustc`;
# `rustc`, the driver a rustup-proxied build of the `trust` channel executes
# (one hard-linked file with `trustc` in the atpkg package); and `ay`, the one
# solver trust-cg-verify admits (the building toolchain's own `bin/ay`). A file
# present in one sysroot and absent from the other is a divergence too.
COMPILER_DIGEST_BIN = ("trustc", "rustc", "ay")


def compiler_digest(root: Path) -> str:
    """SHA-256 over the compiler a Trust sysroot defines.

    Covers `COMPILER_DIGEST_BIN` and every entry under `lib/` and `libexec/`
    (relative path, kind, executable bit, content). Other `bin/` tools (a
    `cargo` or `rustdoc` alias) are build tools, not the compiler that builds
    and loads the backend. Two sysroots with the same digest and the same 40-hex
    commit carry one compiler even at two paths: aterm's rustup `trust` link is
    a copied tree of the store package. Treating those as one toolchain, and
    refusing any other divergence, is ruling OD-05 (docs/decision-record.md).

    Covered symlinks are refused: equal link text does not bind equal referent
    bytes, and library-directory links can hide an entire dependency tree.
    This is copied-tree comparison, not a claim of an immutable sealed sysroot.
    """
    digest = hashlib.sha256()
    base = Path(root)
    paths = [base / "bin"] + [base / "bin" / name for name in COMPILER_DIGEST_BIN]
    for tree in ("lib", "libexec"):
        directory = base / tree
        if directory.is_symlink():
            raise OSError(f"compiler identity refuses symlink: {directory}")
        paths.append(directory)
        paths.extend(sorted(directory.rglob("*")))
    for path in paths:
        relative = path.relative_to(base).as_posix().encode()
        if path.is_symlink():
            raise OSError(f"compiler identity refuses symlink: {path}")
        elif path.is_file():
            content = hashlib.sha256()
            with path.open("rb") as source:
                for chunk in iter(lambda: source.read(1 << 20), b""):
                    content.update(chunk)
            digest.update(b"F" + relative + b"\0" + content.digest()
                          + (b"x" if os.access(path, os.X_OK) else b"-"))
        elif path.is_dir():
            digest.update(b"D" + relative + b"\0")
        else:
            digest.update(b"?" + relative + b"\0")
    return digest.hexdigest()


def same_compiler(first_root: Path, first_commit: str, second_root: Path, second_commit: str) -> bool:
    """Whether two sysroots carry one compiler: one 40-hex commit, one digest."""
    if first_commit != second_commit or not re.fullmatch(r"[0-9a-f]{40}", first_commit or ""):
        return False
    try:
        return compiler_digest(first_root) == compiler_digest(second_root)
    except OSError:
        return False


def resolve(
    driver: Optional[str] = None,
    *,
    pin: Path = PIN,
    path: Optional[str] = None,
    runner: Runner = _probe,
    purpose: str = "bridge",
) -> dict:
    """Resolve and identify the pinned Trust compiler package.

    `driver` names the package `trustc` explicitly; otherwise the PATH `trustc`
    and `targo` pair is used. `path` overrides the PATH searched (tests only).
    `purpose` is `bridge` (the private crates are required) or `workspace`.
    Raises ToolchainError on every incoherent or unidentified toolchain.
    """
    if purpose not in PURPOSES:
        raise ToolchainError(f"unknown purpose {purpose!r} (expected one of {', '.join(PURPOSES)})")
    channel = require_trust_pin(pin)
    launchers: Optional[dict] = None
    if driver is None:
        found = shutil.which("trustc", path=path)
        if found is None:
            raise ToolchainError(
                "required installed Trust tool is missing from PATH: trustc "
                "(name the package compiler with --driver <sysroot>/bin/trustc)"
            )
        found_targo = shutil.which("targo", path=path)
        if found_targo is None:
            raise ToolchainError("required installed Trust tool is missing from PATH: targo")
        compiler = _executable_file(Path(found), "Trust compiler")
        targo = _executable_file(Path(found_targo), "Trust build tool")
        if compiler.parent != targo.parent:
            raise ToolchainError(
                f"PATH trustc and targo must resolve to the same installed package: "
                f"{compiler} vs {targo}"
            )
        selection = "path"
        shim_compiler, shim_targo = launcher_target(compiler), launcher_target(targo)
        if shim_compiler is not None or shim_targo is not None:
            if shim_compiler is None or shim_targo is None:
                raise ToolchainError(
                    f"PATH trustc and targo must both be atpkg launcher shims or both be "
                    f"package files: {compiler} vs {targo}"
                )
            launchers = {"trustc": str(compiler), "targo": str(targo)}
            compiler = _executable_file(shim_compiler, "Trust compiler behind the PATH launcher shim")
            targo = _executable_file(shim_targo, "Trust build tool behind the PATH launcher shim")
            if compiler.parent != targo.parent:
                raise ToolchainError(
                    f"PATH launcher shims must exec one installed package: {compiler} vs {targo}"
                )
            selection = "path-launcher"
    else:
        requested = Path(driver).expanduser()
        if not requested.is_absolute():
            requested = Path.cwd() / requested
        compiler = _executable_file(requested, "explicit --driver")
        if compiler.name != "trustc":
            raise ToolchainError(
                f"the Trust lane must run the branded trustc driver, not {compiler.name} "
                f"(stock rustc, including the retired {RETIRED_CHANNEL}, is refused)"
            )
        targo = _executable_file(compiler.parent / "targo", "Trust build tool beside --driver")
        if targo.parent != compiler.parent:
            raise ToolchainError(
                f"--driver and its targo must belong to the same installed package: "
                f"{compiler} vs {targo}"
            )
        selection = "explicit-driver"
    if compiler.name != "trustc":
        raise ToolchainError(f"the Trust lane must run the branded trustc driver, not {compiler.name}")

    identity = runner([str(compiler), "-vV"])
    if _single(identity, "binary") != "trustc":
        raise ToolchainError(
            f"{compiler} did not identify as the branded trustc driver (binary: trustc); "
            f"stock rustc, including the retired {RETIRED_CHANNEL}, is refused"
        )
    commit = _single(identity, "commit-hash")
    if commit is None or not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ToolchainError(
            f"{compiler} did not provide a 40-hex commit identity (commit-hash: {commit}); "
            f"a local or stale toolchain link is refused"
        )
    host = _single(identity, "host")
    if host is None or not re.fullmatch(r"[A-Za-z0-9_.-]+", host):
        raise ToolchainError(f"{compiler} did not report exactly one host triple")

    targo_version = runner([str(targo), "--version"]).strip()
    if not targo_version.startswith("targo "):
        raise ToolchainError(f"{targo} did not identify as targo: {targo_version!r}")

    reported = scheduled_sysroot_query(compiler, targo, runner).strip()
    try:
        sysroot = Path(reported).resolve(strict=True)
    except OSError as error:
        raise ToolchainError(f"{compiler} reported a missing sysroot {reported!r}: {error}") from error
    if sysroot != compiler.parent.parent:
        raise ToolchainError(
            f"Trust compiler/sysroot package mismatch: {compiler} reports sysroot {sysroot}; "
            f"a launcher shim is not the package (use --driver {sysroot / 'bin' / 'trustc'})"
        )
    target_lib = sysroot / "lib" / "rustlib" / host / "lib"
    if not target_lib.is_dir():
        raise ToolchainError(f"Trust sysroot lacks host target libraries: {target_lib}")
    private_crates = PRIVATE_CRATES if purpose == "bridge" else ()
    for component in private_crates:
        if not any(entry.is_file() for entry in target_lib.glob(f"lib{component}-*")):
            raise ToolchainError(f"Trust sysroot private crate missing: {component} in {target_lib}")


    return {
        "schema": SCHEMA,
        "bridge_pin": {
            "path": str(pin), "channel": channel,
            "sha256": hashlib.sha256(Path(pin).read_bytes()).hexdigest(),
        },
        "selection": selection,
        "purpose": purpose,
        "private_crates": list(private_crates),
        "launchers": launchers,
        "requested_driver": driver,
        "compiler": str(compiler),
        "targo": str(targo),
        "sysroot": str(sysroot),
        "target_lib_dir": str(target_lib),
        "host": host,
        "commit": commit,
        "release": _single(identity, "release"),
        "version": identity.strip().splitlines()[0] if identity.strip() else "",
        "identity": identity.strip(),
        "targo_version": targo_version,
        "lane": LANE,
        "lane_label": LANE_LABEL,
        "compiler_flags": list(UNVERIFIED_COMPILER_FLAGS),
        "build_command": [str(targo), "--unverified"],
    }


def summary(record: dict) -> str:
    return (
        f"Trust compiler {record['commit']} ({record['version']}) at {record['compiler']}; "
        f"lane: {record['lane_label']}"
    )


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n", 1)[0], allow_abbrev=False)
    parser.add_argument(
        "--driver", default=None,
        help="explicit package trustc (default: the PATH trustc/targo pair)",
    )
    parser.add_argument(
        "--print", dest="field", default="json",
        choices=("json", "compiler", "targo", "sysroot", "commit", "host", "summary"),
        help="what to print on success (default: the JSON identity record)",
    )
    parser.add_argument(
        "--purpose", default="bridge", choices=PURPOSES,
        help="bridge (default): the package must carry the private crates the backend links; "
             "workspace: root workspace verbs, formatter and linter, which do not",
    )
    args = parser.parse_args(argv)
    try:
        record = resolve(args.driver, purpose=args.purpose)
    except ToolchainError as error:
        print(f"trust-toolchain: {error}", file=sys.stderr)
        return 2
    if args.field == "json":
        print(json.dumps(record, indent=2, sort_keys=True))
    elif args.field == "summary":
        print(summary(record))
    else:
        print(record[args.field])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
