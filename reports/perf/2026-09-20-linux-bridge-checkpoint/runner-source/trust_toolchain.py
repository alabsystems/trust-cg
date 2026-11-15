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
  crates.

The bridge pin must be exactly `trust`. The retired stock `nightly-2026-04-20`
lane, any other stock channel, an unbranded driver (including the pack's own
`rustc` alias) and a toolchain without a commit identity (such as a local
rustup `trust` link reporting `commit-hash: unknown`) are refused. There is no
rustup, bare `rustc` or silent PATH fallback. A launcher shim is not a package:
when PATH holds shims that `exec` the real compiler, name the package compiler
with `--driver <sysroot>/bin/trustc`.

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
import subprocess
import sys
from typing import Callable, Optional, Sequence


ROOT = Path(__file__).resolve().parents[1]
PIN_RELATIVE = Path("crates/rustc-codegen-trust-cg/rust-toolchain.toml")
PIN = ROOT / PIN_RELATIVE
SCHEMA = "trust-cg-trust-toolchain-v1"
REQUIRED_CHANNEL = "trust"
RETIRED_CHANNEL = "nightly-2026-04-20"
PRIVATE_CRATES = ("rustc_middle", "rustc_codegen_ssa")
UNVERIFIED_COMPILER_FLAGS = ("-Ztrust-verify=off",)
LANE = "unverified"
LANE_LABEL = (
    "diagnostic: explicit unverified Trust lane (-Ztrust-verify=off for direct "
    "compiles, targo --unverified for builds); no Trust-verified compilation claim"
)
PROBE_TIMEOUT_SECONDS = 60

Runner = Callable[[Sequence[str]], str]


class ToolchainError(RuntimeError):
    """The pinned Trust compiler cannot be resolved; nothing may be measured."""


def _probe(command: Sequence[str]) -> str:
    try:
        result = subprocess.run(
            list(command), capture_output=True, text=True,
            timeout=PROBE_TIMEOUT_SECONDS, check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise ToolchainError(f"probe {list(command)!r} failed: {error}") from error
    if result.returncode != 0:
        raise ToolchainError(
            f"probe {list(command)!r} exited {result.returncode}: {result.stderr.strip()}"
        )
    return result.stdout


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


def resolve(
    driver: Optional[str] = None,
    *,
    pin: Path = PIN,
    path: Optional[str] = None,
    runner: Runner = _probe,
) -> dict:
    """Resolve and identify the pinned Trust compiler package.

    `driver` names the package `trustc` explicitly; otherwise the PATH `trustc`
    and `targo` pair is used. `path` overrides the PATH searched (tests only).
    Raises ToolchainError on every incoherent or unidentified toolchain.
    """
    channel = require_trust_pin(pin)
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

    reported = runner([str(compiler), "--print", "sysroot"]).strip()
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
    for component in PRIVATE_CRATES:
        if not any(entry.is_file() for entry in target_lib.glob(f"lib{component}-*")):
            raise ToolchainError(f"Trust sysroot private crate missing: {component} in {target_lib}")

    targo_version = runner([str(targo), "--version"]).strip()
    if not targo_version.startswith("targo "):
        raise ToolchainError(f"{targo} did not identify as targo: {targo_version!r}")

    return {
        "schema": SCHEMA,
        "bridge_pin": {
            "path": str(pin), "channel": channel,
            "sha256": hashlib.sha256(Path(pin).read_bytes()).hexdigest(),
        },
        "selection": selection,
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
        choices=("json", "compiler", "targo", "sysroot", "commit", "summary"),
        help="what to print on success (default: the JSON identity record)",
    )
    args = parser.parse_args(argv)
    try:
        record = resolve(args.driver)
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
