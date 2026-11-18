#!/usr/bin/env python3
"""Audit the Cargo configuration a test runner's Cargo invocations will read.

Environment scrubbing does not reach Cargo's own configuration: a config file
can set `[env] PROPTEST_CASES = { value = "0", force = true }`, `[build]
rustflags = ["-Coverflow-checks=off"]`, a `[profile]`, an `[alias]` or a
compiler wrapper, and every Cargo invocation applies it. This module is the
one place both Linux AArch64 runners (scripts/check_linux_aarch64.py and
scripts/run_linux_fuzz_lane.py) ask what Cargo would read and whether it may
change what they build or execute. Both call it before they run any Cargo,
Targo or rustc command, version probes included, and again at the end.

Files. It enumerates the config files Cargo reads for a working directory:
`.cargo/config` and `.cargo/config.toml` in that directory and each ancestor,
then `config` and `config.toml` in Cargo's home unless the ancestor walk
already visited it. The caller selects native Targo or stock Cargo home
semantics explicitly. Targo imports TARGO_HOME only when CARGO_HOME is absent;
an explicitly empty CARGO_HOME still selects HOME/.cargo. Stock Cargo ignores
TARGO_HOME. Relative paths join the actual working directory. Both use the
shared scripts/dependency_identity.py resolver. Each existing regular file
is recorded with its SHA-256 and length. These are problems:
- any existing config path that is not a regular file. A FIFO or a symlink to
  /dev/stdin would hand Cargo bytes this audit never read. A symlink is
  refused whatever it points at: its target can change between the audit and
  Cargo's read.
- `config` and `config.toml` in one directory: Cargo reads only `config`
  (and warns), so the pair is refused rather than guessed at. A `config`
  alone is audited like `config.toml`.
- a key outside the allowlist below.

The repository's committed `.cargo/config.toml` bytes (the caller passes them)
are exempt wherever they appear in the ancestor walk: in this checkout while
unmodified, and in an ancestor that holds a byte-identical copy (a worktree
nested inside a checkout of the same revision). That copy sets only `[build]
jobs`, an unforced `[env] RUST_MIN_STACK` and `[net] git-fetch-with-cli`, so
reading it twice changes nothing. Every other file may contain only:
- the tables `ALLOWED_TABLES` (network, HTTP, registry, installation, cache
  and similar settings that do not select what is compiled);
- the `[term]` keys `ALLOWED_TERM_KEYS` (colour, verbosity, progress). `quiet`
  is refused: it makes libtest print dots, and the runners read test output
  line by line;
- the `[build]` keys `ALLOWED_BUILD_KEYS` (job count, output directories,
  incremental compilation, pipelining).

That refuses `[env]`, `[target]`, `[profile]`, `[alias]`, `[unstable]`,
`[patch]`, `[source]` (including vendoring), `include`, `[build]`
rustflags/rustdocflags/rustc/rustc-wrapper/rustdoc/target, `[term] quiet`,
and every unrecognised table or key.

Variables. Cargo maps `CARGO_<KEY>` onto config keys. A Cargo build under
another name also maps its own prefix: Trust's `targo` reads `TARGO_<KEY>`
(TARGO_BUILD_RUSTFLAGS, TARGO_ALIAS_*, TARGO_ENCODED_RUSTFLAGS,
TARGO_TARGET_<triple>_RUSTFLAGS...) as well as `CARGO_<KEY>`, under any name
it is installed as, while it reads no `.targo/` config directory and no
TRUST_*RUSTFLAGS. Native home selection is a separate explicit caller context;
a tool basename or a variable prefix does not prove which executable will run.
`environment_prefixes` derives the set from the selected tool, and every prefix follows the same key allowlist. Keys
Cargo itself sets for build scripts, rustc and tests (`CHILD_KEYS`, e.g.
CARGO_MANIFEST_DIR, CARGO_PKG_*, CARGO_CFG_*, CARGO_FEATURE_*,
CARGO_MAKEFLAGS) are not config keys: they are recorded, and both runners
remove them from their children, because an ambient one Cargo does not
overwrite (a CARGO_FEATURE_* for a disabled feature) would reach build
scripts.

A file that cannot be parsed, or any non-exempt file when this interpreter
lacks `tomllib`, is a problem too. The audit reads files only; it does not
run Cargo. It covers Cargo's config files and config variables, not other
ambient controls (RUSTFLAGS, RUSTC, compiler wrappers), which each runner
handles itself.
"""

from __future__ import annotations

import hashlib
import importlib.util
import os
from pathlib import Path
import re
import stat
from typing import Mapping, Sequence

try:  # Python 3.11+
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - exercised only on old interpreters
    tomllib = None

# Cargo reads `config` when both names exist in one directory.
CONFIG_NAMES = ("config", "config.toml")
CARGO_PREFIX = "CARGO_"
# Cargo builds that read their own <NAME>_<KEY> variables besides CARGO_<KEY>
# under any installed name: a Trust package installs one executable as both
# `cargo` and `targo`.
CARGO_BUILDS_WITH_OWN_PREFIX = ("targo",)
# Tables that do not select what is compiled or how tests run.
ALLOWED_TABLES = frozenset({
    "net", "http", "registries", "registry", "cargo-new", "credential-alias",
    "install", "future-incompat-report", "cache", "doc", "gc", "resolver",
})
# `[term]` keys that change only Cargo's own terminal output. `quiet` is
# absent: `cargo test` passes it on to libtest, which then prints dots.
ALLOWED_TERM_KEYS = frozenset({"color", "verbose", "progress", "hyperlinks", "unicode"})
# `[build]` keys that choose parallelism and output locations only.
ALLOWED_BUILD_KEYS = frozenset({"jobs", "target-dir", "build-dir", "incremental", "dep-info-basedir", "pipelining"})
# <PREFIX><KEY> variables that are not config keys, or map onto allowed keys.
ALLOWED_ENVIRONMENT_KEYS = frozenset({
    "HOME", "TARGET_DIR", "BUILD_DIR", "INCREMENTAL", "LOG",
    "BUILD_JOBS", "BUILD_TARGET_DIR", "BUILD_BUILD_DIR", "BUILD_INCREMENTAL",
    "BUILD_DEP_INFO_BASEDIR", "BUILD_PIPELINING",
    "TERM_COLOR", "TERM_VERBOSE", "TERM_HYPERLINKS", "TERM_UNICODE",
})
ALLOWED_ENVIRONMENT_KEY_PREFIXES = (
    "NET_", "HTTP_", "REGISTRIES_", "REGISTRY_", "TERM_PROGRESS_", "CARGO_NEW_", "INSTALL_",
    "FUTURE_INCOMPAT_REPORT_", "CACHE_", "DOC_", "GC_", "RESOLVER_", "CREDENTIAL_ALIAS_", "LOG_",
)
# Keys Cargo sets for build scripts, rustc and tests; the runners remove them.
CHILD_KEYS = frozenset({
    "MANIFEST_DIR", "MANIFEST_PATH", "MANIFEST_LINKS", "CRATE_NAME", "BIN_NAME",
    "PRIMARY_PACKAGE", "TARGET_TMPDIR", "MAKEFLAGS", "RUSTC_CURRENT_DIR",
})
CHILD_KEY_PREFIXES = ("PKG_", "CFG_", "FEATURE_", "BIN_EXE_")
VARIABLE_KEY = re.compile(r"[A-Z0-9_]+")
DEPENDENCY_RESOLVER = Path(__file__).resolve().with_name("dependency_identity.py")


def _dependency_identity():
    """scripts/dependency_identity.py, which owns the Cargo home resolver."""
    spec = importlib.util.spec_from_file_location("_cargo_config_audit_dependency_identity", DEPENDENCY_RESOLVER)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"required Cargo home resolver is missing: {DEPENDENCY_RESOLVER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


_RESOLVER = _dependency_identity()


def cargo_home(environment: Mapping[str, str], cwd: Path, *, native_targo: bool = False) -> Path:
    """The Cargo home a Cargo started in `cwd` uses (the shared resolver)."""
    return _RESOLVER.cargo_home_from(environment, Path(os.path.abspath(cwd)), native_targo=native_targo)[0]


def environment_prefixes(tool: str | os.PathLike = "cargo") -> tuple[str, ...]:
    """The variable prefixes the selected build tool maps onto config keys.

    CARGO_ always; the tool's own name's prefix when it is not `cargo`; and
    each CARGO_BUILDS_WITH_OWN_PREFIX name's prefix when the tool is the same
    file as that name beside it (a Trust package's `cargo` is its `targo`).
    A rustup proxy cannot be resolved without running it: the one stock-Cargo
    caller, the Linux fuzz lane (scripts/run_linux_fuzz_lane.py, a STOCK
    EXCEPTION), refuses a Cargo whose `-vV` names a Trust build.
    """
    path = Path(tool)
    names = {path.name}
    try:
        resolved = path.resolve(strict=True)
        for name in CARGO_BUILDS_WITH_OWN_PREFIX:
            sibling = resolved.parent / name
            if sibling.exists() and os.path.samefile(sibling, resolved):
                names.add(name)
    except OSError:
        pass
    prefixes = [CARGO_PREFIX]
    for name in sorted(names):
        prefix = re.sub(r"[^A-Z0-9]", "_", name.upper()) + "_"
        if prefix not in prefixes:
            prefixes.append(prefix)
    return tuple(prefixes)


def variable_key(name: str, prefixes: Sequence[str]) -> str | None:
    """The config key part of `name` under one of `prefixes`, if it has one."""
    for prefix in prefixes:
        if name.startswith(prefix) and VARIABLE_KEY.fullmatch(name[len(prefix):]):
            return name[len(prefix):]
    return None


def child_key(key: str) -> bool:
    """Whether a variable key is one Cargo sets for its children."""
    return key in CHILD_KEYS or key.startswith(CHILD_KEY_PREFIXES)


def child_variable(name: str, prefixes: Sequence[str] = (CARGO_PREFIX,)) -> bool:
    """Whether `name` is a variable Cargo sets for build scripts, rustc and
    tests; the runners remove such ambient variables from their children."""
    return any(name.startswith(prefix) and child_key(name[len(prefix):]) for prefix in prefixes)


def environment_problems(environment: Mapping[str, str], prefixes: Sequence[str] = (CARGO_PREFIX,)) -> list[str]:
    """Config variables under `prefixes` that map onto keys outside the allowlist."""
    problems = []
    for name in environment:
        key = variable_key(name, prefixes)
        if key is None or child_variable(name, prefixes):
            continue
        if key not in ALLOWED_ENVIRONMENT_KEYS and not key.startswith(ALLOWED_ENVIRONMENT_KEY_PREFIXES):
            problems.append(name)
    return sorted(problems)


def config_directories(cwd: Path, environment: Mapping[str, str], *, native_targo: bool = False) -> list[tuple[Path, str]]:
    """Every directory Cargo looks in for config files, in its search order."""
    directory = Path(os.path.abspath(cwd))
    found = [(base / ".cargo", "ancestor") for base in (directory, *directory.parents)]
    home = Path(os.path.abspath(cargo_home(environment, directory, native_targo=native_targo)))
    visited = {os.path.realpath(path) for path, _ in found}
    if os.path.realpath(home) not in visited:
        found.append((home, "home"))
    return found


def file_kind(mode: int) -> str:
    for kind, test in (
        ("file", stat.S_ISREG), ("symlink", stat.S_ISLNK), ("directory", stat.S_ISDIR),
        ("fifo", stat.S_ISFIFO), ("socket", stat.S_ISSOCK), ("character device", stat.S_ISCHR),
        ("block device", stat.S_ISBLK),
    ):
        if test(mode):
            return kind
    return "unknown"


def read_regular(path: Path) -> bytes:
    """A regular file's bytes, without following a symlink or blocking on a
    FIFO swapped in after the caller's lstat."""
    flags = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK | getattr(os, "O_CLOEXEC", 0)
    descriptor = os.open(path, flags)
    try:
        info = os.fstat(descriptor)
        if not stat.S_ISREG(info.st_mode):
            raise OSError(f"{path} became a {file_kind(info.st_mode)}")
        chunks = []
        while chunk := os.read(descriptor, 1 << 20):
            chunks.append(chunk)
        return b"".join(chunks)
    finally:
        os.close(descriptor)


def config_files(cwd: Path, environment: Mapping[str, str], *, native_targo: bool = False) -> list[dict]:
    """Every existing config path Cargo would consult from `cwd`, in its search
    order, with the path problems of each (see the module docstring)."""
    entries = []
    for directory, origin in config_directories(cwd, environment, native_targo=native_targo):
        present = [directory / name for name in CONFIG_NAMES if os.path.lexists(directory / name)]
        for path in present:
            entry = {"path": path, "origin": origin, "problems": []}
            info = os.lstat(path)
            entry["kind"] = file_kind(info.st_mode)
            if stat.S_ISLNK(info.st_mode):
                entry["target"] = os.readlink(path)
                entry["problems"].append(f"is a symbolic link (to {entry['target']}); Cargo would read its target")
            elif not stat.S_ISREG(info.st_mode):
                entry["problems"].append(f"is a {entry['kind']}, not a regular file")
            if len(present) == 2:
                entry["problems"].append(
                    "`config` and `config.toml` both exist in this directory; Cargo reads only `config`"
                )
            entries.append(entry)
    return entries


def table_problems(document: Mapping) -> list[str]:
    """Keys of one parsed config file outside the allowlist."""
    problems = []
    for table, value in sorted(document.items()):
        if table == "build" and isinstance(value, Mapping):
            problems.extend(f"[build] {key}" for key in sorted(value) if key not in ALLOWED_BUILD_KEYS)
        elif table == "term" and isinstance(value, Mapping):
            problems.extend(f"[term] {key}" for key in sorted(value) if key not in ALLOWED_TERM_KEYS)
        elif table not in ALLOWED_TABLES:
            problems.append(f"[{table}]" if isinstance(value, Mapping) else table)
    return problems


def audit(
    cwd: Path, environment: Mapping[str, str], committed: bytes | None = None, tool: str | os.PathLike = "cargo",
    *, native_targo: bool = False,
) -> dict:
    """Record every config path and config variable, and name each problem.

    `committed` is the repository's committed `.cargo/config.toml`, exempt
    wherever the ancestor walk finds a byte-identical copy. `tool` is the
    build tool the caller will run (see `environment_prefixes`).
    `native_targo` selects its home semantics explicitly, independent of names.
    """
    directory = Path(os.path.abspath(cwd))
    own = directory / ".cargo" / "config.toml"
    prefixes = environment_prefixes(tool)
    files, problems = [], []
    for entry in config_files(directory, environment, native_targo=native_targo):
        path = entry.pop("path")
        record = {"path": str(path), **entry}
        found = record["problems"]
        if record["kind"] == "file":
            try:
                data = read_regular(path)
            except OSError as error:
                found.append(f"cannot be read: {error}")
                data = None
            if data is not None:
                record.update(sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))
                if committed is not None and data == committed and record["origin"] == "ancestor":
                    record["exempt"] = ("the repository's committed config" if path == own
                                        else "byte-identical to the repository's committed config")
                else:
                    if path == own and committed is not None:
                        record["modified_from_committed"] = True
                    if tomllib is None:
                        found.extend(["cannot be audited without tomllib"] if data.strip() else [])
                    else:
                        try:
                            found.extend(table_problems(tomllib.loads(data.decode("utf-8"))))
                        except (UnicodeDecodeError, tomllib.TOMLDecodeError) as error:
                            found.append(f"cannot be parsed: {error}")
        problems.extend(f"{path}: {problem}" for problem in found)
        files.append(record)
    variables = environment_problems(environment, prefixes)
    problems.extend(f"environment {name}={environment[name]!r}" for name in variables)
    return {
        "cwd": str(directory), "tool": str(tool), "environment_prefixes": list(prefixes),
        "cargo_home": str(cargo_home(environment, directory, native_targo=native_targo)),
        "native_targo_home": native_targo, "files": files,
        "environment": {
            name: environment[name] for name in sorted(environment)
            if variable_key(name, prefixes) is not None and not child_variable(name, prefixes)
        },
        "child_variables": sorted(name for name in environment if child_variable(name, prefixes)),
        "problems": problems,
    }


def committed_config(root: Path, git: str = "git") -> bytes | None:
    """The repository's tracked `.cargo/config.toml` at HEAD, if any."""
    import subprocess

    try:
        result = subprocess.run(
            [git, "show", "HEAD:.cargo/config.toml"], cwd=root, capture_output=True, timeout=20, check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    return result.stdout if result.returncode == 0 else None


def changes(before: dict, after: dict) -> list[str]:
    """Config paths or variables that differ between two audits."""
    def index(record: dict) -> dict:
        return {entry["path"]: (entry.get("kind"), entry.get("sha256")) for entry in record.get("files", [])}

    found = []
    old, new = index(before), index(after)
    for path in sorted(set(old) | set(new)):
        if old.get(path) != new.get(path):
            found.append(f"{path}: {old.get(path)} -> {new.get(path)}")
    for key in ("environment", "child_variables", "environment_prefixes", "cargo_home", "native_targo_home"):
        if before.get(key) != after.get(key):
            found.append(f"{key} changed")
    return found


def main(argv: Sequence[str] | None = None) -> int:
    import argparse
    import json

    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--cwd", type=Path, default=Path.cwd())
    parser.add_argument("--tool", default="targo",
                        help="the build tool that will run (default: targo, the Trust package's)")
    parser.add_argument("--home-context", choices=("targo", "cargo"), default="targo",
                        help="selected frontend home semantics, independent of the tool filename")
    args = parser.parse_args(argv)
    root = Path(__file__).resolve().parents[1]
    record = audit(args.cwd, os.environ, committed_config(root), args.tool,
                   native_targo=args.home_context == "targo")
    print(json.dumps(record, indent=2))
    return 1 if record["problems"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
