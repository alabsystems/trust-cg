#!/usr/bin/env python3
"""Locate the rustc bridge backend a benchmark or gate loads, and refuse a stale one.

`crates/rustc-codegen-trust-cg` builds a `cdylib` whose file name carries the
host's shared-library suffix: `librustc_codegen_trust_cg.dylib` on Darwin and
`librustc_codegen_trust_cg.so` on Linux. The beat-llvm harness and the landing
gates (`benchmarks/beat-llvm/run.py`, `compile_gate.py` and `scale_gate.py`
beside it, `scripts/compile_time_canary.sh`,
`scripts/compile_determinism_sentinel.sh`) resolve it here, so a Linux host is
not sent looking for a `.dylib` and their freshness rule exists once. Other
benchmark scripts keep their own backend paths and no freshness check:
`benchmarks/beat-llvm/run_gcc_baseline.sh` (a macOS Homebrew-gcc/clang/zsh
diagnostic that also targets `x86_64-apple-darwin`), `benchmarks/compile-scaling`,
`benchmarks/compile-apples` and the `*-xback` lanes.

Resolution. The canonical build writes `target-bridge/release` inside the
bridge crate (see the beat-llvm README). Older recipes wrote elsewhere, and a
long-lived host accumulates copies, so the default is the NEWEST existing
candidate among `BUILD_DIRS`, never a fixed path that may hold a backend days
older than the tree.

Freshness. A backend older than any input of its build measures code that is
not in the checkout, which attributes results to the wrong revision. Every
backend (a resolved default or an explicit one) is refused when one of these
inputs is newer than it (`build_inputs`):
  * every file under `crates/<crate>/` for each crate the bridge's build can
    compile — Rust sources, `Cargo.toml`, the bridge's `Cargo.lock` (which
    carries the trust-ir pin) and `rust-toolchain.toml`, C sources, embedded
    data such as `verdict_db/tier0.vdb` — except documentation (`*.md`),
    hidden files, a crate's own `tests`, `benches`, `examples` and `fixtures`
    directories, `tests` module directories inside its sources, and Cargo
    build directories (`target` or `target-*` at the top of `crates/` or of a
    crate, or any directory holding Cargo's `CACHEDIR.TAG`). The crates are
    the path packages of `crates/rustc-codegen-trust-cg/Cargo.lock`
    (`bridge_crate_directories`), so a change to a crate the bridge never
    compiles (the CLI, the fuzzers) cannot mark a just-built backend stale
    when Cargo rightly relinks nothing. When that set cannot be established
    (no lock, no path package, or one no `crates/*/Cargo.toml` names), every
    crate is scanned;
  * any file a scanned `.rs` names with a literal `include_str!` /
    `include_bytes!` path, even inside an excluded directory, and the file of
    every `#[path = "..."]` module it declares outside `#[cfg(test)]` /
    `#[cfg(all(test, ...))]` (a source shared from another directory);
  * the root `Cargo.toml` (path dependencies inherit its workspace keys) and
    `.cargo/config.toml` (Cargo reads it when building the bridge crate below
    it).
Paths are matched by components relative to `crates/`, never by substring,
so `src/target.rs` or a checkout under `/tests/` is still scanned.

CLI (for the shell gates):
    bridge_backend.py [--repo DIR] [--backend PATH] [--allow-stale] --print path
    bridge_backend.py --print suffix | candidates
Exit 0 prints the answer; 2 when no backend exists or it is stale (the reason is
on stderr). `--allow-stale` prints a stale backend anyway, with a warning, for
diagnostics that are not evidence.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path
from typing import Optional

ROOT = Path(__file__).resolve().parents[1]
STEM = "librustc_codegen_trust_cg"
BUILD_DIRS = (
    "crates/rustc-codegen-trust-cg/target-bridge/release",
    "target-bridge/release",
    "crates/rustc-codegen-trust-cg/target/release",
)
# A crate's top-level directories that are not compiled into the cdylib.
NON_BACKEND_DIRS = ("tests", "benches", "examples", "fixtures")
ROOT_INPUTS = ("Cargo.toml", ".cargo/config.toml")
BRIDGE_LOCK = Path("crates/rustc-codegen-trust-cg/Cargo.lock")
INCLUDE = re.compile(r'include_(?:str|bytes)!\(\s*"([^"]+)"\s*\)')
PATH_MODULE = re.compile(r'#\[path\s*=\s*"([^"]+)"\s*\]')
# An attribute that compiles the item only into a crate's unit tests.
TEST_ONLY_CFG = re.compile(r"#\[cfg\((?:test|all\(\s*test\s*,.*\))\)\]")


class BackendError(RuntimeError):
    """No usable bridge backend: nothing may be measured with it."""


def suffix(platform: Optional[str] = None) -> str:
    """The shared-library suffix a cdylib gets on `platform` (default: this host)."""
    platform = platform or sys.platform
    if platform == "darwin":
        return ".dylib"
    if platform in ("win32", "cygwin"):
        return ".dll"
    return ".so"


def file_name(platform: Optional[str] = None) -> str:
    return STEM + suffix(platform)


def candidates(repo: Path = ROOT, platform: Optional[str] = None) -> list[Path]:
    """Every location a bridge build may have written, in preference order."""
    return [Path(repo) / directory / file_name(platform) for directory in BUILD_DIRS]


def newest(repo: Path = ROOT, platform: Optional[str] = None) -> Optional[Path]:
    """The newest existing candidate (ties keep preference order), else None."""
    found = [path for path in candidates(repo, platform) if path.is_file()]
    if not found:
        return None
    return max(found, key=lambda path: path.stat().st_mtime)


def _build_dir(directory: Path, name: str, depth: int) -> bool:
    """A Cargo build directory: named `target`/`target-*` at the top of
    `crates/` or of a crate, or anywhere when it holds Cargo's CACHEDIR.TAG (a
    source module directory may legitimately be called `target`)."""
    if depth <= 1 and (name == "target" or name.startswith("target-")):
        return True
    return (directory / "CACHEDIR.TAG").exists()


def _input_name(name: str) -> bool:
    return not name.startswith(".") and not name.endswith((".md", "~"))


def bridge_crate_directories(repo: Path) -> Optional[set[str]]:
    """The `crates/` directories whose package the bridge's Cargo.lock resolves
    from a path (the local crates its build can compile), or None when that set
    cannot be established and every crate must be scanned."""
    repo = Path(repo)
    try:
        lock = (repo / BRIDGE_LOCK).read_text(encoding="utf-8")
    except OSError:
        return None
    path_packages = set()
    for block in re.split(r"^\[\[package\]\]\s*$", lock, flags=re.MULTILINE)[1:]:
        name = re.search(r'^name = "([^"]+)"\s*$', block, flags=re.MULTILINE)
        if name and not re.search(r"^source = ", block, flags=re.MULTILINE):
            path_packages.add(name[1])
    if not path_packages:
        return None
    directories, placed = set(), set()
    for manifest in sorted((repo / "crates").glob("*/Cargo.toml")):
        try:
            text = manifest.read_text(encoding="utf-8")
        except OSError:
            return None
        package = re.search(r"^\[package\]\s*$(.*?)(?=^\[|\Z)", text, flags=re.MULTILINE | re.DOTALL)
        name = package and re.search(r'^name\s*=\s*"([^"]+)"', package[1], flags=re.MULTILINE)
        if name and name[1] in path_packages:
            directories.add(manifest.parent.name)
            placed.add(name[1])
    return directories if placed == path_packages else None


def _test_only(text: str, start: int) -> bool:
    """Whether the attribute run directly above `start` gates the item to unit tests."""
    for line in reversed(text[:start].splitlines()):
        line = line.strip()
        if not line.startswith("#["):
            return False
        if TEST_ONLY_CFG.fullmatch(line):
            return True
    return False


def _named_sources(here: Path, text: str):
    """Files a source names by a literal path: include_str!/include_bytes! and
    non-test `#[path]` modules, resolved from the source's directory."""
    for included in INCLUDE.findall(text):
        yield (here / included).resolve()
    for match in PATH_MODULE.finditer(text):
        if not _test_only(text, match.start()):
            yield (here / match[1]).resolve()


def build_inputs(repo: Path):
    """Every file the backend build reads, as far as it can be named without
    running Cargo (see the module docstring), each once."""
    repo = Path(repo)
    crates = repo / "crates"
    compiled = bridge_crate_directories(repo)
    seen = set()

    def once(path: Path):
        if path not in seen:
            seen.add(path)
            return True
        return False

    for relative in ROOT_INPUTS:
        path = repo / relative
        if path.is_file() and once(path):
            yield path
    for root, directories, files in os.walk(crates):
        here = Path(root)
        depth = len(here.relative_to(crates).parts)  # 0 = crates/, 1 = a crate
        kept = []
        for name in directories:
            if name.startswith(".") or _build_dir(here / name, name, depth):
                continue
            if depth == 0 and compiled is not None and name not in compiled:
                continue  # a crate the bridge's build never compiles
            if depth == 1 and name in NON_BACKEND_DIRS:
                continue
            if depth >= 2 and name == "tests":
                continue  # a `#[cfg(test)] mod tests;` directory inside the sources
            kept.append(name)
        directories[:] = sorted(kept)
        for name in sorted(files):
            if not _input_name(name):
                continue
            path = here / name
            if once(path):
                yield path
            if name.endswith(".rs"):
                try:
                    text = path.read_text(encoding="utf-8", errors="replace")
                except OSError:
                    continue
                for target in _named_sources(here, text):
                    if target.is_file() and once(target):
                        yield target


def stale_source(repo: Path, backend: Path) -> Optional[Path]:
    """A build input newer than `backend`, or None if it is current."""
    mtime = Path(backend).stat().st_mtime
    for path in build_inputs(repo):
        try:
            if path.stat().st_mtime > mtime:
                return path
        except OSError:
            continue
    return None


def resolve(repo: Path = ROOT, backend: Optional[Path] = None, *, allow_stale: bool = False,
            platform: Optional[str] = None) -> tuple[Path, Optional[Path]]:
    """The backend to load and the newer source that makes it stale (if allowed).

    Raises BackendError when no backend exists, or when it is stale and
    `allow_stale` is false.
    """
    repo = Path(repo)
    if backend is None:
        backend = newest(repo, platform)
        if backend is None:
            listed = ", ".join(str(path) for path in candidates(repo, platform))
            raise BackendError(f"no bridge backend is built; looked for {listed}")
    backend = Path(backend)
    if not backend.is_file():
        raise BackendError(f"bridge backend missing: {backend}")
    stale = stale_source(repo, backend)
    if stale is not None and not allow_stale:
        raise BackendError(
            f"bridge backend is STALE: {backend} is older than {stale}; rebuild it "
            f"(cd crates/rustc-codegen-trust-cg && CARGO_TARGET_DIR=target-bridge "
            f"RUSTC=<trust-package>/bin/trustc <trust-package>/bin/targo --unverified "
            f"build --release)")
    return backend, stale


def main(argv: Optional[list[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n", 1)[0], allow_abbrev=False)
    parser.add_argument("--repo", type=Path, default=ROOT, help="checkout root (default: this one)")
    parser.add_argument("--backend", type=Path, default=None,
                        help="explicit backend to check (default: the newest candidate)")
    parser.add_argument("--allow-stale", action="store_true",
                        help="print a stale backend anyway (diagnostics only, never evidence)")
    parser.add_argument("--print", dest="field", required=True,
                        choices=("path", "suffix", "candidates"))
    args = parser.parse_args(argv)
    if args.field == "suffix":
        print(suffix())
        return 0
    if args.field == "candidates":
        for path in candidates(args.repo):
            print(path)
        return 0
    try:
        backend, stale = resolve(args.repo, args.backend, allow_stale=args.allow_stale)
    except BackendError as error:
        print(f"bridge-backend: {error}", file=sys.stderr)
        return 2
    if stale is not None:
        print(f"bridge-backend: WARNING: {backend} is STALE ({stale} is newer); "
              "--allow-stale results are not evidence", file=sys.stderr)
    print(backend)
    return 0


if __name__ == "__main__":
    sys.exit(main())
