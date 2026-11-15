"""Driver selection shared by the compile-apples attribution tools.

The bridge pins channel = "trust", so every tool compiles with the Trust compiler
that pin names; a backend built against it cannot load into a stock compiler.
scripts/trust_toolchain.py resolves the PATH trustc/targo package, or the package
trustc named by an explicit `--driver PATH` argument, and refuses the retired stock
nightly-2026-04-20 and any unidentified compiler. Compiles use Trust's explicit
unverified frontend lane (`compiler_flags`, i.e. -Ztrust-verify=off): the same
vanilla frontend these tools always measured, labelled diagnostic, with no
Trust-verified compilation claim.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

_SPEC = importlib.util.spec_from_file_location(
    "trust_cg_trust_toolchain", Path(__file__).resolve().parents[3] / "scripts" / "trust_toolchain.py")
TOOLCHAIN = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(TOOLCHAIN)


def resolve(driver: str | None = None) -> dict:
    """Resolve the pinned Trust compiler or exit; announce its identity on stderr."""
    try:
        record = TOOLCHAIN.resolve(driver)
    except TOOLCHAIN.ToolchainError as error:
        raise SystemExit(f"cannot resolve the pinned Trust compiler: {error}")
    print(f"driver: {TOOLCHAIN.summary(record)}", file=sys.stderr)
    return record


def resolve_from_argv(argv: list) -> dict:
    """Remove an explicit `--driver PATH` from positional argv, then resolve."""
    driver = None
    if "--driver" in argv:
        index = argv.index("--driver")
        if index + 1 >= len(argv):
            raise SystemExit("--driver needs a Trust package trustc path")
        driver = argv[index + 1]
        del argv[index:index + 2]
    return resolve(driver)
