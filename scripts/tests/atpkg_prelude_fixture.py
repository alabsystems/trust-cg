"""A fake Trust package behind atpkg launcher shims whose preludes lie.

scripts/trust_toolchain.py follows an atpkg launcher shim's final exec past a
shell prelude (DR-ATPKG-PRELUDE-SHIM-20261015). That is sound only while no
gate executes a PATH shim: a gate runs the package file the resolver names, or
the file `launcher_target` reads out of the shim. A gate test builds the
counter-example here: one package whose tools answer honestly, and PATH shims
to it that the resolver accepts but whose preludes log every call and answer
chosen questions falsely. A gate that executes a shim leaves a line in the log
and acts on the false answer.

Nothing here runs a real toolchain. The package tools are Python scripts
under the running interpreter; the shims are `#!/bin/sh` files.
"""

from __future__ import annotations

import json
from pathlib import Path
import sys


COMMIT = "5" * 40
HOST = "aarch64-unknown-linux-gnu"
# A stable release: a matrix that reads `--version` from the package keeps
# libtest's plain format, and one that reads a prelude answering "nightly"
# switches to JSON.
VERSION = "rustc 1.99.0 (555555555 2026-09-17) (trustc 0.1.0)"
TARGO_VERSION = "targo 1.99.0 (5555555 2026-09-17) (targo 0.1.0)"

PACKAGE_TOOL = f"#!{sys.executable}\n" + r'''import json
import os
from pathlib import Path
import sys

name = Path(sys.argv[0]).name
arguments = sys.argv[1:]
package = Path(sys.argv[0]).resolve().parent.parent
facts = json.loads((package / "facts.json").read_text())
if name == "targo":
    if arguments in (["--version"], ["--unverified", "--version"]):
        print(facts["targo_version"])
        sys.exit(0)
    if arguments[:1] == ["metadata"]:
        print(json.dumps(facts["metadata"]))
        sys.exit(0)
    if (arguments[:2] == ["--unverified", "rustc"]
            and arguments[-2:] == ["--", "--print=sysroot"]):
        # scripts/trust_toolchain.py asks through Targo's scheduled rustc unit;
        # this fixture has no compiler child, so answer the exact bounded query.
        print(package)
        sys.exit(0)
    sys.exit(64)
if arguments == ["-vV"]:
    print(facts["version"])
    print("binary: trustc")
    print("commit-hash: " + facts["commit"])
    print("commit-date: 2026-09-17")
    print("host: " + facts["host"])
    print("release: 1.99.0")
    sys.exit(0)
if arguments in (["--version"], ["-V"]):
    print(facts["version"])
    sys.exit(0)
if arguments == ["--print", "sysroot"]:
    print(package)
    sys.exit(0)
sys.exit(64)
'''


def make_package(root: Path, *, metadata: dict | None = None, host: str = HOST,
                 version: str = VERSION, targo_version: str = TARGO_VERSION) -> Path:
    """An installed Trust package at `root` that scripts/trust_toolchain.py
    resolves for either purpose; `targo metadata` prints `metadata`."""
    bindir = root / "bin"
    bindir.mkdir(parents=True)
    (root / "facts.json").write_text(json.dumps({
        "host": host, "commit": COMMIT, "version": version, "targo_version": targo_version,
        "metadata": metadata if metadata is not None else {"packages": [], "workspace_members": []},
    }))
    for name in ("trustc", "targo"):
        tool = bindir / name
        tool.write_text(PACKAGE_TOOL)
        tool.chmod(0o755)
    libdir = root / "lib" / "rustlib" / host / "lib"
    libdir.mkdir(parents=True)
    for component in ("rustc_middle", "rustc_codegen_ssa"):
        (libdir / f"lib{component}-fixture.rmeta").touch()
    return root


def lying_shim(path: Path, target: Path, log: Path, lies: dict[str, str] | None = None) -> Path:
    """An atpkg launcher shim the resolver accepts, to `target`.

    Its prelude appends "<name> <arguments>" to `log`, then answers each
    `lies` pattern (a shell `case` pattern over "$*") with that text, one
    printed line per line of it, and exits 0, before the final exec. The text
    must not contain a single quote."""
    lines = ["#!/bin/sh", "# atpkg shim, with a prelude that lies.",
             f"printf '%s\\n' \"{path.name} $*\" >> '{log}'"]
    if lies:
        lines.append('case "$*" in')
        for pattern, answer in lies.items():
            assert "'" not in answer, answer
            pattern = pattern.replace(" ", "\\ ")
            printed = " ".join(f"'{line}'" for line in answer.split("\n"))
            lines.append(f"  {pattern}) printf '%s\\n' {printed}; exit 0 ;;")
        lines.append("esac")
    lines.append(f"exec '{target}' \"$@\"")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n")
    path.chmod(0o755)
    return path


def logged(log: Path) -> list[str]:
    """The calls the shims' preludes logged: empty when no shim ever ran."""
    return log.read_text().splitlines() if log.exists() else []
