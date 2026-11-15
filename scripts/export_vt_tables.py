#!/usr/bin/env python3
"""Export VT-island inputs from committed aterm tables, without changing aterm.

The five-file pure table implementation is compiled verbatim from Git blobs;
uncommitted files and unrelated workspace dependencies are never substituted.
This is a developer evidence exporter, not a replacement aterm distribution.
The host compile runs on the installed Trust package's trustc in its explicit
unverified lane (`-Ztrust-verify=off`; scripts/trust_toolchain.py); there is
no stock rustc default.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


SCRIPTS = Path(__file__).resolve().parent
SOURCES = {
    "crates/aterm-parser/src/state.rs": "aterm/state.rs",
    "crates/aterm-parser/src/table/mod.rs": "aterm/table/mod.rs",
    "crates/aterm-parser/src/table/types.rs": "aterm/table/types.rs",
    "crates/aterm-parser/src/table/dcs_osc.rs": "aterm/table/dcs_osc.rs",
    "crates/aterm-grapheme/src/tables/width.rs": "aterm/width.rs",
}


def git(repo: Path, *args: str) -> bytes:
    return subprocess.run(
        ["git", "-C", str(repo), *args], check=True, capture_output=True, timeout=30,
    ).stdout


def snapshot(repo: Path, revision: str, directory: Path) -> tuple[str, dict]:
    commit = git(repo, "rev-parse", "--verify", "--end-of-options",
                 revision + "^{commit}").decode().strip()
    if not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", commit):
        raise ValueError("Git did not resolve a full commit identity")
    records = git(repo, "ls-tree", "-z", commit, "--", *SOURCES).split(b"\0")
    entries = {}
    for record in filter(None, records):
        metadata, name = record.split(b"\t", 1)
        mode, kind, blob = metadata.decode().split()
        if mode != "100644" or kind != "blob":
            raise ValueError(f"table source is not an ordinary source file: {name!r}")
        entries[name.decode()] = blob
    if entries.keys() != SOURCES.keys():
        raise ValueError("selected aterm commit lacks the supported five-file table layout")
    evidence = {}
    for source, destination in SOURCES.items():
        data = git(repo, "cat-file", "blob", entries[source])
        target = directory / destination
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        evidence[source] = {
            "git_blob": entries[source], "sha256": hashlib.sha256(data).hexdigest(),
        }
    return commit, evidence


# trustc refuses to run while any TRUST_CG_*/TCG_* control is in its
# environment ("... is an untracked Trust semantic/codegen control"), and the
# soundness gate that calls this exporter exports such controls for its tests.
# None of them concerns the export, so every bounded command runs without them.
UNTRACKED_CONTROL_PREFIXES = ("TRUST_CG_", "TCG_")


def bounded(command: list[str], directory: Path) -> bytes:
    environment = {name: value for name, value in os.environ.items()
                   if not name.startswith(UNTRACKED_CONTROL_PREFIXES)}
    # -I: no user site-packages or .pth file (OD-XHOST-GATE-CWD-20261025).
    return subprocess.run(
        [sys.executable, "-I", str(SCRIPTS / "run_with_timeout.py"),
         "--chdir", str(directory), "120", *command],
        check=True, capture_output=True, env=environment,
    ).stdout


def validate_dump(data: bytes, commit: str) -> dict:
    value = json.loads(data)
    if (list(value) != ["schema", "version", "aterm_commit", "vt", "width_runs"]
            or value["schema"] != "aterm.vt-islands.tables"
            or type(value["version"]) is not int or value["version"] != 1
            or value["aterm_commit"] != commit):
        raise ValueError("invalid table dump identity or schema")
    if len(value["vt"]) != 14:
        raise ValueError("VT dump must have 14 states")
    for row in value["vt"]:
        if len(row) != 256:
            raise ValueError("VT dump must have 256 cells per state")
        for cell in row:
            if (len(cell) != 2 or any(type(x) is not int for x in cell)
                    or not 0 <= cell[0] < 14 or not 0 <= cell[1] <= 255):
                raise ValueError("invalid VT transition")
    next_cp = 0
    for run in value["width_runs"]:
        if (len(run) != 3 or any(type(x) is not int for x in run)
                or run[0] != next_cp or not run[0] <= run[1] <= 0x10ffff
                or run[2] not in (0, 1, 2)):
            raise ValueError("invalid or noncontiguous width run")
        if run[0] <= 0xdfff and run[1] >= 0xd800 and run[2] != 1:
            raise ValueError("surrogates must have island width 1")
        next_cp = run[1] + 1
    if next_cp != 0x110000:
        raise ValueError("width runs do not cover the full code-point domain")
    return value


def publish_new(output: Path, data: bytes) -> None:
    # Hard-link a fully written sibling: atomic publication without replacing
    # an existing report, including a symlink or a concurrently created file.
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=output.parent, delete=False,
                                         prefix=f".{output.name}.") as handle:
            temporary = Path(handle.name)
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.link(temporary, output)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def trust_compiler() -> str:
    """The installed Trust package's trustc; no stock fallback."""
    sys.path.insert(0, str(SCRIPTS))
    import trust_toolchain  # noqa: PLC0415

    try:
        return trust_toolchain.resolve()["compiler"]
    except trust_toolchain.ToolchainError as error:
        raise ValueError(f"no installed Trust package resolves: {error}") from error


def export(repo: Path, revision: str, output: Path, rustc: str) -> dict:
    if os.path.lexists(output):
        raise ValueError(f"refusing to replace existing output: {output}")
    with tempfile.TemporaryDirectory(prefix="trust-cg-vt-export-") as temporary:
        directory = Path(temporary)
        commit, sources = snapshot(repo, revision, directory)
        wrapper = (SCRIPTS / "export_vt_tables.rs").read_bytes()
        (directory / "export.rs").write_bytes(wrapper)
        # Resolve a relative executable before changing the subprocess cwd.
        if os.path.dirname(rustc):
            rustc = str(Path(rustc).resolve())
        version = bounded([rustc, "--version", "--verbose"], directory).decode().strip()
        executable = directory / "export-tables"
        flags = ["-Ztrust-verify=off", "--edition=2024", "-C", "opt-level=2"]
        bounded([rustc, *flags, str(directory / "export.rs"),
                 "-o", str(executable)], directory)
        data = bounded([str(executable), commit], directory)
        value = validate_dump(data, commit)
        report = {
            "schema": "trust-cg.vt-table-export.v1", "aterm_commit": commit,
            "input_scope": "committed table implementation only; not the dirty worktree",
            "sources": sources, "rustc": version, "rustc_flags": flags,
            "driver_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "exporter_sha256": hashlib.sha256(wrapper).hexdigest(),
            "tables_sha256": hashlib.sha256(data).hexdigest(),
            "vt_cells": sum(map(len, value["vt"])),
            "width_runs": len(value["width_runs"]),
            "output": str(output.resolve()),
        }
        publish_new(output, data)
        return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument("--aterm", type=Path, required=True, help="local aterm Git repository")
    parser.add_argument("--revision", required=True, help="explicit committed aterm revision")
    parser.add_argument("--output", type=Path, required=True, help="new table dump; never overwritten")
    parser.add_argument("--rustc", default=None,
                        help="Trust trustc used for the host export "
                             "(default: the package scripts/trust_toolchain.py resolves)")
    args = parser.parse_args()
    try:
        rustc = args.rustc or trust_compiler()
        print(json.dumps(export(args.aterm, args.revision, args.output, rustc), indent=2))
    except subprocess.CalledProcessError as error:
        print(f"VT export command failed ({error.returncode}): "
              f"{error.stderr.decode(errors='replace')[-4000:]}", file=sys.stderr)
        return 1
    except (OSError, ValueError, TypeError, KeyError, subprocess.TimeoutExpired) as error:
        print(f"VT export failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
