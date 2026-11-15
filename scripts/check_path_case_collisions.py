#!/usr/bin/env python3
"""Refuse tracked paths that a case-insensitive filesystem stores as one file.

macOS (APFS and HFS+ in their default configuration) and Windows compare path
components case-insensitively, and macOS also compares them after Unicode
normalization. Two tracked paths that differ only that way are one file in
such a checkout: git writes both, the second overwrites the first, and every
checkout shows one of them modified. That dirty tree is exactly what
hooks/pre-push refuses, so the collision blocks every push from macOS while a
case-sensitive Linux host commits it without complaint (ff4c27eca archived
``prior-readelf-S-lld-shared.txt.gz`` beside ``prior-readelf-s-lld-shared.txt.gz``;
74a753fdd renamed them).

``check_path_case_collisions.py [--root DIR] [--rev REV]`` lists the paths
tracked in DIR's index (default: this checkout), or in commit REV when given,
and fails on any two paths, or any path and a directory prefix of another
path, whose folded forms are equal. Folding is NFC normalization followed by
``str.casefold``. The same fold is exposed as ``collisions()`` for other
checkers. hooks/pre-push runs it on the pushed commit, and
scripts/tests/test_path_case_collisions.py runs it on the checkout inside the
release gate's python-unit-tests lane.

Exit status: 0 when no two tracked paths collide, 1 on a collision, 2 when the
tracked-path list cannot be read.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from collections.abc import Iterable
from pathlib import Path
import subprocess
import sys
import unicodedata


ROOT = Path(__file__).resolve().parents[1]


def fold(path: str) -> str:
    """The name a case-insensitive, normalization-insensitive filesystem sees."""
    return unicodedata.normalize("NFC", path).casefold()


def collisions(paths: Iterable[str]) -> list[list[str]]:
    """Every group of two or more distinct spellings that fold to one path.

    Directory prefixes are included, so ``Docs/a`` and ``docs/b`` collide on
    the ``Docs``/``docs`` directory even though the file names differ.
    """
    spellings: dict[str, set[str]] = defaultdict(set)
    for path in paths:
        parts = path.split("/")
        for end in range(1, len(parts) + 1):
            prefix = "/".join(parts[:end])
            spellings[fold(prefix)].add(prefix)
    groups = [sorted(names) for names in spellings.values() if len(names) > 1]
    # Report only the shortest colliding prefix: once `Docs` and `docs` collide,
    # every path beneath them collides too and adds nothing to the report.
    groups.sort(key=lambda names: (names[0].count("/"), names))
    reported: list[list[str]] = []
    for names in groups:
        if any(
            any(name.startswith(prefix + "/") for prefix in earlier for name in names)
            for earlier in reported
        ):
            continue
        reported.append(names)
    return reported


def tracked_paths(root: Path, rev: str | None = None) -> list[str]:
    command = ["git", "-C", str(root)]
    if rev is None:
        command += ["ls-files", "-z"]
    else:
        command += ["ls-tree", "-r", "-z", "--name-only", rev, "--"]
    listing = subprocess.run(command, check=True, capture_output=True)
    return [raw.decode("utf-8", "surrogateescape") for raw in listing.stdout.split(b"\0") if raw]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", type=Path, default=ROOT, help="git checkout to check")
    parser.add_argument("--rev", help="check the tree of this commit instead of the index")
    args = parser.parse_args(argv)
    try:
        paths = tracked_paths(args.root, args.rev)
    except (OSError, subprocess.CalledProcessError) as error:
        print(f"check_path_case_collisions: cannot list tracked paths in {args.root}: {error}", file=sys.stderr)
        return 2
    groups = collisions(paths)
    for names in groups:
        print(
            "check_path_case_collisions: these tracked paths are one file on a "
            "case-insensitive filesystem: " + ", ".join(names),
            file=sys.stderr,
        )
    if groups:
        print(
            "check_path_case_collisions: rename them to names that differ in more than "
            "case or Unicode normalization (rename every colliding spelling, not one).",
            file=sys.stderr,
        )
        return 1
    where = args.rev if args.rev is not None else "the index"
    print(f"check_path_case_collisions: {len(paths)} tracked paths in {where}, no case-insensitive collision")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
