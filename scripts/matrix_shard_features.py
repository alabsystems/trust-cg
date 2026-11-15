#!/usr/bin/env python3
"""Feature coverage of scripts/run_full_test_matrix.sh's shard plan.

Cargo silently skips a target whose ``required-features`` are not enabled:
``cargo test -p trust-cg-verify --tests`` builds and runs every integration
target EXCEPT ``core_byte_store`` and ``core_byte_writer``, which need
``core-byte-replay``, and reports success (TRUSTCG-20). A plan that names a
package, or even the target itself, therefore covers it only if the same shard
also enables every feature the target requires.

The matrix's shard-policy validator calls :func:`feature_gate_problems` with
its parsed plan and the workspace's ``cargo metadata``; the auto-shard
generator calls :func:`feature_args` for each target it assigns. Both are pure
functions of their arguments so scripts/tests/test_matrix_shard_features.py
can drive them with fixtures.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence


TARGET_SELECTORS = frozenset((
    "--bench", "--benches", "--bin", "--bins", "--doc", "--example",
    "--examples", "--lib", "--test", "--tests",
))


def enabled_features(args: Sequence[str]) -> tuple[set[str], bool]:
    """The features a ``cargo test`` argument list enables, and whether it
    passes ``--all-features``. Handles ``--features a,b``, ``--features "a b"``,
    ``--features=a`` and ``-F a``."""
    features: set[str] = set()
    every = False
    index = 0
    while index < len(args):
        arg = args[index]
        value = None
        if arg == "--all-features":
            every = True
        elif arg in ("--features", "-F") and index + 1 < len(args):
            value = args[index + 1]
            index += 1
        elif arg.startswith("--features="):
            value = arg.split("=", 1)[1]
        if value is not None:
            features.update(part for part in value.replace(",", " ").split() if part)
        index += 1
    return features, every


def selects_test_target(args: Sequence[str], name: str) -> bool:
    """Whether the shard's target selection includes integration target NAME."""
    if "--all-targets" in args or "--tests" in args:
        return True
    if not any(arg in TARGET_SELECTORS for arg in args):
        return True
    return any(arg == "--test" and args[index + 1] == name for index, arg in enumerate(args[:-1]))


def feature_gate_problems(
    shards: Iterable[tuple[str, str, Sequence[str]]],
    packages: Iterable[Mapping],
) -> list[str]:
    """Every feature-gated integration target no shard both selects and enables.

    ``shards`` are ``(crate, shard, cargo_args)``; ``packages`` are workspace
    packages from ``cargo metadata``. A package with no shard is reported by
    the matrix's own package check, not here.
    """
    shards = list(shards)
    problems = []
    for package in packages:
        crate = package["name"]
        crate_shards = [(shard, list(args)) for shard_crate, shard, args in shards if shard_crate == crate]
        if not crate_shards:
            continue
        for target in package.get("targets", []):
            required = set(target.get("required-features") or ())
            if not required or "test" not in target.get("kind", []) or not target.get("test", True):
                continue
            name = target["name"]
            covered = False
            for _, args in crate_shards:
                if not selects_test_target(args, name):
                    continue
                features, every = enabled_features(args)
                if every or required <= features:
                    covered = True
                    break
            if not covered:
                problems.append(
                    f"{crate}/{name} requires features {sorted(required)}, but no shard that "
                    "selects it enables them, so Cargo would skip it silently"
                )
    return problems


def feature_args(target: Mapping) -> list[str]:
    """``cargo test`` arguments that enable TARGET's required features."""
    required = sorted(target.get("required-features") or ())
    return ["--features", ",".join(required)] if required else []
