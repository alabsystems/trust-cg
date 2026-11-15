# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Caller-bound, pre-existing active local registry-patch source identities.

The caller's existing committed/protected-input owner must authenticate the
workspace manifest and the COMPLETE tracked file inventory/bytes below each
selected literal patch root, reject redirection/untracked alternate inputs,
and retain/recheck those snapshots for its transaction. This module does not
read an ambient worktree, authenticate Git, inspect Rust semantics or mint any
compiler, policy, provider, proof, resource or native permission. It reconstructs
active Cargo source identity from those supplied bytes and exact old lock rows.
"""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import PurePosixPath
try:
    import tomllib
except ModuleNotFoundError:
    from pip._vendor import tomli as tomllib

REGISTRY = "registry+https://github.com/rust-lang/crates.io-index"
# Keep the existing registry archive owner's 1024-entry / 16MiB source floor;
# apply it in aggregate across the explicitly selected local source roots.
MAX_FILES = 1024
MAX_SOURCE_BYTES = 16 * 1024 * 1024
MAX_WORKSPACE_BYTES = 1024 * 1024
MAX_MANIFEST_BYTES = 128 * 1024


class OwnerError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise OwnerError("AY active registry-patch source owner: " + message)


def _path(value):
    require(isinstance(value, str) and bool(value) and "\\" not in value
            and not PurePosixPath(value).is_absolute()
            and all(part not in ("", ".", "..") for part in value.split("/")),
            "requires canonical workspace-relative protected source paths")
    return value


def _document(data, limit):
    require(isinstance(data, bytes) and len(data) <= limit, "unsupported protected manifest bytes")
    try:
        return tomllib.loads(data.decode("utf-8"))
    except (UnicodeError, ValueError) as error:
        raise OwnerError("AY active registry-patch source owner: malformed protected manifest") from error


def _row_bytes(row):
    require(isinstance(row, dict) and isinstance(row.get("name"), str)
            and isinstance(row.get("version"), str)
            and isinstance(row.get("source"), (str, type(None))), "malformed locked package row")
    require(isinstance(row.get("dependencies", []), list)
            and all(isinstance(edge, str) for edge in row.get("dependencies", [])),
            "malformed locked dependency array")
    try:
        return json.dumps(row, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()
    except (TypeError, ValueError) as error:
        raise OwnerError("AY active registry-patch source owner: malformed lock snapshot") from error


def _identity(row):
    return row.get("name"), row.get("version"), row.get("source")


def _old_snapshot(rows):
    require(isinstance(rows, list), "requires the actual old locked package inventory")
    encoded = tuple(sorted(_row_bytes(row) for row in rows))
    require(len({_identity(row) for row in rows}) == len(rows), "duplicate old locked identity")
    return encoded


@dataclass(frozen=True)
class _Patch:
    name: str
    version: str
    row: bytes
    version_requirement: str | None
    manifest_path: str
    manifest_sha256: str
    source_book: tuple[tuple[str, str], ...]


@dataclass(frozen=True)
class _CheckedPatches:
    patches: tuple[_Patch, ...]
    active_names: frozenset[str]

    def require_edge(self, row, requirements, matches_version):
        """Apply actual declaration intersection and active-patch precedence."""
        require(callable(matches_version) and bool(requirements)
                and all(isinstance(item, str) for item in requirements),
                "requires the existing bounded declaration matcher")
        require(all(matches_version(item, row.get("version")) for item in requirements),
                "edge version violates actual immutable/archive declaration")
        patch = next((item for item in self.patches if item.name == row.get("name")), None)
        if patch is not None and any(matches_version(item, patch.version) for item in requirements):
            require(_row_bytes(row) == patch.row,
                    "compatible active patch requires the exact unchanged pre-existing local row")
            if patch.version_requirement is not None:
                require(matches_version(patch.version_requirement, row["version"]),
                        "local row violates active patch version constraint")
        else:
            require(patch is not None or row.get("name") not in self.active_names,
                    "active registry patch requires explicit protected source selection")
            require(row.get("source") == REGISTRY,
                    "edge has no applicable active local registry-patch authority")


def _reconstruct(workspace_manifest, files, old_rows, selected):
    workspace = _document(workspace_manifest, MAX_WORKSPACE_BYTES)
    require(isinstance(selected, tuple) and bool(selected)
            and all(isinstance(name, str) and bool(name) for name in selected)
            and len(set(selected)) == len(selected), "requires distinct explicit patch selections")
    require(isinstance(files, dict) and all(isinstance(data, bytes) for data in files.values()),
            "requires protected source byte snapshots")
    for path in files:
        _path(path)
    tables = workspace.get("patch", {})
    require(isinstance(tables, dict) and set(tables) <= {"crates-io"}
            and isinstance(tables.get("crates-io", {}), dict),
            "requires the sole canonical crates-io patch-owner table")
    active = tables.get("crates-io", {})
    active_names = [raw.get("package", alias) if isinstance(raw, dict) else alias
                    for alias, raw in active.items()]
    require(all(isinstance(name, str) and bool(name) for name in active_names),
            "malformed active registry patch package name")
    active_names = frozenset(active_names)
    result = []
    roots = set()
    count = total = 0
    for name in selected:
        entries = [(alias, raw) for alias, raw in active.items()
                   if isinstance(raw, dict) and raw.get("package", alias) == name]
        require(len(entries) == 1, "missing or ambiguous selected active registry patch")
        alias, raw = entries[0]
        require(set(raw) <= {"path", "package", "version"}
                and isinstance(raw.get("path"), str)
                and ("version" not in raw or isinstance(raw["version"], str)),
                "requires the actual local path patch without foreign source authority")
        root = _path(raw["path"])
        require(root not in roots and not any(root.startswith(other + "/")
                or other.startswith(root + "/") for other in roots), "overlapping selected patch roots")
        roots.add(root)
        manifest_path = root + "/Cargo.toml"
        require(manifest_path in files and root + "/Targo.toml" not in files,
                "missing protected package manifest or unsupported alternate manifest")
        data = files[manifest_path]
        document = _document(data, MAX_MANIFEST_BYTES)
        package = document.get("package", {})
        require(isinstance(package, dict) and package.get("name") == name
                and isinstance(package.get("version"), str) and bool(package["version"])
                and "workspace" not in package, "foreign or inherited local patch package identity")
        version = package["version"]
        local = [row for row in old_rows if _identity(row) == (name, version, None)]
        require(len(local) == 1 and set(local[0]) <= {"name", "version", "dependencies"},
                "requires one exact pre-existing source-absent local lock row")
        library = document.get("lib", {})
        require(isinstance(library, dict), "malformed local library target")
        target = _path(library.get("path", "src/lib.rs"))
        require(root + "/" + target in files, "missing protected actual local library source")
        build = package.get("build")
        require(build is None or build is False or isinstance(build, str), "unsupported local build target")
        if isinstance(build, str):
            require(root + "/" + _path(build) in files, "missing protected declared build source")
        entries = [(path, content) for path, content in files.items() if path.startswith(root + "/")]
        count += len(entries)
        total += sum(len(content) for _, content in entries)
        require(count <= MAX_FILES and total <= MAX_SOURCE_BYTES, "protected source-book bound exceeded")
        book = tuple(sorted((path, hashlib.sha256(content).hexdigest()) for path, content in entries))
        result.append(_Patch(name, version, _row_bytes(local[0]), raw.get("version"),
                             manifest_path, hashlib.sha256(data).hexdigest(), book))
    return _CheckedPatches(tuple(result), active_names)


@dataclass(frozen=True)
class ActiveRegistryPatches:
    """Immutable source snapshots, not a trusted name/identity approval list.

    Construct with from_protected_inputs. Consumers reconstruct the active
    identities from these bytes and bind the actual previous package inventory.
    Source-file protection/completeness remains the caller's existing owner.
    """
    workspace_manifest: bytes
    protected_files: tuple[tuple[str, bytes], ...]
    previous: tuple[bytes, ...]
    selected: tuple[str, ...]

    def validate(self, old_rows, new_rows):
        require(_old_snapshot(old_rows) == self.previous, "foreign or changed old lock evidence")
        require(isinstance(self.protected_files, tuple)
                and len(dict(self.protected_files)) == len(self.protected_files),
                "ambiguous protected source snapshots")
        checked = _reconstruct(self.workspace_manifest, dict(self.protected_files), old_rows, self.selected)
        require(isinstance(new_rows, list), "malformed current locked package inventory")
        for patch in checked.patches:
            rows = [row for row in new_rows if _identity(row) == (patch.name, patch.version, None)]
            require(len(rows) == 1 and _row_bytes(rows[0]) == patch.row,
                    "selected local patch row or its old edges changed or disappeared")
        return checked


def from_protected_inputs(workspace_manifest, protected_files, old_rows, *, selected):
    """Reconstruct explicitly selected active paths from caller-authenticated bytes.

    protected_files supplies ALL tracked committed files below each literal
    selected root. The caller owns canonical filesystem/Git provenance, source
    inventory completeness and no-redirection/unchanged checks throughout its
    transaction. No arbitrary row/path approval or local-node gain is accepted.
    """
    previous = _old_snapshot(old_rows)
    checked = _reconstruct(workspace_manifest, protected_files, old_rows, selected)
    paths = {path for patch in checked.patches for path, _ in patch.source_book}
    captured = tuple(sorted((path, protected_files[path]) for path in paths))
    return ActiveRegistryPatches(bytes(workspace_manifest), captured, previous, selected)


def checked(active_patches, old_rows, new_rows):
    """Reconstruct a context against the actual caller inventories."""
    require(isinstance(active_patches, ActiveRegistryPatches),
            "requires source-bound ActiveRegistryPatches, not an approval mapping")
    return active_patches.validate(old_rows, new_rows)
