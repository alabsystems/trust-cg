# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""One independently owned source package in AY's selected library graph.

This validates source ownership and locked edges only. It grants no admission,
installed policy, resource, execution, proof or platform-permission authority.
"""
from __future__ import annotations

import re

import ay_registry_patch_owner as patch_owner


AY_URL = "https://github.com/alabsystems/ay.git"
REGISTRY = "registry+https://github.com/rust-lang/crates.io-index"
NAME = "trust-exec-policy"
VERSION = "0.13.0"
DIRECTORY = "vendor/trust-exec-policy"


class OwnerError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise OwnerError("AY exec-policy source owner: " + message)


def immutable_version(authority, excludes, name, resolved, optional):
    require(name == NAME and resolved == DIRECTORY and DIRECTORY in excludes and not optional,
            "requires the exact excluded, required package path")
    require(authority.read_optional(DIRECTORY + "/Targo.toml") is None
            and authority.read_optional(DIRECTORY + "/build.rs") is None,
            "alternate manifest or build script is unsupported")
    doc = authority.read(DIRECTORY + "/Cargo.toml")
    require(set(doc) == {"workspace", "package", "dependencies"} and doc["workspace"] == {},
            "requires its own empty explicit workspace and no redirected targets")
    package = doc["package"]
    require(isinstance(package, dict)
            and set(package) == {"name", "version", "edition", "license", "publish", "description"}
            and package["name"] == NAME and package["version"] == VERSION
            and package["edition"] == "2024" and package["publish"] is False
            and package["license"] == "Apache-2.0 OR MIT"
            and isinstance(package["description"], str),
            "unexpected independent package identity")
    require(doc["dependencies"] == {"libc": "0.2"}, "unexpected package dependency closure")
    return VERSION


def identity(row):
    return row.get("name"), row.get("version"), row.get("source")


def resolve(raw, packages):
    match = re.fullmatch(r"([^ ()]+)(?: ([^ ()]+))?(?: \(([^()]+)\))?", raw) if isinstance(raw, str) else None
    require(match is not None, "malformed dependency")

    def source_matches(value):
        requested = match[3]
        if requested is None or requested == value:
            return True
        if not isinstance(value, str) or not requested.startswith("git+") or "#" in requested:
            return False
        base, separator, precise = value.rpartition("#")
        return bool(separator) and base == requested and re.fullmatch(r"[0-9a-f]{40}", precise) is not None

    selected = [row for row in packages if row.get("name") == match[1]
                and (match[2] is None or row.get("version") == match[2])
                and source_matches(row.get("source"))]
    require(len(selected) == 1, "ambiguous or missing dependency")
    return selected[0]


def locked_identity(packages, revision, ay_version, *, active_patches=None,
                    previous_packages=None, matches_version=None):
    """Check the actual required ay-sys -> policy -> existing libc route.

    Older AY epochs may lack the policy altogether. Presence never follows
    from a name alone: both selected rows and the exact incoming edge are owed.
    Other same-named packages at other sources remain independently owned.
    An explicit active_patches context additionally requires the actual prior
    package inventory and the caller's existing bounded version matcher.
    """
    require(isinstance(packages, list) and all(isinstance(row, dict) for row in packages),
            "malformed package inventory")
    require(all(isinstance(row.get("dependencies", []), list)
                and all(isinstance(edge, str) for edge in row.get("dependencies", []))
                for row in packages), "malformed locked dependency array")
    source = f"git+{AY_URL}?rev={revision}#{revision}"
    vendors = [row for row in packages if row.get("name") == NAME
               and str(row.get("source", "")).startswith("git+" + AY_URL)]
    owners = [row for row in packages if row.get("name") == "ay-sys" and row.get("source") == source]
    incoming = []
    for row in packages:
        for edge in row.get("dependencies", []):
            if isinstance(edge, str) and edge.split(" ", 1)[0] == NAME:
                target = resolve(edge, packages)
                if target in vendors:
                    incoming.append((row, target))
    if not vendors and not incoming:
        return None
    require(ay_version == "0.28.0" and len(vendors) == 1 and len(owners) == 1,
            "unsupported AY version or duplicate/missing actual owner")
    vendor, owner = vendors[0], owners[0]
    require(identity(vendor) == (NAME, VERSION, source)
            and owner.get("version") == ay_version,
            "source/version disagrees with the selected AY owner")
    require(len(incoming) == 1 and incoming[0][0] is owner and incoming[0][1] is vendor,
            "requires exactly the actual ay-sys incoming edge")
    require(set(vendor) == {"name", "version", "source", "dependencies"},
            "unexpected package metadata")
    edges = vendor["dependencies"]
    require(isinstance(edges, list) and len(edges) == 1, "requires the sole libc dependency")
    libc = resolve(edges[0], packages)
    compatible = (libc.get("name") == "libc" and isinstance(libc.get("version"), str)
                  and re.fullmatch(r"0\.2\.(?:0|[1-9][0-9]*)", libc["version"]) is not None)
    if active_patches is None:
        require(compatible and libc.get("source") == REGISTRY,
                "requires a canonical registry libc 0.2 package")
    else:
        require(compatible, "requires the actual compatible libc 0.2 package")
        try:
            checked = patch_owner.checked(active_patches, previous_packages, packages)
            checked.require_edge(libc, ["0.2"], matches_version)
        except patch_owner.OwnerError as error:
            raise OwnerError("AY exec-policy source owner: " + str(error)) from error
    return identity(vendor)
