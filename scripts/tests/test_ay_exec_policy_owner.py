# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Pure source/lock controls; no native policy is installed or observed."""
import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import ay_exec_policy_owner as owner

REV = "1" * 40
SOURCE = f"git+{owner.AY_URL}?rev={REV}#{REV}"


def manifest():
    return {"workspace": {}, "package": {
        "name": owner.NAME, "version": owner.VERSION, "edition": "2024",
        "license": "Apache-2.0 OR MIT", "publish": False,
        "description": "Source identity only; no resource or policy authority."},
        "dependencies": {"libc": "0.2"}}


def packages():
    return [
        {"name": "ay-sys", "version": "0.28.0", "source": SOURCE,
         "dependencies": [owner.NAME]},
        {"name": owner.NAME, "version": owner.VERSION, "source": SOURCE,
         "dependencies": ["libc"]},
        {"name": "libc", "version": "0.2.177", "source": owner.REGISTRY,
         "checksum": "a" * 64},
    ]


class Authority:
    def __init__(self):
        self.doc = manifest()
        self.alternate = None

    def read(self, path):
        assert path == owner.DIRECTORY + "/Cargo.toml"
        return self.doc

    def read_optional(self, path):
        assert path in (owner.DIRECTORY + "/Targo.toml", owner.DIRECTORY + "/build.rs")
        return self.alternate


class ExecPolicyOwnerTests(unittest.TestCase):
    def test_actual_independent_manifest_and_required_path_are_all_owed(self):
        authority = Authority()
        self.assertEqual(owner.immutable_version(authority, [owner.DIRECTORY],
                         owner.NAME, owner.DIRECTORY, False), owner.VERSION)
        for excludes, name, path, optional in (
            ([], owner.NAME, owner.DIRECTORY, False),
            ([owner.DIRECTORY], "other", owner.DIRECTORY, False),
            ([owner.DIRECTORY], owner.NAME, owner.DIRECTORY + "/child", False),
            ([owner.DIRECTORY], owner.NAME, "../" + owner.DIRECTORY, False),
            ([owner.DIRECTORY], owner.NAME, owner.DIRECTORY, True),
        ):
            with self.subTest(path=path, optional=optional), self.assertRaises(owner.OwnerError):
                owner.immutable_version(authority, excludes, name, path, optional)

    def test_foreign_workspace_targets_versions_and_dependencies_refuse(self):
        mutations = [
            lambda d: d.update(workspace={"members": ["child"]}),
            lambda d: d.update(lib={"path": "../foreign.rs"}),
            lambda d: d["package"].update(version="0.14.0"),
            lambda d: d["package"].update(workspace="../../"),
            lambda d: d["package"].update(build="build.rs"),
            lambda d: d["dependencies"].update(libc={"git": "https://invalid/libc"}),
            lambda d: d["dependencies"].update(extra="1"),
        ]
        for index, mutate in enumerate(mutations):
            authority = Authority()
            mutate(authority.doc)
            with self.subTest(mutation=index), self.assertRaises(owner.OwnerError):
                owner.immutable_version(authority, [owner.DIRECTORY], owner.NAME, owner.DIRECTORY, False)
        authority = Authority()
        authority.alternate = {}
        with self.assertRaises(owner.OwnerError):
            owner.immutable_version(authority, [owner.DIRECTORY], owner.NAME, owner.DIRECTORY, False)

    def test_exact_source_qualified_required_owner_and_libc_route(self):
        rows = packages()
        self.assertEqual(owner.locked_identity(rows, REV, "0.28.0"),
                         (owner.NAME, owner.VERSION, SOURCE))
        rows[0]["dependencies"] = [f"{owner.NAME} {owner.VERSION} ({SOURCE.split('#')[0]})"]
        rows.append({"name": owner.NAME, "version": owner.VERSION, "source": owner.REGISTRY})
        self.assertEqual(owner.locked_identity(rows, REV, "0.28.0"),
                         (owner.NAME, owner.VERSION, SOURCE))

    def test_missing_foreign_stale_duplicate_or_aliased_owner_rows_refuse(self):
        mutations = [
            lambda d: d[0].update(version="0.27.0"),
            lambda d: d[1].update(version="0.14.0"),
            lambda d: d[1].update(source=SOURCE.replace(REV, "2" * 40)),
            lambda d: d.append(copy.deepcopy(d[1])),
            lambda d: d[0].update(dependencies=[]),
            lambda d: d.pop(0),
            lambda d: d.append({"name": "other", "version": "1", "dependencies": [owner.NAME]}),
            lambda d: d[0].update(dependencies=[owner.NAME, owner.NAME]),
            lambda d: d[1].update(checksum="b" * 64),
        ]
        for index, mutate in enumerate(mutations):
            rows = packages()
            mutate(rows)
            with self.subTest(mutation=index), self.assertRaises(owner.OwnerError):
                owner.locked_identity(rows, REV, "0.28.0")
        with self.assertRaises(owner.OwnerError):
            owner.locked_identity(packages(), REV, "0.27.0")

    def test_sole_existing_registry_libc_edge_and_full_identity_are_required(self):
        mutations = [
            lambda d: d[1].update(dependencies=[]),
            lambda d: d[1].update(dependencies=["libc", "libc"]),
            lambda d: d[2].update(source=SOURCE),
            lambda d: d[2].update(version="0.3.0"),
            lambda d: d.append(copy.deepcopy(d[2])),
            lambda d: d[1].update(dependencies="libc"),
        ]
        for index, mutate in enumerate(mutations):
            rows = packages()
            mutate(rows)
            with self.subTest(mutation=index), self.assertRaises(owner.OwnerError):
                owner.locked_identity(rows, REV, "0.28.0")

    def test_absent_package_is_not_minted_for_older_epochs(self):
        rows = [{"name": "ay-sys", "version": "0.27.0", "source": SOURCE}]
        self.assertIsNone(owner.locked_identity(rows, REV, "0.27.0"))
        self.assertIsNone(owner.locked_identity([], REV, "0.28.0"))
        with self.assertRaises(owner.OwnerError):
            owner.locked_identity([None], REV, "0.28.0")


if __name__ == "__main__":
    unittest.main(verbosity=2)
