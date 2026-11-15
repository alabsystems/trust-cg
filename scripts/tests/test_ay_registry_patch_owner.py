# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Source/lock controls only; fixtures grant no compilation or native authority."""
import copy
import dataclasses
import hashlib
from pathlib import Path
import sys
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import ay_exec_policy_owner as execution
import ay_registry_patch_owner as patches
import ay_registry_source_owner as registry
from bump_trust_ir_pin import matches_version
import test_ay_registry_source_owner as archive_fixture

WORKSPACE = b'''[patch.crates-io]
libc = { path = "crates/local-libc" }
cfg_aliases = { path = "crates/local-cfg" }
bitflags = { path = "crates/local-bitflags" }
'''
SELECTED = ("libc", "cfg_aliases", "bitflags")


def files():
    result = {}
    for name, root, version in (("libc", "local-libc", "0.2.185"),
                                ("cfg_aliases", "local-cfg", "0.2.1"),
                                ("bitflags", "local-bitflags", "2.11.1")):
        base = "crates/" + root
        result[base + "/Cargo.toml"] = (f'[package]\nname = "{name}"\nversion = "{version}"\n').encode()
        result[base + "/src/lib.rs"] = b"// Source identity fixture, never compiled.\n"
        result[base + "/src/retained.rs"] = b"// Complete caller-authenticated tracked inventory.\n"
    return result


def old_rows():
    return [{"name": "libc", "version": "0.2.185", "dependencies": ["rustc-std-workspace-core"]},
            {"name": "cfg_aliases", "version": "0.2.1"},
            {"name": "cfg_aliases", "version": "0.1.1", "source": patches.REGISTRY, "checksum": "a" * 64},
            {"name": "bitflags", "version": "2.11.1", "dependencies": ["serde_core"]},
            {"name": "rustc-std-workspace-core", "version": "1.0.1", "source": patches.REGISTRY, "checksum": "b" * 64},
            {"name": "serde_core", "version": "1.0.228", "source": patches.REGISTRY, "checksum": "c" * 64}]


def context(rows=None, source_files=None, manifest=WORKSPACE, selected=SELECTED):
    return patches.from_protected_inputs(manifest, files() if source_files is None else source_files,
                                         old_rows() if rows is None else rows, selected=selected)


class ActiveRegistryPatchTests(unittest.TestCase):
    def test_actual_paths_manifests_full_rows_and_every_source_byte_are_bound(self):
        old = old_rows()
        captured = context(old)
        checked = captured.validate(copy.deepcopy(old), copy.deepcopy(old))
        self.assertEqual({p.name for p in checked.patches}, set(SELECTED))
        libc = next(p for p in checked.patches if p.name == "libc")
        self.assertEqual(libc.version, "0.2.185")
        self.assertIn(b"rustc-std-workspace-core", libc.row)
        self.assertEqual(dict(libc.source_book)["crates/local-libc/src/retained.rs"],
                         hashlib.sha256(files()["crates/local-libc/src/retained.rs"]).hexdigest())
        with self.assertRaises(dataclasses.FrozenInstanceError):
            captured.selected = ("other",)

    def test_missing_unselected_foreign_or_escaping_source_identity_refuses(self):
        for manifest, selected in ((WORKSPACE, ("other",)),
                (WORKSPACE.replace(b'crates/local-libc', b'../foreign'), SELECTED),
                (WORKSPACE.replace(b'crates/local-libc', b'/foreign'), SELECTED),
                (WORKSPACE.replace(b'crates/local-libc', b'crates/./local-libc'), SELECTED),
                (WORKSPACE.replace(b'crates/local-libc', b'crates/foreign'), SELECTED),
                (WORKSPACE.replace(b'path = "crates/local-libc"', b'git = "https://foreign.invalid/libc"'), SELECTED),
                (WORKSPACE.replace(b'path = "crates/local-libc"', b'path = "crates/local-libc", git = "https://foreign.invalid/libc"'), SELECTED)):
            with self.subTest(manifest=manifest), self.assertRaises(patches.OwnerError):
                context(manifest=manifest, selected=selected)

    def test_explicit_selection_and_protected_library_manifest_are_required(self):
        for selected in ((), ("libc", "libc"), ["libc"]):
            with self.subTest(selected=selected), self.assertRaises(patches.OwnerError):
                context(selected=selected)
        for missing in ("crates/local-libc/Cargo.toml", "crates/local-libc/src/lib.rs"):
            source = files()
            del source[missing]
            with self.subTest(missing=missing), self.assertRaises(patches.OwnerError):
                context(source_files=source)
        source = files()
        source["crates/local-libc/Targo.toml"] = b"[package]\n"
        with self.assertRaises(patches.OwnerError):
            context(source_files=source)

    def test_manifest_package_version_or_declared_target_cannot_be_borrowed(self):
        original = files()
        for replacement in (b'[package]\nname="foreign"\nversion="0.2.185"\n',
                b'[package]\nname="libc"\nversion="0.2.186"\n',
                b'[package]\nname="libc"\nversion.workspace=true\n',
                b'[package]\nname="libc"\nversion="0.2.185"\nworkspace="../foreign"\n',
                b'[package]\nname="libc"\nversion="0.2.185"\nbuild="missing.rs"\n',
                b'[package]\nname="libc"\nversion="0.2.185"\n[lib]\npath="../foreign.rs"\n'):
            source = dict(original)
            source["crates/local-libc/Cargo.toml"] = replacement
            with self.subTest(replacement=replacement), self.assertRaises(patches.OwnerError):
                context(source_files=source)

    def test_no_new_local_node_foreign_source_checksum_or_duplicate_old_identity(self):
        for mutate in (lambda rows: rows.pop(0),
                lambda rows: rows[0].update(source=patches.REGISTRY),
                lambda rows: rows[0].update(source=None),
                lambda rows: rows[0].update(checksum="a" * 64),
                lambda rows: rows[0].update(source="git+https://foreign.invalid/libc"),
                lambda rows: rows.append(copy.deepcopy(rows[0]))):
            rows = old_rows()
            mutate(rows)
            with self.subTest(rows=rows), self.assertRaises(patches.OwnerError):
                context(rows)

    def test_foreign_old_graph_and_changed_or_missing_local_row_edges_refuse(self):
        old = old_rows()
        captured = context(old)
        foreign = copy.deepcopy(old)
        foreign[-1]["checksum"] = "d" * 64
        with self.assertRaisesRegex(patches.OwnerError, "foreign or changed old lock"):
            captured.validate(foreign, old)
        for mutate in (lambda rows: rows.pop(0),
                lambda rows: rows[0].update(dependencies=[]),
                lambda rows: rows[0].update(version="0.2.186"),
                lambda rows: rows[0].update(source=None),
                lambda rows: rows.append(copy.deepcopy(rows[0]))):
            new = copy.deepcopy(old)
            mutate(new)
            with self.subTest(new=new), self.assertRaises(patches.OwnerError):
                captured.validate(old, new)
        with self.assertRaises(patches.OwnerError):
            patches.checked({"libc": ("libc", "0.2.185", None)}, old, old)

    def test_active_patch_is_mandatory_only_when_the_actual_declarations_admit_it(self):
        old = old_rows()
        checked = context(old).validate(old, old)
        checked.require_edge(old[0], ["0.2"], matches_version)
        checked.require_edge(old[2], ["0.1"], matches_version)
        registry_libc = {"name": "libc", "version": "0.2.177", "source": patches.REGISTRY}
        with self.assertRaisesRegex(patches.OwnerError, "compatible active patch"):
            checked.require_edge(registry_libc, ["0.2"], matches_version)
        with self.assertRaises(patches.OwnerError):
            checked.require_edge(old[1], ["0.1"], matches_version)
        with self.assertRaises(patches.OwnerError):
            checked.require_edge(old[0], ["0.2"], None)

    def test_actual_patch_version_constraint_is_additional_not_a_blanket_approval(self):
        manifest = WORKSPACE.replace(b'path = "crates/local-libc"',
                                     b'path = "crates/local-libc", version = "=0.2.184"')
        old = old_rows()
        with self.assertRaisesRegex(patches.OwnerError, "patch version constraint"):
            context(old, manifest=manifest).validate(old, old).require_edge(old[0], ["0.2"], matches_version)

    def test_source_bounds_refuse_before_source_hash_work(self):
        with mock.patch.object(patches, "MAX_SOURCE_BYTES", 1), \
             mock.patch.object(patches.hashlib, "sha256", side_effect=AssertionError("unpaid hash")):
            with self.assertRaisesRegex(patches.OwnerError, "source-book bound"):
                context()
        with mock.patch.object(patches, "MAX_FILES", 1):
            with self.assertRaisesRegex(patches.OwnerError, "source-book bound"):
                context()

    def execution_graph(self):
        old = old_rows()
        source = f"git+{execution.AY_URL}?rev={'1' * 40}#{'1' * 40}"
        new = copy.deepcopy(old) + [
            {"name": "ay-sys", "version": "0.28.0", "source": source,
             "dependencies": [execution.NAME]},
            {"name": execution.NAME, "version": execution.VERSION, "source": source,
             "dependencies": ["libc"]}]
        return old, new, context(old), source

    def test_exec_policy_requires_explicit_old_bound_patch_and_keeps_default_registry_only(self):
        old, new, captured, source = self.execution_graph()
        with self.assertRaises(execution.OwnerError):
            execution.locked_identity(new, "1" * 40, "0.28.0")
        self.assertEqual(execution.locked_identity(new, "1" * 40, "0.28.0",
                         active_patches=captured, previous_packages=old, matches_version=matches_version),
                         (execution.NAME, execution.VERSION, source))
        self.assertIsNone(execution.locked_identity(old, "1" * 40, "0.27.0"))

    def test_exec_policy_refuses_forged_missing_old_foreign_or_changed_row_evidence(self):
        old, new, captured, _ = self.execution_graph()
        for kwargs in ({"active_patches": {"libc": True}, "previous_packages": old, "matches_version": matches_version},
                {"active_patches": captured, "matches_version": matches_version},
                {"active_patches": captured, "previous_packages": old},
                {"active_patches": captured, "previous_packages": old[1:], "matches_version": matches_version}):
            with self.subTest(kwargs=kwargs.keys()), self.assertRaises(execution.OwnerError):
                execution.locked_identity(new, "1" * 40, "0.28.0", **kwargs)
        for mutate in (lambda rows: rows[0].update(dependencies=[]),
                       lambda rows: rows[0].update(source=patches.REGISTRY),
                       lambda rows: rows[-1].update(dependencies=["libc", "libc"]),
                       lambda rows: rows[-2].update(dependencies=[])):
            changed = copy.deepcopy(new)
            mutate(changed)
            with self.subTest(changed=changed), self.assertRaises(execution.OwnerError):
                execution.locked_identity(changed, "1" * 40, "0.28.0",
                    active_patches=captured, previous_packages=old, matches_version=matches_version)

    def registry_graph(self):
        fixture = archive_fixture.AyRegistrySourceOwnerTests()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        captured = fixture.capture()
        old, new = fixture.graph()
        replacements = {"libc": old_rows()[0], "cfg_aliases": old_rows()[1], "bitflags": old_rows()[3]}
        for rows in (old, new):
            for index, row in enumerate(rows):
                if row["name"] in replacements:
                    rows[index] = copy.deepcopy(replacements[row["name"]])
            rows.extend(copy.deepcopy(old_rows()[4:]))
        return fixture, old, new, captured, context(old)

    def test_checksum_owned_nix_can_reuse_only_exact_old_active_patch_rows(self):
        _, old, new, captured, local = self.registry_graph()
        resolver = lambda edge: execution.resolve(edge, new)
        with self.assertRaises(registry.OwnerError):
            registry.validate_gain(old, new, captured, resolver, matches_version)
        self.assertEqual(registry.validate_gain(old, new, captured, resolver, matches_version,
                         active_patches=local), {(registry.NAME, registry.VERSION, registry.REGISTRY)})
        self.assertEqual(new[0], old[0])
        self.assertEqual(new[2], old[2])

    def test_registry_gain_cannot_borrow_wrong_old_source_changed_row_or_checksum(self):
        _, old, original, captured, local = self.registry_graph()
        for mutate in (lambda rows: rows[0].update(dependencies=[]),
                       lambda rows: rows[1].update(source=patches.REGISTRY),
                       lambda rows: rows[2].update(version="2.11.2"),
                       lambda rows: rows[-3].update(checksum="f" * 64)):
            new = copy.deepcopy(original)
            mutate(new)
            with self.subTest(new=new), self.assertRaises((registry.OwnerError, ValueError)):
                registry.validate_gain(old, new, captured, lambda edge: execution.resolve(edge, new),
                                       matches_version, active_patches=local)
        with self.assertRaises(registry.OwnerError):
            registry.validate_gain(old[1:], original, captured,
                lambda edge: execution.resolve(edge, original), matches_version, active_patches=local)

    def omitted_registry_cfg_graph(self, gained):
        fixture, old, new, captured, _ = self.registry_graph()
        data = archive_fixture.source_archive(
            b'[package]\nname="cfg_aliases"\nversion="0.2.1"\n',
            registry.REUSED_NAME, registry.REUSED_VERSION)
        checksum = hashlib.sha256(data).hexdigest()
        (fixture.archive.with_name("cfg_aliases-0.2.1.crate")).write_bytes(data)
        fixture.authority.docs["Cargo.lock"]["package"].append({"name": "cfg_aliases",
            "version": "0.2.1", "source": registry.REGISTRY, "checksum": checksum})
        captured = registry.from_ay(fixture.authority,
            (registry.SELECTION, registry.REUSED_SELECTION), fixture.home)
        replacement = {"name": "cfg_aliases", "version": "0.2.1",
                       "source": registry.REGISTRY, "checksum": checksum}
        if not gained:
            old.append(copy.deepcopy(replacement))
        new.append(copy.deepcopy(replacement))
        nix = next(row for row in new if row["name"] == "nix")
        nix["dependencies"] = [edge if edge != "cfg_aliases" else
            f"cfg_aliases 0.2.1 ({registry.REGISTRY})" for edge in nix["dependencies"]]
        local = context(old, selected=("libc", "bitflags"))
        return old, new, captured, local

    def test_omitted_active_patch_cannot_fall_through_to_a_gained_registry_node(self):
        old, new, captured, local = self.omitted_registry_cfg_graph(True)
        with self.assertRaisesRegex(registry.OwnerError, "explicit protected source selection"):
            registry.validate_gain(old, new, captured,
                lambda edge: execution.resolve(edge, new), matches_version, active_patches=local)

    def test_omitted_active_patch_cannot_borrow_a_preexisting_registry_node(self):
        old, new, captured, local = self.omitted_registry_cfg_graph(False)
        with self.assertRaisesRegex(registry.OwnerError, "explicit protected source selection"):
            registry.validate_gain(old, new, captured,
                lambda edge: execution.resolve(edge, new), matches_version, active_patches=local)

    def test_unselected_source_requires_authentication_even_to_prove_version_exclusion(self):
        old = old_rows()
        checked = context(old, selected=("libc",)).validate(old, old)
        with self.assertRaisesRegex(patches.OwnerError, "explicit protected source selection"):
            checked.require_edge(old[2], ["0.1"], matches_version)
        full = context(old).validate(old, old)
        full.require_edge(old[2], ["0.1"], matches_version)

    def test_alternate_registry_patch_owner_cannot_be_silently_ignored(self):
        manifest = WORKSPACE + b'[patch."https://github.com/rust-lang/crates.io-index"]\nextra={path="crates/foreign"}\n'
        with self.assertRaisesRegex(patches.OwnerError, "sole canonical crates-io"):
            context(manifest=manifest)

    def test_new_local_cfg_aliases_cannot_be_gained_or_approved_by_name(self):
        _, old, new, captured, _ = self.registry_graph()
        without_cfg = [row for row in old if row["name"] != "cfg_aliases"]
        local = context(without_cfg, selected=("libc", "bitflags"))
        with self.assertRaises(registry.OwnerError):
            registry.validate_gain(without_cfg, new, captured,
                lambda edge: execution.resolve(edge, new), matches_version, active_patches=local)
        with self.assertRaises(registry.OwnerError):
            registry.validate_gain(old, new, captured,
                lambda edge: execution.resolve(edge, new), matches_version, active_patches={"cfg_aliases": True})


if __name__ == "__main__":
    unittest.main(verbosity=2)
