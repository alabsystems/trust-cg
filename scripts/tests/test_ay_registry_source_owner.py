# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Synthetic source/checksum/graph controls; no registry or compiler executes."""
import copy
import gzip
import hashlib
import io
from pathlib import Path
import sys
import tarfile
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import ay_registry_source_owner as owner
from ay_exec_policy_owner import resolve
from bump_trust_ir_pin import matches_version

REV = "1" * 40
SOURCE = f"git+https://github.com/alabsystems/ay.git?rev={REV}#{REV}"
MANIFEST = b'''[package]
name = "nix"
version = "0.29.0"
[dependencies.libc]
version = "0.2"
[dependencies.bitflags]
version = "2"
[build-dependencies.cfg_aliases]
version = "0.2"
'''


def source_archive(data=MANIFEST, name=owner.NAME, version=owner.VERSION):
    stream = io.BytesIO()
    with tarfile.open(fileobj=stream, mode="w") as archive:
        entry = tarfile.TarInfo(f"{name}-{version}/Cargo.toml")
        entry.size = len(data)
        archive.addfile(entry, io.BytesIO(data))
    return gzip.compress(stream.getvalue(), mtime=0)


class Authority:
    revision = REV

    def __init__(self, checksum):
        self.docs = {
            "Cargo.toml": {"workspace": {"package": {"version": "0.28.0"},
                "members": ["crates/ay-sys"], "dependencies": {"nix": {
                    "version": "0.29", "default-features": False,
                    "features": ["process", "signal", "term"]}}}},
            "crates/ay-sys/Cargo.toml": {"package": {"name": "ay-sys", "version": {"workspace": True}}, "target": {
                "cfg(unix)": {"dependencies": {"nix": {"workspace": True}}}}},
            "Cargo.lock": {"package": [{"name": "nix", "version": "0.29.0",
                "source": owner.REGISTRY, "checksum": checksum}]},
        }

    def read(self, path):
        return self.docs[path]


class AyRegistrySourceOwnerTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="ay-nix-owner-")
        self.addCleanup(self.temporary.cleanup)
        self.home = Path(self.temporary.name)
        self.archive = self.home / "registry/cache/index.crates.io-fixture/nix-0.29.0.crate"
        self.archive.parent.mkdir(parents=True)
        self.archive.write_bytes(source_archive())
        self.checksum = hashlib.sha256(self.archive.read_bytes()).hexdigest()
        self.authority = Authority(self.checksum)

    def capture(self):
        return owner.from_ay(self.authority, (owner.SELECTION,), self.home)

    def graph(self):
        old = [{"name": name, "version": version, "source": owner.REGISTRY,
                "checksum": "a" * 64} for name, version in (
                    ("libc", "0.2.177"), ("bitflags", "2.13.0"), ("cfg_aliases", "0.2.1"))]
        old.append({"name": "ay-sys", "version": "0.27.0", "source": SOURCE})
        new = copy.deepcopy(old)
        new[-1].update(version="0.28.0", dependencies=["nix"])
        new.append({"name": "nix", "version": "0.29.0", "source": owner.REGISTRY,
                    "checksum": self.checksum, "dependencies": ["libc", "bitflags", "cfg_aliases"]})
        return old, new

    def test_actual_archive_bytes_and_immutable_ay_request_own_the_manifest(self):
        captured = self.capture()
        package = captured[owner.NAME, owner.VERSION]
        self.assertEqual((package.ay_revision, package.checksum), (REV, self.checksum))
        self.assertEqual(package.required, {"libc", "bitflags", "cfg_aliases"})
        old, new = self.graph()
        self.assertTrue(owner.validate_gain(old, new, captured,
                         lambda edge: resolve(edge, new), matches_version))

    def test_unknown_duplicate_or_missing_explicit_selection_refuses(self):
        for selection in ((), ("other@0.29.0",), (owner.SELECTION, owner.SELECTION)):
            with self.subTest(selection=selection), self.assertRaises(owner.OwnerError):
                owner.from_ay(self.authority, selection, self.home)

    def test_foreign_unix_owner_requirement_feature_or_checksum_refuses(self):
        mutations = [
            lambda d: d["Cargo.toml"]["workspace"]["package"].update(version="0.27.0"),
            lambda d: d["Cargo.toml"]["workspace"]["dependencies"]["nix"].update(version="0.31"),
            lambda d: d["Cargo.toml"]["workspace"]["dependencies"]["nix"].update(**{"default-features": True}),
            lambda d: d["crates/ay-sys/Cargo.toml"]["target"]["cfg(unix)"]["dependencies"]["nix"].update(optional=True),
            lambda d: d["Cargo.lock"]["package"][0].update(checksum="b" * 64),
        ]
        for index, mutate in enumerate(mutations):
            self.authority = Authority(self.checksum)
            mutate(self.authority.docs)
            with self.subTest(mutation=index), self.assertRaises(owner.OwnerError):
                self.capture()

    def test_changed_missing_or_foreign_archive_cannot_mint_the_source_owner(self):
        for data in (b"not an archive", source_archive(MANIFEST.replace(b'"0.29.0"', b'"0.31.0"'))):
            self.archive.write_bytes(data)
            with self.assertRaises(owner.OwnerError):
                self.capture()
        self.archive.unlink()
        with self.assertRaises(owner.OwnerError):
            self.capture()

    def test_gain_requires_exact_checksum_existing_dependency_nodes_and_actual_ay_edge(self):
        captured = self.capture()
        mutations = [
            lambda n: n[-1].update(checksum="c" * 64),
            lambda n: n[-1].update(dependencies=["libc", "bitflags"]),
            lambda n: n[0].update(version="0.3.0"),
            lambda n: n[-2].update(source=SOURCE.replace(REV, "2" * 40)),
            lambda n: n[-2].update(dependencies=[]),
            lambda n: n[-1].update(dependencies=["libc", "bitflags", "cfg_aliases", "new"]),
        ]
        for index, mutate in enumerate(mutations):
            old, new = self.graph()
            mutate(new)
            with self.subTest(mutation=index), self.assertRaises((owner.OwnerError, ValueError)):
                owner.validate_gain(old, new, captured, lambda edge: resolve(edge, new), matches_version)
        old, new = self.graph()
        with self.assertRaises(owner.OwnerError):
            owner.validate_gain(old, new, None, lambda edge: resolve(edge, new), matches_version)

    def test_existing_registry_node_remains_owned_by_the_ordinary_exact_graph_check(self):
        old, new = self.graph()
        old.append(copy.deepcopy(new[-1]))
        self.assertFalse(owner.validate_gain(old, new, None,
                         lambda edge: resolve(edge, new), matches_version))

    def test_new_cfg_aliases_requires_explicit_checksum_source_and_actual_new_nix_edge(self):
        data = source_archive(b'[package]\nname = "cfg_aliases"\nversion = "0.2.1"\n',
                              owner.REUSED_NAME, owner.REUSED_VERSION)
        path = self.archive.with_name("cfg_aliases-0.2.1.crate")
        path.write_bytes(data)
        checksum = hashlib.sha256(data).hexdigest()
        self.authority.docs["Cargo.lock"]["package"].append({"name": "cfg_aliases",
            "version": "0.2.1", "source": owner.REGISTRY, "checksum": checksum})
        captured = owner.from_ay(self.authority,
            (owner.SELECTION, owner.REUSED_SELECTION), self.home)
        old, new = self.graph()
        old = [row for row in old if row["name"] != "cfg_aliases"]
        new = [row for row in new if row["name"] != "cfg_aliases"]
        new.append({"name": "cfg_aliases", "version": "0.2.1",
                    "source": owner.REGISTRY, "checksum": checksum})
        gained = owner.validate_gain(old, new, captured, lambda edge: resolve(edge, new), matches_version)
        self.assertEqual({key[0] for key in gained}, {"nix", "cfg_aliases"})
        with self.assertRaises(owner.OwnerError):
            owner.validate_gain(old, new, self.capture(), lambda edge: resolve(edge, new), matches_version)
        new[-2]["dependencies"] = ["libc", "bitflags"]
        with self.assertRaises(owner.OwnerError):
            owner.validate_gain(old, new, captured, lambda edge: resolve(edge, new), matches_version)

    def test_resolution_constraints_preserve_every_preexisting_registry_owner(self):
        captured = self.capture()
        captured[owner.REUSED_NAME, owner.REUSED_VERSION] = None
        old, new = self.graph()
        old[2]["version"] = new[2]["version"] = "0.2.2"
        self.assertEqual(owner.resolution_constraints(old, new, captured, matches_version), [])
        no_cfg_before = [row for row in old if row["name"] != "cfg_aliases"]
        self.assertEqual(owner.resolution_constraints(no_cfg_before, new, captured, matches_version),
                         [("cfg_aliases", "0.2.2", "0.2.1")])
        new[2]["version"] = "1.0.0"
        with self.assertRaises(owner.OwnerError):
            owner.resolution_constraints(no_cfg_before, new, captured, matches_version)

    def wait_owner(self):
        data = source_archive(b'''[package]
name = "wait-timeout"
version = "0.2.1"
[target.'cfg(unix)'.dependencies.libc]
version = "0.2.56"
''', owner.WAIT_NAME, owner.WAIT_VERSION)
        path = self.archive.with_name("wait-timeout-0.2.1.crate")
        path.write_bytes(data)
        checksum = hashlib.sha256(data).hexdigest()
        self.authority.docs["Cargo.toml"]["workspace"]["dependencies"][owner.WAIT_NAME] = owner.WAIT_VERSION
        self.authority.docs["crates/ay-sys/Cargo.toml"]["dependencies"] = {
            owner.WAIT_NAME: {"workspace": True}}
        self.authority.docs["Cargo.lock"]["package"].append({"name": owner.WAIT_NAME,
            "version": owner.WAIT_VERSION, "source": owner.REGISTRY, "checksum": checksum})
        captured = owner.from_ay(self.authority, (owner.WAIT_SELECTION,), self.home)
        old = [{"name": "libc", "version": "0.2.177", "source": owner.REGISTRY,
                "checksum": "a" * 64}]
        new = copy.deepcopy(old) + [{"name": "ay-sys", "version": "0.28.0",
            "source": SOURCE, "dependencies": [owner.WAIT_NAME]},
            {"name": owner.WAIT_NAME, "version": owner.WAIT_VERSION,
             "source": owner.REGISTRY, "checksum": checksum, "dependencies": ["libc"]}]
        return captured, old, new

    def test_wait_timeout_requires_actual_primary_ay_request_and_source_checksum(self):
        captured, old, new = self.wait_owner()
        self.assertEqual(owner.validate_gain(old, new, captured,
            lambda edge: resolve(edge, new), matches_version),
            {(owner.WAIT_NAME, owner.WAIT_VERSION, owner.REGISTRY)})
        self.assertEqual(captured[owner.WAIT_NAME, owner.WAIT_VERSION].required, {"libc"})
        for raw in ({"workspace": True, "optional": True}, {"version": "0.2.1"}):
            self.authority.docs["crates/ay-sys/Cargo.toml"]["dependencies"][owner.WAIT_NAME] = raw
            with self.assertRaises(owner.OwnerError):
                owner.from_ay(self.authority, (owner.WAIT_SELECTION,), self.home)

    def test_wait_timeout_cannot_borrow_foreign_or_missing_ay_edge_or_libc(self):
        captured, old, original = self.wait_owner()
        for mutate in (
            lambda n: n[-1].update(dependencies=[]),
            lambda n: n[-1].update(checksum="f" * 64),
            lambda n: n[-2].update(dependencies=[]),
            lambda n: n[-2].update(source=SOURCE.replace(REV, "2" * 40)),
            lambda n: n[0].update(version="0.3.0"),
        ):
            new = copy.deepcopy(original)
            mutate(new)
            with self.assertRaises(owner.OwnerError):
                owner.validate_gain(old, new, captured, lambda edge: resolve(edge, new), matches_version)


    def clean_cfg_fixture(self):
        data = source_archive(b'[package]\nname = "cfg_aliases"\nversion = "0.2.2"\n',
                              "cfg_aliases", "0.2.2")
        archive = self.archive.with_name("cfg_aliases-0.2.2.crate")
        archive.write_bytes(data)
        clean = Authority(self.checksum)
        clean.revision = "9" * 40
        clean.repository = "alabsystems/clean"
        row = {"name": "cfg_aliases", "version": "0.2.2", "source": owner.REGISTRY,
               "checksum": hashlib.sha256(data).hexdigest()}
        clean.docs["Cargo.lock"]["package"] = [row]
        return clean, row, archive

    def capture_clean_cfg(self, clean, revision=None):
        return owner.from_ay(self.authority, (owner.SELECTION, owner.CLEAN_REUSED_SELECTION),
                             self.home, clean_authority=clean,
                             clean_revision=clean.revision if revision is None else revision)

    def test_primary_clean_cfg022_keeps_ay_request_owner_and_actual_nix_edge(self):
        clean, row, _ = self.clean_cfg_fixture()
        captured = self.capture_clean_cfg(clean)
        cfg = captured["cfg_aliases", "0.2.2"]
        self.assertEqual(cfg.ay_revision, REV)
        self.assertEqual(cfg.source_revision, clean.revision)
        old, new = self.graph()
        old = [r for r in old if r["name"] != "cfg_aliases"]
        new = [r for r in new if r["name"] != "cfg_aliases"] + [copy.deepcopy(row)]
        gained = owner.validate_gain(old, new, captured, lambda edge: resolve(edge, new), matches_version)
        self.assertEqual({key[:2] for key in gained}, {("nix", "0.29.0"), ("cfg_aliases", "0.2.2")})
        new[-2]["dependencies"].remove("cfg_aliases")
        with self.assertRaisesRegex(owner.OwnerError, "missing actual registry dependency"):
            owner.validate_gain(old, new, captured, lambda edge: resolve(edge, new), matches_version)

    def test_cfg022_requires_gained_nix_not_an_existing_requirer(self):
        clean, row, _ = self.clean_cfg_fixture()
        captured = self.capture_clean_cfg(clean)
        old, new = self.graph()
        old = [r for r in old if r["name"] != "cfg_aliases"]
        new = [r for r in new if r["name"] != "cfg_aliases"] + [copy.deepcopy(row)]
        old.append(copy.deepcopy(new[-2]))
        with self.assertRaisesRegex(owner.OwnerError, "actually gained nix build edge"):
            owner.validate_gain(old, new, captured, lambda edge: resolve(edge, new), matches_version)

    def test_cfg022_still_requires_actual_nix_manifest_semver(self):
        clean, row, _ = self.clean_cfg_fixture()
        captured = self.capture_clean_cfg(clean)
        old, new = self.graph()
        old = [r for r in old if r["name"] != "cfg_aliases"]
        new = [r for r in new if r["name"] != "cfg_aliases"] + [copy.deepcopy(row)]
        captured[owner.NAME, owner.VERSION].declarations["cfg_aliases"][0]["version"] = "0.1"
        with self.assertRaisesRegex(owner.OwnerError, "checksum-bound manifest"):
            owner.validate_gain(old, new, captured, lambda edge: resolve(edge, new), matches_version)

    def test_cfg022_requires_exact_selected_clean_owner_and_revision(self):
        clean, _, _ = self.clean_cfg_fixture()
        for repository, revision in [("foreign/clean", "9" * 40),
                                     ("alabsystems/clean", "8" * 40)]:
            clean.repository, clean.revision = repository, revision
            with self.subTest(repository=repository, revision=revision):
                with self.assertRaises(owner.OwnerError):
                    self.capture_clean_cfg(clean, revision="9" * 40)
        clean.repository, clean.revision = "alabsystems/clean", "9" * 40
        with self.assertRaises(owner.OwnerError):
            owner.from_ay(self.authority, (owner.SELECTION, owner.CLEAN_REUSED_SELECTION), self.home)

    def test_cfg022_missing_ambiguous_and_corrupt_checksum_refuse(self):
        clean, row, _ = self.clean_cfg_fixture()
        for rows in [[], [row, row], [dict(row, checksum="0" * 64)]]:
            with self.subTest(rows=rows):
                clean.docs["Cargo.lock"]["package"] = rows
                with self.assertRaises(owner.OwnerError):
                    self.capture_clean_cfg(clean)

    def test_cfg022_foreign_or_symlink_archive_refuses(self):
        clean, _, archive = self.clean_cfg_fixture()
        archive.write_bytes(b"foreign archive")
        with self.assertRaises(owner.OwnerError):
            self.capture_clean_cfg(clean)
        clean, _, archive = self.clean_cfg_fixture()
        actual = archive.with_suffix(".saved")
        archive.rename(actual)
        archive.symlink_to(actual)
        with self.assertRaises(owner.OwnerError):
            self.capture_clean_cfg(clean)


if __name__ == "__main__":
    unittest.main(verbosity=2)
