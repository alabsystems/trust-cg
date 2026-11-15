# Copyright 2026 Andrew Yates | Apache-2.0
"""Two synthetic integration controls; real caller/owner code, no native process."""
import copy
import gzip
import hashlib
import io
import os
from pathlib import Path
from types import SimpleNamespace
import tarfile
import tempfile
import unittest
from unittest.mock import Mock, patch

import bump_trust_ir_pin as bump
import ay_registry_source_owner as registry
import ay_exec_policy_owner as policy

IR_REV, CLEAN_REV, OLD_AY, AY_REV = (digit * 40 for digit in "2456")
AY_NAMES = ["ay", "ay-core", "ay-dpll", "ay-proof", "ay-frontend", "ay-translate", "ay-lean-bridge"]


def archive(name, version, manifest):
    out = io.BytesIO()
    with tarfile.open(fileobj=out, mode="w") as tar:
        member = tarfile.TarInfo(f"{name}-{version}/Cargo.toml")
        member.size = len(manifest)
        tar.addfile(member, io.BytesIO(manifest))
    return gzip.compress(out.getvalue(), mtime=0)


class PrimaryCleanCallerIntegrationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="primary-clean-callchain-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.cargo = self.root / "cargo"
        cache = self.cargo / "registry/cache/index.crates.io-synthetic"
        cache.mkdir(parents=True)
        payloads = {
            ("nix", "0.29.0"): b'[package]\nname="nix"\nversion="0.29.0"\n[build-dependencies.cfg_aliases]\nversion="0.2"\n',
            ("cfg_aliases", "0.2.2"): b'[package]\nname="cfg_aliases"\nversion="0.2.2"\n',
        }
        self.checksums = {}
        for (name, version), manifest in payloads.items():
            data = archive(name, version, manifest)
            (cache / f"{name}-{version}.crate").write_bytes(data)
            self.checksums[name] = hashlib.sha256(data).hexdigest()
        self.snapshot = {str(p.relative_to(self.root)): p.read_bytes() for p in self.root.rglob("*") if p.is_file()}
        dep = lambda url, rev, version: {"git": url, "rev": rev, "version": version}
        self.docs = {
            bump.IR_URL: {
                "Cargo.toml": {"workspace": {"package": {"version": "0.14.0"}}},
                "crates/trust-ir/Cargo.toml": {"package": {"name": "trust-ir", "version": {"workspace": True}},
                    "dependencies": {"clean-kernel": dep(bump.CLEAN_URL, CLEAN_REV, "0.9.0")}},
                "crates/trust-ir-build/Cargo.toml": {"package": {"name": "trust-ir-build", "version": {"workspace": True}},
                    "dependencies": {"clean-kernel": dep(bump.CLEAN_URL, CLEAN_REV, "0.9.0")}},
                "crates/trust-ir-ay/Cargo.toml": {"dependencies": {
                    name: dep(bump.AY_URL, AY_REV, "0.28.0") for name in ["ay", "ay-proof"]}},
            },
            bump.CLEAN_URL: {
                "Cargo.toml": {"workspace": {"package": {"version": "0.9.0"},
                    "dependencies": {name: dep(bump.AY_URL, AY_REV, "0.28.0") for name in AY_NAMES}}},
                "crates/clean-kernel/Cargo.toml": {"package": {"name": "clean-kernel", "version": {"workspace": True}}},
                "Cargo.lock": {"package": [{"name": "cfg_aliases", "version": "0.2.2", "source": registry.REGISTRY,
                    "checksum": self.checksums["cfg_aliases"]}]},
            },
            bump.AY_URL: {
                "Cargo.toml": {"workspace": {"package": {"version": "0.28.0"}, "members": ["crates/ay-sys"],
                    "exclude": [policy.DIRECTORY], "dependencies": {"nix": {"version": "0.29", "default-features": False,
                        "features": ["process", "signal", "term"]}}}},
                "crates/ay-sys/Cargo.toml": {"package": {"name": "ay-sys", "version": {"workspace": True}}, "target": {
                    "cfg(unix)": {"dependencies": {"nix": {"workspace": True}}},
                    'cfg(target_os = "macos")': {"dependencies": {policy.NAME: {"path": "../../" + policy.DIRECTORY}}}}},
                policy.DIRECTORY + "/Cargo.toml": {"workspace": {}, "package": {
                    "name": policy.NAME, "version": policy.VERSION, "edition": "2024", "license": "Apache-2.0 OR MIT",
                    "publish": False, "description": "Synthetic independent source owner; no execution authority."},
                    "dependencies": {"libc": "0.2"}},
                "Cargo.lock": {"package": [
                    {"name": "nix", "version": "0.29.0", "source": registry.REGISTRY, "checksum": self.checksums["nix"]},
                    # Deliberate decoy: selecting AY instead of primary Clean must not work.
                    {"name": "cfg_aliases", "version": "0.2.2", "source": registry.REGISTRY, "checksum": "f" * 64}]},
            },
        }
        self.state = SimpleNamespace(ir_packages={"trust-ir": "0.14.0", "trust-ir-build": "0.14.0"},
            clean_packages={"clean-kernel": "0.9.0"}, ay_packages={"ay-sys": "0.28.0"}, ay=OLD_AY, ay_version="0.28.0")
        self.commands = Mock(spec=bump.Commands)
        self.commands.run.side_effect = AssertionError("No native command is part of this source control")
        self.created = {}
        self.bad_identity = None

    def authority(self, commands, directory, url, revision):
        self.assertIs(commands, self.commands)
        self.assertEqual(revision, {bump.IR_URL: IR_REV, bump.CLEAN_URL: CLEAN_REV, bump.AY_URL: AY_REV}[url])
        test = self
        class SyntheticImmutableAuthority:
            def __init__(self):
                self.revision = revision
                self.repository = url.removeprefix("https://github.com/").removesuffix(".git")
                self.reads = []
                if url == bump.CLEAN_URL and test.bad_identity == "repository":
                    self.repository = "foreign/clean"
                if url == bump.CLEAN_URL and test.bad_identity == "revision":
                    self.revision = "e" * 40
            def read(self, relative):
                self.reads.append(relative)
                return copy.deepcopy(test.docs[url][relative])
            def read_optional(self, relative):
                self.reads.append(relative)
                return copy.deepcopy(test.docs[url].get(relative))
        value = SyntheticImmutableAuthority()
        self.created[url] = value
        return value

    def invoke(self):
        return bump.target_cohort(self.commands, self.root / "authority-snapshot", self.state, IR_REV,
            ay_revision=AY_REV, admit_registry=(registry.CLEAN_REUSED_SELECTION, registry.SELECTION))

    def test_primary_clean_object_and_exact_revision_cross_both_real_callers(self):
        original_validate = bump.validate_ay_target
        original_from_ay = registry.from_ay
        original_policy = policy.immutable_version
        home_before = os.environ.get("HOME")
        with patch.object(bump, "Authority", side_effect=self.authority), \
             patch.object(bump, "validate_ay_target", wraps=original_validate) as middle, \
             patch.object(registry, "from_ay", wraps=original_from_ay) as endpoint, \
             patch.object(policy, "immutable_version", wraps=original_policy) as policy_route, \
             patch.object(bump.os, "environ", {**os.environ, "CARGO_HOME": str(self.cargo)}):
            result = self.invoke()
        clean, ay = self.created[bump.CLEAN_URL], self.created[bump.AY_URL]
        middle.assert_called_once()
        endpoint.assert_called_once()
        for call in [middle.call_args, endpoint.call_args]:
            self.assertIs(call.kwargs["clean_authority"], clean)
            self.assertEqual(call.kwargs["clean_revision"], CLEAN_REV)
        self.assertIs(endpoint.call_args.args[0], ay)
        self.assertEqual(endpoint.call_args.args[1], (registry.CLEAN_REUSED_SELECTION, registry.SELECTION))
        self.assertEqual(endpoint.call_args.args[2], self.cargo)
        self.assertEqual(result.clean, CLEAN_REV)
        self.assertTrue(result.ay.exec_policy)
        policy_route.assert_called_once()
        self.assertIs(policy_route.call_args.args[0], ay)
        captured = result.ay.registry_owners["cfg_aliases", "0.2.2"]
        self.assertEqual((captured.source_revision, captured.ay_revision, captured.checksum),
                         (CLEAN_REV, AY_REV, self.checksums["cfg_aliases"]))
        self.assertIn("Cargo.lock", clean.reads)
        self.assertNotEqual(self.docs[bump.AY_URL]["Cargo.lock"]["package"][1]["checksum"], captured.checksum)
        self.commands.run.assert_not_called()
        self.assertEqual(os.environ.get("HOME"), home_before)
        self.assertEqual({str(p.relative_to(self.root)): p.read_bytes() for p in self.root.rglob("*") if p.is_file()}, self.snapshot)

    def test_mismatched_selected_primary_clean_refuses_through_real_owner_before_native(self):
        original_validate = bump.validate_ay_target
        original_from_ay = registry.from_ay
        for bad_identity in ["repository", "revision"]:
            self.bad_identity = bad_identity
            self.created = {}
            with self.subTest(identity=bad_identity), \
                 patch.object(bump, "Authority", side_effect=self.authority), \
                 patch.object(bump, "validate_ay_target", wraps=original_validate) as middle, \
                 patch.object(registry, "from_ay", wraps=original_from_ay) as endpoint, \
                 patch.object(bump.os, "environ", {**os.environ, "CARGO_HOME": str(self.cargo)}):
                with self.assertRaisesRegex(bump.Refusal, "authenticated selected primary Clean owner") as refused:
                    self.invoke()
                self.assertIsInstance(refused.exception.__cause__, registry.OwnerError)
            clean = self.created[bump.CLEAN_URL]
            middle.assert_called_once()
            endpoint.assert_called_once()
            self.assertIs(middle.call_args.kwargs["clean_authority"], clean)
            self.assertIs(endpoint.call_args.kwargs["clean_authority"], clean)
            self.assertEqual(middle.call_args.kwargs["clean_revision"], CLEAN_REV)
            self.assertEqual(endpoint.call_args.kwargs["clean_revision"], CLEAN_REV)
            # cfg_aliases is selected first, so bad identity refuses before any archive/lock resolution.
            self.assertNotIn("Cargo.lock", clean.reads)
            self.assertNotIn("Cargo.lock", self.created[bump.AY_URL].reads)
            self.commands.run.assert_not_called()
            self.assertEqual({str(p.relative_to(self.root)): p.read_bytes() for p in self.root.rglob("*") if p.is_file()}, self.snapshot)


if __name__ == "__main__":
    unittest.main(verbosity=2)
