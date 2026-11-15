"""scripts/soundness_attestation.py: records, verification, anchoring and policies.

The records come from a real `soundness_check.sh --attest` run in a throwaway
constellation (scripts/tests/soundness_fixture.py: fake toolchain, fake x86-64
host behind a fake ssh). Every failure mode is then produced by editing a copy
of a real record, never by hand-writing a record from scratch, so a check that
stops looking at a field fails here.
"""

from __future__ import annotations

import copy
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import atpkg_prelude_fixture as SHIMS  # noqa: E402
import soundness_fixture as fixture  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("soundness_attestation", ROOT / "scripts/soundness_attestation.py")
SA = importlib.util.module_from_spec(SPEC)
sys.modules["soundness_attestation"] = SA
SPEC.loader.exec_module(SA)

HOST_X86 = "x86_64-unknown-linux-gnu"
HOST_LOCAL = "aarch64-apple-darwin"


def native_host(**changes):
    host = {"machine": "x86_64", "system": "Linux", "translated": False,
            "cpuinfo": {"vendor_id": "GenuineIntel", "model name": "Intel(R) Xeon(R)"},
            "cpuid": {"available": True, "vendor": "GenuineIntel", "brand": "Intel(R) Xeon(R)",
                      "hypervisor": False, "hypervisor_vendor": "", "sse41": True}}
    for key, value in changes.items():
        if key.startswith("cpuid_"):
            host["cpuid"][key[6:]] = value
        elif key.startswith("cpuinfo_"):
            host["cpuinfo"][key[8:]] = value
        else:
            host[key] = value
    return host


class RecordJsonAdmissionTests(unittest.TestCase):
    BAD = [b'{"scope":"portable","scope":"full"}',
           b'{"legs":[{"status":"FAIL","status":"PASS"}]}',
           b'{"scope":"full","scope":"full"}',
           br'{"\u0073cope":"full","scope":"full"}',
           b'{"value":NaN}', b'{"value":Infinity}', b'{"value":-Infinity}',
           b'{"value":1e9999}', b'{"note":"\xff"}',
           '{"scope":"full"}'.encode("utf-16"),
           b'[]', b'null', b'false', b'42', b'"record"', b'{} {}',
           b'{"value":' + b'[' * 2000 + b'0' + b']' * 2000 + b'}']

    def test_record_reader_refuses_ambiguous_or_nonstandard_documents(self):
        for payload in self.BAD:
            with self.subTest(payload=payload), \
                    mock.patch.object(SA, "run", return_value=subprocess.CompletedProcess([], 0, payload, b"")), \
                    self.assertRaises(SA.Malformed):
                SA.load_record(Path.cwd(), "a" * 40)

    def test_valid_record_bytes_keep_nested_objects_and_finite_numbers(self):
        payload = b'{"a":{"status":"PASS"},"b":{"status":"FAIL"},"value":1.25,"count":3}'
        with mock.patch.object(SA, "run", return_value=subprocess.CompletedProcess([], 0, payload, b"")):
            self.assertEqual(SA.load_record(Path.cwd(), "a" * 40), json.loads(payload))

    @staticmethod
    def nested_record(depth, kind):
        value = 0
        for index in range(depth - 1):
            value = [value] if kind == "array" or (kind == "mixed" and index % 2) else {"x": value}
        return json.dumps({"value": value}).encode()

    def test_record_depth_limit_is_explicit_and_portable(self):
        for kind in ("array", "object", "mixed"):
            with self.subTest(kind=kind):
                allowed = self.nested_record(SA.MAX_RECORD_JSON_DEPTH, kind)
                self.assertEqual(SA.record_document(allowed, "boundary"), json.loads(allowed))
                refused = self.nested_record(SA.MAX_RECORD_JSON_DEPTH + 1, kind)
                with self.assertRaisesRegex(SA.Malformed, "JSON nesting exceeds"):
                    SA.record_document(refused, "over boundary")

    def test_writer_refuses_one_over_depth_limit_before_git(self):
        with tempfile.TemporaryDirectory() as directory:
            args = SA.build_parser().parse_args(["write", "--record-dir", directory])
            for kind in ("array", "object", "mixed"):
                Path(directory, "attestation.json").write_bytes(
                    self.nested_record(SA.MAX_RECORD_JSON_DEPTH + 1, kind))
                with self.subTest(kind=kind), mock.patch.object(SA, "run") as run:
                    with self.assertRaises(SA.Malformed):
                        SA.cmd_write(args)
                    run.assert_not_called()

    def test_nesting_budget_ignores_escaped_quotes_and_delimiters_in_strings(self):
        value = {"note": '"' + "[{" * 2000 + '\\"' + "}]" * 2000}
        payload = json.dumps(value).encode()
        self.assertEqual(SA.record_document(payload, "fixture"), value)

    def test_writer_refuses_missing_identity_before_any_git_command(self):
        with tempfile.TemporaryDirectory() as directory:
            args = SA.build_parser().parse_args(["write", "--record-dir", directory])
            for value in ({}, {"subject": {}}, {"host": {"triple": HOST_LOCAL}}):
                Path(directory, "attestation.json").write_text(json.dumps(value))
                with self.subTest(value=value), mock.patch.object(SA, "run") as run:
                    with self.assertRaises(SA.Refused):
                        SA.cmd_write(args)
                    run.assert_not_called()

    def test_writer_refuses_bad_documents_before_any_git_command(self):
        with tempfile.TemporaryDirectory() as directory:
            args = SA.build_parser().parse_args(["write", "--record-dir", directory])
            for payload in self.BAD:
                Path(directory, "attestation.json").write_bytes(payload)
                with self.subTest(payload=payload), mock.patch.object(SA, "run") as run:
                    with self.assertRaises(SA.Malformed):
                        SA.cmd_write(args)
                    run.assert_not_called()


class RecordShapeTests(unittest.TestCase):
    @staticmethod
    def base():
        return {"schema": SA.SCHEMA, "subject": {"commit": "a" * 40, "tree": "b" * 40},
                "host": {"triple": HOST_LOCAL, "machine": "aarch64", "system": "Darwin"},
                "scope": "full", "inventory": {"sha256": "c" * 64}, "dependencies": {},
                "toolchains": {"trust": {"overlay": None}}, "executed": {},
                "environment": {"settings": []}, "imported": [],
                "legs": [{"id": "example", "status": "PASS"}]}

    @classmethod
    def mutants(cls):
        cases = [("subject", []), ("subject.commit", []), ("host", "host"),
                 ("host.triple", 42), ("host.machine", []), ("host.cpuid", []),
                 ("host.cpuid", {"brand": None}), ("host.cpuinfo", {"model name": []}),
                 ("inventory", None), ("dependencies", []), ("dependencies.aterm", []),
                 ("toolchains", []), ("toolchains.rustc", {}), ("toolchains.trust", []),
                 ("toolchains.trust.overlay", "overlay"), ("executed.ay", "ay"),
                 ("environment", []), ("environment.settings", [None]),
                 ("environment.settings", [{"name": []}]), ("legs", None),
                 ("legs", ["leg"]), ("legs", [{"id": [], "status": "PASS"}]),
                 ("legs", [{"id": "leg"}]), ("imported", {}),
                 ("imported", [{"triple": [], "record": "d" * 40}]),
                 ("imported", [{"triple": HOST_X86, "record": "--all"}]),
                 ("imported", [{"triple": "bad triple", "record": "d" * 40}]), ("scope", [])]
        for path, value in cases:
            record = cls.base()
            parent = record
            keys = path.split(".")
            for key in keys[:-1]:
                parent = parent.setdefault(key, {})
            parent[keys[-1]] = value
            yield path, record

    def test_malformed_shapes_never_reach_writer_git(self):
        with tempfile.TemporaryDirectory() as directory:
            args = SA.build_parser().parse_args(["write", "--record-dir", directory])
            for path, record in self.mutants():
                Path(directory, "attestation.json").write_text(json.dumps(record))
                with self.subTest(path=path, record=record), mock.patch.object(SA, "run") as run:
                    with self.assertRaises(SA.Malformed):
                        SA.cmd_write(args)
                    run.assert_not_called()

    def test_reader_checks_the_same_shapes_before_semantic_checks(self):
        for path, record in self.mutants():
            with self.subTest(path=path, record=record), \
                    mock.patch.object(SA, "git", return_value="d" * 40 + " " + "a" * 40), \
                    mock.patch.object(SA, "run", return_value=subprocess.CompletedProcess(
                        [], 0, json.dumps(record).encode(), b"")), \
                    self.assertRaises(SA.Malformed):
                SA.check_record(Path.cwd(), "d" * 40, "a" * 40, HOST_LOCAL)

    def test_optional_absence_and_nullable_legacy_evidence_keep_their_semantics(self):
        record = self.base()
        SA.record_shape(record, "test")
        for key in ("toolchains", "executed", "environment", "imported"):
            record.pop(key)
        SA.record_shape(record, "test")
        record["host"].update(cpuid=None, cpuinfo=None)
        record["dependencies"]["aterm"] = None
        SA.record_shape(record, "test")


class FetchImportTests(unittest.TestCase):
    """Real Git transport objects; no compiler or attestation verdict is mocked."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="attestation-fetch-")
        self.addCleanup(self.temporary.cleanup)
        self.origin = Path(self.temporary.name) / "origin.git"
        subprocess.run(["git", "init", "--quiet", "--bare", "--initial-branch=main", str(self.origin)], check=True)
        tree = SA.git(self.origin, "mktree", input_bytes=b"").strip()

        def commit(message, *parents):
            return SA.git(self.origin, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                          "commit-tree", tree, *parents, "-m", message).strip()

        self.commit = commit("subject")
        SA.git(self.origin, "update-ref", "refs/heads/main", self.commit)
        self.refs = {triple: commit(triple, "-p", self.commit) for triple in (HOST_LOCAL, HOST_X86)}
        for triple, oid in self.refs.items():
            SA.git(self.origin, "update-ref", SA.ref_name(self.commit, triple), oid)


    def test_fetch_imports_separate_evidence_commits_through_shared_transport(self):
        with tempfile.TemporaryDirectory(dir=self.temporary.name) as directory:
            clone = Path(directory) / "clone"
            subprocess.run(["git", "clone", "-q", str(self.origin), str(clone)], check=True)
            head = SA.rev_parse(clone, "HEAD")
            self.assertEqual(SA.records_for(clone, self.commit), {})
            args = SA.build_parser().parse_args(["fetch", self.commit, "--repo", str(clone)])
            with mock.patch("sys.stdout", new=io.StringIO()):
                self.assertEqual(SA.cmd_fetch(args), 0)
            self.assertEqual(SA.records_for(clone, self.commit), self.refs)
            self.assertEqual(SA.rev_parse(clone, "HEAD"), head)
            for oid in self.refs.values():
                self.assertEqual(SA.rev_parse(clone, oid + "^"), self.commit)

    def test_conflicting_record_ref_makes_the_local_import_atomic(self):
        with tempfile.TemporaryDirectory(dir=self.temporary.name) as directory:
            clone = Path(directory) / "clone"
            subprocess.run(["git", "clone", "-q", str(self.origin), str(clone)], check=True)
            # Both records are siblings parented by the subject: neither can
            # fast-forward the other. The other absent ref must not be imported.
            SA.git(clone, "update-ref", SA.ref_name(self.commit, HOST_LOCAL), self.refs[HOST_X86])
            before = SA.records_for(clone, self.commit)
            args = SA.build_parser().parse_args(["fetch", self.commit, "--repo", str(clone),
                                                "--remote", str(self.origin)])
            with mock.patch("sys.stdout", new=io.StringIO()):
                self.assertEqual(SA.cmd_fetch(args), 1)
            self.assertEqual(SA.records_for(clone, self.commit), before)

    def test_transport_failure_is_returned_without_a_verdict(self):
        args = SA.build_parser().parse_args(["fetch", self.commit, "--repo", str(self.origin)])
        failure = subprocess.CompletedProcess([], 1, b"", b"reader refused")
        real_run = SA.run
        calls = []

        def run(argv, **kwargs):
            if "records" in argv:
                calls.append(argv)
                return failure
            return real_run(argv, **kwargs)

        with mock.patch.object(SA, "run", side_effect=run), \
                mock.patch("sys.stdout", new=io.StringIO()):
            self.assertEqual(SA.cmd_fetch(args), 1)
        self.assertEqual(len(calls), 1)
        self.assertEqual(calls[0][-3:], ["records", "--subject", self.commit])


class DarwinCOracleTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="darwin-oracle-")
        self.addCleanup(self.temporary.cleanup)
        root = Path(self.temporary.name).resolve()
        self.compiler = root / "toolchain/bin/clang"
        self.compiler.parent.mkdir(parents=True)
        self.compiler.write_bytes(b"native-compiler")
        self.compiler.chmod(0o700)
        self.sdk = root / "MacOSX.sdk"
        self.sdk.mkdir()
        (self.sdk / "SDKSettings.json").write_text('{"Version":"26.0"}')
        self.calls = []

    def run_oracle(self, *, probe_code=0, compiler_path=None):
        def run(argv, **kwargs):
            self.calls.append((argv, kwargs))
            if argv == ["/usr/bin/xcrun", "--sdk", "macosx", "--find", "clang"]:
                out = str(self.compiler if compiler_path is None else compiler_path).encode()
            elif argv == ["/usr/bin/xcrun", "--sdk", "macosx", "--show-sdk-path"]:
                out = str(self.sdk).encode()
            else:
                self.assertEqual(argv[0], str(self.compiler))
                self.assertEqual(argv[1:3], ["-isysroot", str(self.sdk)])
                self.assertIn(b"#include <stdio.h>", kwargs["input_bytes"])
                return subprocess.CompletedProcess(argv, probe_code, b"", b"missing stdio.h")
            return subprocess.CompletedProcess(argv, 0, out + b"\n", b"")
        with mock.patch.object(SA, "run", side_effect=run), \
             mock.patch.object(SA, "tool_version", return_value="Apple clang native"), \
             mock.patch.dict(os.environ, {"PATH": "/hostile/lean/bin"}):
            return SA.darwin_c_oracle()

    def test_ignores_path_clang_and_binds_compiler_and_sdk(self):
        oracle = self.run_oracle()
        self.assertEqual(oracle["compiler"]["path"], str(self.compiler))
        self.assertEqual(oracle["sdk"]["path"], str(self.sdk))
        record = {"toolchains": {"darwin_c_oracle": oracle}}
        self.assertIsNone(SA.darwin_c_oracle_problem(record))
        for part in ("compiler", "sdk"):
            altered = copy.deepcopy(record)
            altered["toolchains"]["darwin_c_oracle"][part].pop("sha256")
            self.assertIn("SHA-256", SA.darwin_c_oracle_problem(altered))
        altered = copy.deepcopy(record)
        altered["toolchains"]["darwin_c_oracle"]["sdk"]["settings"] = "/other/SDKSettings.json"
        self.assertIn("do not belong", SA.darwin_c_oracle_problem(altered))
        self.assertIsNotNone(SA.darwin_c_oracle_problem({}))

    def test_missing_headers_fail_before_the_native_train(self):
        with self.assertRaisesRegex(SA.Refused, "stdio.h"):
            self.run_oracle(probe_code=1)

    def test_relative_or_ambiguous_compiler_is_refused(self):
        for value in ("clang", "/one/clang\n/two/clang"):
            with self.subTest(value=value), self.assertRaisesRegex(SA.Refused, "discovery failed"):
                self.run_oracle(compiler_path=value)

    @unittest.skipUnless(sys.platform == "darwin", "requires the native Apple SDK")
    def test_native_sdk_compiles_standard_header_with_a_hostile_path(self):
        decoys = Path(self.temporary.name) / "decoys"
        decoys.mkdir()
        for name in ("clang", "cc", "xcrun"):
            executable = decoys / name
            executable.write_text("#!/bin/sh\nexit 97\n")
            executable.chmod(0o700)
        with mock.patch.dict(os.environ, {"PATH": str(decoys)}):
            oracle = SA.darwin_c_oracle()
        self.assertIsNone(SA.darwin_c_oracle_problem({"toolchains": {"darwin_c_oracle": oracle}}))
        self.assertNotEqual(Path(oracle["compiler"]["path"]).parent, decoys)


class NativeVerdictTests(unittest.TestCase):
    def test_native_intel_and_amd_hosts_are_native(self):
        self.assertEqual(SA.native_x86_64_verdict(native_host()), (True, []))
        amd = native_host(cpuid_vendor="AuthenticAMD", cpuinfo_vendor_id="AuthenticAMD")
        self.assertTrue(SA.native_x86_64_verdict(amd)[0])
        # A hardware-virtualized guest executes x86-64 natively: recorded, not refused.
        self.assertTrue(SA.native_x86_64_verdict(native_host(cpuid_hypervisor=True,
                                                             cpuid_hypervisor_vendor="KVMKVMKVM"))[0])

    def test_translation_and_emulation_are_refused(self):
        for name, host, fragment in (
            ("arm64", native_host(machine="arm64"), "not x86-64"),
            ("rosetta", native_host(system="Darwin", translated=True), "translated"),
            ("qemu brand", native_host(cpuid_brand="QEMU Virtual CPU version 2.5+"), "QEMU/TCG"),
            ("tcg hypervisor", native_host(cpuid_hypervisor=True, cpuid_hypervisor_vendor="TCGTCGTCGTCG"),
             "QEMU/TCG"),
            ("qemu-user cpuinfo", dict(native_host(), cpuinfo={"CPU implementer": "0x41"}), "ARM CPU"),
            ("unknown vendor", native_host(cpuid_vendor="VirtualApple"), "not a hardware vendor"),
            ("no cpuid", native_host(cpuid={"available": False, "reason": "no cc"}), "CPUID was not executed"),
        ):
            with self.subTest(name):
                native, reasons = SA.native_x86_64_verdict(host)
                self.assertFalse(native)
                self.assertTrue(any(fragment in reason for reason in reasons), reasons)

    def test_this_host_probe_is_honest(self):
        host = SA.probe_host(run_cpuid=False)
        if host["machine"] not in SA.X86_MACHINES:
            self.assertFalse(host["native_x86_64"])

    def test_host_triple_comes_from_the_package_not_a_path_launcher_shim(self):
        # The triple names the record's ref. A PATH trustc may be an atpkg
        # launcher shim whose prelude the resolver reads but never runs
        # (DR-ATPKG-PRELUDE-SHIM-20261015); this one claims an x86-64 host.
        with tempfile.TemporaryDirectory(prefix="trust-cg-attest-triple-") as temporary:
            root = Path(temporary).resolve()
            package = SHIMS.make_package(root / "pkg", host="aarch64-unknown-linux-gnu")
            log = root / "shim-calls.log"
            shims = root / "atpkg-bin"
            forged = "\n".join(["rustc 1.99.0 (forged)", "binary: trustc", "commit-hash: " + "6" * 40,
                                 f"host: {HOST_X86}"])
            SHIMS.lying_shim(shims / "trustc", package / "bin" / "trustc", log, {"-vV": forged})
            SHIMS.lying_shim(shims / "targo", package / "bin" / "targo", log)
            lied = subprocess.run([str(shims / "trustc"), "-vV"], text=True,
                                  capture_output=True, timeout=60, check=True)
            self.assertIn(f"host: {HOST_X86}", lied.stdout.splitlines())
            log.unlink()
            with mock.patch.dict(os.environ, {"PATH": f"{shims}:/usr/bin:/bin"}):
                self.assertEqual(SA.compiler_host_triple(), "aarch64-unknown-linux-gnu")
            self.assertEqual(SHIMS.logged(log), [], "the host probe executed a PATH launcher shim")
            with mock.patch.dict(os.environ, {"PATH": "/usr/bin:/bin"}):
                self.assertIsNone(SA.compiler_host_triple())


class EnvironmentPolicyTests(unittest.TestCase):
    BASE = {"TRUST_CG_RUN_FORMAL_PROOF_TESTS": "1"}

    def report(self, environ=None, explicit=(), fuzz="200", checkout="/checkout"):
        return SA.environment_report(dict(self.BASE, **(environ or {})), explicit=explicit,
                                     effective={"WASM_CFG_FUZZ_FUNCS": fuzz}, checkout=checkout)

    def test_defaults_pass_and_record(self):
        report = self.report({"SOUNDNESS_COMMAND_TIMEOUT_SECONDS": "7200"})
        self.assertEqual(report["refused"], [])
        self.assertIn("SOUNDNESS_COMMAND_TIMEOUT_SECONDS",
                      [row["name"] for row in report["settings"] if row["verdict"] == "recorded"])

    def test_leg_weakening_settings_are_refused(self):
        for name, kwargs, fragment in (
            ("fuzz below floor", {"fuzz": "1"}, "WASM_CFG_FUZZ_FUNCS"),
            ("fuzz not a number", {"fuzz": "lots"}, "WASM_CFG_FUZZ_FUNCS"),
            ("caller tables", {"explicit": ["ISLAND_VT_TABLES"]}, "ISLAND_VT_TABLES"),
            ("explicit clean", {"explicit": ["CLEAN_DIR"]}, "CLEAN_DIR"),
            ("explicit ay", {"environ": {"AY_DIR": "/elsewhere"}}, "AY_DIR"),
            ("explicit targo", {"environ": {"TRUST_TARGO": "/x/bin/targo"}}, "TRUST_TARGO"),
            ("solver override", {"environ": {"AY_SOLVER_PATH": "/x/ay"}}, "AY_SOLVER_PATH"),
            ("ssh transport", {"environ": {"SOUNDNESS_SSH": "fake-ssh"}}, "SOUNDNESS_SSH"),
            ("test control", {"environ": {"TCG_NO_DECODE_CHECK": "1"}}, "TCG_NO_DECODE_CHECK"),
            ("wrong control value", {"environ": {"TRUST_CG_RUN_ROSETTA_LINKRUN": "0"}}, "ROSETTA"),
            ("campaign off", {"environ": {"TRUST_CG_RUN_FORMAL_PROOF_TESTS": "0"}},
             "TRUST_CG_RUN_FORMAL_PROOF_TESTS"),
            ("runner", {"environ": {"CARGO_TARGET_AARCH64_APPLE_DARWIN_RUNNER": "true"}}, "RUNNER"),
            ("profile", {"environ": {"CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS": "false"}}, "PROFILE"),
            ("rustflags", {"environ": {"RUSTFLAGS": "--cfg skip"}}, "RUSTFLAGS"),
            ("nocapture", {"environ": {"RUST_TEST_NOCAPTURE": "1"}}, "NOCAPTURE"),
            ("foreign checkout", {"environ": {"TRUST_CG_DIR": "/somewhere/else"}}, "TRUST_CG_DIR"),
        ):
            with self.subTest(name):
                report = self.report(**kwargs)
                self.assertTrue(any(fragment in item for item in report["refused"]), report["refused"])

    def test_required_campaign_control_must_be_present(self):
        report = SA.environment_report({}, explicit=(), effective={"WASM_CFG_FUZZ_FUNCS": "200"},
                                       checkout="/checkout")
        self.assertTrue(any("TRUST_CG_RUN_FORMAL_PROOF_TESTS" in item for item in report["refused"]))

    def test_gate_owned_controls_and_own_checkout_are_allowed(self):
        with tempfile.TemporaryDirectory() as checkout:
            report = self.report({"TRUST_CG_RUN_ROSETTA_LINKRUN": "1", "TRUST_CG_REQUIRE_X86_SILICON": "1",
                                  "TRUST_CG_DIR": checkout}, checkout=checkout, fuzz="500")
            self.assertEqual(report["refused"], [])


class EnvironmentAllowlistTests(unittest.TestCase):
    """The allowlist: what an attested run's legs may see, and what a caller may not set."""

    LEG_AFFECTING = (
        "PYTHONPATH", "PYTHONHOME", "PYTHONSTARTUP", "NODE_OPTIONS", "NODE_PATH", "DYLD_INSERT_LIBRARIES",
        "DYLD_LIBRARY_PATH", "LD_PRELOAD", "LD_LIBRARY_PATH", "LEAN_PATH", "LEAN_SYSROOT", "ELAN_TOOLCHAIN",
        "LAKE_HOME", "RUSTFLAGS", "RUSTDOCFLAGS", "RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
        "RUSTC_BOOTSTRAP", "RUST_TEST_NOCAPTURE", "CARGO_BUILD_RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS",
        "CARGO_TARGET_AARCH64_APPLE_DARWIN_RUNNER", "CARGO_PROFILE_DEV_DEBUG_ASSERTIONS", "CARGO_UNSTABLE_BUILD_STD",
        "CARGO_BUILD_TARGET", "CC", "CXX", "CFLAGS", "CC_aarch64_apple_darwin", "TARGET_CC", "LDFLAGS", "CPATH",
        "LIBRARY_PATH", "BASH_ENV", "ENV", "BASH_FUNC_cargo%%", "GIT_CONFIG_COUNT", "GIT_DIR", "TRUST_SYSROOT",
        "TCG_NO_DECODE_CHECK", "TRUST_CG_PROOF_GATE", "AY_BIN", "CLEAN_CHECKER", "PERL5LIB", "SOUNDNESS_NEW_KNOB",
        # git reads objects from another store with these (LD-75): removed
        # from an attested run's environment, and refused by name.
        "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_OBJECT_DIRECTORY",
    )

    def test_every_named_leg_affecting_variable_is_refused(self):
        for name in self.LEG_AFFECTING:
            with self.subTest(name):
                verdict, reason = SA.classify_variable(name, "/elsewhere", "/checkout")
                self.assertEqual(verdict, "refused", reason)
                kept, refused, dropped = SA.scrub_environment({name: "/elsewhere", "HOME": "/h"}, "/checkout")
                self.assertEqual(kept, {"HOME": "/h"})
                self.assertEqual([item["name"] for item in refused], [name])
                report = SA.environment_report({name: "/elsewhere", "TRUST_CG_RUN_FORMAL_PROOF_TESTS": "1"},
                                               explicit=(), effective={}, checkout="/checkout")
                self.assertTrue(any(item.startswith(name + ":") for item in report["refused"]), report["refused"])

    def test_unlisted_variables_are_dropped_by_the_scrub_and_refused_in_the_legs(self):
        kept, refused, dropped = SA.scrub_environment(
            {"PATH": "/bin", "SOME_TOKEN": "secret", "SSH_AUTH_SOCK": "/s", "CPATH": ""}, "/checkout")
        self.assertEqual(set(kept), {"PATH", "SSH_AUTH_SOCK"})
        self.assertEqual((refused, dropped), ([], ["CPATH", "SOME_TOKEN"]))
        report = SA.environment_report({"SOME_TOKEN": "secret", "SSH_AUTH_SOCK": "/s",
                                        "TRUST_CG_RUN_FORMAL_PROOF_TESTS": "1"},
                                       explicit=(), effective={}, checkout="/checkout")
        rows = {row["name"]: row for row in report["settings"]}
        self.assertEqual(rows["SOME_TOKEN"]["verdict"], "refused")
        # Neither an unknown nor an inert variable's value is ever recorded.
        self.assertNotIn("value", rows["SOME_TOKEN"])
        self.assertEqual((rows["SSH_AUTH_SOCK"]["verdict"], "value" in rows["SSH_AUTH_SOCK"]), ("inert", False))

    def test_platform_defaults_are_recorded_only_at_their_default(self):
        for name, value in SA.ENV_PLATFORM_DEFAULTS.items():
            self.assertEqual(SA.classify_variable(name, value, "/c")[0], "recorded")
            self.assertEqual(SA.classify_variable(name, ":" + value, "/c")[0], "refused")
        self.assertEqual(SA.classify_variable("MANPATH", "/x", "/c")[0], "inert")

    def test_caller_refusals_and_drops_travel_into_the_legs_report(self):
        environ = {"TRUST_CG_RUN_FORMAL_PROOF_TESTS": "1",
                   "SOUNDNESS_CALLER_REFUSED": json.dumps([{"name": "PYTHONPATH", "reason": "r"}]),
                   "SOUNDNESS_CALLER_DROPPED": "A,B", "SOUNDNESS_ENV_SCRUBBED": "1"}
        report = SA.environment_report(environ, explicit=(), effective={}, checkout="/c")
        self.assertEqual(report["refused"], ["PYTHONPATH: set by the caller: r"])
        self.assertEqual(report["dropped"], ["A", "B"])
        environ["SOUNDNESS_CALLER_REFUSED"] = "not json"
        self.assertTrue(SA.environment_report(environ, explicit=(), effective={}, checkout="/c")["refused"])

    def test_program_naming_variables_are_dropped(self):
        """EDITOR, VISUAL, PAGER, LESS, GIT_EDITOR and GIT_PAGER each name a
        program (or its options) git or a git helper runs, which the host
        trust boundary does not judge; they are dropped from a scrubbed run,
        not kept (OD-XHOST-GIT-PROGRAM-KEYS-20261024), and refused if one
        reaches the legs past the scrub (no record is written). The verdict
        RULES of allowlist-v1 are unchanged (repair round 3): each is still
        inert there, so a record an earlier writer made with such a row keeps
        verifying (RecordTests). GIT_SSH_COMMAND (judged at the
        boundary) stays recorded."""
        names = ("EDITOR", "VISUAL", "PAGER", "LESS", "GIT_EDITOR", "GIT_PAGER")
        self.assertEqual(SA.ENV_DROPPED_PROGRAMS, frozenset(names))
        for name in names:
            self.assertEqual(SA.classify_variable(name, "vim", "/c"), ("inert", ""), name)
        kept, refused, dropped = SA.scrub_environment({"EDITOR": "vim", "PAGER": "less", "HOME": "/h"}, "/c")
        self.assertNotIn("EDITOR", kept)
        self.assertNotIn("PAGER", kept)
        self.assertEqual(kept["HOME"], "/h")
        self.assertEqual(refused, [])
        self.assertEqual(set(dropped), {"EDITOR", "PAGER"})
        for name in names:
            with self.subTest(past_the_scrub=name):
                report = SA.environment_report({name: "vim", "TRUST_CG_RUN_FORMAL_PROOF_TESTS": "1"}, explicit=(),
                                               effective={}, checkout="/c")
                self.assertEqual(len(report["refused"]), 1, report["refused"])
                self.assertTrue(report["refused"][0].startswith(f"{name}: names a program git or a git helper "
                                                                "runs"), report["refused"])
                self.assertEqual(report["policy"], "allowlist-v1")
        self.assertEqual(SA.classify_variable("GIT_SSH_COMMAND", "/usr/bin/ssh", "/c")[0], "recorded")

    def test_the_allowlist_v1_rules_are_the_ones_records_were_written_under(self):
        """ENV_POLICY names the verdict rules the record verifier re-derives
        each environment row by; under one policy name they never change
        (repair round 3 of OD-XHOST-GIT-PROGRAM-KEYS-20261024: 850f69fd0
        reclassified six inert names under allowlist-v1, and its verifier
        refused 25 of the 26 local records). The inert set is pinned here as
        allowlist-v1 wrote it."""
        self.assertEqual(SA.ENV_POLICY, "allowlist-v1")
        self.assertEqual(SA.ENV_INERT, frozenset({
            "TERM", "TERM_PROGRAM", "TERM_PROGRAM_VERSION", "TERM_SESSION_ID", "COLORTERM", "COLUMNS", "LINES",
            "SHLVL", "PWD", "OLDPWD", "_", "SSH_AUTH_SOCK", "SSH_AGENT_PID", "SSH_CLIENT", "SSH_CONNECTION",
            "SSH_TTY", "XPC_FLAGS", "XPC_SERVICE_NAME", "__CFBundleIdentifier", "__CF_USER_TEXT_ENCODING",
            "COMMAND_MODE", "SECURITYSESSIONID", "MAIL", "DISPLAY", "EDITOR", "VISUAL", "PAGER", "LESS",
            "GIT_EDITOR", "GIT_PAGER", "HOSTNAME", "TMUX", "TMUX_PANE"}))
        self.assertLessEqual(SA.ENV_DROPPED_PROGRAMS, SA.ENV_INERT, "the writer only scrubs more")

    def test_exec_scrubbed_passes_only_the_allowlist(self):
        env = {"PATH": os.environ["PATH"], "HOME": "/h", "PYTHONPATH": "/elsewhere", "SOME_TOKEN": "secret",
               "SDKROOT": "/sdk"}
        result = subprocess.run([sys.executable, "-I", str(ROOT / "scripts/soundness_attestation.py"),
                                 "exec-scrubbed", "--checkout", "/checkout", "--", "/usr/bin/env"],
                                env=env, capture_output=True, text=True, check=True)
        seen = dict(line.split("=", 1) for line in result.stdout.splitlines() if "=" in line)
        self.assertNotIn("PYTHONPATH", seen)
        self.assertNotIn("SOME_TOKEN", seen)
        self.assertEqual((seen["HOME"], seen["SDKROOT"], seen["SOUNDNESS_ENV_SCRUBBED"]), ("/h", "/sdk", "1"))
        self.assertEqual(json.loads(seen["SOUNDNESS_CALLER_REFUSED"])[0]["name"], "PYTHONPATH")
        self.assertIn("SOME_TOKEN", seen["SOUNDNESS_CALLER_DROPPED"].split(","))

    def test_exec_scrubbed_pins_the_interpreters_and_refuses_a_callers_pin(self):
        """Repair round 3 of OD-XHOST-GATE-CWD-20261025: the re-executed gate
        runs ONE python3, so exec-scrubbed exports SOUNDNESS_PYTHON3, the
        canonical path of the interpreter it runs as, and runs its command
        (the gate's bash) by its canonical path. The pin is the gate's own: a
        caller's value is refused by the scrub (and replaced), and a census
        run's own export is not reported as the caller's. environment_report
        writes no row for the pin (classify_variable, an allowlist-v1 rule,
        still calls the name an unknown gate setting) and refuses a pin that
        is not the interpreter making the report. A command not named by an
        absolute path refuses."""
        with tempfile.TemporaryDirectory() as directory:
            printer = Path(os.path.realpath(directory), "printer.sh")
            printer.write_text('#!/bin/sh\necho "argv0=$0"\nexec /usr/bin/env\n')
            printer.chmod(0o700)
            link = Path(directory, "printer-link")
            link.symlink_to(printer)
            env = {"PATH": os.environ["PATH"], "HOME": "/h", "SOUNDNESS_PYTHON3": "/elsewhere/python3"}
            result = subprocess.run([sys.executable, "-I", str(ROOT / "scripts/soundness_attestation.py"),
                                     "exec-scrubbed", "--checkout", "/checkout", "--", str(link)],
                                    env=env, capture_output=True, text=True, check=True)
        seen = dict(line.split("=", 1) for line in result.stdout.splitlines() if "=" in line)
        self.assertEqual(seen["argv0"], str(printer), "the command runs by its canonical path")
        self.assertEqual(seen["SOUNDNESS_PYTHON3"], os.path.realpath(sys.executable))
        refused = json.loads(seen["SOUNDNESS_CALLER_REFUSED"])
        self.assertEqual([item["name"] for item in refused], ["SOUNDNESS_PYTHON3"])
        self.assertIn("is the gate's own pin of the one python3 it runs", refused[0]["reason"])
        self.assertEqual(SA.classify_variable("SOUNDNESS_PYTHON3", "/x", "/c")[0], "refused",
                         "the allowlist-v1 rule is unchanged")
        relative = subprocess.run([sys.executable, "-I", str(ROOT / "scripts/soundness_attestation.py"),
                                   "exec-scrubbed", "--checkout", "/checkout", "--", "env"],
                                  env={"PATH": os.environ["PATH"]}, capture_output=True, text=True)
        self.assertNotEqual(relative.returncode, 0)
        self.assertIn("exec-scrubbed runs a command named by an absolute path", relative.stdout + relative.stderr)
        running = os.path.realpath(sys.executable)
        base = {"TRUST_CG_RUN_FORMAL_PROOF_TESTS": "1", "SOUNDNESS_PYTHON3": running}
        report = SA.environment_report(base, explicit=(), effective={}, checkout="/c", running_python3=running)
        self.assertEqual(report["refused"], [])
        self.assertNotIn("SOUNDNESS_PYTHON3", [row["name"] for row in report["settings"]])
        report = SA.environment_report(dict(base, SOUNDNESS_PYTHON3="/elsewhere/python3"), explicit=(),
                                       effective={}, checkout="/c", running_python3=running)
        self.assertEqual(len(report["refused"]), 1, report["refused"])
        self.assertTrue(report["refused"][0].startswith("SOUNDNESS_PYTHON3: names /elsewhere/python3, not the "
                                                        "interpreter the gate runs"), report["refused"])
        census = {"PATH": os.environ["PATH"], "HOME": "/h", "SOUNDNESS_PYTHON3": running}
        for explicit, expected in (((), 0), (("--explicit", "SOUNDNESS_PYTHON3"), 1)):
            with self.subTest(explicit=explicit):
                result = subprocess.run([sys.executable, "-I", str(ROOT / "scripts/soundness_attestation.py"),
                                         "check-env", "--checkout", "/checkout", "--caller", *explicit,
                                         "--effective", "WASM_CFG_FUZZ_FUNCS=200"],
                                        env=census, capture_output=True, text=True)
                self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
                self.assertEqual("SOUNDNESS_PYTHON3" in result.stdout, bool(expected), result.stdout)

    def test_uncommitted_cargo_configs_are_found_and_committed_ones_are_not(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            checkout = root / "work" / "trust-cg"
            (checkout / ".cargo").mkdir(parents=True)
            (checkout / ".cargo" / "config.toml").write_text("[build]\njobs = 2\n")
            subprocess.run(["git", "init", "-q", str(checkout)], check=True)
            subprocess.run(["git", "-C", str(checkout), "add", ".cargo/config.toml"], check=True)
            self.assertEqual(SA.cargo_config_files([str(checkout)], cargo_home=str(root / "cargo-home"), home=None),
                             [])
            above = root / "work" / ".cargo" / "config.toml"
            above.parent.mkdir()
            above.write_text('[target.aarch64-apple-darwin]\nrunner = "true"\n')
            (root / "cargo-home").mkdir()
            (root / "cargo-home" / "config.toml").write_text("[build]\nrustflags = ['--cfg', 'x']\n")
            untracked = root / "deps" / "clean-x" / ".cargo" / "config"
            untracked.parent.mkdir(parents=True)
            untracked.write_text("[env]\nX = '1'\n")
            found = {item["path"] for item in SA.cargo_config_files(
                [str(checkout), str(root / "deps")], cargo_home=str(root / "cargo-home"), home=None)}
            self.assertEqual(found, {str(above), str(root / "cargo-home" / "config.toml"), str(untracked)})
            report = SA.environment_report({"TRUST_CG_RUN_FORMAL_PROOF_TESTS": "1"}, explicit=(), effective={},
                                           checkout=str(checkout),
                                           cargo_configs=[{"path": str(above), "sha256": "0" * 64}])
            self.assertTrue(any("uncommitted Cargo configuration" in item for item in report["refused"]))


class GitEnvironmentIsolationTests(unittest.TestCase):
    """R3 of OD-XHOST-GIT-PROGRAM-KEYS-20261024: isolate_git_environment runs
    before the host trust boundary (soundness_check.sh execs exec-scrubbed
    first), so it must run no program. It drops the fixed GIT_LOCAL_ENVIRONMENT
    set instead of asking PATH's git."""

    def test_isolate_runs_no_program_and_drops_the_local_variables(self):
        planted = {name: "set" for name in SA.GIT_LOCAL_ENVIRONMENT}
        planted.update(GIT_SSH_COMMAND="keep-me", HOME="/h")
        with mock.patch.object(SA.subprocess, "run",
                               side_effect=AssertionError("isolate_git_environment ran a program")), \
             mock.patch.dict(os.environ, planted, clear=True):
            SA.isolate_git_environment()
            for name in SA.GIT_LOCAL_ENVIRONMENT:
                self.assertNotIn(name, os.environ, name)
            # A GIT_ variable that is not repository-local (the boundary judges
            # it) is kept, so a scrubbed run still carries GIT_SSH_COMMAND.
            self.assertEqual(os.environ.get("GIT_SSH_COMMAND"), "keep-me")

    def test_the_fixed_set_is_a_superset_of_the_installed_gits(self):
        git = shutil.which("git")
        if git is None:
            self.skipTest("no git on PATH")
        out = subprocess.run([git, "rev-parse", "--local-env-vars"], capture_output=True, text=True,
                             check=True, env=dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull,
                                                  GIT_CONFIG_NOSYSTEM="1")).stdout.split()
        missing = [name for name in out if name not in SA.GIT_LOCAL_ENVIRONMENT]
        self.assertEqual(missing, [], f"GIT_LOCAL_ENVIRONMENT misses {missing}; add them")


class AyIdentityTests(unittest.TestCase):
    def test_stamp_is_read_from_bytes(self):
        with tempfile.TemporaryDirectory() as directory:
            ay = Path(directory, "ay")
            ay.write_bytes(b"\x00junk 0.27.0+build.9624.075a482a@2026-09-01T00:00:00Z junk")
            identity = SA.ay_identity(ay)
            self.assertEqual((identity["version"], identity["build"], identity["commit"]),
                             ("0.27.0", 9624, "075a482a"))
            self.assertEqual(identity["sha256"], SA.sha256_bytes(ay.read_bytes()))
            ay.write_bytes(b"0.26.0+build.1.aaaaaaa@2026-09-01T00:00:00Z 0.27.0+build.2.bbbbbbb@2026-09-01T00:00:00Z")
            self.assertIsNone(SA.ay_identity(ay)["version"])


class RecordTests(unittest.TestCase):
    """One real attested run; every case edits a copy of its records."""

    @classmethod
    def setUpClass(cls):
        cls.temporary = fixture.FixtureDirectory("attestation-")
        cls.world = fixture.Constellation(Path(cls.temporary.name))
        # The caller sets two of the program-naming names the writer drops
        # (test_a_fresh_record_carries_no_row_for_a_dropped_program_name).
        result = cls.world.run_gate("--attest", EDITOR="vi", GIT_PAGER="less")
        if result.returncode != 0:
            raise AssertionError("fixture attest run failed:\n" + result.stdout[-4000:] + result.stderr[-2000:])
        cls.commit = cls.world.head()
        cls.logdir = fixture.logdir_of(result)
        cls.refs = SA.records_for(cls.world.cg, cls.commit)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def setUp(self):
        # Every case starts from the two green records.
        for triple, oid in self.refs.items():
            SA.git(self.world.cg, "update-ref", SA.ref_name(self.commit, triple), oid)
        for triple in set(SA.records_for(self.world.cg, self.commit)) - set(self.refs):
            SA.git(self.world.cg, "update-ref", "-d", SA.ref_name(self.commit, triple))

    def verify(self, *args, commit=None):
        result = self.world.tool("verify", commit or self.commit, "--repo", str(self.world.cg), *args)
        return result.returncode, result.stdout + result.stderr

    def test_darwin_oracle_binding_cannot_be_omitted_or_hidden_by_the_system_label(self):
        for system_label in ("Darwin", "Linux"):
            with self.subTest(system=system_label):
                def remove_oracle(record):
                    record["host"]["system"] = system_label
                    record["toolchains"].pop("darwin_c_oracle", None)
                self.edit(HOST_LOCAL, remove_oracle)
                rc, output = self.verify()
                self.assertEqual(rc, 1, output)
                self.assertIn("Darwin C oracle does not record Apple SDK discovery", output)

    def test_darwin_oracle_requires_compiler_and_sdk_digests(self):
        for part in ("compiler", "sdk"):
            with self.subTest(part=part):
                self.edit(HOST_LOCAL, lambda record:
                          record["toolchains"]["darwin_c_oracle"][part].pop("sha256"))
                rc, output = self.verify()
                self.assertEqual(rc, 1, output)
                self.assertIn(f"Darwin C oracle {part} is not bound", output)

    def edit(self, triple, change, *, parent=None, ref_triple=None, text_change=None):
        """Replace a record by an edited copy (same tree otherwise)."""
        oid = self.refs[triple]
        record = json.loads(SA.show_blob(self.world.cg, oid, "attestation.json"))
        change(record)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory, "attestation.json")
            text = json.dumps(record)
            path.write_text(text_change(text) if text_change else text)
            blob = SA.git(self.world.cg, "hash-object", "-w", str(path)).strip()
        entries = SA.git(self.world.cg, "ls-tree", oid).splitlines()
        entries = [line for line in entries if not line.endswith("\tattestation.json")]
        entries.append(f"100644 blob {blob}\tattestation.json")
        tree = SA.git(self.world.cg, "mktree", input_bytes=("\n".join(entries) + "\n").encode()).strip()
        new = SA.git(self.world.cg, "commit-tree", tree, "-p", parent or self.commit, "-m", "edited").strip()
        SA.git(self.world.cg, "update-ref", SA.ref_name(self.commit, ref_triple or triple), new)
        return new

    def test_an_allowlist_v1_record_with_inert_editor_rows_still_verifies(self):
        """Records written under allowlist-v1 before OD-XHOST-GIT-PROGRAM-KEYS-
        20261024 carry EDITOR, PAGER, ... as inert rows (main's 96226db68 has a
        GIT_EDITOR one). This verifier re-derives every row under the same
        rules, so such a record verifies as it always did (at 850f69fd0 it was
        refused: `GIT_EDITOR is inert in the record but unknown`). A row the
        writer never produces with another verdict still refuses."""
        rows = [{"name": name, "explicit": False, "verdict": "inert"} for name in sorted(SA.ENV_DROPPED_PROGRAMS)]
        imported = self.edit(HOST_X86, lambda r: r["environment"]["settings"].extend(rows))

        def local(record):
            record["environment"]["settings"].extend(rows)
            record["imported"] = [{"triple": HOST_X86, "record": imported}]
        self.edit(HOST_LOCAL, local)
        rc, output = self.verify()
        self.assertEqual(rc, 0, output)
        self.assertIn("attested by", output)
        self.setUp()
        self.edit(HOST_LOCAL, lambda r: r["environment"]["settings"].append(
            {"name": "GIT_EDITOR", "value": "vim", "verdict": "recorded"}))
        rc, output = self.verify()
        self.assertEqual(rc, 1, output)
        self.assertIn("GIT_EDITOR is recorded in the record but inert under the allowlist-v1 allowlist", output)

    def test_a_fresh_record_carries_no_row_for_a_dropped_program_name(self):
        """The writer scrubs ENV_DROPPED_PROGRAMS: the caller of this class's
        run set EDITOR and GIT_PAGER, and the local record names them as
        dropped and holds no row for them, so main's verifier (which calls
        them inert) and this one judge it alike."""
        record = SA.load_record(self.world.cg, self.refs[HOST_LOCAL])
        names = {row.get("name") for row in record["environment"]["settings"]}
        self.assertEqual(names & SA.ENV_DROPPED_PROGRAMS, set())
        self.assertLessEqual({"EDITOR", "GIT_PAGER"}, set(record["environment"]["dropped"]))
        self.assertEqual(record["environment"]["policy"], "allowlist-v1")

    # ---- the green baseline ------------------------------------------------
    def test_green_run_writes_a_local_and_an_imported_x86_record(self):
        self.assertEqual(set(self.refs), {HOST_LOCAL, HOST_X86})
        rc, output = self.verify()
        self.assertEqual(rc, 0, output)
        self.assertIn("attested by", output)
        local = SA.load_record(self.world.cg, self.refs[HOST_LOCAL])
        remote = SA.load_record(self.world.cg, self.refs[HOST_X86])
        self.assertEqual((local["scope"], remote["scope"]), ("full", "x86_64-native"))
        # The local record never carries the legs imported from the x86-64 host.
        self.assertFalse([leg for leg in local["legs"] if leg["class"] == "x86_64-native"])
        self.assertIn({"triple": HOST_X86, "record": self.refs[HOST_X86]}, local["imported"])
        self.assertEqual(local["executed"]["ay"]["sha256"], local["executed"]["campaign_ay"]["sha256"])
        self.assertEqual(local["executed"]["campaign_ay"]["route"], "toolchain-pinned-ay")
        # Every Cargo leg ran on the fixture's Trust package, bound by its bytes.
        trust = local["toolchains"]["trust"]
        self.assertEqual(trust["commit"], fixture.TRUST_COMMIT)
        self.assertEqual(Path(trust["compiler"]), (self.world.sysroot / "bin" / "trustc").resolve())
        for tool in ("trustc", "targo"):
            self.assertTrue(SA.SHA256.match(local["executed"][tool]["sha256"]))
        self.assertEqual(local["executed"]["ay"]["version"], fixture.AY_PIN_VERSION)
        self.assertTrue(SA.SHA256.match(local["executed"]["clean"]["sha256"]))
        self.assertTrue(SA.SHA256.match(local["dependencies"]["aterm"]["vt_tables_sha256"]))
        # The islands' stock twin is recorded by path, bytes and -vV, with its setting.
        twin = local["toolchains"]["island_twin"]
        self.assertEqual(twin["path"], str(self.world.bin / "rustc"))
        self.assertTrue(SA.SHA256.match(twin["sha256"]))
        self.assertIn("release: ", twin["rustc"])
        self.assertIn(("ISLAND_TWIN_RUSTC", str(self.world.bin / "rustc"), "recorded"),
                      [(row["name"], row.get("value"), row["verdict"]) for row in local["environment"]["settings"]])
        self.assertEqual((local["environment"]["schema"], local["environment"]["policy"]),
                         (SA.ENV_SCHEMA, SA.ENV_POLICY))
        # Per-leg evidence survives the run's log directory.
        tree = SA.git(self.world.cg, "ls-tree", "-r", "--name-only", self.refs[HOST_LOCAL]).split()
        self.assertTrue(any(name.endswith(".json") and name.startswith("legs/") for name in tree))
        self.assertTrue(any(name.endswith(".tail") for name in tree))
        # A record is a commit whose single parent is the subject; no branch moved.
        parents = SA.git(self.world.cg, "rev-list", "--parents", "-n", "1", self.refs[HOST_LOCAL]).split()
        self.assertEqual(parents[1:], [self.commit])
        self.assertEqual(self.world.head(), self.commit)

    def test_records_travel_through_a_scratch_remote(self):
        """push/fetch move refs/attest/soundness/<C>/* only; a fresh clone then verifies C."""
        with tempfile.TemporaryDirectory(dir=self.temporary.name) as directory:
            remote = Path(directory, "remote.git")
            clone = Path(directory, "clone")
            subprocess.run(["git", "init", "-q", "--bare", str(remote)], check=True)
            result = self.world.tool("push", self.commit, "--repo", str(self.world.cg), "--remote", str(remote))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            listed = subprocess.run(["git", "-C", str(remote), "for-each-ref", "--format=%(refname) %(objectname)"],
                                    capture_output=True, text=True, check=True).stdout.split("\n")
            self.assertEqual(sorted(filter(None, listed)),
                             sorted(f"{SA.ref_name(self.commit, triple)} {oid}" for triple, oid in self.refs.items()))
            # No branch was pushed; the parent-C binding carries the subject along.
            subprocess.run(["git", "clone", "-q", "--no-local", str(self.world.cg), str(clone)], check=True)
            subprocess.run(["git", "-C", str(clone), "checkout", "-q", "--detach", self.commit], check=True)
            rc = self.world.tool("verify", self.commit, "--repo", str(clone)).returncode
            self.assertEqual(rc, 3)
            result = self.world.tool("fetch", self.commit, "--repo", str(clone), "--remote", str(remote))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(SA.records_for(clone, self.commit), self.refs)
            result = self.world.tool("verify", self.commit, "--repo", str(clone))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_absent_records_exit_three(self):
        SA.git(self.world.cg, "update-ref", "-d", SA.ref_name(self.commit, HOST_LOCAL))
        SA.git(self.world.cg, "update-ref", "-d", SA.ref_name(self.commit, HOST_X86))
        rc, output = self.verify()
        self.assertEqual(rc, 3, output)

    # ---- malformed (exit 2) ------------------------------------------------
    def test_structural_mismatches_are_malformed(self):
        other = SA.git(self.world.cg, "commit-tree", SA.rev_parse(self.world.cg, self.commit + "^{tree}"),
                       "-m", "another commit").strip()
        cases = (
            ("parent is not the subject", lambda r: None, {"parent": other}, "exactly one parent"),
            ("subject tree", lambda r: r["subject"].update(tree="0" * 40), {}, "subject.tree"),
            ("subject commit", lambda r: r["subject"].update(commit=other), {}, "names subject"),
            ("schema", lambda r: r.update(schema="v0"), {}, "schema"),
            ("host triple vs ref", lambda r: r["host"].update(triple="x86_64-apple-darwin"), {}, "ref names"),
        )
        for name, change, kwargs, fragment in cases:
            with self.subTest(name):
                self.setUp()
                self.edit(HOST_X86, change, **kwargs)
                rc, output = self.verify()
                self.assertEqual(rc, 2, output)
                self.assertIn(fragment, output)

    def test_x86_legs_need_a_native_host(self):
        def emulate(record):
            record["host"]["cpuid"]["brand"] = "QEMU Virtual CPU version 2.5+"
        self.edit(HOST_X86, emulate)
        rc, output = self.verify()
        self.assertEqual(rc, 2, output)
        self.assertIn("not native x86-64", output)
        self.setUp()

        def smuggle(record):
            record["legs"].append({"id": "x86_sse_lane_gate", "class": "x86_64-native", "status": "PASS"})
        self.edit(HOST_LOCAL, smuggle)
        rc, output = self.verify()
        self.assertEqual(rc, 2, output)
        self.assertIn("not native x86-64", output)

    def test_unsigned_record_fails_a_signature_requirement(self):
        rc, output = self.verify("--require-signature")
        self.assertEqual(rc, 2, output)
        self.assertIn("signature", output)

    # ---- incomplete or failing (exit 1) ------------------------------------
    def test_incomplete_or_failing_records(self):
        def leg(record, leg_id):
            return next(row for row in record["legs"] if row["id"] == leg_id)

        cases = (
            ("SKIP leg", HOST_LOCAL, lambda r: leg(r, "proof_gate_strict").update(status="SKIP"), "is SKIP"),
            ("FAIL leg", HOST_X86, lambda r: leg(r, "x86_sse_lane_gate").update(status="FAIL"), "is FAIL"),
            ("parser disagrees", HOST_LOCAL, lambda r: leg(r, "meta_theorems").update(parser_status="skipped"),
             "parser status"),
            ("missing leg", HOST_LOCAL, lambda r: r.update(legs=[x for x in r["legs"] if x["id"] != "meta_theorems"]),
             "legs missing"),
            ("undeclared leg", HOST_LOCAL, lambda r: r["legs"].append(
                {"id": "made-up leg", "class": "host-independent", "status": "PASS"}), "outside this record"),
            ("dependency", HOST_LOCAL, lambda r: r["dependencies"].update(clean="2" * 40), "dependency tuple"),
            ("runner blob", HOST_LOCAL, lambda r: r["runner"].update(soundness_check="3" * 40), "runner blobs"),
            ("inventory", HOST_X86, lambda r: r["inventory"].update(sha256="4" * 64), "recorded inventory"),
            ("unbranded compiler", HOST_LOCAL,
             lambda r: r["toolchains"]["trust"].update(identity="binary: rustc\ncommit-hash: " + "7" * 40),
             "not a branded trustc"),
            ("no compiler commit", HOST_LOCAL,
             lambda r: r["toolchains"]["trust"].update(commit="unknown"), "no 40-hex commit identity"),
            ("targo unbound", HOST_X86, lambda r: r["executed"].pop("targo"), "executed targo is not bound"),
            ("ay unbound", HOST_LOCAL, lambda r: r["executed"]["campaign_ay"].update(sha256="5" * 64),
             "executed AY is not bound"),
            ("ay version", HOST_LOCAL, lambda r: r["executed"]["ay"].update(version="0.26.0"), "ay-pb pin"),
            ("clean unbound", HOST_LOCAL, lambda r: r["executed"].pop("clean"), "Clean checker"),
            ("aterm unrecorded", HOST_LOCAL, lambda r: r["dependencies"].pop("aterm"), "aterm"),
            ("refused setting", HOST_LOCAL, lambda r: r["environment"].update(refused=["X: y"]), "refused"),
            ("fuzz floor", HOST_LOCAL, lambda r: next(
                row for row in r["environment"]["settings"] if row["name"] == "WASM_CFG_FUZZ_FUNCS").update(value="10"),
             "below the floor"),
            ("imported mismatch", HOST_LOCAL, lambda r: r.update(
                imported=[{"triple": HOST_X86, "record": "6" * 40}]), "imported record"),
            # The environment rows are re-judged by the verifier's own allowlist.
            ("per-setting verdict", HOST_LOCAL, lambda r: r["environment"]["settings"].append(
                {"name": "SOME_KNOB", "verdict": "dropped"}), "setting SOME_KNOB was dropped"),
            ("re-derived allowlist", HOST_X86, lambda r: r["environment"]["settings"].append(
                {"name": "PYTHONPATH", "value": "/elsewhere", "verdict": "recorded"}),
             "PYTHONPATH is recorded in the record but refused under the allowlist-v1 allowlist"),
            ("policy", HOST_LOCAL, lambda r: r["environment"].update(policy="denylist"), "not the allowlist-v1"),
            ("cargo config", HOST_LOCAL, lambda r: r["environment"].update(
                cargo_configs=[{"path": "/elsewhere/.cargo/config.toml", "sha256": "0" * 64}]),
             "uncommitted Cargo configuration"),
            # The per-host Trust compiler pin (scripts/run_public_release_checks.sh at C).
            ("trustc pin", HOST_LOCAL, lambda r: r["toolchains"]["trust"].update(
                identity=r["toolchains"]["trust"]["identity"].replace(
                    "(7777777 2026-09-17)", "(94d61d9b6 2026-06-15)", 1)), "pins 'rustc 1.99.0-dev (7777777"),
            ("targo of another build", HOST_LOCAL, lambda r: r["toolchains"]["trust"].update(
                targo_version="targo 1.99.0-dev (8888888 2026-09-18) (targo 0.1.0)"), "is not the build of"),
            ("trust host", HOST_LOCAL, lambda r: r["toolchains"]["trust"].update(host="aarch64-unknown-linux-gnu"),
             "is not the one its -vV reports"),
            # A derived overlay is not a release input (OD-RELEASE-BOUNDARY-20261008),
            # and a record that does not say whether its package was one is refused.
            ("overlay toolchain", HOST_LOCAL, lambda r: r["toolchains"]["trust"].update(
                overlay={"path": "/o/overlay.json", "sha256": "e" * 64, "schema": "trust-cg.trust-overlay.v1"}),
             "an overlay is not a release input"),
            ("overlay unstated", HOST_X86, lambda r: r["toolchains"]["trust"].pop("overlay"),
             "does not state whether its Trust package was a derived overlay"),
        )
        for name, triple, change, fragment in cases:
            with self.subTest(name):
                self.setUp()
                self.edit(triple, change)
                rc, output = self.verify()
                self.assertEqual(rc, 1, output)
                self.assertIn(fragment, output)

    def test_a_host_without_a_pin_is_reported_not_compared(self):
        rc, output = self.verify()
        self.assertEqual(rc, 0, output)
        self.assertIn(f"pins no exact Trust compiler for {HOST_X86}", output)
        self.assertNotIn(f"pins no exact Trust compiler for {HOST_LOCAL}", output)

    def test_missing_x86_record_is_incomplete(self):
        SA.git(self.world.cg, "update-ref", "-d", SA.ref_name(self.commit, HOST_X86))
        rc, output = self.verify()
        self.assertEqual(rc, 1, output)
        self.assertIn("x86_64-native leg x86_sse_lane_gate has no PASS from a native x86-64 host", output)
        self.assertIn("imported record", output)

    def test_landing_verdict_of_a_full_record_set_is_the_release_one(self):
        rc, output = self.verify("--landing")
        self.assertEqual(rc, 0, output)
        self.assertIn("attested for landing by", output)
        self.assertNotIn("NOT ATTESTED", output)
        # A full record without its x86-64 record is no landing record either:
        # the deferral applies to portable records only.
        SA.git(self.world.cg, "update-ref", "-d", SA.ref_name(self.commit, HOST_X86))
        rc, output = self.verify("--landing")
        self.assertEqual(rc, 1, output)
        self.assertIn("x86_64-native leg x86_sse_lane_gate has no PASS from a native x86-64 host", output)

    def test_an_overlay_record_is_a_landing_record_only(self):
        self.edit(HOST_LOCAL, lambda r: r["toolchains"]["trust"].update(
            overlay={"path": "/o/overlay.json", "sha256": "e" * 64, "schema": "trust-cg.trust-overlay.v1"}))
        rc, output = self.verify()
        self.assertEqual(rc, 1, output)
        self.assertIn("never satisfies release verification", output)
        rc, output = self.verify("--landing")
        self.assertEqual(rc, 0, output)
        self.assertIn("accepted for landing only, an overlay is not a release input", output)

    def test_x86_record_alone_is_incomplete(self):
        SA.git(self.world.cg, "update-ref", "-d", SA.ref_name(self.commit, HOST_LOCAL))
        rc, output = self.verify()
        self.assertEqual(rc, 1, output)
        self.assertIn("no full-scope record", output)

    # ---- write -------------------------------------------------------------
    def test_duplicate_scope_cannot_be_written_or_verify_as_a_green_record(self):
        text = SA.show_blob(self.world.cg, self.refs[HOST_LOCAL], "attestation.json")
        ambiguous = lambda value: '{"scope":"portable",' + value.lstrip()[1:]
        self.assertEqual(json.loads(ambiguous(text)), json.loads(text))
        with tempfile.TemporaryDirectory() as directory:
            Path(directory, "attestation.json").write_text(ambiguous(text))
            result = self.world.tool("write", "--repo", str(self.world.cg), "--record-dir", directory)
            self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
            self.assertEqual(SA.records_for(self.world.cg, self.commit), self.refs)
        self.edit(HOST_LOCAL, lambda record: None, text_change=ambiguous)
        rc, output = self.verify()
        self.assertEqual(rc, 2, output)
        self.assertIn("duplicate", output)

    def test_wrong_record_shapes_are_malformed_for_writer_and_verifier(self):
        baseline = json.loads(SA.show_blob(self.world.cg, self.refs[HOST_LOCAL], "attestation.json"))
        for path, mutant in RecordShapeTests.mutants():
            # Use the real green fixture, not a hand-written attestation.
            keys = path.split(".")
            value = mutant
            for key in keys:
                value = value[key]
            record = copy.deepcopy(baseline)
            parent = record
            for key in keys[:-1]:
                parent = parent.setdefault(key, {})
            parent[keys[-1]] = value
            with self.subTest(path=path), tempfile.TemporaryDirectory() as directory:
                for triple, oid in self.refs.items():
                    SA.git(self.world.cg, "update-ref", SA.ref_name(self.commit, triple), oid)
                Path(directory, "attestation.json").write_text(json.dumps(record))
                result = self.world.tool("write", "--repo", str(self.world.cg), "--record-dir", directory)
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertNotIn("Traceback", result.stderr)
                self.assertEqual(SA.records_for(self.world.cg, self.commit), self.refs)
                self.edit(HOST_LOCAL, lambda original: (original.clear(), original.update(record)))
                rc, output = self.verify()
                self.assertEqual(rc, 2, output)
                self.assertNotIn("Traceback", output)

    def test_write_keeps_a_green_record_and_refuses_a_bad_one(self):
        with tempfile.TemporaryDirectory() as directory:
            record = json.loads(SA.show_blob(self.world.cg, self.refs[HOST_LOCAL], "attestation.json"))
            Path(directory, "attestation.json").write_text(json.dumps(record))
            result = self.world.tool("write", "--repo", str(self.world.cg), "--record-dir", directory)
            self.assertEqual(result.returncode, 0, result.stdout)
            self.assertIn("kept it", result.stdout)
            self.assertEqual(SA.records_for(self.world.cg, self.commit)[HOST_LOCAL], self.refs[HOST_LOCAL])
            self.edit(HOST_LOCAL, lambda r: r["subject"].update(tree="0" * 40))
            result = self.world.tool("write", "--repo", str(self.world.cg), "--record-dir", directory)
            self.assertEqual(result.returncode, 1, result.stdout)
            self.assertIn("not a valid record", result.stdout)

    def test_write_publishes_the_local_and_imported_records_together_or_not_at_all(self):
        # A lock on the local record's ref makes its create fail after the
        # imported record's create was queued: one transaction leaves neither.
        local_ref = SA.ref_name(self.commit, HOST_LOCAL)
        with tempfile.TemporaryDirectory() as directory:
            record_dir = Path(directory, "record")
            record_dir.mkdir()
            archive = subprocess.run(["git", "-C", str(self.world.cg), "archive", self.refs[HOST_LOCAL]],
                                     check=True, capture_output=True).stdout
            with tarfile.open(fileobj=io.BytesIO(archive)) as packed:
                for member in packed.getmembers():
                    destination = (record_dir / member.name).resolve()
                    destination.relative_to(record_dir.resolve())
                    if member.isdir():
                        destination.mkdir(parents=True, exist_ok=True)
                    else:
                        self.assertTrue(member.isfile(), member.name)
                        destination.parent.mkdir(parents=True, exist_ok=True)
                        with packed.extractfile(member) as source:
                            destination.write_bytes(source.read())
            for triple in self.refs:
                SA.git(self.world.cg, "update-ref", "-d", SA.ref_name(self.commit, triple))
            lock = Path(SA.git(self.world.cg, "rev-parse", "--path-format=absolute", "--git-path",
                               local_ref).strip() + ".lock")
            lock.parent.mkdir(parents=True, exist_ok=True)
            lock.write_text("")
            try:
                result = self.world.tool("write", "--repo", str(self.world.cg), "--record-dir", str(record_dir))
            finally:
                lock.unlink()
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertEqual(SA.records_for(self.world.cg, self.commit), {})
            # Unlocked, the same write publishes both.
            result = self.world.tool("write", "--repo", str(self.world.cg), "--record-dir", str(record_dir))
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(set(SA.records_for(self.world.cg, self.commit)), {HOST_LOCAL, HOST_X86})
            self.assertEqual(SA.records_for(self.world.cg, self.commit)[HOST_X86], self.refs[HOST_X86])

    # ---- build -------------------------------------------------------------
    def test_build_refuses_what_verify_would_refuse(self):
        self.assertIsNotNone(self.logdir)
        for name, edit, fragment in (
            ("a leg did not pass", lambda text: text.replace("\tPASS\t", "\tFAIL\t", 1), "not every leg passed"),
            ("a declared leg is missing", lambda text: "\n".join(
                line for line in text.splitlines() if not line.startswith("meta_theorems\t")) + "\n",
             "missing ['meta_theorems']"),
            ("an undeclared leg", lambda text: text + "extra\tPASS\t0\t\tfixture\n", "undeclared ['extra']"),
            ("a leg recorded twice", lambda text: text + text.splitlines()[0] + "\n", "recorded twice"),
        ):
            with self.subTest(name), tempfile.TemporaryDirectory() as directory:
                logdir = Path(directory, "logs")
                shutil.copytree(self.logdir, logdir)
                tsv = logdir / "legs.tsv"
                tsv.write_text(edit(tsv.read_text()))
                result = self.world.tool("build", "--repo", str(self.world.cg), "--commit", self.commit,
                                         "--scope", "full", "--logdir", str(logdir), "--out",
                                         str(Path(directory, "record")), "--clean-bin", str(self.world.cg / "Cargo.toml"),
                                         "--aterm", str(logdir / "aterm.json"))
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn(fragment, result.stdout)

    def test_build_refuses_an_unbound_campaign_ay(self):
        """The proof_gate_strict log must name exactly one AY, admitted by the toolchain route."""
        line = "proof_gate_strict: executed-ay "
        for name, rewrite, fragment in (
            ("no line", lambda text: "\n".join(l for l in text.splitlines() if not l.startswith(line)) + "\n",
             "exactly one executed AY"),
            ("unresolved", lambda text: text + line + "unresolved: TCG-AY-IDENTITY-UNRECORDED\n", "admitted no AY"),
            ("override route", lambda text: text.replace("route=toolchain-pinned-ay", "route=override-pinned-ay"),
             "not toolchain-pinned-ay"),
            ("two AYs", lambda text: text + line + "sha256=" + "9" * 64 + " route=toolchain-pinned-ay ay=/x/ay\n",
             "exactly one executed AY"),
        ):
            with self.subTest(name), tempfile.TemporaryDirectory() as directory:
                logdir = Path(directory, "logs")
                shutil.copytree(self.logdir, logdir)
                log = next(logdir.glob("cargo_trust-cg-verify_integration_proof_gate_strict.log"))
                log.write_text(rewrite(log.read_text()))
                legs = (logdir / "legs.tsv").read_text().replace(str(self.logdir), str(logdir))
                (logdir / "legs.tsv").write_text(legs)
                result = self.world.tool("build", "--repo", str(self.world.cg), "--commit", self.commit,
                                         "--scope", "full", "--logdir", str(logdir), "--out",
                                         str(Path(directory, "record")), "--clean-bin", str(self.world.cg / "Cargo.toml"),
                                         "--aterm", str(logdir / "aterm.json"))
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn(fragment, result.stdout)

    def test_build_binds_the_ay_the_campaign_executed(self):
        with tempfile.TemporaryDirectory() as directory:
            logdir = Path(directory, "logs")
            shutil.copytree(self.logdir, logdir)
            identities = json.loads((logdir / "identities.json").read_text())
            identities["executed"]["ay"]["sha256"] = "7" * 64
            (logdir / "identities.json").write_text(json.dumps(identities))
            result = self.world.tool("build", "--repo", str(self.world.cg), "--commit", self.commit, "--scope", "full",
                                     "--logdir", str(logdir), "--out", str(Path(directory, "record")),
                                     "--clean-bin", str(self.world.cg / "Cargo.toml"),
                                     "--aterm", str(logdir / "aterm.json"))
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("executed AY sha256", result.stdout)



class FixtureGitIdentityTests(unittest.TestCase):
    def test_system_python_link_names_the_interpreter_behind_a_dispatcher(self):
        import shlex

        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            system = root / "system"
            system.mkdir()
            dispatcher = system / "python3"
            dispatcher.write_text("#!/bin/sh\nexec " + shlex.quote(sys.executable) + ' "$@"\n')
            dispatcher.chmod(0o700)
            with mock.patch.object(fixture, "SYSTEM_PATH", (str(system),)):
                commands = fixture.system_commands(root / "commands")
            linked = commands / "python3"
            self.assertEqual(linked.resolve(), Path(sys.executable).resolve())
            self.assertNotEqual(linked.resolve(), dispatcher)

    def test_darwin_fixture_identity_is_explicitly_synthetic_and_byte_bound(self):
        temporary = fixture.FixtureDirectory("attestation-darwin-fixture-")
        self.addCleanup(temporary.cleanup)
        world = fixture.Constellation(Path(temporary.name))
        spec = importlib.util.spec_from_file_location("fixture_darwin_attestation",
                                                      world.cg / "scripts/soundness_attestation.py")
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        oracle = module.darwin_c_oracle()
        self.assertIn("synthetic soundness fixture", oracle["compiler"]["version"])
        self.assertEqual(oracle["compiler"]["sha256"], SA.sha256_file(Path(oracle["compiler"]["path"])))
        self.assertIsNone(SA.darwin_c_oracle_problem({"toolchains": {"darwin_c_oracle": oracle}}))
        spec = importlib.util.spec_from_file_location("fixture_darwin_boundary",
                                                      world.cg / "scripts/host_boundary.py")
        boundary_module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(boundary_module)
        boundary = mock.Mock()
        boundary.resolve.side_effect = lambda path, place: path
        boundary_module.judge_darwin_c_oracle(boundary)
        boundary.resolve.assert_called_once_with(oracle["compiler"]["path"], "the Darwin C oracle")
        compiler_root = str(Path(oracle["compiler"]["path"]).parent.parent)
        boundary.judge_tree.assert_any_call(compiler_root, "the Darwin C compiler install root")
        boundary.judge_tree.assert_any_call(oracle["sdk"]["path"], "the Darwin C oracle SDK")

    def test_raw_fixture_commit_needs_no_global_or_environment_identity(self):
        temporary = fixture.FixtureDirectory("attestation-local-identity-")
        self.addCleanup(temporary.cleanup)
        world = fixture.Constellation(Path(temporary.name))
        env = dict(os.environ)
        for name in ("GIT_AUTHOR_NAME", "GIT_AUTHOR_EMAIL", "GIT_COMMITTER_NAME", "GIT_COMMITTER_EMAIL"):
            env.pop(name, None)
        env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")
        with mock.patch.dict(os.environ, env, clear=True):
            tree = SA.rev_parse(world.cg, world.head() + "^{tree}")
            commit = SA.git(world.cg, "commit-tree", tree, "-m", "fixture with no global identity").strip()
            identity = SA.git(world.cg, "show", "-s", "--format=%an <%ae>%n%cn <%ce>", commit)
        self.assertEqual(identity.splitlines(), ["Fixture <fixture@example.invalid>"] * 2)


class AnchorTests(unittest.TestCase):
    """verify-anchored runs the anchor's verifier and refuses inventory shrinkage."""

    @classmethod
    def setUpClass(cls):
        cls.temporary = fixture.FixtureDirectory("attestation-anchor-")
        cls.world = fixture.Constellation(Path(cls.temporary.name))
        cls.anchor = cls.world.head()
        script = cls.world.cg / "scripts" / "soundness_check.sh"
        text = script.read_text()
        # The candidate drops a gate from the inventory.
        script.write_text(text.replace("  x86_movsxd_sib_gate\n  x86_addressing_gate\n", "  x86_addressing_gate\n"))
        cls.candidate = cls.world.commit_all("drop a gate")
        result = cls.world.run_gate("--attest")
        if result.returncode != 0:
            raise AssertionError("fixture attest run failed:\n" + result.stdout[-4000:])

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def anchored(self, commit, anchor, *extra):
        result = self.world.tool("verify-anchored", commit, "--anchor", anchor, "--repo", str(self.world.cg), *extra)
        return result.returncode, result.stdout + result.stderr

    def test_candidate_verifies_alone_but_not_against_its_anchor(self):
        result = self.world.tool("verify", self.candidate, "--repo", str(self.world.cg))
        self.assertEqual(result.returncode, 0, result.stdout)
        # A commit never anchors its own verification.
        rc, output = self.anchored(self.candidate, self.candidate)
        self.assertEqual(rc, 2, output)
        self.assertIn("the candidate itself", output)
        result = self.world.tool("verify", self.candidate, "--anchor", self.candidate, "--repo", str(self.world.cg))
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("never anchors its own verification", result.stdout)
        rc, output = self.anchored(self.candidate, self.anchor)
        self.assertEqual(rc, 1, output)
        self.assertIn("'x86_movsxd_sib_gate' is in anchor", output)
        self.assertIn("notice: gate surface changed since anchor", output)
        self.assertIn("scripts/soundness_check.sh", output)
        self.assertIn(f"anchored: verifier from {self.anchor[:12]}", output)

    def test_an_explicitly_accepted_removal_verifies(self):
        rc, output = self.anchored(self.candidate, self.anchor, "--accept-removed-legs", "x86_movsxd_sib_gate")
        self.assertEqual(rc, 0, output)
        self.assertIn("removed since the anchor (explicitly accepted)", output)

    def test_the_anchor_verifier_is_the_one_that_runs(self):
        # A candidate whose own verifier approves everything is still judged by
        # the anchor's committed verifier.
        tool = self.world.cg / "scripts" / "soundness_attestation.py"
        original = tool.read_text()
        tool.write_text(original.replace('def cmd_verify(args) -> int:\n',
                                         'def cmd_verify(args) -> int:\n    print("CANDIDATE VERIFIER"); return 0\n'))
        weakened = self.world.commit_all("weaken the verifier")
        try:
            rc, output = self.anchored(weakened, self.anchor)
            self.assertNotIn("CANDIDATE VERIFIER", output)
            self.assertEqual(rc, 3, output)  # the weakened commit has no records
            # Naming the candidate as its own anchor is refused before any verifier runs.
            rc, output = self.anchored(weakened, weakened)
            self.assertEqual(rc, 2, output)
            self.assertNotIn("CANDIDATE VERIFIER", output)
        finally:
            tool.write_text(original)
            self.world.commit_all("restore the verifier")

    def test_an_anchor_without_a_verifier_is_reported_unanchored(self):
        tool = self.world.cg / "scripts" / "soundness_attestation.py"
        original = tool.read_text()
        tool.unlink()
        bare = self.world.commit_all("no verifier")
        tool.write_text(original)
        restored = self.world.commit_all("verifier back")
        rc, output = self.anchored(restored, bare)
        self.assertEqual(rc, 2, output)
        self.assertIn("refused: UNANCHORED", output)
        rc, output = self.anchored(restored, bare, "--allow-unanchored-bootstrap")
        self.assertIn("UNANCHORED (bootstrap)", output)
        self.assertIn("not an anchored attestation", output)
        self.assertEqual(rc, 3, output)

    def test_anchor_must_be_an_ancestor(self):
        unrelated = SA.git(self.world.cg, "commit-tree", SA.rev_parse(self.world.cg, self.anchor + "^{tree}"),
                           "-m", "unrelated root").strip()
        result = self.world.tool("verify", self.candidate, "--anchor", unrelated, "--repo", str(self.world.cg))
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("is not an ancestor", result.stdout)
        # verify-anchored refuses it itself, before any anchored verifier runs.
        rc, output = self.anchored(self.candidate, unrelated)
        self.assertEqual(rc, 2, output)
        self.assertIn(f"refused: the anchor {unrelated[:12]} is not an ancestor", output)
        self.assertNotIn("anchored: verifier from", output)


class AnchorPolicyTests(unittest.TestCase):
    """anchor_checks directly: what an anchor demands of a candidate's inventory and pins."""

    @classmethod
    def setUpClass(cls):
        cls.temporary = fixture.FixtureDirectory("attestation-anchor-policy-")
        cls.world = fixture.Constellation(Path(cls.temporary.name))
        cls.anchor = cls.world.head()
        (cls.world.cg / "NEXT").write_text("next\n")
        cls.candidate = cls.world.commit_all("next")

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    @staticmethod
    def inventory(**legs):
        return {"legs": [{"id": leg_id, "class": leg_class} for leg_id, leg_class in legs.items()]}

    def check(self, anchor_class, now_class, **kwargs):
        return SA.anchor_checks(self.world.cg, self.candidate, self.anchor, self.inventory(leg=now_class),
                                self.inventory(leg=anchor_class), (), **kwargs)

    def test_a_leg_may_not_leave_a_stronger_class(self):
        for before, after in (("x86_64-native", "host-independent"), ("x86_64-native", "dispatch"),
                              ("per-run", "host-independent"), ("host-independent", "dispatch")):
            with self.subTest(f"{before} -> {after}"):
                problems, _ = self.check(before, after)
                self.assertEqual(problems, [f"leg 'leg' changed class {before} -> {after} since the anchor"])

    def test_other_class_changes_are_notes(self):
        for before, after in (("host-independent", "per-run"), ("dispatch", "host-independent")):
            with self.subTest(f"{before} -> {after}"):
                problems, lines = self.check(before, after)
                self.assertEqual(problems, [])
                self.assertIn(f"note: leg 'leg' changed class {before} -> {after} since the anchor", lines)

    def test_a_leg_may_not_move_into_a_class_the_anchor_defers(self):
        # While the anchor defers x86_64-native for landing, moving a leg there
        # would let a portable record skip it; with no deferral it is a note.
        problems, _ = self.check("host-independent", "x86_64-native")
        self.assertEqual(problems, ["leg 'leg' changed class host-independent -> x86_64-native since the anchor "
                                    "(into a class this verifier defers for landing)"])
        saved = SA.DEFERRED_LANDING_CLASSES
        SA.DEFERRED_LANDING_CLASSES = {}
        try:
            problems, lines = self.check("host-independent", "x86_64-native")
        finally:
            SA.DEFERRED_LANDING_CLASSES = saved
        self.assertEqual(problems, [])
        self.assertIn("note: leg 'leg' changed class host-independent -> x86_64-native since the anchor", lines)

    def test_a_candidate_cannot_add_a_deferred_class(self):
        """The deferral only shrinks: the anchor's verifier refuses a candidate
        whose constant names a class its own does not, whatever its records."""
        problems, _ = self.check("per-run", "per-run",
                                 candidate_deferred=dict(SA.DEFERRED_LANDING_CLASSES, **{"host-independent": "x"}))
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("defers 'host-independent', which the anchor's does not", problems[0])
        saved = SA.DEFERRED_LANDING_CLASSES
        SA.DEFERRED_LANDING_CLASSES = {}
        try:
            problems, _ = self.check("per-run", "per-run", candidate_deferred={"x86_64-native": "x"})
        finally:
            SA.DEFERRED_LANDING_CLASSES = saved
        self.assertEqual(len(problems), 1, problems)
        self.assertIn("defers 'x86_64-native', which the anchor's does not", problems[0])
        # Shrinking (the withdrawal) is a note, never a problem.
        problems, lines = self.check("per-run", "per-run", candidate_deferred={})
        self.assertEqual(problems, [])
        self.assertIn("withdraws the landing deferral of 'x86_64-native'", "\n".join(lines))

    def test_the_candidate_is_never_its_own_anchor(self):
        problems, _ = SA.anchor_checks(self.world.cg, self.candidate, self.candidate, self.inventory(leg="per-run"),
                                       self.inventory(leg="per-run"), ())
        self.assertTrue(problems and "never anchors its own verification" in problems[0], problems)

    def test_a_trustc_pin_may_not_disappear(self):
        problems, _ = self.check("per-run", "per-run", pins={}, anchor_pins={HOST_LOCAL: "rustc x"})
        self.assertEqual(len(problems), 1)
        self.assertIn(f"the anchor pins a Trust compiler for {HOST_LOCAL}", problems[0])
        problems, _ = self.check("per-run", "per-run", pins={HOST_LOCAL: "rustc y"},
                                 anchor_pins={HOST_LOCAL: "rustc x"})
        self.assertEqual(problems, [])  # moving a pin is a toolchain migration, listed as a gate-surface change


class TrustcPinParsingTests(unittest.TestCase):
    def test_trustc_pins_read_the_release_gate_spelling(self):
        text = (ROOT / SA.TRUSTC_PIN_FILE).read_text()
        pins = SA.trustc_pins(text)
        self.assertEqual(set(pins), {"aarch64-apple-darwin", "aarch64-unknown-linux-gnu"})
        for line in pins.values():
            self.assertRegex(line, r"^rustc \S+ \([^)]+\) \(trustc [^()]+\)$")
        # Hosts can move to different Trust versions. Preserve each exact pin,
        # including branded build metadata, rather than assuming one version.
        darwin = "rustc 1.101.0-dev (d460ce139 2026-10-28) (trustc 0.12.0+gd460ce139)"
        linux = "rustc 1.99.0-dev (ae9c2c1da 2026-09-21) (trustc 0.1.0)"
        source = (f"aarch64-apple-darwin)\n expected_trustc='{darwin}'\n;;\n"
                  f"aarch64-unknown-linux-gnu)\n expected_trustc='{linux}'\n;;\n")
        self.assertEqual(SA.trustc_pins(source),
                         {"aarch64-apple-darwin": darwin, "aarch64-unknown-linux-gnu": linux})
        with self.assertRaises(SA.Malformed):
            SA.trustc_pins("a-b)\n expected_trustc='x'\na-b) expected_trustc='y'\n")


class IdentityPreflightTests(unittest.TestCase):
    """`identities`, the preflight row: it refuses a wrong AY or Trust compiler before any leg runs."""

    def setUp(self):
        self.temporary = fixture.FixtureDirectory("attestation-identities-")
        self.addCleanup(self.temporary.cleanup)
        self.world = fixture.Constellation(Path(self.temporary.name))

    def identities(self):
        out = Path(self.temporary.name, "identities.json")
        result = self.world.tool("identities", "--repo", str(self.world.cg), "--scope", "full", "--out", str(out),
                                 "--island-twin-rustc", str(self.world.bin / "rustc"))
        return result.returncode, result.stdout + result.stderr

    def test_a_matching_package_passes(self):
        rc, output = self.identities()
        self.assertEqual(rc, 0, output)

    def test_an_ay_of_another_version_is_refused(self):
        fixture.write(self.world.sysroot / "bin" / "ay",
                      f"#!/bin/sh\necho 'ay {fixture.AY_STAMP.replace(fixture.AY_PIN_VERSION, '0.26.0')}'\n",
                      executable=True)
        rc, output = self.identities()
        self.assertEqual(rc, 1, output)
        self.assertIn(f"is version 0.26.0, not the ay-pb pin version {fixture.AY_PIN_VERSION}", output)

    def test_an_overlay_sysroot_is_recorded_and_a_pack_is_stated_as_none(self):
        out = Path(self.temporary.name, "identities.json")
        rc, output = self.identities()
        self.assertEqual(rc, 0, output)
        self.assertIsNone(json.loads(out.read_text())["toolchains"]["trust"]["overlay"])
        manifest = self.world.sysroot / "overlay.json"
        manifest.write_text(json.dumps({"schema": "trust-cg.trust-overlay.v1"}))
        rc, output = self.identities()
        self.assertEqual(rc, 0, output)
        overlay = json.loads(out.read_text())["toolchains"]["trust"]["overlay"]
        self.assertEqual(overlay["schema"], "trust-cg.trust-overlay.v1")
        self.assertEqual(overlay["sha256"], SA.sha256_bytes(manifest.read_bytes()))

    def test_a_trustc_other_than_the_host_pin_is_refused(self):
        pin = self.world.cg / SA.TRUSTC_PIN_FILE
        pin.write_text(pin.read_text().replace("(7777777 2026-09-17)", "(94d61d9b6 2026-06-15)"))
        rc, output = self.identities()
        self.assertEqual(rc, 1, output)
        self.assertIn("pins 'rustc 1.99.0-dev (94d61d9b6 2026-06-15) (trustc 0.1.0)'", output)


class LandingExceptionDiscoveryTests(unittest.TestCase):
    """Real local remotes: absent clone metadata cannot authorize a bypass.

    A deliberately malformed record ref is used ONLY for the documented
    presence ratchet. It must end the exception and grants no proof verdict.
    No network service, Rust job, or actual publication is involved.
    """

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="landing-discovery-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        config = self.base / "gitconfig"
        config.write_text("[user]\n name = Discovery fixture\n email = discovery@example.invalid\n"
                          "[commit]\n gpgSign = false\n[init]\n defaultBranch = main\n")
        self.env = dict(os.environ, GIT_CONFIG_GLOBAL=str(config), GIT_CONFIG_NOSYSTEM="1")
        self.remote = self.base / "remote.git"
        self.seed = self.base / "seed"
        self.clone = self.base / "clone"
        self.git(self.base, "init", "-q", "--bare", str(self.remote))
        self.git(self.base, "init", "-q", str(self.seed))
        (self.seed / "source").write_text("initial\n")
        self.git(self.seed, "add", "source")
        self.git(self.seed, "commit", "-qm", "initial")
        self.anchor = self.git(self.seed, "rev-parse", "HEAD").strip()
        self.git(self.seed, "remote", "add", "origin", str(self.remote))
        self.git(self.seed, "push", "-q", "origin", "HEAD:refs/heads/main")
        self.git(self.base, "clone", "-q", str(self.remote), str(self.clone))
        self.record_ref = f"{SA.REF_PREFIX}/{self.anchor}/presence-only-fixture"

    def git(self, repo, *args):
        result = subprocess.run(["git", "-C", str(repo), *args], env=self.env,
                                capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def query(self, *, anchor="origin/main", remote="origin"):
        return subprocess.run([sys.executable, str(ROOT / "scripts/soundness_attestation.py"),
                               "landing-exception", "--repo", str(self.clone),
                               "--anchor", anchor, f"--remote={remote}"], env=self.env,
                              capture_output=True, text=True, timeout=30)

    def publish_presence(self):
        self.git(self.seed, "update-ref", self.record_ref, self.anchor)
        self.git(self.seed, "push", "-q", "origin", self.record_ref)

    def test_fresh_clone_discovers_remote_record_before_claiming_in_force(self):
        self.publish_presence()
        self.assertEqual(self.git(self.clone, "for-each-ref", SA.REF_PREFIX + "/"), "")
        self.assertTrue(SA.landing_exception(self.clone, self.anchor)[0])
        result = self.query()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("ENDED", result.stdout)
        self.assertIn("grants no landing or release verdict", result.stdout)
        self.assertTrue(self.git(self.clone, "for-each-ref", self.record_ref))

    def test_actual_initial_epoch_requires_successful_remote_discovery(self):
        result = self.query()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("IN FORCE", result.stdout)
        self.assertIn("discovered from the selected remote", result.stdout)

    def test_unavailable_remote_cannot_turn_absent_local_refs_into_permission(self):
        self.git(self.clone, "remote", "set-url", "origin", str(self.base / "unavailable.git"))
        result = self.query()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("UNDETERMINED", result.stdout)
        self.assertNotIn("IN FORCE", result.stdout)

    def test_stale_literal_anchor_refuses_and_tracking_anchor_refreshes(self):
        (self.seed / "source").write_text("later\n")
        self.git(self.seed, "commit", "-qam", "later")
        self.git(self.seed, "push", "-q", "origin", "HEAD:refs/heads/main")
        result = self.query(anchor=self.anchor)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("UNDETERMINED", result.stdout)
        self.assertNotIn("IN FORCE", result.stdout)
        result = self.query()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_selected_nondefault_remote_is_not_replaced_by_empty_origin(self):
        decoy = self.base / "decoy.git"
        self.git(self.base, "clone", "-q", "--bare", str(self.remote), str(decoy))
        self.publish_presence()
        self.git(self.clone, "remote", "set-url", "origin", str(decoy))
        self.git(self.clone, "remote", "add", "actual", str(self.remote))
        result = self.query(anchor=self.anchor, remote="actual")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("ENDED", result.stdout)

    def test_retained_record_cannot_be_revived_by_remote_deletion_or_failure(self):
        self.publish_presence()
        self.assertEqual(self.query().returncode, 1)
        self.git(self.seed, "push", "-q", "origin", ":" + self.record_ref)
        self.git(self.clone, "remote", "set-url", "origin", str(self.base / "gone.git"))
        result = self.query()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("ENDED", result.stdout)

    def test_a_named_remotes_decoy_fetch_url_cannot_hide_its_push_records(self):
        decoy = self.base / "decoy.git"
        self.git(self.base, "clone", "-q", "--bare", str(self.remote), str(decoy))
        self.publish_presence()
        self.git(self.clone, "remote", "set-url", "origin", str(decoy))
        self.git(self.clone, "remote", "set-url", "--push", "origin", str(self.remote))
        result = self.query(anchor=self.anchor)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("ENDED", result.stdout)

    def test_multiple_push_locations_do_not_authorize_a_single_bypass(self):
        self.git(self.clone, "remote", "set-url", "--add", "--push", "origin", str(self.remote))
        self.git(self.clone, "remote", "set-url", "--add", "--push", "origin", str(self.base / "other.git"))
        result = self.query()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("UNDETERMINED", result.stdout)
        self.assertNotIn("IN FORCE", result.stdout)

    def test_remote_option_cannot_be_interpreted_as_a_git_option(self):
        result = self.query(remote="--upload-pack=unexpected")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("UNDETERMINED", result.stdout)
        self.assertNotIn("IN FORCE", result.stdout)

    def test_named_push_url_cannot_be_interpreted_as_a_git_option(self):
        self.git(self.clone, "config", "remote.origin.pushurl", "--upload-pack=unexpected")
        result = self.query()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("UNDETERMINED", result.stdout)
        self.assertNotIn("IN FORCE", result.stdout)


class PortableLandingTests(unittest.TestCase):
    """A real `--attest --scope portable` run: a landing record, never a release one."""

    @classmethod
    def setUpClass(cls):
        cls.temporary = fixture.FixtureDirectory("attestation-portable-")
        cls.world = fixture.Constellation(Path(cls.temporary.name))
        cls.anchor = cls.world.head()
        (cls.world.cg / "NEXT").write_text("a landing\n")
        cls.commit = cls.world.commit_all("a landing")
        result = cls.world.run_gate("--attest", "--scope", "portable")
        if result.returncode != 0:
            raise AssertionError("fixture portable run failed:\n" + result.stdout[-4000:] + result.stderr[-2000:])
        cls.workloads = cls.world.workloads()
        cls.logdir = fixture.logdir_of(result)
        cls.refs = SA.records_for(cls.world.cg, cls.commit)

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def verify(self, *args, commit=None):
        result = self.world.tool("verify", commit or self.commit, "--repo", str(self.world.cg), *args)
        return result.returncode, result.stdout + result.stderr

    def test_a_portable_run_writes_one_portable_record_and_dispatches_nothing(self):
        self.assertEqual(set(self.refs), {HOST_LOCAL})
        record = SA.load_record(self.world.cg, self.refs[HOST_LOCAL])
        self.assertEqual(record["scope"], "portable")
        self.assertEqual(record["imported"], [])
        classes = {leg["class"] for leg in record["legs"]}
        self.assertEqual(classes, {"per-run", "host-independent"})
        # It binds what a full record binds.
        self.assertEqual(record["executed"]["ay"]["sha256"], record["executed"]["campaign_ay"]["sha256"])
        self.assertTrue(SA.SHA256.match(record["executed"]["clean"]["sha256"]))
        self.assertTrue(SA.SHA256.match(record["dependencies"]["aterm"]["vt_tables_sha256"]))
        self.assertIsNone(record["toolchains"]["trust"]["overlay"])
        self.assertFalse([line for line in self.workloads if line.startswith("ssh ")], self.workloads)

    def test_release_verify_never_accepts_a_portable_record(self):
        """Guard: the release verdict demands a full record; it never reads the deferral."""
        rc, output = self.verify()
        self.assertEqual(rc, 1, output)
        self.assertIn("a portable record is a landing record (verify --landing), never a release record", output)
        self.assertNotIn("NOT ATTESTED", output)

    def test_landing_verify_accepts_it_while_the_class_is_deferred(self):
        rc, output = self.verify("--landing")
        self.assertEqual(rc, 0, output)
        self.assertIn("x86_64-native: NOT ATTESTED (OD-LANDING-X86-DEFERRAL-20261008): ", output)
        self.assertIn("x86_sse_lane_gate", output)
        self.assertIn("dispatch: NOT ATTESTED (OD-LANDING-X86-DEFERRAL-20261008): ", output)
        self.assertIn("coverage credits NOT ANCHORED on native silicon in this landing: Pshufd, Pmovmskb, MovdqaRR",
                      output)
        self.assertIn("attested for landing by", output)
        self.assertIn("NOT a release record", output)

    def test_the_deferral_that_applies_is_the_running_verifiers_not_the_candidates(self):
        # The candidate's committed verifier defers the class. A verifier whose
        # own constant is empty (an anchor after the withdrawal) refuses the
        # same records: the candidate's constant is never consulted.
        self.assertIn("x86_64-native", SA.deferred_landing_classes_in(
            SA.show_blob(self.world.cg, self.commit, "scripts/soundness_attestation.py")))
        saved = SA.DEFERRED_LANDING_CLASSES
        SA.DEFERRED_LANDING_CLASSES = {}
        try:
            rc, lines = SA.verify(self.world.cg, self.commit, landing=True)
        finally:
            SA.DEFERRED_LANDING_CLASSES = saved
        self.assertEqual(rc, 1, lines)
        self.assertIn("x86_64-native leg x86_sse_lane_gate has no PASS and the class is not deferred for landing",
                      "\n".join(lines))
        rc, lines = SA.verify(self.world.cg, self.commit, landing=True)
        self.assertEqual(rc, 0, lines)

    def test_anchored_landing_verification_runs_the_anchors_verifier(self):
        result = self.world.tool("verify-anchored", self.commit, "--anchor", self.anchor, "--landing",
                                 "--repo", str(self.world.cg))
        output = result.stdout + result.stderr
        self.assertEqual(result.returncode, 0, output)
        self.assertIn(f"anchored: verifier from {self.anchor[:12]}", output)
        self.assertIn("x86_64-native: NOT ATTESTED", output)
        # Without --landing the same anchored verifier gives the release verdict.
        result = self.world.tool("verify-anchored", self.commit, "--anchor", self.anchor, "--repo", str(self.world.cg))
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)

    def test_the_interim_exception_ends_at_the_first_landing_attested_commit(self):
        # The pure retained-record decision has no remote-discovery authority.
        self.assertTrue(SA.landing_exception(self.world.cg, self.anchor)[0])
        result = self.world.tool("landing-exception", "--repo", str(self.world.cg), "--anchor", self.anchor)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn("UNDETERMINED", result.stdout)
        result = self.world.tool("landing-exception", "--repo", str(self.world.cg), "--anchor", self.commit)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(f"ENDED: {self.commit}", result.stdout)
        # A later, unattested main tip (a bypass) does not revive it.
        (self.world.cg / "LATER").write_text("a bypass\n")
        later = self.world.commit_all("an unattested push")
        try:
            result = self.world.tool("landing-exception", "--repo", str(self.world.cg), "--anchor", later)
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        finally:
            SA.git(self.world.cg, "reset", "-q", "--hard", self.commit)
        # Withdrawing the deferral refuses the old record for a NEW landing,
        # but cannot revive permission to bypass the gate.
        saved = SA.DEFERRED_LANDING_CLASSES
        SA.DEFERRED_LANDING_CLASSES = {}
        try:
            in_force, lines = SA.landing_exception(self.world.cg, self.commit)
        finally:
            SA.DEFERRED_LANDING_CLASSES = saved
        self.assertFalse(in_force, lines)

    def test_historical_record_presence_is_not_revalidated_or_credited_as_a_verdict(self):
        from unittest.mock import patch

        # Schema upgrades can invalidate historical records too. The bypass
        # decision must not consult the new verdict; actual landing still does.
        with patch.object(SA, "verify", side_effect=AssertionError("historical revalidation")):
            in_force, lines = SA.landing_exception(self.world.cg, self.commit)
        self.assertFalse(in_force, lines)
        self.assertIn("Record presence grants no landing or release verdict", "\n".join(lines))

    def test_even_a_malformed_historical_record_conservatively_ends_the_exception(self):
        ref = SA.ref_name(self.commit, HOST_LOCAL)
        original = self.refs[HOST_LOCAL]
        # A ref to an ordinary source commit has no attestation.json. Forging
        # a record may end bypass permission early, never authorize a landing.
        SA.git(self.world.cg, "update-ref", ref, self.anchor)
        try:
            rc, lines = SA.verify(self.world.cg, self.commit, landing=True)
            self.assertNotEqual(rc, 0, lines)
            in_force, lines = SA.landing_exception(self.world.cg, self.commit)
            self.assertFalse(in_force, lines)
        finally:
            SA.git(self.world.cg, "update-ref", ref, original)

    def test_deferred_classes_prints_the_constant(self):
        result = self.world.tool("deferred-classes")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(json.loads(result.stdout), SA.DEFERRED_LANDING_CLASSES)

    def test_incomplete_git_history_cannot_authorize_bypassing(self):
        shallow = self.world.cg / ".git" / "shallow"
        self.assertFalse(shallow.exists())
        shallow.write_text(self.commit + "\n")
        try:
            in_force, lines = SA.landing_exception(self.world.cg, self.commit)
            self.assertFalse(in_force, lines)
            self.assertIn("incomplete Git history", "\n".join(lines))
        finally:
            shallow.unlink()

    def test_ancestry_error_is_not_treated_as_a_genuine_nonancestor(self):
        from unittest.mock import patch

        original_run = SA.run

        def failed_ancestry(argv, **kwargs):
            if "merge-base" in argv:
                return subprocess.CompletedProcess(argv, 128, b"", b"missing object")
            return original_run(argv, **kwargs)

        with patch.object(SA, "run", side_effect=failed_ancestry):
            in_force, lines = SA.landing_exception(self.world.cg, self.commit)
        self.assertFalse(in_force, lines)
        self.assertIn("cannot establish", "\n".join(lines))

    def test_a_portable_build_imports_nothing(self):
        with tempfile.TemporaryDirectory(dir=self.temporary.name) as directory:
            result = self.world.tool("build", "--repo", str(self.world.cg), "--commit", self.commit,
                                     "--scope", "portable", "--logdir", str(self.logdir), "--out",
                                     str(Path(directory, "record")), "--clean-bin", str(self.world.cg / "Cargo.toml"),
                                     "--aterm", str(self.logdir / "aterm.json"), "--imported", f"{HOST_X86}={'1' * 40}")
            self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
            self.assertIn("a portable record imports nothing", result.stdout)


class DeferralSourceTests(unittest.TestCase):
    """deferred_landing_classes_in: the candidate's constant, read without executing it."""

    def test_the_committed_constant_reads_back_exactly(self):
        source = (ROOT / "scripts/soundness_attestation.py").read_text()
        self.assertEqual(SA.deferred_landing_classes_in(source), SA.DEFERRED_LANDING_CLASSES)
        self.assertEqual(SA.DEFERRED_LANDING_CLASSES, {"x86_64-native": "OD-LANDING-X86-DEFERRAL-20261008"})

    def test_absent_constant_or_file_is_the_withdrawal(self):
        self.assertEqual(SA.deferred_landing_classes_in(None), {})
        self.assertEqual(SA.deferred_landing_classes_in("X = 1\n"), {})

    def test_anything_but_one_literal_binding_is_malformed(self):
        for name, source in (
            ("not a literal", "DEFERRED_LANDING_CLASSES = dict(a='b')\n"),
            ("not str -> str", "DEFERRED_LANDING_CLASSES = {'a': 1}\n"),
            ("assigned twice", "DEFERRED_LANDING_CLASSES = {}\nDEFERRED_LANDING_CLASSES = {'a': 'b'}\n"),
            ("changed in place", "DEFERRED_LANDING_CLASSES = {}\nDEFERRED_LANDING_CLASSES.update(a='b')\n"),
            ("item assignment", "DEFERRED_LANDING_CLASSES = {}\nDEFERRED_LANDING_CLASSES['a'] = 'b'\n"),
            ("rebound in a function", "DEFERRED_LANDING_CLASSES = {}\ndef f():\n    global DEFERRED_LANDING_CLASSES\n"
                                      "    DEFERRED_LANDING_CLASSES = {'a': 'b'}\n"),
            ("augmented", "DEFERRED_LANDING_CLASSES = {}\nDEFERRED_LANDING_CLASSES |= {'a': 'b'}\n"),
            ("imported", "from elsewhere import DEFERRED_LANDING_CLASSES\n"),
            ("globals()", "DEFERRED_LANDING_CLASSES = {}\nglobals()['DEFERRED_LANDING_CLASSES'] = {'a': 'b'}\n"),
            ("attribute store", "import sys\nDEFERRED_LANDING_CLASSES = {}\n"
                                "sys.modules[__name__].DEFERRED_LANDING_CLASSES = {'a': 'b'}\n"),
            ("syntax error", "DEFERRED_LANDING_CLASSES = {\n"),
        ):
            with self.subTest(name), self.assertRaises(SA.Malformed):
                SA.deferred_landing_classes_in(source)

    def test_coverage_names_only_what_a_portable_record_left_out(self):
        classes = {"a": "per-run", "b": "host-independent", "x": "x86_64-native", "d": "dispatch"}
        # Nothing native: the x86-64 class and its transport rows, both under the one ruling.
        groups = list(SA.deferred_coverage(classes, {"a": ["h"], "b": ["h"], "x": [], "d": []}))
        ruling = SA.DEFERRED_LANDING_CLASSES["x86_64-native"]
        self.assertEqual(groups, [("x86_64-native", ruling, ["x"]), ("dispatch", ruling, ["d"])])
        # A native record covers every x86-64 leg: the transport rows are not
        # asked for, and nothing is NOT ATTESTED.
        self.assertEqual(list(SA.deferred_coverage(classes, {"a": ["h"], "b": ["h"], "x": ["n"], "d": []})), [])
        # Without a deferral the same gap has no ruling.
        saved = SA.DEFERRED_LANDING_CLASSES
        SA.DEFERRED_LANDING_CLASSES = {}
        try:
            groups = list(SA.deferred_coverage(classes, {"a": ["h"], "b": ["h"], "x": [], "d": []}))
        finally:
            SA.DEFERRED_LANDING_CLASSES = saved
        self.assertEqual(groups, [("x86_64-native", None, ["x"]), ("dispatch", None, ["d"])])

    def test_dependent_credits_are_the_sse_lane_rows(self):
        """The NOT ANCHORED list is trust-cg-verify's SSE_LANE_ROWS, in order."""
        rust = (ROOT / "crates/trust-cg-verify/src/x86_sse_lane_proofs.rs").read_text()
        body = rust.split("pub const SSE_LANE_ROWS: [SseLaneOp; 10] = [", 1)[1].split("];", 1)[0]
        rows = tuple(item.strip().removeprefix("SseLaneOp::") if hasattr(str, "removeprefix")
                     else item.strip()[len("SseLaneOp::"):] for item in body.split(",") if item.strip())
        self.assertEqual(rows, SA.DEFERRED_CLASS_DEPENDENT_CREDITS["x86_64-native"])


class DependencyTupleTests(unittest.TestCase):
    def test_split_standalone_lock_is_malformed(self):
        with tempfile.TemporaryDirectory(prefix="attestation-deps-") as directory:
            world = fixture.Constellation(Path(directory))
            lock = world.cg / "fuzz" / "Cargo.lock"
            lock.write_text(lock.read_text().replace(world.clean_rev, "9" * 40))
            commit = world.commit_all("split the fuzz lock")
            with self.assertRaises(SA.Malformed):
                SA.dependency_tuple(world.cg, commit)
            deps = SA.dependency_tuple(world.cg, commit + "~1")
            self.assertEqual((deps["clean"], deps["ay_source"], deps["trust_ir"]),
                             (world.clean_rev, world.ay_rev, fixture.TRUST_IR))


if __name__ == "__main__":
    unittest.main()
