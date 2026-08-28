from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CHECKER_PATH = ROOT / "scripts" / "check_trust_default_authority.py"
SPEC = importlib.util.spec_from_file_location("check_trust_default_authority", CHECKER_PATH)
assert SPEC is not None and SPEC.loader is not None
CHECKER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CHECKER
SPEC.loader.exec_module(CHECKER)


class TrustDefaultAuthorityTests(unittest.TestCase):
    TRUST = '[toolchain]\nchannel = "trust"\n'
    COMMIT = "0123456789abcdef0123456789abcdef01234567"

    def test_upstream_default_is_honestly_unverified(self) -> None:
        self.assertEqual(
            CHECKER.policy_issues('[toolchain]\nchannel = "1.97.1"\n', ""), []
        )

    def test_advisory_refutation_acceptance_is_rejected(self) -> None:
        issues = CHECKER.policy_issues(
            self.TRUST,
            '[target.any]\nrustflags = ["-Ztrust-policy=advisory"]\n',
        )
        self.assertTrue(any("not strict or certify" in issue for issue in issues))

    def test_split_flags_and_every_non_authoritative_policy_are_rejected(self) -> None:
        for config in (
            '[target.any]\nrustflags = ["-Z", "trust-verify=off"]\n',
            '[target.any]\nrustflags = ["-Z", "trust-policy=memory-safe"]\n',
            '[target.any]\nrustflags = ["-Ztrust-policy=unknown"]\n',
        ):
            with self.subTest(config=config):
                self.assertTrue(CHECKER.policy_issues(self.TRUST, config))

    def test_strict_and_certify_are_the_only_explicit_policies(self) -> None:
        for policy in ("strict", "certify"):
            config = f'[target.any]\nrustflags = ["-Z", "trust-policy={policy}"]\n'
            with self.subTest(policy=policy):
                self.assertEqual(CHECKER.policy_issues(self.TRUST, config), [])

    def test_verified_default_requires_an_explicit_authoritative_policy(self) -> None:
        issues = CHECKER.policy_issues(self.TRUST, '[target.any]\nrustflags = []\n')
        self.assertTrue(any("explicitly select strict or certify" in issue for issue in issues))

    def test_rustc_wrappers_and_alternate_compilers_are_rejected(self) -> None:
        for config in (
            '[build]\nrustc-wrapper = "/tmp/wrapper"\n',
            '[build]\nrustc-workspace-wrapper = "/tmp/wrapper"\n',
            '[build]\nrustc = "/tmp/rustc"\n',
            'build.rustc = "/tmp/rustc"\n',
            '[env]\nRUSTC = "/tmp/rustc"\n',
            '[env]\nRUSTC_WRAPPER = "/tmp/wrapper"\n',
            '[env]\nRUSTC_WORKSPACE_WRAPPER = "/tmp/wrapper"\n',
            '[env]\nCARGO_BUILD_RUSTC = "/tmp/rustc"\n',
            '[env]\n"RUSTC\\u005fWRAPPER" = "/tmp/wrapper"\n',
        ):
            with self.subTest(config=config):
                issues = CHECKER.policy_issues(self.TRUST, config)
                self.assertTrue(any("wrapper or alternate rustc" in issue for issue in issues))

    def test_env_inline_and_encoded_trust_flags_are_rejected(self) -> None:
        configs = (
            '[build]\nrustflags = ["-Ztrust-policy=strict"]\n'
            '[env]\nRUSTFLAGS = "-Z trust-verify=off"\n',
            '[build]\nrustflags = ["-Ztrust-policy=strict"]\n'
            '[env]\nRUSTDOCFLAGS = { value = "-Ztrust-policy=advisory", force = true }\n',
            '[build]\nrustflags = ["-Ztrust-policy=strict"]\n'
            '[env]\nCARGO_ENCODED_RUSTFLAGS = "-Z\\u001ftrust-verify=off"\n',
            '[build]\nrustflags = ["-Ztrust-policy=strict"]\n'
            '[env]\nRUSTFLAGS = "\\u002dZtrust-policy=memory-safe"\n',
        )
        for config in configs:
            with self.subTest(config=config):
                issues = CHECKER.policy_issues(self.TRUST, config)
                self.assertTrue(
                    any(
                        "disables verification" in issue
                        or "not strict or certify" in issue
                        for issue in issues
                    )
                )

    def test_comments_cannot_inject_or_hide_trust_flags(self) -> None:
        config = (
            '[build]\nrustflags = ["-Ztrust-policy=strict"]\n'
            '# RUSTFLAGS = "-Ztrust-verify=off"\n'
        )
        self.assertEqual(CHECKER.policy_issues(self.TRUST, config), [])

    def test_ambient_flags_and_compiler_overrides_are_rejected(self) -> None:
        config = '[build]\nrustflags = ["-Ztrust-policy=strict"]\n'
        environments = (
            {"RUSTC_WRAPPER": "/tmp/wrapper"},
            {"CARGO_TARGET_TEST_HOST_RUSTFLAGS": "-Ztrust-verify=off"},
            {"CARGO_ENCODED_RUSTFLAGS": "-Z\x1ftrust-policy=advisory"},
        )
        for environment in environments:
            with self.subTest(environment=environment):
                self.assertTrue(CHECKER.policy_issues(self.TRUST, config, environment))

    def test_legacy_and_ambiguous_cargo_configuration_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "rust-toolchain.toml").write_text(self.TRUST, encoding="utf-8")
            cargo = root / ".cargo"
            cargo.mkdir()
            legacy = cargo / "config"
            legacy.write_text(
                '[build]\nrustflags = ["-Ztrust-policy=advisory"]\n', encoding="utf-8"
            )
            issues = CHECKER.check(root, False)
            self.assertTrue(any("not strict or certify" in issue for issue in issues))

            (cargo / "config.toml").write_text(
                '[build]\nrustflags = ["-Ztrust-policy=strict"]\n', encoding="utf-8"
            )
            issues = CHECKER.check(root, False)
            self.assertTrue(any("precedence is ambiguous" in issue for issue in issues))

    def test_rustdoc_and_host_opt_outs_are_rejected(self) -> None:
        for config in (
            '[target.any]\nrustdocflags = ["-Ztrust-verify=off"]\n',
            '[host]\nrustflags = ["-Ztrust-verify=off"]\n',
        ):
            with self.subTest(config=config):
                self.assertTrue(CHECKER.policy_issues(self.TRUST, config))

    def resolved(self, root: Path, commit_hash: str = COMMIT) -> object:
        host = "test-host"
        rustc = root / "bin" / "rustc"
        rustc.parent.mkdir(parents=True)
        rustc.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        rustc.chmod(0o555)
        std = root / "lib" / "rustlib" / host / "lib" / "libstd-test.rlib"
        std.parent.mkdir(parents=True)
        std.write_bytes(b"std")
        driver = root / "lib" / "librustc_driver-test.dylib"
        driver.write_bytes(b"driver")
        for artifact in root.rglob("*"):
            if artifact.is_dir():
                artifact.chmod(0o555)
            elif artifact == rustc:
                artifact.chmod(0o555)
            else:
                artifact.chmod(0o444)
        root.chmod(0o555)
        return CHECKER.ResolvedToolchain(rustc, root, root, root, host, commit_hash)

    def test_complete_read_only_sysroot_is_accepted(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / f"trust-{self.COMMIT}"
            root.mkdir()
            resolved = self.resolved(root)
            self.assertEqual(CHECKER.resolved_issues(resolved), [])

    def test_missing_rustc_and_sysroot_fail_closed(self) -> None:
        missing = CHECKER.ResolvedToolchain(None, None, None, None, None, None)
        issues = CHECKER.resolved_issues(missing)
        self.assertTrue(any("rustc" in issue for issue in issues))
        self.assertTrue(any("sysroot" in issue for issue in issues))

    def test_mutable_stage2_link_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            stage2 = Path(temporary) / "build" / "host" / "stage2"
            stage2.mkdir(parents=True)
            resolved = self.resolved(stage2)
            issues = CHECKER.resolved_issues(resolved)
            self.assertTrue(any("mutable build/host/stage2" in issue for issue in issues))

    def test_commit_hash_must_match_the_canonical_directory_name(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "trust-wrong"
            root.mkdir()
            issues = CHECKER.resolved_issues(self.resolved(root))
            self.assertTrue(any("directory must be named" in issue for issue in issues))

    def test_writable_nested_std_and_driver_artifacts_are_rejected(self) -> None:
        for relative in (
            Path("lib/rustlib/test-host/lib/libstd-test.rlib"),
            Path("lib/librustc_driver-test.dylib"),
        ):
            with self.subTest(relative=relative), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary) / f"trust-{self.COMMIT}"
                root.mkdir()
                resolved = self.resolved(root)
                (root / relative).chmod(0o644)
                issues = CHECKER.resolved_issues(resolved)
                self.assertTrue(any("writable artifact" in issue for issue in issues))

    def test_nested_symlink_escape_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = base / f"trust-{self.COMMIT}"
            root.mkdir()
            resolved = self.resolved(root)
            outside = base / "mutable-driver"
            outside.write_bytes(b"outside")
            lib = root / "lib"
            lib.chmod(0o755)
            (lib / "librustc_driver-escape.dylib").symlink_to(outside)
            lib.chmod(0o555)
            issues = CHECKER.resolved_issues(resolved)
            self.assertTrue(any("symlinked artifact" in issue for issue in issues))

    def fake_compiler(self, directory: Path, body: str) -> Path:
        compiler = directory / "rustc"
        compiler.write_text(f"#!/bin/sh\n{body}\n", encoding="utf-8")
        compiler.chmod(0o755)
        return compiler

    def test_behavioral_canary_requires_positive_and_refutation_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            compiler = self.fake_compiler(
                directory,
                """
case "$*" in
  *positive.rs*) exit 0 ;;
  *refutation.rs*)
    echo 'note: Trust verification: 0 proved, 1 failed, 0 unknown' >&2
    echo 'note: [div-zero] FAILED; counterexample: y = 0' >&2
    exit 1 ;;
  *) exit 91 ;;
esac
""",
            )
            self.assertEqual(CHECKER.behavioral_issues(compiler), [])

    def test_behavioral_canary_rejects_acceptance_and_nontrust_errors(self) -> None:
        bodies = (
            "exit 0",
            "case \"$*\" in *positive.rs*) exit 0 ;; *) echo syntax-error >&2; exit 1 ;; esac",
        )
        for body in bodies:
            with self.subTest(body=body), tempfile.TemporaryDirectory() as temporary:
                compiler = self.fake_compiler(Path(temporary), body)
                self.assertTrue(CHECKER.behavioral_issues(compiler))

    def test_symlink_cannot_be_the_sealed_root(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            actual = base / f"trust-{self.COMMIT}"
            actual.mkdir()
            resolved = self.resolved(actual)
            alias = base / "trust-current"
            alias.symlink_to(actual, target_is_directory=True)
            issues = CHECKER.resolved_issues(
                CHECKER.ResolvedToolchain(
                    resolved.rustc,
                    resolved.sysroot,
                    alias,
                    alias,
                    resolved.host,
                    resolved.commit_hash,
                )
            )
            self.assertTrue(any("must be a versioned directory" in issue for issue in issues))


if __name__ == "__main__":
    unittest.main()
