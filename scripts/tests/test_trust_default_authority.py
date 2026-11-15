from __future__ import annotations

import hashlib
import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Optional


ROOT = Path(__file__).resolve().parents[2]
CHECKER_PATH = ROOT / "scripts" / "check_trust_default_authority.py"
SPEC = importlib.util.spec_from_file_location("check_trust_default_authority", CHECKER_PATH)
assert SPEC is not None and SPEC.loader is not None
CHECKER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = CHECKER
SPEC.loader.exec_module(CHECKER)

LINUX = "aarch64-unknown-linux-gnu"
DARWIN = "aarch64-apple-darwin"
COMMIT = "0123456789abcdef0123456789abcdef01234567"
# Captured 2026-09-18 from a real Trust compiler, not written by hand: the
# refutation canary's stderr from trustc 1.99.0-dev, commit-hash
# 321aaeda75478038420d97830f14724c33c8dc39, host aarch64-apple-darwin (atpkg
# store build 9192), run as `trustc --crate-name trust_default_refutation
# --crate-type lib --edition=2021 --emit metadata -o refutation.rmeta
# refutation.rs` with no Trust flags. Only the scratch directory prefix of the
# source path was removed.
REAL_REFUTATION = (
    ROOT / "scripts" / "tests" / "fixtures" / "trust_default_authority"
    / "trustc-321aaeda-refutation.stderr"
)

# ``binary`` is expanded by the shell: ``${0##*/}`` makes the fake brand itself
# from argv[0], as the real atpkg driver does (``bin/rustc`` and ``bin/trustc``
# are one hard-linked file there, and ``rustc -Vv`` reports ``binary: rustc``).
ARGV0_BRANDED = "${0##*/}"
FAKE_COMPILER = """#!/bin/sh
{refuse}if [ -n "$FAKE_TRUST_MARKER" ]; then printf '%s\\n' "$*" >> "$FAKE_TRUST_MARKER"; fi
case "$*" in
  "--print sysroot") cd "${{0%/*}}/.." && pwd -P ;;
  "-Vv") printf 'rustc 1.99.0-dev\\nbinary: %s\\ncommit-hash: {commit}\\nhost: {host}\\n' "{binary}" ;;
  *positive.rs*) exit 0 ;;
  *refutation.rs*)
    while IFS= read -r line || [ -n "$line" ]; do printf '%s\\n' "$line"; done < '{fixture}' >&2
    exit {refutation_status} ;;
  *) exit 91 ;;
esac
"""
# Measured trustc behaviour: it refuses to run at all, even `-Vv`, while any
# TRUST_CG_* or TCG_* variable is in its environment.
# Shell builtins only: a test PATH may hold nothing but the fake package.
REFUSE_UNTRACKED_CONTROLS = """case "$(export -p)" in
  *" TRUST_CG_"*|*" TCG_"*)
    echo 'error: environment variable is an untracked Trust semantic/codegen control' >&2
    exit 1 ;;
esac
"""


# targo accepts `--unverified --version`; upstream cargo shipped under the name
# rejects the flag, which is the one discriminator between them.
REAL_TARGO = """#!/bin/sh
case "$*" in
  "--unverified --version") echo "targo 1.99.0-dev (0123456 2026-09-17) (targo 0.1.0)" ;;
  *) exit 0 ;;
esac
"""
CARGO_UNDER_TARGO_NAME = """#!/bin/sh
case "$1" in
  --unverified) echo "error: unexpected argument '--unverified' found" >&2; exit 1 ;;
esac
echo "cargo 1.99.0-dev"
"""


def seal(root: Path) -> None:
    """Drop every write bit: directories 0o555, files 0o444 or 0o555."""
    artifacts = [root, *root.rglob("*")]
    for artifact in reversed(artifacts):
        if artifact.is_symlink():
            continue
        if artifact.is_dir() or artifact.stat().st_mode & 0o111:
            artifact.chmod(0o555)
        else:
            artifact.chmod(0o444)


def unseal_dirs(root: Path) -> None:
    for artifact in [root, *root.rglob("*")]:
        if artifact.is_dir() and not artifact.is_symlink():
            artifact.chmod(0o755)


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class TrustDefaultAuthorityTests(unittest.TestCase):
    TRUST = '[toolchain]\nchannel = "trust"\n'
    COMMIT = COMMIT
    HOST = LINUX

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

    def test_every_spelling_rustc_accepts_for_a_trust_option_is_canonical(self) -> None:
        # rustc folds `-` to `_` in -Z names and parses -Z through getopts, so
        # each of these switched verification off with trustc 321aaeda7.
        for flags in (
            ["-Ztrust-verify=off"],
            ["-Ztrust_verify=off"],
            ["-Z", "trust_verify=off"],
            ["-Z trust_verify=off"],
            ["--Z", "trust-verify=off"],
            ["--Z=trust_verify=off"],
            ["-OZtrust-verify=off"],
            ["-gZ", "trust_verify=off"],
            ["-Z\x1ftrust_verify=off"],
        ):
            with self.subTest(flags=flags):
                self.assertEqual(list(CHECKER._canonical_trust_flags(flags)), ["-Ztrust-verify=off"])
        self.assertEqual(
            list(CHECKER._canonical_trust_flags(["-Z", "trust_policy=strict", "-Zthreads=2"])),
            ["-Ztrust-policy=strict"],
        )
        # A value that names no Trust option is not consumed: the flag after it
        # is still read as a flag.
        self.assertEqual(
            list(CHECKER._canonical_trust_flags(["-Z", "-Ztrust_verify=off"])), ["-Ztrust-verify=off"]
        )
        for flags in (["-Zthreads=2"], ["-Ctarget-cpu=native"], ["--cfg", "trust_verify"], ["-Z"]):
            with self.subTest(flags=flags):
                self.assertEqual(list(CHECKER._canonical_trust_flags(flags)), [])

    def test_an_off_switch_after_a_strict_policy_is_rejected_in_any_spelling(self) -> None:
        for off in ('"-Ztrust_verify=off"', '"-Z", "trust_verify=off"', '"--Z=trust-verify=off"',
                    '"-OZtrust-verify=off"'):
            config = f'[build]\nrustflags = ["-Ztrust-policy=strict", {off}]\n'
            with self.subTest(config=config):
                issues = CHECKER.policy_issues(self.TRUST, config)
                self.assertTrue(any("disables verification" in issue for issue in issues), issues)

    def test_argfiles_and_the_no_verify_transport_are_rejected(self) -> None:
        strict = '[build]\nrustflags = ["-Ztrust-policy=strict"]\n'
        for config, expected in (
            ('[build]\nrustflags = ["-Ztrust-policy=strict", "@flags.txt"]\n', "argfile"),
            (strict + '[env]\nTRUST_NO_VERIFY = "1"\n', "TRUST_NO_VERIFY"),
            (strict + '[env]\nTRUST_NO_VERIFY = { value = "1", force = true }\n', "TRUST_NO_VERIFY"),
            (strict + '[env]\n"TRUST\\u005fNO_VERIFY" = "1"\n', "TRUST_NO_VERIFY"),
        ):
            with self.subTest(config=config):
                issues = CHECKER.policy_issues(self.TRUST, config)
                self.assertTrue(any(expected in issue for issue in issues), issues)
        for environment, expected in (
            ({"RUSTFLAGS": "@flags.txt"}, "argfile"),
            ({"TRUST_NO_VERIFY": "1"}, "TRUST_NO_VERIFY"),
        ):
            with self.subTest(environment=environment):
                issues = CHECKER.policy_issues(self.TRUST, strict, environment)
                self.assertTrue(any(expected in issue for issue in issues), issues)

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

    # -- Sealed sysroot, linked model, built without running a compiler. --

    def resolved(
        self,
        root: Path,
        commit_hash: str = COMMIT,
        host: str = LINUX,
        binary: str = "trustc",
        provenance: Optional[str] = None,
        std: bool = True,
    ) -> object:
        rustc = root / "bin" / "rustc"
        rustc.parent.mkdir(parents=True, exist_ok=True)
        rustc.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        rustc.chmod(0o555)
        std_dir = root / "lib" / "rustlib" / host / "lib"
        std_dir.mkdir(parents=True, exist_ok=True)
        if std:
            (std_dir / "libstd-test.rlib").write_bytes(b"std")
        (root / "lib" / "librustc_driver-test.dylib").write_bytes(b"driver")
        if provenance is not None:
            (root / "PROVENANCE").write_text(provenance, encoding="utf-8")
        seal(root)
        return CHECKER.ResolvedToolchain(
            rustc, root, root, root, host, commit_hash, model="linked", binary=binary
        )

    def judge(self, resolved: object, **options: object) -> list:
        options.setdefault("machine_host", self.HOST)
        return CHECKER.resolved_issues(resolved, **options)

    def clean_provenance(self, **overrides: str) -> str:
        fields = {
            "provenance_class": "BUILD-STAMPED-CLEAN",
            "seal_name": f"trust-{COMMIT[:8]}",
            "reported_rev": COMMIT[:9],
            "reported_commit": COMMIT,
            "artifact_driver_name": "librustc_driver-test.dylib",
            "artifact_driver_sha256": sha256_bytes(b"driver"),
            "artifact_bin_rustc_sha256": sha256_bytes(b"#!/bin/sh\nexit 0\n"),
        }
        fields.update(overrides)
        lines = ["# PROVENANCE - what this sealed toolchain actually is"]
        lines += [f"{key}={value}" for key, value in fields.items() if value is not None]
        # promote copies the build stamp with a prefix that is not a field.
        lines.append("build_stamp:seal_name=trust-ffffffff")
        return "\n".join(lines) + "\n"

    def test_complete_read_only_sysroot_is_accepted(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / f"trust-{self.COMMIT}"
            root.mkdir()
            resolved = self.resolved(root)
            self.assertEqual(self.judge(resolved), [])

    def test_promote_short_hash_seal_names_are_accepted(self) -> None:
        for length in (8, 12):
            with self.subTest(length=length), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary) / f"trust-{self.COMMIT[:length]}"
                root.mkdir()
                resolved = self.resolved(root)
                self.assertEqual(self.judge(resolved), [])
                self.assertEqual(CHECKER.seal_binding(root, COMMIT, None)[0], "name")

    def test_seal_names_that_do_not_bind_the_reported_hash_are_rejected(self) -> None:
        for name in (
            "trust-wrong",
            f"trust-{COMMIT[:7]}",
            "trust-89abcdef",
            f"trust-{COMMIT[:8].upper()}X",
            f"trust-{COMMIT}0",
            "9192",
            f"toolchain-{COMMIT[:8]}",
        ):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary) / name
                root.mkdir()
                issues = self.judge(self.resolved(root))
                self.assertTrue(
                    any("neither named trust-<prefix of" in issue for issue in issues), issues
                )

    def test_store_layout_binds_through_clean_provenance(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "9192"
            root.mkdir()
            resolved = self.resolved(root, provenance=self.clean_provenance())
            self.assertEqual(self.judge(resolved), [])
            provenance, issues = CHECKER.read_provenance(root)
            self.assertEqual(issues, [])
            self.assertEqual(CHECKER.seal_binding(root, COMMIT, provenance)[0], "provenance")

    def test_provenance_that_contradicts_the_compiler_or_tree_is_rejected(self) -> None:
        cases = {
            "reported_commit": self.clean_provenance(reported_commit="f" * 40),
            "seal_name": self.clean_provenance(seal_name="trust-deadbeef"),
            "provenance_class is BUILD-STAMPED-DIRTY": self.clean_provenance(
                provenance_class="BUILD-STAMPED-DIRTY"
            ),
            "provenance_class is UNVERIFIED-PROVENANCE": self.clean_provenance(
                provenance_class="UNVERIFIED-PROVENANCE"
            ),
            "provenance_class is absent": self.clean_provenance(provenance_class=None),
            "waives dirty build provenance": self.clean_provenance(dirty_provenance_waived="yes"),
            "compiler driver does not match": self.clean_provenance(
                artifact_driver_sha256=sha256_bytes(b"other driver")
            ),
            "malformed compiler driver digest": self.clean_provenance(
                artifact_driver_sha256="not-a-digest"
            ),
            "absent at seal time but is present": self.clean_provenance(
                artifact_bin_rustc_sha256="-"
            ),
            "recorded in PROVENANCE is missing": self.clean_provenance(
                artifact_bin_trustc_sha256=sha256_bytes(b"trustc")
            ),
            "reported_commit absent": self.clean_provenance()
            + f"reported_commit={'e' * 40}\n",
        }
        for expected, provenance in cases.items():
            with self.subTest(expected=expected), tempfile.TemporaryDirectory() as temporary:
                # The name binds on its own; the record must still not contradict it.
                root = Path(temporary) / f"trust-{COMMIT[:8]}"
                root.mkdir()
                issues = self.judge(self.resolved(root, provenance=provenance))
                self.assertTrue(any(expected in issue for issue in issues), issues)

    def test_symlinked_provenance_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            outside = base / "PROVENANCE.outside"
            outside.write_text(self.clean_provenance(), encoding="utf-8")
            root = base / "9192"
            root.mkdir()
            resolved = self.resolved(root)
            root.chmod(0o755)
            (root / "PROVENANCE").symlink_to(outside)
            root.chmod(0o555)
            issues = self.judge(resolved)
            self.assertTrue(any("PROVENANCE is not a regular file" in issue for issue in issues))
            self.assertTrue(any("neither named trust-<prefix of" in issue for issue in issues))

    def test_missing_rustc_and_sysroot_fail_closed(self) -> None:
        missing = CHECKER.ResolvedToolchain(None, None, None, None, None, None)
        issues = self.judge(missing)
        self.assertTrue(any("rustc" in issue for issue in issues))
        self.assertTrue(any("sysroot" in issue for issue in issues))
        unresolved = CHECKER.ResolvedToolchain(None, None, None, None, None, None, model=None)
        self.assertTrue(
            any("no Trust compiler resolved" in issue for issue in self.judge(unresolved))
        )

    def test_mutable_stage2_link_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            stage2 = Path(temporary) / "build" / "host" / "stage2"
            stage2.mkdir(parents=True)
            resolved = self.resolved(stage2)
            issues = self.judge(resolved)
            self.assertTrue(any("mutable build/host/stage2" in issue for issue in issues))

    def test_writable_nested_std_and_driver_artifacts_are_rejected(self) -> None:
        for relative in (
            Path(f"lib/rustlib/{LINUX}/lib/libstd-test.rlib"),
            Path("lib/librustc_driver-test.dylib"),
        ):
            with self.subTest(relative=relative), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary) / f"trust-{self.COMMIT}"
                root.mkdir()
                resolved = self.resolved(root)
                (root / relative).chmod(0o644)
                issues = self.judge(resolved)
                self.assertTrue(any("writable artifact" in issue for issue in issues))

    def test_writable_seal_root_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / f"trust-{COMMIT[:8]}"
            root.mkdir()
            resolved = self.resolved(root)
            root.chmod(0o755)
            issues = self.judge(resolved)
            self.assertIn("sealed sysroot root retains write bits", issues)

    @unittest.skipIf(hasattr(os, "geteuid") and os.geteuid() == 0, "root reads any directory")
    def test_unreadable_directory_in_the_seal_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / f"trust-{COMMIT[:8]}"
            root.mkdir()
            hidden = root / "libexec"
            hidden.mkdir()
            resolved = self.resolved(root)
            hidden.chmod(0o111)
            try:
                issues = self.judge(resolved)
            finally:
                hidden.chmod(0o555)
            self.assertTrue(any("unreadable directory" in issue for issue in issues), issues)

    @unittest.skipIf(hasattr(os, "geteuid") and os.geteuid() == 0, "root searches any directory")
    def test_listable_but_unsearchable_directory_fails_without_crashing(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / f"trust-{COMMIT[:8]}"
            root.mkdir()
            resolved = self.resolved(root)
            rustlib = root / "lib" / "rustlib"
            # Readable but not searchable: listing works, every lstat below fails.
            rustlib.chmod(0o444)
            try:
                issues = self.judge(resolved, require_cg_backend=True)
                described = CHECKER.describe_installed(
                    resolved, LINUX, None, root / CHECKER.IDENTITY_LOCK_NAME
                )
                self.assertIsNone(CHECKER._sealed_tree_for_digest(resolved))
            finally:
                rustlib.chmod(0o555)
            unsearchable = root.resolve() / "lib" / "rustlib"
            self.assertIn(
                f"sealed sysroot contains an unreadable directory: {unsearchable}", issues
            )
            self.assertIn(f"sealed sysroot has no std artifact for {LINUX}", issues)
            self.assertTrue(any("ships no CG backend" in issue for issue in issues), issues)
            self.assertIsNone(described["libstd"])
            self.assertFalse(described["cg_backend"]["satisfied"])

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
            issues = self.judge(resolved)
            self.assertTrue(any("symlinked artifact" in issue for issue in issues))

    def test_symlink_cannot_be_the_sealed_root(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            actual = base / f"trust-{self.COMMIT}"
            actual.mkdir()
            resolved = self.resolved(actual)
            alias = base / "trust-current"
            alias.symlink_to(actual, target_is_directory=True)
            issues = self.judge(
                CHECKER.ResolvedToolchain(
                    resolved.rustc,
                    resolved.sysroot,
                    alias,
                    alias,
                    resolved.host,
                    resolved.commit_hash,
                    model="linked",
                    binary="trustc",
                )
            )
            self.assertTrue(any("must be a versioned directory" in issue for issue in issues))

    def test_unbranded_or_unidentified_compiler_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / f"trust-{COMMIT[:8]}"
            root.mkdir()
            issues = self.judge(self.resolved(root, binary="rustc"))
            self.assertTrue(any("branded trustc driver" in issue for issue in issues))
        for commit_hash in ("unknown", COMMIT[:9], COMMIT.upper()):
            with self.subTest(commit_hash=commit_hash), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary) / f"trust-{COMMIT[:8]}"
                root.mkdir()
                issues = self.judge(self.resolved(root, commit_hash=commit_hash))
                self.assertTrue(any("canonical 40-hex commit-hash" in issue for issue in issues))

    # -- Host/target coherence. --

    def test_host_must_be_the_required_running_primary_target(self) -> None:
        cases = (
            ({"machine_host": DARWIN}, "does not equal the required target aarch64-apple-darwin"),
            ({"machine_host": DARWIN}, "no std artifact for aarch64-apple-darwin"),
            ({"machine_host": None}, "not a primary-target host"),
            (
                {"machine_host": DARWIN, "required_target": LINUX},
                "is not the running machine host aarch64-apple-darwin",
            ),
            ({"machine_host": None, "required_target": LINUX}, "running machine host unrecognized"),
            (
                {"machine_host": LINUX, "required_target": "x86_64-unknown-linux-gnu"},
                "not a repository primary target",
            ),
        )
        for options, expected in cases:
            with self.subTest(options=options), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary) / f"trust-{COMMIT[:8]}"
                root.mkdir()
                issues = self.judge(self.resolved(root), **options)
                self.assertTrue(any(expected in issue for issue in issues), issues)

    def test_non_primary_host_and_missing_std_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / f"trust-{COMMIT[:8]}"
            root.mkdir()
            issues = self.judge(self.resolved(root, host="x86_64-unknown-linux-gnu"))
            self.assertTrue(any("does not equal the required target" in issue for issue in issues))
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / f"trust-{COMMIT[:8]}"
            root.mkdir()
            issues = self.judge(self.resolved(root, std=False))
            self.assertIn(f"sealed sysroot has no std artifact for {LINUX}", issues)

    def test_darwin_host_is_accepted_on_a_darwin_machine(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / f"trust-{COMMIT[:8]}"
            root.mkdir()
            resolved = self.resolved(root, host=DARWIN)
            self.assertEqual(self.judge(resolved, machine_host=DARWIN), [])
            self.assertEqual(
                self.judge(resolved, machine_host=DARWIN, required_target=DARWIN), []
            )

    def test_running_host_triple_recognizes_only_primary_targets(self) -> None:
        cases = (
            (("darwin", "arm64", None), DARWIN),
            (("linux", "aarch64", True), LINUX),
            (("linux", "aarch64", False), None),
            (("linux", "x86_64", True), None),
            (("darwin", "x86_64", None), None),
            (("win32", "ARM64", None), None),
            (("freebsd13", "aarch64", True), None),
        )
        for (system, machine, glibc), expected in cases:
            with self.subTest(system=system, machine=machine, glibc=glibc):
                self.assertEqual(CHECKER.running_host_triple(system, machine, glibc), expected)

    # -- CG backend expectation. --

    def test_cg_backend_expectation_is_diagnostic_unless_required(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / f"trust-{COMMIT[:8]}"
            root.mkdir()
            resolved = self.resolved(root)
            self.assertEqual(self.judge(resolved), [])
            self.assertFalse(CHECKER.cg_backend_expectation(root, LINUX)["satisfied"])
            issues = self.judge(resolved, require_cg_backend=True)
            self.assertTrue(any("ships no CG backend" in issue for issue in issues))

    def test_only_a_trust_backend_or_bridge_dylib_satisfies_the_expectation(self) -> None:
        cases = (
            (f"lib/rustlib/{LINUX}/codegen-backends/librustc_codegen_trust_ir_cg-1.99.0-dev.so", True),
            (f"lib/rustlib/{LINUX}/codegen-backends/librustc_codegen_trust-ir-cg-1.99.0-dev.so", True),
            ("lib/librustc_codegen_trust_cg.so", True),
            (f"lib/rustlib/{LINUX}/lib/librustc_codegen_trust_cg-0a1b2c3d.so", True),
            (f"lib/rustlib/{LINUX}/codegen-backends/librustc_codegen_cranelift-1.99.0-dev.so", False),
            ("lib/librustc_codegen_trust_cg.dylib", False),
            ("lib/librustc_codegen_trust_cg.so.txt", False),
        )
        for relative, satisfied in cases:
            with self.subTest(relative=relative), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary) / f"trust-{COMMIT[:8]}"
                root.mkdir()
                backend = root / relative
                backend.parent.mkdir(parents=True, exist_ok=True)
                backend.write_bytes(b"backend")
                resolved = self.resolved(root)
                expectation = CHECKER.cg_backend_expectation(root, LINUX)
                self.assertEqual(expectation["satisfied"], satisfied, expectation)
                issues = self.judge(resolved, require_cg_backend=True)
                self.assertEqual(
                    any("ships no CG backend" in issue for issue in issues), not satisfied
                )

    # -- Fake installed packs, resolved the way the runners resolve them. --

    def make_pack(
        self,
        base: Path,
        name: str = f"trust-{COMMIT[:8]}",
        *,
        host: str = LINUX,
        commit_hash: str = COMMIT,
        binary: str = "trustc",
        backend: bool = False,
        refutation_status: int = 1,
        targo: Optional[str] = None,
        refuse_controls: bool = False,
    ) -> Path:
        targo = REAL_TARGO if targo is None else targo
        root = base / name
        (root / "bin").mkdir(parents=True)
        script = FAKE_COMPILER.format(
            refuse=REFUSE_UNTRACKED_CONTROLS if refuse_controls else "",
            binary=binary,
            commit=commit_hash,
            host=host,
            fixture=os.fspath(REAL_REFUTATION),
            refutation_status=refutation_status,
        )
        for tool in ("trustc", "rustc"):
            (root / "bin" / tool).write_text(script, encoding="utf-8")
            (root / "bin" / tool).chmod(0o755)
        (root / "bin" / "targo").write_text(targo, encoding="utf-8")
        (root / "bin" / "targo").chmod(0o755)
        std_dir = root / "lib" / "rustlib" / host / "lib"
        std_dir.mkdir(parents=True)
        (std_dir / "libstd-test.rlib").write_bytes(b"std")
        (root / "lib" / "librustc_driver-test.so").write_bytes(b"driver")
        if backend:
            suffix = ".dylib" if host.endswith("apple-darwin") else ".so"
            (root / "lib" / f"librustc_codegen_trust_cg{suffix}").write_bytes(b"backend")
        seal(root)
        return root

    def environment(self, base: Path, pack: Optional[Path], **extra: str) -> dict:
        env = {
            "PATH": os.fspath(pack / "bin") if pack is not None else os.fspath(base / "empty"),
            "RUSTUP_HOME": os.fspath(base / "rustup-home"),
            "FAKE_TRUST_MARKER": os.fspath(base / "invocations.log"),
        }
        if pack is not None:
            env["TRUST_SEALED_SYSROOT"] = os.fspath(pack)
        env.update(extra)
        return env

    def invocations(self, base: Path) -> list:
        log = base / "invocations.log"
        return log.read_text(encoding="utf-8").splitlines() if log.exists() else []

    def test_resolve_installed_prefers_the_path_pack(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            pack = self.make_pack(base)
            resolved = CHECKER.resolve_installed(base, self.environment(base, pack))
            self.assertEqual(resolved.model, "pack")
            self.assertEqual(resolved.rustc, (pack / "bin" / "trustc").resolve())
            self.assertEqual(resolved.build_tool, (pack / "bin" / "targo").resolve())
            self.assertEqual(resolved.sysroot.resolve(), pack.resolve())
            self.assertEqual(
                (resolved.commit_hash, resolved.host, resolved.binary), (COMMIT, LINUX, "trustc")
            )
            self.assertIsNone(resolved.rustup_link)
            self.assertEqual(self.judge(resolved), [])

    def test_pack_model_rejects_split_or_divergent_toolchains(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            pack = self.make_pack(base)
            elsewhere = base / "elsewhere"
            elsewhere.mkdir()
            (elsewhere / "targo").write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            (elsewhere / "targo").chmod(0o755)
            split = self.environment(
                base, pack, PATH=os.pathsep.join([os.fspath(elsewhere), os.fspath(pack / "bin")])
            )
            issues = self.judge(CHECKER.resolve_installed(base, split))
            self.assertIn("PATH trustc and targo must resolve to the same installed package", issues)
            self.assertIn("resolved targo is not the build tool inside the sealed sysroot", issues)

            other = self.make_pack(base, "trust-recon")
            toolchains = base / "rustup-home" / "toolchains"
            toolchains.mkdir(parents=True)
            (toolchains / "trust").symlink_to(other, target_is_directory=True)
            issues = self.judge(CHECKER.resolve_installed(base, self.environment(base, pack)))
            self.assertTrue(any("diverges from the PATH Trust package" in issue for issue in issues))

            (toolchains / "trust").unlink()
            (toolchains / "trust").symlink_to(pack, target_is_directory=True)
            self.assertEqual(
                self.judge(CHECKER.resolve_installed(base, self.environment(base, pack))), []
            )

            copy = self.make_pack(base, f"trust-{COMMIT[:10]}")
            recorded_copy = self.environment(base, pack, TRUST_SEALED_SYSROOT=os.fspath(copy))
            issues = self.judge(CHECKER.resolve_installed(base, recorded_copy))
            self.assertIn(
                "compiler sysroot and TRUST_SEALED_SYSROOT do not resolve identically", issues
            )
            self.assertIn("resolved trustc is not the compiler inside the sealed sysroot", issues)

            unrecorded = self.environment(base, pack)
            del unrecorded["TRUST_SEALED_SYSROOT"]
            issues = self.judge(CHECKER.resolve_installed(base, unrecorded))
            self.assertIn("TRUST_SEALED_SYSROOT does not name an existing directory", issues)

    def test_pack_compiler_identity_failures_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            pack = self.make_pack(base, binary="rustc", commit_hash="unknown")
            resolved = CHECKER.resolve_installed(base, self.environment(base, pack))
            issues = self.judge(resolved)
            self.assertIn("Trust compiler did not report a canonical 40-hex commit-hash", issues)
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            pack = self.make_pack(base, binary="rustc")
            issues = self.judge(CHECKER.resolve_installed(base, self.environment(base, pack)))
            self.assertIn("Trust compiler is not the branded trustc driver: binary rustc", issues)
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            lonely = base / "lonely"
            lonely.mkdir()
            (lonely / "targo").write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            (lonely / "targo").chmod(0o755)
            resolved = CHECKER.resolve_installed(
                base, {"PATH": os.fspath(lonely), "RUSTUP_HOME": os.fspath(base / "none")}
            )
            self.assertEqual(resolved.model, "pack")
            self.assertIn("PATH did not resolve an executable Trust trustc", self.judge(resolved))

    def test_resolve_installed_falls_back_to_a_rustup_link(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            pack = self.make_pack(base)
            rustup_home = base / "rustup-home"
            link = rustup_home / "toolchains" / "trust"
            link.parent.mkdir(parents=True)
            link.symlink_to(pack, target_is_directory=True)
            fake_bin = base / "fake-bin"
            fake_bin.mkdir()
            rustup = fake_bin / "rustup"
            rustup.write_text(
                "#!/bin/sh\n"
                'if [ "$*" = "which --toolchain trust rustc" ]; then\n'
                f"  printf '%s\\n' '{link}/bin/rustc'\n"
                "  exit 0\n"
                "fi\n"
                "exit 1\n",
                encoding="utf-8",
            )
            rustup.chmod(0o755)
            env = self.environment(base, pack, PATH=os.fspath(fake_bin))
            resolved = CHECKER.resolve_installed(base, env)
            self.assertEqual(resolved.model, "linked")
            self.assertEqual(resolved.rustup_link, link)
            self.assertEqual(resolved.commit_hash, COMMIT)
            self.assertEqual(self.judge(resolved), [])

            env_without_link = self.environment(
                base, pack, PATH=os.fspath(fake_bin), RUSTUP_HOME=os.fspath(base / "nowhere")
            )
            issues = self.judge(CHECKER.resolve_installed(base, env_without_link))
            self.assertIn("rustup Trust toolchain link is missing", issues)

            other = self.make_pack(base, f"trust-{COMMIT[:10]}")
            env_other_record = self.environment(
                base, pack, PATH=os.fspath(fake_bin), TRUST_SEALED_SYSROOT=os.fspath(other)
            )
            issues = self.judge(CHECKER.resolve_installed(base, env_other_record))
            self.assertIn(
                "rustup link, compiler sysroot, and TRUST_SEALED_SYSROOT do not resolve identically",
                issues,
            )
            self.assertIn("resolved rustc is not the compiler inside the sealed sysroot", issues)

    def test_argv0_branded_driver_qualifies_only_through_the_pack_model(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            pack = self.make_pack(base, binary=ARGV0_BRANDED)
            resolved = CHECKER.resolve_installed(base, self.environment(base, pack))
            self.assertEqual((resolved.model, resolved.binary), ("pack", "trustc"))
            self.assertEqual(self.judge(resolved), [])

            link = base / "rustup-home" / "toolchains" / "trust"
            link.parent.mkdir(parents=True)
            link.symlink_to(pack, target_is_directory=True)
            fake_bin = base / "fake-bin"
            fake_bin.mkdir()
            rustup = fake_bin / "rustup"
            rustup.write_text(
                "#!/bin/sh\n"
                f"[ \"$*\" = 'which --toolchain trust rustc' ] && printf '%s\\n' '{link}/bin/rustc'\n",
                encoding="utf-8",
            )
            rustup.chmod(0o755)
            linked = CHECKER.resolve_installed(
                base, self.environment(base, pack, PATH=os.fspath(fake_bin))
            )
            self.assertEqual((linked.model, linked.binary), ("linked", "rustc"))
            self.assertEqual(
                self.judge(linked),
                ["Trust compiler is not the branded trustc driver: binary rustc"],
            )

    def test_resolve_installed_without_any_trust_compiler(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            (base / "empty").mkdir()
            resolved = CHECKER.resolve_installed(base, self.environment(base, None))
            self.assertIsNone(resolved.model)
            issues = self.judge(resolved)
            self.assertTrue(
                any(
                    "no Trust compiler resolved" in issue and "rustup is not on PATH" in issue
                    for issue in issues
                ),
                issues,
            )
            self.assertEqual(
                CHECKER.resolve_installed(base, {"PATH": ""}).model, None
            )

            failing = base / "failing-rustup"
            failing.mkdir()
            rustup = failing / "rustup"
            rustup.write_text(
                "#!/bin/sh\necho \"error: toolchain 'trust' is not installed\" >&2\nexit 1\n",
                encoding="utf-8",
            )
            rustup.chmod(0o755)
            resolved = CHECKER.resolve_installed(
                base, self.environment(base, None, PATH=os.fspath(failing))
            )
            self.assertIsNone(resolved.model)
            self.assertIn("toolchain 'trust' is not installed", resolved.note)
            self.assertTrue(any("is not installed" in issue for issue in self.judge(resolved)))

    # -- Content identity and the committed lock. --

    def test_sysroot_tree_digest_binds_content_paths_and_executable_bits(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            first = self.make_pack(base / "a")
            second = self.make_pack(base / "b")
            digest = CHECKER.sysroot_tree_digest(first)
            self.assertRegex(digest, r"^[0-9a-f]{64}$")
            self.assertEqual(CHECKER.sysroot_tree_digest(second), digest)
            os.utime(second / "lib" / "librustc_driver-test.so", (1, 1))
            self.assertEqual(CHECKER.sysroot_tree_digest(second), digest)

            unseal_dirs(second)
            driver = second / "lib" / "librustc_driver-test.so"
            driver.chmod(0o644)
            driver.write_bytes(b"patched driver")
            self.assertNotEqual(CHECKER.sysroot_tree_digest(second), digest)
            driver.write_bytes(b"driver")
            self.assertEqual(CHECKER.sysroot_tree_digest(second), digest)
            driver.chmod(0o755)
            self.assertNotEqual(CHECKER.sysroot_tree_digest(second), digest)
            driver.chmod(0o444)
            driver.rename(second / "lib" / "librustc_driver-renamed.so")
            self.assertNotEqual(CHECKER.sysroot_tree_digest(second), digest)
            (second / "lib" / "librustc_driver-renamed.so").rename(driver)
            (second / "lib" / "extra").mkdir()
            self.assertNotEqual(CHECKER.sysroot_tree_digest(second), digest)

    def write_lock(self, root: Path, text: str) -> Path:
        lock = root / CHECKER.IDENTITY_LOCK_NAME
        lock.write_text(text, encoding="utf-8")
        return lock

    def test_identity_lock_is_required_and_must_match(self) -> None:
        digest = "a" * 64
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            lock = root / CHECKER.IDENTITY_LOCK_NAME

            def lock_issues(computed: Optional[str] = digest) -> list:
                return CHECKER.identity_lock_issues(lock, LINUX, COMMIT, lambda: computed)

            self.assertTrue(
                any("no committed Trust toolchain identity lock" in issue for issue in lock_issues())
            )
            rejected = {
                "# nothing pinned\n": "names no identity",
                f"identity = {LINUX} {COMMIT}\n": "expected identity =",
                f"pin = {LINUX} {COMMIT} {digest}\n": "expected identity =",
                f"identity = x86_64-unknown-linux-gnu {COMMIT} {digest}\n": "not a repository primary target",
                f"identity = {LINUX} {COMMIT[:9]} {digest}\n": "not canonical 40-hex",
                f"identity = {LINUX} {COMMIT} {digest[:63]}\n": "not 64-hex SHA-256",
                f"identity = {LINUX} {COMMIT} {digest}\nidentity = {LINUX} {COMMIT} {'b' * 64}\n": "more than once",
                f"identity = {DARWIN} {COMMIT} {digest}\n": "pins no identity for host",
                f"identity = {LINUX} {'f' * 40} {digest}\n": "is not the locked",
                f"identity = {LINUX} {COMMIT} {'b' * 64}\n": "tree digest",
            }
            for text, expected in rejected.items():
                with self.subTest(text=text):
                    self.write_lock(root, text)
                    issues = lock_issues()
                    self.assertTrue(any(expected in issue for issue in issues), issues)

            self.write_lock(root, f"# qualified Linux seal\nidentity = {LINUX} {COMMIT} {digest}  # ok\n")
            self.assertEqual(lock_issues(), [])
            self.assertTrue(any("was not computed" in issue for issue in lock_issues(None)))

            lock.unlink()
            elsewhere = root / "elsewhere.lock"
            elsewhere.write_text(f"identity = {LINUX} {COMMIT} {digest}\n", encoding="utf-8")
            lock.symlink_to(elsewhere)
            self.assertTrue(any("must not be a symlink" in issue for issue in lock_issues()))

    # -- The whole checker, end to end, over fake packs on PATH. --

    def repository(
        self, base: Path, channel: str = "1.97.1", policy: Optional[str] = "strict",
        config: Optional[str] = None,
    ) -> Path:
        root = base / "repo"
        (root / ".cargo").mkdir(parents=True)
        (root / "rust-toolchain.toml").write_text(
            f'[toolchain]\nchannel = "{channel}"\n', encoding="utf-8"
        )
        if config is None:
            config = (
                "[build]\njobs = 2\n" if policy is None
                else f'[build]\nrustflags = ["-Ztrust-policy={policy}"]\n'
            )
        (root / ".cargo" / "config.toml").write_text(config, encoding="utf-8")
        return root

    def lock_pack(self, root: Path, pack: Path, host: str = LINUX) -> None:
        digest = CHECKER.sysroot_tree_digest(pack.resolve())
        self.write_lock(root, f"identity = {host} {COMMIT} {digest}\n")

    def canary_ran(self, base: Path) -> bool:
        return any("refutation.rs" in line for line in self.invocations(base))

    def test_stock_default_resolves_nothing_and_runs_no_compiler(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = self.repository(base)
            pack = self.make_pack(base)
            report = CHECKER.evaluate(
                root, False, environment=self.environment(base, pack), machine_host=LINUX
            )
            self.assertEqual((report.issues, report.informational, report.diagnostics), ([], [], None))
            self.assertEqual(self.invocations(base), [])

    def test_inspect_reports_the_installed_pack_on_a_stock_channel(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = self.repository(base)
            pack = self.make_pack(base, backend=True)
            report = CHECKER.evaluate(
                root,
                False,
                inspect=True,
                environment=self.environment(base, pack),
                machine_host=LINUX,
            )
            self.assertEqual(report.issues, [])
            self.assertEqual(len(report.informational), 1, report.informational)
            self.assertIn("no committed Trust toolchain identity lock", report.informational[0])
            diagnostics = report.diagnostics
            json.dumps(diagnostics)
            self.assertEqual(diagnostics["model"], "pack")
            self.assertEqual(diagnostics["commit_hash"], COMMIT)
            self.assertEqual(diagnostics["binary"], "trustc")
            self.assertEqual((diagnostics["host"], diagnostics["required_target"]), (LINUX, LINUX))
            self.assertEqual(diagnostics["seal_binding"], "name")
            self.assertEqual(diagnostics["behavioral_canaries"], "pass")
            self.assertTrue(diagnostics["cg_backend"]["satisfied"])
            self.assertEqual(
                diagnostics["sysroot_tree_sha256"], CHECKER.sysroot_tree_digest(pack.resolve())
            )
            self.assertTrue(self.canary_ran(base))

    def test_inspect_runs_canaries_and_describes_an_unsound_pack(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = self.repository(base)
            pack = self.make_pack(base, name="9192")
            unseal_dirs(pack)
            report = CHECKER.evaluate(
                root,
                False,
                inspect=True,
                environment=self.environment(base, pack),
                machine_host=DARWIN,
            )
            self.assertEqual(report.issues, [])
            notes = "\n".join(report.informational)
            for expected in (
                "neither named trust-<prefix of",
                "retains write bits",
                "does not equal the required target aarch64-apple-darwin",
                "no committed Trust toolchain identity lock",
            ):
                self.assertIn(expected, notes)
            self.assertIsNone(report.diagnostics["seal_binding"])
            self.assertIsNone(report.diagnostics["sysroot_tree_sha256"])
            self.assertEqual(report.diagnostics["behavioral_canaries"], "pass")

    def test_require_verified_default_on_a_stock_channel_reports_installed_findings(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = self.repository(base)
            pack = self.make_pack(base)
            report = CHECKER.evaluate(
                root, True, environment=self.environment(base, pack), machine_host=LINUX
            )
            self.assertEqual(
                report.issues[0], "verified default required, but repository channel is 1.97.1"
            )
            self.assertTrue(
                any("no committed Trust toolchain identity lock" in issue for issue in report.issues)
            )
            self.assertTrue(any("ships no CG backend" in issue for issue in report.issues))
            self.assertIsNone(report.diagnostics)
            self.assertFalse(self.canary_ran(base))

    def test_trust_channel_accepts_a_complete_locked_pack_end_to_end(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = self.repository(base, channel="trust")
            pack = self.make_pack(base, backend=True)
            self.lock_pack(root, pack)
            env = self.environment(base, pack)
            self.assertEqual(CHECKER.check(root, True, environment=env, machine_host=LINUX), [])
            self.assertTrue(self.canary_ran(base))
            report = CHECKER.evaluate(
                root, True, inspect=True, environment=env, machine_host=LINUX
            )
            self.assertEqual(report.issues, [])
            self.assertEqual(report.diagnostics["identity_lock"]["locked_commit_hash"], COMMIT)

    def test_trust_channel_checks_every_identity_before_running_canaries(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = self.repository(base, channel="trust")
            pack = self.make_pack(base, backend=True)
            self.write_lock(root, f"identity = {LINUX} {COMMIT} {'0' * 64}\n")
            issues = CHECKER.check(
                root, True, environment=self.environment(base, pack), machine_host=LINUX
            )
            self.assertTrue(any("tree digest" in issue for issue in issues), issues)
            self.assertFalse(self.canary_ran(base))

            self.lock_pack(root, pack)
            issues = CHECKER.check(
                root, True, environment=self.environment(base, pack), machine_host=DARWIN
            )
            self.assertTrue(any("does not equal the required target" in issue for issue in issues))
            self.assertFalse(self.canary_ran(base))

    def test_trust_channel_rejects_a_compiler_that_accepts_the_refutation(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = self.repository(base, channel="trust")
            pack = self.make_pack(base, backend=True, refutation_status=0)
            self.lock_pack(root, pack)
            issues = CHECKER.check(
                root, True, environment=self.environment(base, pack), machine_host=LINUX
            )
            self.assertEqual(issues, ["Trust compiler accepted the deliberate default refutation"])

    def test_cg_backend_absence_fails_only_under_require_verified_default(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = self.repository(base, channel="trust")
            pack = self.make_pack(base)
            self.lock_pack(root, pack)
            env = self.environment(base, pack)
            self.assertEqual(CHECKER.check(root, False, environment=env, machine_host=LINUX), [])
            issues = CHECKER.check(root, True, environment=env, machine_host=LINUX)
            self.assertEqual(len(issues), 1, issues)
            self.assertIn("ships no CG backend", issues[0])

    def test_trust_channel_policy_failures_skip_resolution_unless_inspecting(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = self.repository(base, channel="trust", policy="advisory")
            pack = self.make_pack(base, backend=True)
            self.lock_pack(root, pack)
            env = self.environment(base, pack)
            issues = CHECKER.check(root, False, environment=env, machine_host=LINUX)
            self.assertEqual(len(issues), 1, issues)
            self.assertIn("not strict or certify", issues[0])
            self.assertEqual(self.invocations(base), [])
            report = CHECKER.evaluate(root, False, inspect=True, environment=env, machine_host=LINUX)
            self.assertIn("not strict or certify", report.issues[0])
            self.assertEqual(report.diagnostics["behavioral_canaries"], "pass")

    # -- A Trust toolchain selection: channel "trust" with a flag-free config. --

    def test_trust_selection_passes_on_a_coherent_package_without_a_claim(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = self.repository(base, channel="trust", policy=None)
            pack = self.make_pack(base, name="9192")
            unseal_dirs(pack)
            env = self.environment(base, pack)
            env.pop("TRUST_SEALED_SYSROOT")
            report = CHECKER.evaluate(root, False, environment=env, machine_host=DARWIN)
            self.assertEqual((report.issues, report.informational, report.diagnostics), ([], [], None))
            self.assertEqual(report.selection["commit_hash"], COMMIT)
            self.assertEqual(report.selection["compiler"], os.fspath((pack / "bin" / "trustc").resolve()))
            self.assertIsNone(report.selection["launchers"])
            # No canary runs: a selection makes no claim about the no-flag default.
            self.assertFalse(self.canary_ran(base))
            # The verified-default claim is still the whole contract.
            issues = CHECKER.check(root, True, environment=env, machine_host=DARWIN)
            self.assertTrue(
                any("explicitly select strict or certify" in issue for issue in issues), issues
            )
            # --inspect reports the unqualified contract as information only.
            report = CHECKER.evaluate(root, False, inspect=True, environment=env, machine_host=DARWIN)
            self.assertEqual(report.issues, [])
            self.assertTrue(
                any("no committed Trust toolchain identity lock" in note for note in report.informational)
            )

    def test_trust_selection_follows_atpkg_launcher_shims(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = self.repository(base, channel="trust", policy=None)
            pack = self.make_pack(base, name="9192")
            shims = base / "shims"
            shims.mkdir()
            for tool in ("trustc", "targo"):
                (shims / tool).write_text(
                    f"#!/bin/sh\n# atpkg shim\nexec '{(pack / 'bin' / tool).resolve()}' \"$@\"\n",
                    encoding="utf-8",
                )
                (shims / tool).chmod(0o755)
            env = self.environment(base, pack, PATH=os.fspath(shims))
            report = CHECKER.evaluate(root, False, environment=env, machine_host=LINUX)
            self.assertEqual(report.issues, [])
            self.assertEqual(report.selection["launchers"]["trustc"], os.fspath((shims / "trustc").resolve()))
            self.assertEqual(report.selection["build_tool"], os.fspath((pack / "bin" / "targo").resolve()))

    def test_trust_selection_refuses_an_incoherent_or_disguised_package(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = self.repository(base, channel="trust", policy=None)
            cases = {
                "PATH targo is not targo": dict(targo=CARGO_UNDER_TARGO_NAME),
                "branded trustc driver": dict(binary="rustc"),
                "40-hex commit-hash": dict(commit_hash="unknown"),
            }
            for expected, options in cases.items():
                with self.subTest(expected=expected):
                    pack = self.make_pack(base / expected.replace(" ", "-"), **options)
                    issues = CHECKER.check(
                        root, False, environment=self.environment(base, pack), machine_host=LINUX
                    )
                    self.assertTrue(any(expected in issue for issue in issues), issues)
            issues = CHECKER.check(
                root, False, environment=self.environment(base, None), machine_host=LINUX
            )
            self.assertTrue(any("there is no stock fallback" in issue for issue in issues), issues)

    def test_trust_selection_refuses_overrides_and_every_config_trust_flag(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            pack = self.make_pack(base)
            env = self.environment(base, pack)
            configs = {
                '[build]\nrustc-wrapper = "/tmp/wrapper"\n': "rustc wrapper",
                '[env]\nRUSTC = "/tmp/rustc"\n': "rustc wrapper",
                # Any Trust flag is a claim, judged by the whole contract, in
                # every spelling rustc accepts for it.
                '[build]\nrustflags = ["-Ztrust-verify=off"]\n': "disables verification",
                '[build]\nrustflags = ["-Ztrust_verify=off"]\n': "disables verification",
                '[build]\nrustflags = ["-Z", "trust_verify=off"]\n': "disables verification",
                '[build]\nrustflags = ["--Z=trust-verify=off"]\n': "disables verification",
                '[build]\nrustflags = ["-OZtrust-verify=off"]\n': "disables verification",
                '[target.any]\nrustdocflags = ["-Ztrust-verify=off"]\n': "disables verification",
                '[target.any]\nrustflags = ["-Ztrust-policy=advisory"]\n': "not strict or certify",
                '[target.any]\nrustflags = ["-Z", "trust_policy=advisory"]\n': "not strict or certify",
                # Off-switches without a -Z spelling are refused outright.
                '[build]\nrustflags = ["@flags.txt"]\n': "argfile",
                '[env]\nTRUST_NO_VERIFY = "1"\n': "TRUST_NO_VERIFY",
            }
            for config, expected in configs.items():
                with self.subTest(config=config):
                    root = self.repository(base / str(abs(hash(config))), channel="trust", config=config)
                    issues = CHECKER.check(root, False, environment=env, machine_host=LINUX)
                    self.assertTrue(any(expected in issue for issue in issues), issues)
            root = self.repository(base / "ambient", channel="trust", policy=None)
            for extra, expected in (
                ({"RUSTC_WRAPPER": "/tmp/wrapper"}, "ambient rustc override"),
                ({"RUSTFLAGS": "-Ztrust-verify=off"}, "ambient Trust compiler flags"),
                ({"RUSTFLAGS": "-Ztrust_verify=off"}, "ambient Trust compiler flags"),
                ({"RUSTFLAGS": "-Z trust_verify=off"}, "ambient Trust compiler flags"),
                ({"CARGO_ENCODED_RUSTFLAGS": "-Z\x1ftrust_verify=off"}, "ambient Trust compiler flags"),
                ({"RUSTDOCFLAGS": "--Z=trust_verify=off"}, "ambient Trust compiler flags"),
                ({"RUSTFLAGS": "@flags.txt"}, "argfile"),
                ({"TRUST_NO_VERIFY": "1"}, "TRUST_NO_VERIFY"),
            ):
                with self.subTest(extra=extra):
                    issues = CHECKER.check(
                        root, False, environment=self.environment(base, pack, **extra),
                        machine_host=LINUX,
                    )
                    self.assertTrue(any(expected in issue for issue in issues), issues)

    def test_trust_selection_probes_identity_without_the_controls_trustc_refuses(self) -> None:
        # A gate may export TRUST_CG_*/TCG_* for its test binaries; trustc
        # refuses to run under them, so identity probes run without them.
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = self.repository(base, channel="trust", policy=None)
            pack = self.make_pack(base, refuse_controls=True)
            env = self.environment(
                base, pack, TRUST_CG_RUN_FORMAL_PROOF_TESTS="1", TCG_SOLVER_PATH="/ay"
            )
            report = CHECKER.evaluate(root, False, environment=env, machine_host=LINUX)
            self.assertEqual(report.issues, [])
            self.assertEqual(report.selection["commit_hash"], COMMIT)

    def test_repository_root_is_a_trust_selection(self) -> None:
        self.assertEqual(
            CHECKER.toolchain_channel((ROOT / "rust-toolchain.toml").read_text(encoding="utf-8")),
            "trust",
        )
        self.assertFalse(
            CHECKER.configures_trust_flags(
                (ROOT / ".cargo" / "config.toml").read_text(encoding="utf-8")
            )
        )

    # -- Behavioral canaries. --

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

    def test_real_trustc_refutation_diagnostic_satisfies_the_canary(self) -> None:
        evidence = REAL_REFUTATION.read_text(encoding="utf-8")
        self.assertIn("Trust verification: 0 proved, 2 failed", evidence)
        for status, expected in ((1, []), (0, ["Trust compiler accepted the deliberate default refutation"])):
            with self.subTest(status=status), tempfile.TemporaryDirectory() as temporary:
                compiler = self.fake_compiler(
                    Path(temporary),
                    'case "$*" in *positive.rs*) exit 0 ;; esac\n'
                    f"while IFS= read -r line || [ -n \"$line\" ]; do printf '%s\\n' \"$line\"; "
                    f"done < '{REAL_REFUTATION}' >&2\n"
                    f"exit {status}",
                )
                self.assertEqual(CHECKER.behavioral_issues(compiler), expected)

    def test_behavioral_canary_rejects_acceptance_and_nontrust_errors(self) -> None:
        bodies = (
            "exit 0",
            "case \"$*\" in *positive.rs*) exit 0 ;; *) echo syntax-error >&2; exit 1 ;; esac",
            "exit 1",
        )
        for body in bodies:
            with self.subTest(body=body), tempfile.TemporaryDirectory() as temporary:
                compiler = self.fake_compiler(Path(temporary), body)
                self.assertTrue(CHECKER.behavioral_issues(compiler))

    # -- Command line. --

    def run_cli(self, base: Path, root: Path, pack: Path, *arguments: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            [sys.executable, "-B", os.fspath(CHECKER_PATH), "--root", os.fspath(root), *arguments],
            env=self.environment(base, pack),
            check=False,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=120,
        )

    def test_cli_inspect_prints_json_and_keeps_a_stock_pass(self) -> None:
        host = CHECKER.running_host_triple() or LINUX
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = self.repository(base)
            pack = self.make_pack(base, host=host)
            completed = self.run_cli(base, root, pack, "--inspect")
            self.assertEqual(completed.returncode, 0, completed.stderr)
            self.assertIn("INSPECT: installed Trust toolchain diagnostics", completed.stdout)
            self.assertIn("INFO: installed Trust toolchain would not qualify:", completed.stdout)
            self.assertTrue(completed.stdout.rstrip().endswith(
                "PASS: repository default makes no uncertified Trust authority claim"
            ))
            start = completed.stdout.index("{")
            diagnostics, _ = json.JSONDecoder().raw_decode(completed.stdout[start:])
            self.assertEqual(diagnostics["model"], "pack")
            self.assertEqual(diagnostics["commit_hash"], COMMIT)

            completed = self.run_cli(base, root, pack, "--require-verified-default")
            self.assertEqual(completed.returncode, 1)
            self.assertIn(
                "FAIL: verified default required, but repository channel is 1.97.1",
                completed.stderr,
            )
            self.assertNotIn("INSPECT:", completed.stdout)

    def test_cli_rejects_a_non_primary_required_target(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            root = self.repository(base)
            pack = self.make_pack(base)
            completed = self.run_cli(
                base, root, pack, "--inspect", "--required-target", "x86_64-unknown-linux-gnu"
            )
            self.assertEqual(completed.returncode, 2)


if __name__ == "__main__":
    unittest.main()
