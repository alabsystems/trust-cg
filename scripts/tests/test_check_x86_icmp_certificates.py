"""The x86-64 vector-compare certificate gate's bookkeeping.

scripts/check_x86_icmp_certificates.py re-runs the certificates behind the
certificate-ground `chc_x86` icmp cells under `trust_ir::CHC_X86_ICMP_CERTIFICATE_RULE`,
which the query dump writes from the compiled trust-ir: the rule's AY under
`--strict-proofs` and the rule's Clean, both built by revision, on query bytes
that must hash to their pins and state trust-ir's spec side. These cases hold
its decisions without a real AY or Clean: the lock reader, the rule reader
(each malformed field refused), the AY export's config strip, the tool build
cache (warm hits, tampering, the banner rule, missing sources, the heavy_gate
admission and its failure), the coverage rule over a synthetic query dump
(ground consequences, unknown grounds, the spec subterm), the verdict parsers
(held to the same cases as their Rust originals in `obligation_cert_store.rs`),
and whole gate runs over fake AY and Clean executables obtained through
pre-seeded cache slots, each failure named: the dump comes through the
regeneration path (the example's run replaced by a copy of the synthetic dump),
and a dump supplied with `--queries` is re-run but never passes. The real run
is measured in reports/2026-10-09-x86-icmp-certificate-rule-as-code.md. Test
rung, not proof.
"""

from __future__ import annotations

import contextlib
import copy
import ctypes
import errno
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import shlex
import tempfile
from typing import Optional
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("check_x86_icmp_certificates",
                                              ROOT / "scripts" / "check_x86_icmp_certificates.py")
assert SPEC is not None and SPEC.loader is not None
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)

class WorkspaceToolResolution(unittest.TestCase):
    def test_ordinary_tool_build_uses_the_existing_workspace_purpose(self):
        result = subprocess.CompletedProcess([], 0, "/selected/bin/targo\n", "")
        with mock.patch.object(GATE.subprocess, "run", return_value=result) as run:
            self.assertEqual(GATE.resolve_targo(), Path("/selected/bin/targo"))
        self.assertEqual(run.call_args.args[0][-4:],
                         ["--purpose", "workspace", "--print", "targo"])


class ResourceDescriptorTransport(unittest.TestCase):
    def test_invalid_resource_locator_refuses_before_starting_a_child(self):
        for environment in ({"TRUST_CPU_IMPLICIT_FD": "2"},
                            {"ATERM_WORKLOAD_CPU_FDS_V1": "9999999"},
                            {"TRUST_FIXED_ADMISSION_FD_V1": "requires-live-ancestor-v1"}):
            with self.subTest(environment=environment), \
                    mock.patch.object(GATE, "descendants", return_value=[]), \
                    mock.patch.object(GATE.subprocess, "Popen") as launch:
                with self.assertRaises(GATE.Finding) as raised:
                    GATE.run_admitted_build(["never-start"], ROOT, environment, None, 10)
                self.assertEqual(raised.exception.code, "inherited-resources-invalid")
                launch.assert_not_called()

    def test_advertised_descriptor_reaches_the_actual_build_child(self):
        """A numeric pipe fixture tests transport, not native CPU authority."""
        read_fd, write_fd = os.pipe()
        try:
            environment = GATE.build_environment()
            # Keep this isolated from a real outer resource advertisement.
            for name in ("ATERM_SDK_LEASE_V3", "ATERM_WORKLOAD_HOST_STORE_FD_V1",
                         "TRUST_CPU_IMPLICIT_FD", "TRUST_FIXED_ADMISSION_FD_V1",
                         "ATERM_WORKLOAD_CPU_FDS_V1", "BUILD_SLOT_FENCE_FDS",
                         "CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS"):
                environment.pop(name, None)
            environment["TRUST_CPU_IMPLICIT_FD"] = str(write_fd)
            with tempfile.TemporaryFile(mode="w+") as output:
                code = GATE.run_admitted_build(
                    [sys.executable, "-c",
                     "import os; os.write(int(os.environ['TRUST_CPU_IMPLICIT_FD']), b'transported')"],
                    ROOT, environment, output, 10)
                output.seek(0)
                self.assertEqual(code, 0, output.read())
            self.assertEqual(os.read(read_fd, 11), b"transported")
        finally:
            os.close(read_fd)
            os.close(write_fd)


IR, AY, OTHER, CLEAN_REV = "1" * 40, "a" * 40, "b" * 40, "d" * 40
SCHEME = "git" + "+"


def python_launcher() -> str:
    # A managed interpreter can live under Application Support. The kernel
    # splits whitespace in shebangs; a shell/Python trampoline preserves it.
    return "#!/bin/sh\n" + "'''exec' " + shlex.quote(sys.executable) + ' "$0" "$@"\n' + "' '''\n"


def UNGATED(tool, label: str, work: Path) -> list:
    return []


def lock(ay_revs=(AY, AY), ir=IR) -> str:
    text = "version = 4\n"
    text += (f'\n[[package]]\nname = "trust-ir"\nversion = "0.1.0"\n'
             f'source = "{SCHEME}https://github.com/example/trust-ir.git?rev={ir}#{ir}"\n')
    for index, rev in enumerate(ay_revs):
        name = "ay" if index == 0 else f"ay-part{index}"
        text += (f'\n[[package]]\nname = "{name}"\nversion = "0.27.0"\n'
                 f'source = "{SCHEME}https://github.com/example/ay.git?rev={rev}#{rev}"\n')
    return text


def rule_block(ay_sha=("e" * 64,), clean_sha=("f" * 64,), ay=AY) -> dict:
    """`CHC_X86_ICMP_CERTIFICATE_RULE` as the example serializes it."""
    return {
        "ay": {"package": "ay", "rev": ay, "version": "0.27.0", "build_args": ["-p", "ay", "--features", "cli"],
               "certifying_sha256": list(ay_sha)},
        "ay_args": ["-smt2", "{query}", "--strict-proofs", "--proof", "{proof}", "--proof-format", "alethe"],
        "ay_verdict": "unsat",
        "ay_certificate_report": [["unproved_steps", "0"], ["foreign_assumes", "no"], ["trust_free", "yes"]],
        "unchecked_proof_rules": ["hole", "lia_generic"],
        "clean": {"package": "clean", "rev": CLEAN_REV, "version": "0.9.0",
                  "build_args": ["-p", "clean", "--features", "clean/carcara-verify"],
                  "certifying_sha256": list(clean_sha)},
        "clean_args": ["cert", "verify-external", "{certificate}", "--verbose"],
        "clean_proof_status": "fully verified",
    }


def named(test: unittest.TestCase, findings, code: str) -> None:
    codes = [finding.code for finding in findings]
    test.assertIn(code, codes, f"expected a `{code}` finding, got {[str(f) for f in findings]}")


class LockTests(unittest.TestCase):
    def test_pinned_rev_reads_one_revision_per_repository(self):
        self.assertEqual(GATE.pinned_rev(lock(), "ay", "ay"), AY)
        self.assertEqual(GATE.pinned_rev(lock(), "trust-ir", "trust-ir"), IR)
        with self.assertRaises(GATE.Finding) as raised:
            GATE.pinned_rev(lock((AY, OTHER)), "ay", "ay")
        self.assertEqual(raised.exception.code, "lock-ambiguous")
        with self.assertRaises(GATE.Finding) as raised:
            GATE.pinned_rev(lock(), "ay", "ay-missing")
        self.assertEqual(raised.exception.code, "lock-unreadable")
        self.assertEqual(GATE.lock_pins(lock()), {"trust_ir_rev": IR, "ay_rev": AY})

    def test_the_real_lock_pins_one_ay_revision(self):
        text = (ROOT / "Cargo.lock").read_text()
        self.assertRegex(GATE.pinned_rev(text, "ay", "ay"), r"\A[0-9a-f]{40}\Z")


class SourceAcquisitionTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="icmp-source-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.remote, self.producer, self.source = (self.base / name for name in ("remote.git", "producer", "source"))
        self.environment = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        self.environment.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1", GIT_ALLOW_PROTOCOL="file")
        self.patch = mock.patch.dict(os.environ, self.environment, clear=True)
        self.patch.start()
        self.addCleanup(self.patch.stop)
        self.git(self.base, "init", "-q", "--bare", str(self.remote))
        self.git(self.base, "init", "-q", str(self.producer))
        self.git(self.producer, "config", "user.name", "t")
        self.git(self.producer, "config", "user.email", "t@example.invalid")
        (self.producer / "body").write_text("base\n")
        self.git(self.producer, "add", ".")
        self.git(self.producer, "commit", "-qm", "base")
        self.first = self.git(self.producer, "rev-parse", "HEAD")
        self.git(self.producer, "push", "-q", str(self.remote), "HEAD:refs/heads/main")
        self.git(self.base, "clone", "-q", "--no-local", "--branch", "main", str(self.remote), str(self.source))
        (self.producer / "body").write_text("locked revision\n")
        self.git(self.producer, "commit", "-qam", "locked revision")
        self.pin = self.git(self.producer, "rev-parse", "HEAD")
        self.git(self.producer, "push", "-q", str(self.remote), "HEAD:refs/heads/main")

    def git(self, where, *args):
        return subprocess.run(["git", "-C", str(where), *args], check=True, capture_output=True,
                              text=True).stdout.strip()

    def test_rule_source_fetches_exact_owned_object_without_moving_its_head(self):
        self.assertEqual(GATE.git_dirs_with(self.pin, [self.source]), [])
        self.assertEqual(GATE.source_with("clean", self.pin, self.source), self.source)
        self.assertEqual(self.git(self.source, "rev-parse", "HEAD"), self.first)
        self.assertEqual(self.git(self.source, "rev-parse", "refs/remotes/origin/main"), self.first)
        self.assertEqual(self.git(self.source, "cat-file", "-t", self.pin), "commit")

    def test_other_ssh_host_refuses_and_does_not_raw_fetch(self):
        self.git(self.source, "config", "remote.origin.url", "git@elsewhere.invalid:owner/clean.git")
        with mock.patch.object(GATE.subprocess, "run", wraps=subprocess.run) as commands:
            with self.assertRaises(GATE.MissingInput) as raised:
                GATE.source_with("clean", self.pin, self.source)
        self.assertTrue(any("pin" in call.args[0] for call in commands.call_args_list))
        self.assertFalse(any(call.args[0][0] == "git" and "fetch" in call.args[0]
                             for call in commands.call_args_list))
        self.assertEqual(raised.exception.code, "clean-source-missing")
        self.assertEqual(GATE.git_dirs_with(self.pin, [self.source]), [])
        self.assertEqual(self.git(self.source, "rev-parse", "HEAD"), self.first)


class RuleTests(unittest.TestCase):
    def test_a_well_formed_rule_is_read(self):
        rule = GATE.read_certificate_rule({"certificate_rule": rule_block()})
        self.assertEqual(rule["ay"], GATE.Tool("ay", AY, "0.27.0", ("-p", "ay", "--features", "cli"), ("e" * 64,)))
        self.assertEqual(rule["clean"].rev, CLEAN_REV)
        self.assertEqual(rule["clean"].cache_schema, "trust-cg.clean-cli-build.v2")
        self.assertEqual(rule["ay_certificate_report"],
                         {"unproved_steps": "0", "foreign_assumes": "no", "trust_free": "yes"})
        self.assertEqual(json.loads(json.dumps(GATE.rule_summary(rule)))["ay"]["rev"], AY)

    def test_each_malformed_or_weakened_field_is_refused(self):
        def mutate(path, value):
            block = rule_block()
            target = block
            for key in path[:-1]:
                target = target[key]
            if value is KeyError:
                del target[path[-1]]
            else:
                target[path[-1]] = value
            return block

        cases = [
            (("ay",), KeyError), (("ay", "package"), "clean"), (("ay", "rev"), "abc"),
            (("clean", "version"), "0.9"), (("clean", "build_args"), ["--features", "x"]),
            (("ay", "certifying_sha256"), []), (("clean", "certifying_sha256"), ["not-a-digest"]),
            (("ay_args",), ["-smt2", "{query}", "--proof", "{proof}"]),
            (("ay_args",), ["-smt2", "--strict-proofs", "--proof", "{proof}"]),
            (("ay_verdict",), "sat"), (("ay_certificate_report",), []),
            (("ay_certificate_report",), [["unproved_steps", "0"], ["unproved_steps", "1"]]),
            (("unchecked_proof_rules",), ["lia_generic"]),
            (("clean_args",), ["cert", "verify-external", "--verbose"]),
            (("clean_proof_status",), "verified"),
        ]
        for path, value in cases:
            with self.subTest(path=path, value=value):
                with self.assertRaises(GATE.Finding) as raised:
                    GATE.read_certificate_rule({"certificate_rule": mutate(path, value)})
                self.assertEqual(raised.exception.code, "rule-unreadable")
        with self.assertRaises(GATE.Finding) as raised:
            GATE.read_certificate_rule({})
        self.assertEqual(raised.exception.code, "rule-unreadable")

    def test_the_lock_ay_must_be_the_rule_ay(self):
        rule = GATE.read_certificate_rule({"certificate_rule": rule_block()})
        GATE.require_rule_ay(AY, rule, IR)
        with self.assertRaises(GATE.Finding) as raised:
            GATE.require_rule_ay(OTHER, rule, IR)
        self.assertEqual(raised.exception.code, "ay-pin-differs-from-rule")


class AyExportTests(unittest.TestCase):
    CONFIG = ("# AY build configuration.\n"
              "# ── BEGIN Trust lane config (T3 strips this whole block; byte-coupled) ──\n"
              "target-applies-to-host = true\n"
              "[host]\nrustflags = [\"-Ztrust-verify=on\"]\n"
              "# ── END Trust lane config ────\n"
              "[profile.release]\nlto = \"thin\"\n")

    def test_the_banner_must_name_the_revision_and_version(self):
        banner = f"ay 0.27.0+build.0.{AY}@2026-09-23T12:31:32Z"
        self.assertTrue(GATE.banner_names(banner, AY, "0.27.0"))
        self.assertFalse(GATE.banner_names(banner, OTHER, "0.27.0"))
        self.assertFalse(GATE.banner_names(banner, AY, "0.26.0"))
        self.assertFalse(GATE.banner_names("ay 0.27.0+build.0.unknown@2026", AY, "0.27.0"))

    def test_the_clean_banner_is_exactly_its_version(self):
        clean = GATE.Tool("clean", CLEAN_REV, "0.9.0", ("-p", "clean"), ())
        self.assertTrue(GATE.banner_is_the_rules(clean, "clean 0.9.0"))
        self.assertTrue(GATE.banner_is_the_rules(clean, "clean 0.9.0+g" + CLEAN_REV))
        unknown = "clean 0.9.0 (git sha unknown: built without git provenance)"
        self.assertTrue(GATE.banner_is_the_rules(clean, unknown))
        for banner in ("clean 0.9.1", "clean 0.9.0+dirty", "ay 0.9.0", "",
                       "clean 0.9.0+g" + OTHER, "clean 0.9.0+g" + CLEAN_REV[:12],
                       "clean 0.9.0+gunknown", unknown + " junk", unknown + "\n", " " + unknown,
                       unknown.replace("0.9.0", "0.9.1"), unknown.replace("unknown:", "unknown")):
            with self.subTest(banner=banner):
                self.assertFalse(GATE.banner_is_the_rules(clean, banner))


class CleanExportTests(unittest.TestCase):
    def test_only_exact_retired_clock_assignments_change(self):
        prefix = b'[workspace]\r\nmembers = ["crates/clean"]\r\n[profile.release]\r\nlto = false\r\n'
        suffix = b'[workspace.metadata.identity]\r\nfunction_budget_ms = 999\r\n'
        policy = b'[trust] # old build metadata\r\n# keep this comment\r\n'
        original = prefix + policy + b'function_budget_ms = 3_000 # legacy\r\ntimeout_ms = 5000\r\n' + suffix
        derived, record = GATE.unverified_tool_export(original, "clean")
        self.assertEqual(derived, prefix + policy + suffix)
        self.assertEqual(record["removed_legacy_clock_ms"], {"function_budget_ms": 3000, "timeout_ms": 5000})
        self.assertEqual(record["original_sha256"], hashlib.sha256(original).hexdigest())
        self.assertEqual(record["build_sha256"], hashlib.sha256(derived).hexdigest())
        self.assertTrue(GATE.valid_tool_export_record(record, "clean"))

    def test_current_policies_and_manifests_without_legacy_clocks_are_byte_identical(self):
        for original in (b'[workspace]\nmembers = []\n', b'[trust]\neffort = 2\nbackstop = 1000\n',
                         b'[workspace.metadata]\nfunction_budget_ms = 3000\n'):
            with self.subTest(original=original):
                derived, record = GATE.unverified_tool_export(original, "clean")
                self.assertEqual(derived, original)
                self.assertEqual(record["removed_legacy_clock_ms"], {})
                self.assertTrue(GATE.valid_tool_export_record(record, "clean"))

    def test_compound_unknown_malformed_or_unsupported_legacy_policies_refuse(self):
        for original in (b'[trust]\nfunction_budget_ms = 3000\neffort = 2\n',
                         b'[trust]\nfunction_budget_ms = 3000\nbackstop = 1000\n',
                         b'[trust]\nfunction_budget_ms = 3000\nenabled = true\n',
                         b'[trust]\nfunction_budget_ms = 3000\ntimout_ms = 5000\n',
                         b'[trust]\nfunction_budget_ms = true\n',
                         b'[trust]\nfunction_budget_ms = "3000"\n',
                         b'[trust]\nfunction_budget_ms = 0\n',
                         b'[trust]\nfunction_budget_ms = -1\n',
                         b'[trust]\n"function_budget_ms" = 3000\n',
                         b'trust.function_budget_ms = 3000\n',
                         b'[trust]\nfunction_budget_ms = 3000\nfunction_budget_ms = 4000\n'):
            with self.subTest(original=original):
                with self.assertRaises(GATE.Finding) as raised:
                    GATE.unverified_tool_export(original, "clean")
                self.assertEqual(raised.exception.code, "clean-export-policy-unrecognized")

    def test_misleading_text_never_changes_nonpolicy_values(self):
        original = b'description = """\n[trust]\nfunction_budget_ms = 3000\n"""\n[trust]\nfunction_budget_ms = 3000\n'
        with self.assertRaises(GATE.Finding) as raised:
            GATE.unverified_tool_export(original, "clean")
        self.assertEqual(raised.exception.code, "clean-export-policy-unrecognized")

    def test_ay_clock_only_export_retains_explicit_units_without_conversion(self):
        original = b'[workspace]\nmembers = []\n[trust]\nfunction_budget_ms = 3000\ncompiler_timeout_secs = 72000\n'
        derived, record = GATE.unverified_tool_export(original, "ay")
        self.assertEqual(derived, b'[workspace]\nmembers = []\n[trust]\n')
        self.assertEqual(record["removed_legacy_clock_settings"], {
            "compiler_timeout_secs": 72000, "function_budget_ms": 3000,
        })
        self.assertTrue(GATE.valid_tool_export_record(record, "ay"))
        self.assertFalse(GATE.valid_tool_export_record(record, "clean"))

    def test_ay_active_unknown_or_ambiguous_clock_policy_refuses(self):
        for extra in (b'effort = 2\n', b'backstop = 1000\n', b'enabled = false\n',
                      b'compiler_timeuot_secs = 1\n', b'compiler_timeout_secs = true\n',
                      b'"compiler_timeout_secs" = 72000\n'):
            original = b'[trust]\nfunction_budget_ms = 3000\n' + extra
            with self.subTest(extra=extra), self.assertRaises(GATE.Finding) as raised:
                GATE.unverified_tool_export(original, "ay")
            self.assertEqual(raised.exception.code, "ay-export-policy-unrecognized")


def seed_slot(cache: Path, tool, payload: bytes, banner: str, **record) -> Path:
    """A slot as the gate writes it, whatever this process's umask
    (scripts/private_cache.py; a slot others could write is refused first,
    see test_private_cache.py). `record` overrides fields of its identity
    record."""
    slot = cache / tool.cache_key
    GATE.private_cache.create_private_dir_all(slot)
    binary = slot / tool.package
    GATE.private_cache.write_private_file(binary, payload)
    os.chmod(binary, 0o500)
    identity = {"schema": tool.cache_schema, "rev": tool.rev, "version": tool.version,
                "sha256": hashlib.sha256(payload).hexdigest(), "banner": banner, "build_seconds": 1}
    identity["recipe"] = {
        "command": ["--unverified", "build", "--release", "--locked", *tool.build_args],
        "unverified_export": GATE.unverified_tool_export(b'[workspace]\n', tool.package)[1],
        "cargo_config": "export's own .cargo/config.toml",
    }
    identity.update(record)
    GATE.private_cache.write_private_file(slot / "identity.json", json.dumps(identity))
    return slot


def git_repository(base: Path, files: dict, name: str) -> tuple[Path, str]:
    repo = base / name
    for relative, (text, executable) in files.items():
        path = repo / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        if executable:
            os.chmod(path, 0o755)
    env = dict(os.environ, GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")
    git = ["git", "-C", str(repo), "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
           "-c", "commit.gpgSign=false"]
    subprocess.run(["git", "init", "-q", str(repo)], check=True, env=env)
    subprocess.run(git + ["add", "-A"], check=True, env=env)
    subprocess.run(git + ["commit", "-q", "-m", name], check=True, env=env)
    rev = subprocess.run(["git", "-C", str(repo), "rev-parse", "HEAD"], capture_output=True, text=True,
                         check=True).stdout.strip()
    return repo, rev


# A fixture targo for a cold Clean build: it checks it was started in the
# export, then writes `clean`, whose `--version` is `clean 0.9.0`.
FAKE_TARGO = r'''#!/bin/sh
[ "$1 $2" = "--unverified build" ] || { echo "fixture targo: unexpected: $*" >&2; exit 64; }
[ -f Cargo.toml ] || { echo "fixture targo: not in the export" >&2; exit 65; }
mkdir -p "$CARGO_TARGET_DIR/release" || exit 68
printf '#!/bin/sh\necho "clean 0.9.0"\n' > "$CARGO_TARGET_DIR/release/clean"
chmod +x "$CARGO_TARGET_DIR/release/clean"
'''

# A fixture targo whose build never ends: it records its pid and its child's,
# then waits on the child.
HANGING_TARGO = r'''#!/bin/sh
sleep 300 &
echo "$$ $!" > "$FIXTURE_PIDS"
wait
'''


def alive(pid: int) -> bool:
    """A process that exists and is not a zombie."""
    if sys.platform == "darwin":
        # Avoid the setuid ps executable, which macOS refuses in a sandbox.
        # launchd reaps orphaned children; eventually_gone waits for that too.
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return False
        return True
    state = subprocess.run(["ps", "-o", "stat=", "-p", str(pid)], capture_output=True, text=True).stdout.strip()
    return bool(state) and not state.startswith("Z")


def eventually_gone(pids, seconds: float = 10.0) -> list:
    """The pids still alive after `seconds`."""
    import time
    deadline = time.monotonic() + seconds
    while time.monotonic() < deadline and any(alive(pid) for pid in pids):
        time.sleep(0.1)
    return [pid for pid in pids if alive(pid)]


# A fixture heavy_gate: `run <gb> <label> -- cmd...` records its admission and
# runs the command, or refuses it (exit 75) when FIXTURE_HEAVY_GATE_REFUSE is set.
FAKE_HEAVY_GATE = r'''#!/bin/sh
[ "$1" = run ] || exit 64
echo "admitted $2 $3" >> "$(dirname "$0")/../../admissions.log"
shift 3
[ "$1" = "--" ] && shift
if [ -n "${FIXTURE_HEAVY_GATE_REFUSE:-}" ]; then echo "heavy_gate: refused (fixture)" >&2; exit 75; fi
exec "$@"
'''


class ToolBuildTests(unittest.TestCase):
    """`obtain_build` for both tools: the warm hit, tampering, the banner rule,
    a missing source, and a cold build under the heavy_gate admission."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.clean = GATE.Tool("clean", CLEAN_REV, "0.9.0", ("-p", "clean", "--features", "clean/carcara-verify"),
                               (hashlib.sha256(b"clean bytes").hexdigest(),))

    def test_a_warm_slot_is_used_and_a_changed_binary_is_refused(self):
        for tool, banner in ((GATE.Tool("ay", AY, "0.27.0", ("-p", "ay"), ()), f"ay 0.27.0+build.0.{AY}@x"),
                             (self.clean, "clean 0.9.0")):
            with self.subTest(tool=tool.package):
                cache = self.base / f"{tool.package}-cli"
                slot = seed_slot(cache, tool, b"clean bytes", banner)
                self.assertEqual(GATE.obtain_build(tool, cache, None, False, UNGATED)["cache"], "warm")
                os.chmod(slot / tool.package, 0o700)
                (slot / tool.package).write_bytes(b"clean bytes, then changed")
                with self.assertRaises(GATE.Finding) as raised:
                    GATE.obtain_build(tool, cache, None, False, UNGATED)
                self.assertEqual(raised.exception.code, f"{tool.package}-cache-tampered")

    def test_a_warm_slot_recorded_for_another_revision_or_schema_is_refused(self):
        """The record must name the slot's revision and the tool's cache
        schema, even when the bytes match the recorded digest."""
        for tool, banner in ((GATE.Tool("ay", AY, "0.27.0", ("-p", "ay"), ()), f"ay 0.27.0+build.0.{AY}@x"),
                             (self.clean, "clean 0.9.0")):
            for field, value in (("rev", OTHER), ("schema", "trust-cg.ay-cli-build.v0")):
                with self.subTest(tool=tool.package, field=field):
                    cache = self.base / f"{tool.package}-{field}-cli"
                    seed_slot(cache, tool, b"clean bytes", banner, **{field: value})
                    with self.assertRaises(GATE.Finding) as raised:
                        GATE.obtain_build(tool, cache, None, False, UNGATED)
                    self.assertEqual(raised.exception.code, f"{tool.package}-cache-tampered")

    def test_a_warm_slot_with_another_banner_is_refused(self):
        cache = self.base / "clean-cli"
        seed_slot(cache, self.clean, b"clean bytes", "clean 0.8.0")
        with self.assertRaises(GATE.Finding) as raised:
            GATE.obtain_build(self.clean, cache, None, False, UNGATED)
        self.assertEqual(raised.exception.code, "clean-banner-mismatch")

    def test_no_source_with_the_revision_is_a_missing_input(self):
        for tool in (GATE.Tool("ay", AY, "0.27.0", ("-p", "ay"), ()), self.clean):
            with self.subTest(tool=tool.package):
                with self.assertRaises(GATE.MissingInput) as raised:
                    GATE.obtain_build(tool, self.base / f"{tool.package}-cache", self.base / "no-repo", False,
                                      UNGATED)
                self.assertEqual(raised.exception.code, f"{tool.package}-source-missing")

    def test_cold_ay_retains_policy_and_does_not_reuse_stripped_cache(self):
        config = AyExportTests.CONFIG
        repo, rev = git_repository(self.base, {
            "Cargo.toml": ('[package]\nname = "ay"\nversion = "0.27.0"\n', False),
            "src/main.rs": ('fn main() {}\n', False),
            "Cargo.lock": ('version = 4\n', False),
            ".cargo/config.toml": (config, False),
        }, "ay-source")
        tool = GATE.Tool("ay", rev, "0.27.0", ("-p", "ay", "--features", "cli"), ())
        cache = self.base / "ay-policy-cache"
        old = cache / f"{rev}-unverified-export-v1"
        old.mkdir(parents=True)
        (old / "identity.json").write_text("old stripped-policy cache")
        targo = self.base / "targo"

        def build(command, cwd, env, log_handle, timeout):
            self.assertEqual((cwd / ".cargo/config.toml").read_text(), config)
            self.assertIn("--unverified", command)
            binary = Path(env["CARGO_TARGET_DIR"]) / "release" / "ay"
            binary.parent.mkdir(parents=True)
            binary.write_text(f'#!/bin/sh\necho "ay 0.27.0+build.0.{rev}@2026"\n')
            binary.chmod(0o700)
            return 0

        with mock.patch.object(GATE, "resolve_targo", return_value=targo), \
                mock.patch.object(GATE, "run_admitted_build", side_effect=build):
            identity = GATE.obtain_build(tool, cache, repo, False, UNGATED)
        self.assertEqual(identity["cache"], "cold")
        self.assertEqual(identity["recipe"]["cargo_config"], "export's own .cargo/config.toml")
        self.assertEqual((repo / ".cargo/config.toml").read_text(), config)
        self.assertEqual((old / "identity.json").read_text(), "old stripped-policy cache")
        record = cache / tool.cache_key / "identity.json"
        changed = json.loads(record.read_text())
        changed["recipe"]["cargo_config"] = "export's Trust-lane config block removed"
        record.write_text(json.dumps(changed))
        with self.assertRaises(GATE.Finding) as raised:
            GATE.obtain_build(tool, cache, repo, False, UNGATED)
        self.assertEqual(raised.exception.code, "ay-cache-tampered")

    def cold_clean(self, targo_script: str = FAKE_TARGO,
                   manifest: str = '[package]\nname = "clean"\nversion = "0.9.0"\n', **environment: str):
        repo, rev = git_repository(self.base, {
            "Cargo.toml": (manifest, False),
            "src/main.rs": ('fn main() {}\n', False),
            "Cargo.lock": ('version = 4\n', False),
            ".cargo/config.toml": ("[build]\njobs = 4\n", False),
            "scripts/heavy_gate.sh": (FAKE_HEAVY_GATE, True),
            "scripts/heavy_gate_weights.sh": ("# weights\n", False),
        }, "clean-source")
        tool = GATE.Tool("clean", rev, "0.9.0", ("-p", "clean", "--features", "clean/carcara-verify"), ())
        targo = self.base / "bin" / "targo"
        targo.parent.mkdir(exist_ok=True)
        targo.write_text(targo_script)
        os.chmod(targo, 0o755)
        cache = self.base / "xdg" / "clean-cli"
        admission = GATE.heavy_gate_admission(tool, repo)
        with mock.patch.object(GATE, "resolve_targo", return_value=targo), \
                mock.patch.dict(os.environ, environment), contextlib.redirect_stdout(io.StringIO()):
            return GATE.obtain_build(tool, cache, repo, True, admission), cache, rev

    def test_a_cold_build_runs_under_the_rules_heavy_gate(self):
        identity, cache, rev = self.cold_clean()
        self.assertEqual((identity["cache"], identity["banner"], identity["rev"]), ("cold", "clean 0.9.0", rev))
        self.assertEqual(identity["schema"], "trust-cg.clean-cli-build.v2")
        weight = f'auto:x86-icmp-clean-build-cold:{GATE.TOOL_BUILD_FALLBACK_GB["clean"]}'
        self.assertEqual(identity["admission"], ["run", weight, f"x86-icmp-clean-{rev[:12]}"])
        self.assertEqual(identity["recipe"]["cargo_config"], "export's own .cargo/config.toml")
        admissions = list(cache.glob("build-*/admissions.log"))
        self.assertEqual(len(admissions), 1, admissions)
        self.assertEqual(admissions[0].read_text(), f"admitted {weight} x86-icmp-clean-{rev[:12]}\n")

    def test_resume_revalidates_source_and_runs_the_normal_command_preserving_failed_outputs(self):
        identity, cache, rev = self.cold_clean()
        tool = GATE.Tool("clean", rev, "0.9.0", ("-p", "clean", "--features", "clean/carcara-verify"), ())
        # A completed but unpublished build has its original work and no slot.
        shutil.rmtree(cache / tool.cache_key)
        work = next(cache.glob("build-*")).resolve()
        old_log = (work / "build.log").read_bytes()
        old_image = (work / "clean").read_bytes() if (work / "clean").exists() else b"failed staged image"
        (work / "clean").write_bytes(old_image)
        repo = self.base / "clean-source"
        targo = self.base / "bin/targo"
        with mock.patch.object(GATE, "resolve_targo", return_value=targo):
            resumed = GATE.obtain_build(tool, cache, repo, False,
                GATE.heavy_gate_admission(tool, repo), resume_work=work)
        self.assertEqual(resumed["sha256"], identity["sha256"])
        self.assertTrue(resumed["resumed_build"]["source_checked_before_and_after"])
        self.assertEqual((work / "build.log").read_bytes(), old_log)
        self.assertEqual((work / "clean").read_bytes(), old_image)
        self.assertTrue(Path(resumed["resumed_build"]["log"]).is_file())
        admissions = list(work.glob("resume-admission-*/admissions.log"))
        self.assertEqual(len(admissions), 1)
        self.assertIn("x86-icmp-clean-build-resume:", admissions[0].read_text())

    def test_resume_refuses_changed_missing_or_extra_source_before_any_build(self):
        _, cache, rev = self.cold_clean()
        tool = GATE.Tool("clean", rev, "0.9.0", ("-p", "clean", "--features", "clean/carcara-verify"), ())
        work = next(cache.glob("build-*")).resolve()
        source = work / "src/src/main.rs"
        original = source.read_bytes()
        for mutation in ("changed", "missing", "extra"):
            with self.subTest(mutation=mutation), mock.patch.object(GATE, "run_admitted_build") as build:
                if mutation == "changed": source.write_bytes(original + b"changed")
                elif mutation == "missing": source.unlink()
                else: (work / "src/Targo.toml").write_text("[workspace]\n")
                with self.assertRaises(GATE.Finding) as refused:
                    GATE.check_resumed_export(tool, cache.resolve(), work.resolve(), self.base / "clean-source")
                self.assertEqual(refused.exception.code, "clean-resume-source-mismatch")
                build.assert_not_called()
                source.write_bytes(original)
                (work / "src/Targo.toml").unlink(missing_ok=True)

    def test_resume_refuses_foreign_target_descendants_before_a_build(self):
        _, cache, rev = self.cold_clean()
        tool = GATE.Tool("clean", rev, "0.9.0", ("-p", "clean", "--features", "clean/carcara-verify"), ())
        work = next(cache.glob("build-*")).resolve()
        target = work / "target"
        foreign = self.base / "foreign-target"
        foreign.mkdir(mode=0o700)
        foreign_binary = foreign / "clean"
        foreign_binary.write_text("foreign")
        for case in ("release", "binary"):
            path = target / "release" if case == "release" else target / "release/clean"
            saved = path.with_name(path.name + ".saved")
            path.rename(saved)
            path.symlink_to(foreign if case == "release" else foreign_binary,
                            target_is_directory=case == "release")
            with self.subTest(case=case), mock.patch.object(GATE, "run_admitted_build") as build:
                with self.assertRaises(GATE.Finding) as refused:
                    GATE.check_resumed_export(tool, cache.resolve(), work, self.base / "clean-source")
                self.assertEqual(refused.exception.code, "clean-resume-target-not-private")
                build.assert_not_called()
            path.unlink()
            saved.rename(path)
        (target / "confined-link").symlink_to("release/clean")
        GATE.check_resumed_export(tool, cache.resolve(), work, self.base / "clean-source")

    def test_cold_legacy_export_discloses_manifest_and_preserves_repository_inputs(self):
        original = '[package]\nname = "clean"\nversion = "0.9.0"\n[trust]\nfunction_budget_ms = 3000\n'
        identity, cache, rev = self.cold_clean(manifest=original)
        record = identity["recipe"]["unverified_export"]
        self.assertTrue(GATE.valid_tool_export_record(record, "clean"))
        self.assertEqual(record["removed_legacy_clock_ms"], {"function_budget_ms": 3000})
        source = self.base / "clean-source"
        exported = next(cache.glob("build-*/src"))
        self.assertEqual((source / "Cargo.toml").read_text(), original)
        self.assertNotIn("function_budget_ms", (exported / "Cargo.toml").read_text())
        for path in ("src/main.rs", "Cargo.lock", ".cargo/config.toml"):
            self.assertEqual((source / path).read_bytes(), (exported / path).read_bytes())
        self.assertEqual(GATE.obtain_build(GATE.Tool("clean", rev, "0.9.0", ("-p", "clean", "--features", "clean/carcara-verify"), ()),
                                          cache, None, False, UNGATED)["cache"], "warm")

    def test_clean_cache_cannot_omit_or_falsify_the_export_recipe(self):
        _, valid = GATE.unverified_tool_export(b'[workspace]\n', "clean")
        invalid = [None, [], {}, dict(valid, schema="other"), dict(valid, build_sha256="bad"),
                   dict(valid, removed_legacy_clock_ms={"effort": 0}),
                   dict(valid, removed_legacy_clock_ms={"timeout_ms": True}),
                   dict(valid, removed_legacy_clock_ms={"timeout_ms": 3000})]
        for index, record in enumerate(invalid):
            cache = self.base / f"invalid-recipe-{index}"
            seed_slot(cache, self.clean, b"clean bytes", "clean 0.9.0", recipe={
                "command": ["--unverified", "build", "--release", "--locked", *self.clean.build_args],
                "unverified_export": record,
            })
            with self.assertRaises(GATE.Finding) as raised:
                GATE.obtain_build(self.clean, cache, None, False, UNGATED)
            self.assertEqual(raised.exception.code, "clean-cache-tampered")

    def test_a_different_checker_build_feature_set_cannot_reuse_the_new_recipe(self):
        cache = self.base / "different-features"
        seed_slot(cache, self.clean, b"clean bytes", "clean 0.9.0")
        wrong = self.clean._replace(build_args=("-p", "clean"))
        with self.assertRaises(GATE.Finding) as raised:
            GATE.obtain_build(wrong, cache, None, False, UNGATED)
        self.assertEqual(raised.exception.code, "clean-cache-tampered")

    def test_legacy_clean_cache_is_preserved_without_satisfying_the_derived_recipe(self):
        cache = self.base / "legacy-cache"
        legacy = cache / self.clean.rev
        GATE.private_cache.create_private_dir_all(legacy)
        marker = legacy / "identity.json"
        GATE.private_cache.write_private_file(marker, '{"schema":"trust-cg.clean-cli-build.v1"}')
        with self.assertRaises(GATE.MissingInput) as raised:
            GATE.obtain_build(self.clean, cache, self.base / "no-repo", False, UNGATED)
        self.assertEqual(raised.exception.code, "clean-source-missing")
        self.assertEqual(marker.read_text(), '{"schema":"trust-cg.clean-cli-build.v1"}')

    def test_a_heavy_gate_refusal_is_a_named_build_failure(self):
        with self.assertRaises(GATE.Finding) as raised:
            self.cold_clean(FIXTURE_HEAVY_GATE_REFUSE="1")
        self.assertEqual(raised.exception.code, "clean-build-failed")
        self.assertIn("heavy_gate: refused (fixture)", raised.exception.message)

    def test_a_build_past_its_timeout_is_stopped_with_its_whole_tree(self):
        """`subprocess.run`'s timeout kills only the direct child (here the
        admission), which would orphan the build. The gate stops the tree:
        the admission, the build and the build's own child."""
        pids_file = self.base / "pids"
        with mock.patch.object(GATE, "BUILD_TIMEOUT_SECONDS", 2), self.assertRaises(GATE.Finding) as raised:
            self.cold_clean(HANGING_TARGO, FIXTURE_PIDS=str(pids_file))
        self.assertEqual(raised.exception.code, "clean-build-failed")
        self.assertIn("no build within 2s", raised.exception.message)
        pids = [int(pid) for pid in pids_file.read_text().split()]
        self.assertEqual(len(pids), 2)
        self.assertEqual(eventually_gone(pids), [], "the timed-out build's processes outlived the gate's stop")

    def test_an_interrupted_build_is_stopped_with_its_whole_tree(self):
        import _thread
        import threading
        import time
        pids_file = self.base / "pids"
        script = self.base / "hang.sh"
        script.write_text(HANGING_TARGO)
        os.chmod(script, 0o755)

        def interrupt_once_started():
            deadline = time.monotonic() + 10
            while time.monotonic() < deadline and not (pids_file.exists() and pids_file.read_text().strip()):
                time.sleep(0.05)
            _thread.interrupt_main()
        threading.Thread(target=interrupt_once_started, daemon=True).start()
        with open(self.base / "build.log", "w") as log, self.assertRaises(KeyboardInterrupt):
            GATE.run_admitted_build([str(script)], self.base, dict(os.environ, FIXTURE_PIDS=str(pids_file)), log,
                                    60)
        pids = [int(pid) for pid in pids_file.read_text().split()]
        self.assertEqual(eventually_gone(pids), [], "the interrupted build's processes outlived the gate")

    def test_a_clean_without_heavy_gate_is_refused(self):
        repo, rev = git_repository(self.base, {"Cargo.toml": ("[package]\n", False)}, "bare-clean")
        tool = GATE.Tool("clean", rev, "0.9.0", ("-p", "clean"), ())
        work = self.base / "work"
        work.mkdir()
        with self.assertRaises(GATE.Finding) as raised:
            GATE.heavy_gate_admission(tool, repo)(tool, "x86-icmp-ay-x", work)
        self.assertEqual(raised.exception.code, "heavy-gate-missing")


class QueryDumpTests(unittest.TestCase):
    """Execute the real dump runner with fixture commands, including live
    descendants. No compiler, certificate verdict or supplied-dump credit."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name) / "query owner with spaces"
        (self.base / "scripts").mkdir(parents=True)
        self.script = self.base / "scripts" / "trust_cargo.sh"
        self.out = self.base / "dump with spaces"

    def command(self, source: str) -> None:
        self.script.write_text(source)
        self.script.chmod(0o755)

    def run_dump(self, **environment: str) -> None:
        with mock.patch.object(GATE, "ROOT", self.base), \
                mock.patch.dict(os.environ, environment), contextlib.redirect_stdout(io.StringIO()):
            GATE.dump_queries(self.out)

    def test_query_dump_success_preserves_exact_argv_environment_and_owner_artifact(self):
        self.command(python_launcher() + '''import json, os, sys
from pathlib import Path
out = Path(sys.argv[-1])
out.mkdir()
(out / "manifest.json").write_text(json.dumps({
    "argv": sys.argv[1:], "cwd": str(Path.cwd()),
    "inherited": os.environ["FIXTURE_QUERY_DUMP_VALUE"]}))
print("fixture query dump completed", flush=True)
''')
        self.run_dump(FIXTURE_QUERY_DUMP_VALUE="original-context")
        actual = json.loads((self.out / "manifest.json").read_text())
        self.assertEqual(actual, {
            "argv": ["run", "--locked", "-p", "trust-cg-verify", "--example", GATE.EXAMPLE,
                     "--", str(self.out)],
            "cwd": str(self.base.resolve()), "inherited": "original-context",
        })

    def test_query_dump_nonzero_is_named_and_retains_only_last_thirty_ordered_lines(self):
        self.command(python_launcher() + '''import sys
for index in range(1000):
    print(f"query-line-{index:04d}", file=sys.stdout if index % 2 == 0 else sys.stderr, flush=True)
sys.exit(23)
''')
        with self.assertRaises(GATE.Finding) as raised:
            self.run_dump()
        self.assertEqual(raised.exception.code, "queries-dump-failed")
        reason, tail = raised.exception.message.split("; last lines:\n  ", 1)
        self.assertEqual(reason, "exit 23")
        self.assertEqual(tail.split("\n  "), [f"query-line-{index:04d}" for index in range(970, 1000)])
        self.assertFalse(self.out.exists(), "a failing dumper produced no successful owner artifact")

    def test_query_dump_timeout_stops_the_actual_parent_and_descendant(self):
        self.command(HANGING_TARGO)
        pids_file = self.base / "pids"
        with mock.patch.object(GATE, "QUERY_DUMP_TIMEOUT_SECONDS", 2), \
                self.assertRaises(GATE.Finding) as raised:
            self.run_dump(FIXTURE_PIDS=str(pids_file))
        self.assertEqual(raised.exception.code, "queries-dump-failed")
        self.assertIn("no query dump within 2s; its process tree was stopped", raised.exception.message)
        pids = [int(pid) for pid in pids_file.read_text().split()]
        self.assertEqual(len(pids), 2, "the real parent and sleeping child must have started")
        self.assertEqual(eventually_gone(pids), [], "the query build outlived timeout cleanup")

    def test_query_dump_interrupt_propagates_after_actual_descendant_cleanup(self):
        import _thread
        import threading
        import time
        self.command(HANGING_TARGO)
        pids_file = self.base / "pids"
        started = threading.Event()

        def interrupt_once_started():
            deadline = time.monotonic() + 10
            while time.monotonic() < deadline:
                if pids_file.exists() and pids_file.read_text().strip():
                    started.set()
                    _thread.interrupt_main()
                    return
                time.sleep(0.05)

        interrupter = threading.Thread(target=interrupt_once_started, daemon=True)
        interrupter.start()
        try:
            with mock.patch.object(GATE, "QUERY_DUMP_TIMEOUT_SECONDS", 60), self.assertRaises(KeyboardInterrupt):
                self.run_dump(FIXTURE_PIDS=str(pids_file))
        finally:
            interrupter.join(timeout=10)
        self.assertFalse(interrupter.is_alive(), "the fixture interrupt worker must finish")
        self.assertTrue(started.is_set(), "interruption must follow real descendant startup")
        pids = [int(pid) for pid in pids_file.read_text().split()]
        self.assertEqual(len(pids), 2)
        self.assertEqual(eventually_gone(pids), [], "the interrupted query build outlived the gate")


# A synthetic query dump: two descriptors, three operations.
MODEL_Q = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(assert false)\n(check-sat)\n"
SPEC_TEXT = "(concat (ite (= x x) #xff #x00) (ite (= x x) #xff #x00))"


def cert_query(tag: str, spec: str = SPEC_TEXT) -> str:
    return (f"(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(assert (not (= {spec} (bvnot x))))\n; {tag}\n"
            "(check-sat)\n")


def synthetic_dump(directory: Path, rule: Optional[dict] = None) -> dict:
    cells = []
    pins = []
    for shape, bits, lanes in (("V4I32", 32, 4), ("V16I8", 8, 16)):
        for cond, operation in (("Eq", "icmp.eq"), ("Ult", "icmp.ult"), ("Ne", "icmp.ne")):
            model = operation == "icmp.eq"
            query = MODEL_Q if model else cert_query(f"{shape} {cond}")
            name = f"{shape}_{cond}.smt2"
            (directory / name).write_text(query)
            digest = None if model else hashlib.sha256(query.encode()).hexdigest()
            if digest:
                pins.append([shape, cond, digest])
            cells.append({
                "shape": shape, "lane_bits": bits, "lanes": lanes, "cond": cond, "operation": operation,
                "reader": {"status": "available", "reason": "canonical_contract", "fail_closed": False,
                           "feature_guard": "x86.sse2"},
                "ground": "instruction-model" if model else "certificate",
                "obligation_count": 1, "obligation": f"x86_64: {shape}Icmp_{cond} -> X",
                "degenerate": model, "query_file": name, "certified_sha256": digest,
                "spec": {"fn": "trust_ir::chc_x86_vector_icmp_spec", "trust_ir_build": "fixture",
                         "sha256": hashlib.sha256(SPEC_TEXT.encode()).hexdigest(), "text": SPEC_TEXT},
            })
    manifest = {
        "schema": GATE.QUERY_MANIFEST_SCHEMA, "trust_ir_build": "fixture",
        "certificate_rule": rule if rule is not None else rule_block(),
        "operations": ["Eq", "Ult", "Ne"],
        "descriptors": [{"shape": "V4I32", "lane_bits": 32, "lanes": 4},
                        {"shape": "V16I8", "lane_bits": 8, "lanes": 16}],
        "certified_pins": pins, "reviewed_fail_closed": [], "measured_not_admitted": [], "cells": cells,
    }
    (directory / "manifest.json").write_text(json.dumps(manifest))
    return manifest


def cell(manifest: dict, shape: str, cond: str) -> dict:
    return next(c for c in manifest["cells"] if c["shape"] == shape and c["cond"] == cond)


class CoverageTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.dir = Path(self.temporary.name)
        self.manifest = synthetic_dump(self.dir)

    def findings(self):
        return GATE.coverage_findings(self.manifest, self.dir)

    def test_a_complete_dump_has_no_finding(self):
        self.assertEqual([str(f) for f in self.findings()], [])

    def test_every_reader_cell_is_covered_exactly_once(self):
        self.manifest["cells"].pop()
        named(self, self.findings(), "cell-uncovered")
        self.setUp()
        self.manifest["cells"].append(dict(self.manifest["cells"][0]))
        named(self, self.findings(), "cell-duplicated")
        self.setUp()
        self.manifest["descriptors"].append({"shape": None, "lane_bits": 16, "lanes": 8})
        named(self, self.findings(), "cell-uncovered")

    def test_a_ground_trust_ir_does_not_answer_is_refused(self):
        cell(self.manifest, "V4I32", "Ne")["ground"] = "certificate-or-model"
        named(self, self.findings(), "ground-unknown")
        self.setUp()
        cell(self.manifest, "V4I32", "Ne")["ground"] = None
        named(self, self.findings(), "ground-unknown")

    def test_fail_closed_is_the_readers_verdict(self):
        cell(self.manifest, "V4I32", "Eq")["reader"]["fail_closed"] = True
        named(self, self.findings(), "ground-mismatch")
        self.setUp()
        cell(self.manifest, "V4I32", "Ult")["ground"] = "fail-closed"
        named(self, self.findings(), "ground-mismatch")

    def test_instruction_model_queries_are_degenerate_and_unpinned(self):
        (self.dir / "V4I32_Eq.smt2").write_text(cert_query("claims evidence"))
        named(self, self.findings(), "instruction-model-not-degenerate")
        self.setUp()
        cell(self.manifest, "V16I8", "Eq")["degenerate"] = False
        named(self, self.findings(), "instruction-model-not-degenerate")
        self.setUp()
        cell(self.manifest, "V16I8", "Eq")["certified_sha256"] = "0" * 64
        named(self, self.findings(), "pin-on-instruction-model-cell")

    def test_certificate_queries_are_not_degenerate(self):
        (self.dir / "V4I32_Ult.smt2").write_text(MODEL_Q)
        named(self, self.findings(), "certificate-degenerate")

    def test_query_whose_spec_subterm_was_rewritten_is_refused(self):
        """B-T3f: the dump's spec is S, the query's assertion embeds a
        simplified S'. Scope: simplification pass-through only."""
        rewritten = SPEC_TEXT.replace("(= x x)", "true")
        (self.dir / "V4I32_Ult.smt2").write_text(cert_query("simplified", rewritten))
        named(self, self.findings(), "spec-not-trust-ir-statement")
        self.setUp()
        spec = cell(self.manifest, "V16I8", "Ne")["spec"]
        spec["text"] = spec["text"] + " "
        named(self, self.findings(), "spec-unreadable")
        self.setUp()
        cell(self.manifest, "V16I8", "Ne")["spec"] = None
        named(self, self.findings(), "spec-unreadable")

    def test_every_pin_is_used_once_and_every_certificate_cell_has_one(self):
        cell(self.manifest, "V16I8", "Ne")["certified_sha256"] = None
        named(self, self.findings(), "pin-unused")
        named(self, self.findings(), "pin-missing")
        self.setUp()
        self.manifest["certified_pins"].append(list(self.manifest["certified_pins"][0]))
        named(self, self.findings(), "pin-duplicated")
        self.setUp()
        target = cell(self.manifest, "V4I32", "Ult")
        target["reader"]["fail_closed"] = True
        target["ground"] = "fail-closed"
        named(self, self.findings(), "pin-on-fail-closed-cell")


class VerdictTests(unittest.TestCase):
    def test_ay_stdout_contract_matches_obligation_cert_store(self):
        # The cases of `ay_mint_requires_one_exact_successful_unsat_verdict`.
        self.assertTrue(GATE.ay_stdout_is_exact_unsat(0, "unsat\n"))
        self.assertTrue(GATE.ay_stdout_is_exact_unsat(0, "producer diagnostic\nunsat\nproof written\n"))
        for returncode, stdout in ((1, "unsat\n"), (0, "solver could not produce an unsat proof\n"),
                                   (0, "unknown\n"), (0, "sat\n"), (0, "unsat\nsat\n"), (0, "unsat\nunsat\n"),
                                   (0, "(error \"proof emission failed\")\nunsat\n")):
            with self.subTest(stdout=stdout):
                self.assertFalse(GATE.ay_stdout_is_exact_unsat(returncode, stdout))

    def test_clean_stdout_contract_matches_obligation_cert_store(self):
        # The cases of `clean_alethe_success_parser_requires_the_exact_full_verification_contract`.
        genuine = ("External certificate verification: PASSED\nType: Alethe SMT proof\n"
                   "Problem bytes: 12, proof bytes: 34\nProof status: fully verified\nVerified in 0.001000s\n")
        self.assertTrue(GATE.clean_alethe_stdout_is_fully_verified(genuine))
        for stdout in ("Batch verification complete: 1/2 passed, 1 failed\n",
                       "External certificate verification: PASSED\nType: Alethe SMT proof\n",
                       "External certificate verification: PASSED\nType: Alethe SMT proof\n"
                       "Proof status: fully verified\nExternal certificate verification: FAILED\n"):
            with self.subTest(stdout=stdout):
                self.assertFalse(GATE.clean_alethe_stdout_is_fully_verified(stdout))

    def test_ay_certificate_report_must_be_one_complete_trust_free_line(self):
        fields = GATE.read_certificate_rule({"certificate_rule": rule_block()})["ay_certificate_report"]
        good = ("c ay.session.start build.stamp=x\nc ay.proof.certificate path=p unproved_steps=0 foreign_assumes=no "
                "trust_free=yes ay_self_checkable=yes\nc ay.session.end exit.code=0\n")
        self.assertEqual(GATE.certificate_report_findings(good, fields), [])
        for stderr, code in ((good.replace("unproved_steps=0", "unproved_steps=1").replace("trust_free=yes",
                                                                                          "trust_free=no"),
                              "ay-unproved-steps"),
                             (good.replace("unproved_steps=0 ", ""), "ay-unproved-steps"),
                             (good.replace("foreign_assumes=no", "foreign_assumes=yes"), "ay-proof-not-trust-free"),
                             ("c ay.session.end exit.code=0\n", "ay-unproved-steps"),
                             (good + good, "ay-unproved-steps")):
            with self.subTest(stderr=stderr):
                self.assertEqual([code for code, _ in GATE.certificate_report_findings(stderr, fields)], [code])

    def test_unchecked_rules_are_seen(self):
        rules = ["hole", "lia_generic"]
        self.assertEqual(GATE.unchecked_rules_in("(step t1 (cl (= a b)) :rule hole)\n", rules), ["hole"])
        self.assertEqual(GATE.unchecked_rules_in("(step t1 (cl (<= a b)) :rule lia_generic)\n", rules),
                         ["lia_generic"])
        self.assertEqual(GATE.unchecked_rules_in("(step t1 (cl (= a b)) :rule bitblast_bvxor)\n; hole\n", rules), [])
        self.assertEqual(GATE.unchecked_rules_in("(step t1 (cl) :rule lia_generic_extra)\n", rules), [])
        self.assertTrue(GATE.proof_has_hole("(step t1 (cl (= a b)) :rule hole)\n"))

    def test_the_rules_placeholders_are_filled(self):
        rule = GATE.read_certificate_rule({"certificate_rule": rule_block()})
        self.assertEqual(GATE.fill(rule["ay_args"], query="Q", proof="P"),
                         ["-smt2", "Q", "--strict-proofs", "--proof", "P", "--proof-format", "alethe"])
        self.assertEqual(GATE.fill(rule["clean_args"], certificate="C"), ["cert", "verify-external", "C", "--verbose"])


FAKE_AY = """{launcher}
import sys
from pathlib import Path
mode = Path({mode!r}).read_text().strip()
args = sys.argv[1:]
assert "--strict-proofs" in args, args
proof = Path(args[args.index("--proof") + 1])
query = Path(args[args.index("-smt2") + 1]).read_text()
if mode == "sat" or "SAT-ME" in query:
    print("sat"); sys.exit(0)
hole = mode == "hole"
rule = "hole" if hole else ("lia_generic" if mode == "lia" else "refl")
proof.write_text("(assume t0 (not (= a b)))\\n(step t1 (cl (= a b)) :rule " + rule + ")\\n"
                 "(step t2 (cl) :rule resolution :premises (t0 t1))\\n")
print("c ay.proof.certificate path=p unproved_steps=" + ("1" if hole else "0") + " foreign_assumes=no trust_free="
      + ("no" if hole else "yes"), file=sys.stderr)
print("unsat")
"""

FAKE_CLEAN = """{launcher}
import json, sys
from pathlib import Path
mode = Path({mode!r}).read_text().strip()
certificate = json.loads(Path(sys.argv[3]).read_text())
assert sys.argv[1:3] == ["cert", "verify-external"] and sys.argv[4] == "--verbose", sys.argv
if mode == "reject" or ":rule hole" in certificate["proof"]:
    print("External certificate verification: FAILED")
    print("Error: proof_verification_failed: Alethe proof was accepted only as holey or incomplete")
    sys.exit(1)
if mode == "quiet":
    print("External certificate verification: PASSED")
    sys.exit(0)
if mode == "lying-exit":
    print("External certificate verification: PASSED\\nType: Alethe SMT proof\\nProof status: fully verified")
    sys.exit(1)
print("External certificate verification: PASSED\\nType: Alethe SMT proof\\nProof status: fully verified")
"""


class GateRunTests(unittest.TestCase):
    """Whole gate runs over a synthetic dump (with the rule block) and fake AY
    and Clean executables obtained through pre-seeded cache slots."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.mode_file = self.base / "mode"
        self.mode("ok")
        self.payload = {name: body.format(launcher=python_launcher(), mode=str(self.mode_file)).encode()
                        for name, body in (("ay", FAKE_AY), ("clean", FAKE_CLEAN))}
        self.digest = {name: hashlib.sha256(body).hexdigest() for name, body in self.payload.items()}
        self.queries = self.base / "queries"
        self.queries.mkdir()
        self.manifest = synthetic_dump(self.queries, rule_block((self.digest["ay"],), (self.digest["clean"],)))
        self.rule = GATE.read_certificate_rule(self.manifest)
        self.ay_cache = self.base / "cache" / "ay-cli"
        self.clean_cache = self.base / "cache" / "clean-cli"
        seed_slot(self.ay_cache, self.rule["ay"], self.payload["ay"], f"ay 0.27.0+build.0.{AY}@fixture")
        seed_slot(self.clean_cache, self.rule["clean"], self.payload["clean"], "clean 0.9.0")

    def mode(self, mode: str) -> None:
        self.mode_file.write_text(mode)

    def rewrite_manifest(self) -> None:
        (self.queries / "manifest.json").write_text(json.dumps(self.manifest))

    def run_gate(self, *flags: str, lock_ay: str = AY, supplied: bool = False):
        """A gate run whose dump is regenerated (the example's run replaced by
        a copy of the synthetic dump), or with `supplied`, named by
        `--queries`."""
        argv = ["--cache-dir", str(self.ay_cache), "--clean-cache-dir", str(self.clean_cache), "--ay-source",
                str(self.base / "no-ay"), "--clean-source", str(self.base / "no-clean"), "--jobs", "2", *flags]
        if supplied:
            argv = ["--queries", str(self.queries), *argv]

        def regenerate(out: Path) -> None:
            self.assertFalse(supplied, "a supplied dump must not be regenerated")
            shutil.copytree(self.queries, out)
        with mock.patch.object(GATE, "lock_pins", return_value={"trust_ir_rev": IR, "ay_rev": lock_ay}), \
                mock.patch.object(GATE, "resolve_targo", return_value=Path("/fixture/targo")), \
                mock.patch.object(GATE, "dump_queries", side_effect=regenerate), \
                contextlib.redirect_stdout(io.StringIO()):
            return GATE.run_gate(self._args(argv))

    @staticmethod
    def _args(argv):
        captured = {}

        def fake_run_gate(args):
            captured["args"] = args
            return 0, {}
        with mock.patch.object(GATE, "run_gate", side_effect=fake_run_gate):
            GATE.main(argv)
        return captured["args"]

    def codes(self, report) -> list[str]:
        return sorted({finding["code"] for finding in report["findings"]})

    def test_a_certified_dump_passes_and_reports_the_certifying_bytes(self):
        code, report = self.run_gate()
        self.assertEqual(code, GATE.EXIT_PASS, report["findings"])
        self.assertEqual(report["queries"], {"source": "regenerated"})
        self.assertEqual(len(report["cells"]), 4)
        self.assertEqual(report["instruction_model_cells"], 2)
        self.assertEqual((report["ay"]["certifying_bytes"], report["clean"]["certifying_bytes"]), (True, True))
        self.assertEqual((report["ay"]["cache"], report["clean"]["cache"]), ("warm", "warm"))
        self.assertEqual(report["rule"]["clean"]["rev"], CLEAN_REV)
        self.assertEqual({row["clean_exit"] for row in report["cells"]}, {0})

    def test_other_bytes_of_the_rules_revisions_pass_and_say_so(self):
        self.manifest["certificate_rule"]["clean"]["certifying_sha256"] = ["0" * 64]
        self.rewrite_manifest()
        code, report = self.run_gate()
        self.assertEqual(code, GATE.EXIT_PASS, report["findings"])
        self.assertEqual((report["ay"]["certifying_bytes"], report["clean"]["certifying_bytes"]), (True, False))

    def test_keep_work_keeps_the_proofs_and_certificates(self):
        kept = self.base / "kept"
        code, report = self.run_gate("--keep-work", str(kept))
        self.assertEqual(code, GATE.EXIT_PASS, report["findings"])
        self.assertEqual(len(list(kept.glob("*.alethe"))), len(report["cells"]))
        self.assertEqual(len(list(kept.glob("*.cert.json"))), len(report["cells"]))

    def test_a_changed_query_is_named_and_not_solved(self):
        (self.queries / "V16I8_Ult.smt2").write_text(cert_query("respelled"))
        code, report = self.run_gate()
        self.assertEqual(code, GATE.EXIT_FAIL)
        self.assertEqual(self.codes(report), ["query-digest-mismatch"])

    def test_a_holey_proof_is_named_by_ay_the_proof_and_clean(self):
        self.mode("hole")
        code, report = self.run_gate()
        self.assertEqual(code, GATE.EXIT_FAIL)
        self.assertEqual(self.codes(report), ["ay-unproved-steps", "clean-not-fully-verified", "proof-hole"])

    def test_an_unchecked_rule_the_rule_names_is_refused(self):
        self.mode("lia")
        code, report = self.run_gate()
        self.assertEqual(code, GATE.EXIT_FAIL)
        self.assertEqual(self.codes(report), ["proof-unchecked-rule"])

    def test_a_non_unsat_answer_is_named(self):
        self.mode("sat")
        code, report = self.run_gate()
        self.assertEqual(code, GATE.EXIT_FAIL)
        self.assertEqual(self.codes(report), ["ay-not-unsat"])

    def test_a_clean_rejection_is_named(self):
        self.mode("reject")
        code, report = self.run_gate()
        self.assertEqual(code, GATE.EXIT_FAIL)
        self.assertEqual(self.codes(report), ["clean-not-fully-verified"])
        self.assertEqual({row["clean_exit"] for row in report["cells"]}, {1})

    def test_a_clean_nonzero_exit_is_the_verdict_whatever_it_prints(self):
        """Clean's exit status is the verdict: a run that prints PASSED and
        `Proof status: fully verified` but exits 1 is refused."""
        self.mode("lying-exit")
        code, report = self.run_gate()
        self.assertEqual(code, GATE.EXIT_FAIL)
        self.assertEqual(self.codes(report), ["clean-not-fully-verified"])
        self.assertEqual({row["clean_exit"] for row in report["cells"]}, {1})

    def test_a_tool_whose_bytes_change_during_the_run_is_named(self):
        certify = GATE.certify_cell
        binary = self.clean_cache / self.rule["clean"].cache_key / "clean"

        def certify_then_change_clean(*args, **kwargs):
            row = certify(*args, **kwargs)
            os.chmod(binary, 0o700)
            with open(binary, "ab") as handle:
                handle.write(b"\n# changed while the gate ran\n")
            return row
        with mock.patch.object(GATE, "certify_cell", side_effect=certify_then_change_clean):
            code, report = self.run_gate()
        self.assertEqual(code, GATE.EXIT_FAIL)
        self.assertEqual(self.codes(report), ["tool-changed-during-run"])

    def test_a_supplied_dump_is_re_run_but_never_passes(self):
        """The reviewer's probe: a supplied dump whose rule is weakened (no
        `lia_generic`, one report field) and whose build string is forged
        re-runs clean, and is still not a PASS: its rule is the dump's."""
        rule = self.manifest["certificate_rule"]
        rule["unchecked_proof_rules"] = ["hole"]
        rule["ay_certificate_report"] = [["unproved_steps", "0"]]
        self.manifest["trust_ir_build"] = "forged-not-compiled"
        self.rewrite_manifest()
        code, report = self.run_gate(supplied=True)
        self.assertEqual(code, GATE.EXIT_SUPPLIED, report["findings"])
        self.assertNotEqual(code, GATE.EXIT_PASS)
        self.assertEqual(report["queries"], {"source": "supplied", "path": str(self.queries)})
        self.assertEqual(report["findings"], [])
        self.assertEqual(len(report["cells"]), 4)

    def test_a_supplied_dump_still_fails_on_a_finding(self):
        (self.queries / "V16I8_Ult.smt2").write_text(cert_query("respelled"))
        code, report = self.run_gate(supplied=True)
        self.assertEqual(code, GATE.EXIT_FAIL)
        self.assertEqual(self.codes(report), ["query-digest-mismatch"])

    def test_tools_path_refuses_a_supplied_dump(self):
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
            GATE.main(["tools-path", "--queries", str(self.queries)])
        self.assertEqual(raised.exception.code, GATE.EXIT_USAGE)

    def test_a_clean_exit_zero_without_the_status_line_is_named(self):
        self.mode("quiet")
        code, report = self.run_gate()
        self.assertEqual(code, GATE.EXIT_FAIL)
        self.assertEqual(self.codes(report), ["clean-not-fully-verified"])

    def test_the_lock_ay_must_be_the_rules(self):
        code, report = self.run_gate(lock_ay=OTHER)
        self.assertEqual(code, GATE.EXIT_FAIL)
        self.assertEqual(self.codes(report), ["ay-pin-differs-from-rule"])

    def test_a_malformed_rule_fails_before_any_tool_runs(self):
        del self.manifest["certificate_rule"]["clean_proof_status"]
        self.rewrite_manifest()
        code, report = self.run_gate()
        self.assertEqual(code, GATE.EXIT_FAIL)
        self.assertEqual(self.codes(report), ["rule-unreadable"])
        self.assertNotIn("ay", report)

    def test_a_dump_of_another_schema_is_refused_before_any_tool_runs(self):
        self.manifest["schema"] = "trust-cg.x86-icmp-cell-queries.v1"
        self.rewrite_manifest()
        code, report = self.run_gate()
        self.assertEqual(code, GATE.EXIT_FAIL)
        self.assertEqual(self.codes(report), ["queries-manifest-unreadable"])
        self.assertNotIn("rule", report)
        self.assertNotIn("ay", report)

    def test_a_missing_input_fails_unless_explicitly_skipped(self):
        for slot in self.clean_cache.iterdir():
            if slot.is_dir():
                for entry in slot.iterdir():
                    os.chmod(entry, 0o600)
                    entry.unlink()
                slot.rmdir()
        code, report = self.run_gate()
        self.assertEqual(code, GATE.EXIT_FAIL)
        self.assertEqual(self.codes(report), ["toolchain-input-missing"])
        code, report = self.run_gate("--skip-missing-toolchain")
        self.assertEqual(code, GATE.EXIT_SKIPPED)
        self.assertEqual([item["code"] for item in report["missing"]], ["clean-source-missing"])
        self.assertEqual(report["cells"], [])

    def test_the_skip_never_covers_a_tampered_tool(self):
        binary = self.clean_cache / self.rule["clean"].cache_key / "clean"
        os.chmod(binary, 0o700)
        binary.write_bytes(self.payload["clean"] + b"\n# one more byte\n")
        code, report = self.run_gate("--skip-missing-toolchain")
        self.assertEqual(code, GATE.EXIT_FAIL)
        self.assertEqual(self.codes(report), ["clean-cache-tampered"])
        self.assertEqual(report["missing"], [])

    def test_an_unknown_ground_is_refused(self):
        changed = copy.deepcopy(self.manifest)
        cell(changed, "V4I32", "Ne")["ground"] = "kernel-certificate"
        (self.queries / "manifest.json").write_text(json.dumps(changed))
        code, report = self.run_gate()
        self.assertEqual(code, GATE.EXIT_FAIL)
        # The cell rests on no ground, so its pin names no certificate cell.
        self.assertEqual(self.codes(report), ["ground-unknown", "pin-unused"])


class ProcessSupervisionTests(unittest.TestCase):
    def with_child_listing(self, listing):
        class Library:
            proc_listchildpids = staticmethod(listing)
        return mock.patch.object(ctypes, "CDLL", return_value=Library())

    def test_darwin_listing_returns_pid_count_not_byte_count(self):
        def listing(pid, buffer, size):
            self.assertEqual(pid, 42)
            self.assertEqual(size, ctypes.sizeof(buffer))
            buffer[0], buffer[1] = 43, 44
            return 2
        with self.with_child_listing(listing):
            self.assertEqual(GATE.darwin_child_pids(42), [43, 44])

    def test_darwin_listing_retries_a_full_buffer(self):
        capacities = []
        def listing(pid, buffer, size):
            capacities.append(len(buffer))
            if len(buffer) == 128:
                return 128
            buffer[0] = 43
            return 1
        with self.with_child_listing(listing):
            self.assertEqual(GATE.darwin_child_pids(42), [43])
        self.assertEqual(capacities, [128, 256])

    def test_darwin_listing_refusal_is_not_an_empty_tree(self):
        def listing(pid, buffer, size):
            ctypes.set_errno(errno.EPERM)
            return 0
        with self.with_child_listing(listing), self.assertRaises(PermissionError):
            GATE.darwin_child_pids(42)

    def test_a_listing_that_never_fits_is_bounded(self):
        def listing(pid, buffer, size):
            return len(buffer)
        with self.with_child_listing(listing), self.assertRaises(OSError) as raised:
            GATE.darwin_child_pids(42)
        self.assertEqual(raised.exception.errno, errno.EOVERFLOW)

    def test_a_parent_that_exited_has_no_remaining_children(self):
        def listing(pid, buffer, size):
            ctypes.set_errno(errno.ESRCH)
            return 0
        with self.with_child_listing(listing):
            self.assertEqual(GATE.darwin_child_pids(42), [])

    def test_native_walk_reaches_grandchildren_once(self):
        children = {42: [43, 44], 43: [45], 44: [], 45: [42]}
        with mock.patch.object(sys, "platform", "darwin"), \
                mock.patch.object(GATE, "darwin_child_pids", side_effect=children.__getitem__):
            self.assertEqual(GATE.descendants(42), [43, 44, 45])

    def test_unavailable_supervision_refuses_before_launch(self):
        for error in (PermissionError("refused"), subprocess.CalledProcessError(1, ["ps"])):
            with self.subTest(error=error), \
                    mock.patch.object(GATE, "descendants", side_effect=error), \
                    mock.patch.object(GATE.subprocess, "Popen") as launch, \
                    self.assertRaises(GATE.Finding) as raised:
                GATE.run_admitted_build(["fixture"], Path.cwd(), {}, None, 1)
            self.assertEqual(raised.exception.code, "process-supervision-unavailable")
            launch.assert_not_called()


if __name__ == "__main__":
    unittest.main()
