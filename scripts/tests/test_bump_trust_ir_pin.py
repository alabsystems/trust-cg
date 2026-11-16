#!/usr/bin/env python3
"""Synthetic authority/rollback controls; no real remote or compiler is invoked."""

from __future__ import annotations

import ast
from contextlib import redirect_stderr, redirect_stdout
import fcntl
import io
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import unittest
import zlib
from unittest.mock import Mock, patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import bump_trust_ir_pin as bump  # noqa: E402


OLD_IR, NEW_IR = "1" * 40, "2" * 40
OLD_CLEAN, NEW_CLEAN, AY = "3" * 40, "4" * 40, "5" * 40
NEW_AY = "6" * 40
TRUST_IR_CURRENT, TRUST_IR_TARGET = bump.IR_VERSION_MIGRATION
TRUST_IR_UNSUPPORTED = "0.16.0"
CLEAN_CURRENT, CLEAN_TARGET = bump.CLEAN_VERSION_MIGRATION
CLEAN_UNSUPPORTED = "0.9.3"
# A synthetic vendored container fixture tree (relative to VENDORED_FIXTURES).
VENDORED = ("SOURCE.txt", "conformance/b1_scalars.tmbc", "conformance/b1_scalars.json",
            "pinned_writer/crystal_lane_v49.tmbc")
# Frontend steps: metadata/update per lock (0-5), locked metadata (6-8), then
# the eight guards in run order (9-16); the must-refuse corpus guard is last.
GUARD_STEPS = {("trust-cg-test", "dependency_authority"): 9,
               ("trust-cg-verify", "fsym_layout"): 10,
               ("trust-cg-verify", "fsym_ub_map"): 11,
               ("trust-cg-lower", "trust_ir_construct_inventory"): 12,
               ("trust-cg-codegen", "trust_ir_corpus_roundtrip"): 13,
               ("trust-cg-codegen", "trust_ir_binary_container"): 14,
               ("trust-cg-cli", "trust_ir_binary_container"): 15,
               ("trust-cg-codegen", "must_refuse_corpus"): 16}
FRONTEND_STEPS = 17


def dep(url: str, revision: str, version: str = "") -> str:
    version_field = f'version = "{version}", ' if version else ""
    return f'{{ {version_field}git = "{url}", rev = "{revision}" }}'


def package(name: str, version: str, identity: str = "", dependencies=()) -> str:
    text = f'\n[[package]]\nname = "{name}"\nversion = "{version}"\n'
    if identity:
        text += f'source = "{identity}"\n'
    if dependencies:
        text += "dependencies = [" + ", ".join(f'"{item}"' for item in dependencies) + "]\n"
    return text


def immutable_documents() -> dict[tuple[str, str], str]:
    docs = {
        (bump.IR_URL, "Cargo.toml"): f'[workspace.package]\nversion = "{TRUST_IR_CURRENT}"\n',
        (bump.CLEAN_URL, "Cargo.toml"): f'[workspace.package]\nversion = "{CLEAN_CURRENT}"\n'
        '[workspace.dependencies]\n' + "\n".join(
            f'{name} = {dep(bump.AY_URL, AY, "0.26.0")}'
            for name in ["ay", "ay-core", "ay-dpll", "ay-proof", "ay-frontend",
                         "ay-translate", "ay-lean-bridge"]),
    }
    for name in ["trust-ir", "trust-ir-build", "trust-ir-giveback", "trust-ir-conformance",
                 "clean-kernel", "clean-olean"]:
        url = bump.CLEAN_URL if name in ("clean-kernel", "clean-olean") else bump.IR_URL
        text = f'[package]\nname = "{name}"\nversion.workspace = true\n'
        if name in ["trust-ir", "trust-ir-build"]:
            text += '\n[dependencies]\nclean-kernel = ' + dep(bump.CLEAN_URL, NEW_CLEAN, CLEAN_CURRENT)
        if name == "trust-ir-build":
            text += '\n[dev-dependencies]\nclean-verify = ' + dep(bump.CLEAN_URL, NEW_CLEAN, CLEAN_CURRENT)
        docs[url, f"crates/{name}/Cargo.toml"] = text
    return docs


def blob_oid(data):
    return bump.hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


class SyntheticCommands(bump.Commands):
    """Route the actual command-building code through an exact synthetic census."""

    def __init__(self, root: Path):
        self.root = root
        self.git = "/synthetic/bin/git"
        self.agh = "/synthetic/bin/agh"
        self.targo = root / "tools" / "targo"
        self.calls = []
        self.documents = immutable_documents()
        self.tree_entries = {}
        self.fetched = {}
        self.dirty = ""
        self.status_reads = 0
        self.fail_step = None
        self.frontend_count = 0
        self.interruption = None
        self.mutate = None
        self.wrong_fetch = False
        self.fail_agh = False
        self.rewrite = ""
        self.preinstall_change = False
        self.ay_revision = AY
        self.ay_version_move = None
        self.clean_version_move = None
        self.ir_version_move = None
        self.guard_environments = []

    def _test_guard_transport(self, args):
        return "legacy"

    def run(self, argv, *, cwd, capture=False, git=False, allowed=(0,), discard_stdout=False, raw=False,
            env=None):
        self.calls.append((list(argv), Path(cwd), capture, git, allowed))
        if argv[0] == self.agh:
            if self.fail_agh:
                raise bump.Refusal("synthetic Agh operation refused")
            if argv[1] == "cat":
                if not raw or not capture or not git:
                    raise AssertionError("authority transport must preserve raw bytes")
                repository, selected = argv[2].split("@", 1)
                revision, relative = selected.split(":", 1)
                url, fetched = self.fetched[Path(cwd)]
                if repository != url.removeprefix("https://github.com/").removesuffix(".git") or revision != fetched:
                    raise AssertionError("blob read must name exact routed authority")
                return self.documents[url, relative].encode()
            if (len(argv) != 6 or argv[1:3] != ["repo", "fetch-main"]
                    or argv[4] != str(cwd) or argv[5] != "--blobless"):
                raise AssertionError(f"unexpected Agh authority operation: {argv}")
            url = "https://github.com/" + argv[3] + ".git"
            revision = {bump.IR_URL: NEW_IR, bump.CLEAN_URL: NEW_CLEAN,
                        bump.AY_URL: self.ay_revision}[url]
            self.fetched[Path(cwd)] = url, revision
            return ""
        if argv[0] == self.git:
            return self.git_command(argv[1:], Path(cwd))
        if argv[0] != str(self.targo):
            raise AssertionError(f"unexpected executable, including stock fallback: {argv}")
        args = argv[1:]
        step = self.frontend_count
        self.frontend_count += 1
        if args[0] in ("metadata", "update"):
            manifest = Path(args[args.index("--manifest-path") + 1])
            lock = manifest.with_name("Cargo.lock")
            if "--locked" not in args:
                data = lock.read_text().replace(OLD_IR, NEW_IR).replace(OLD_CLEAN, NEW_CLEAN).replace(AY, self.ay_revision)
                if self.ir_version_move is not None:
                    previous, following = self.ir_version_move
                    blocks = data.split("[[package]]")
                    for index, block in enumerate(blocks[1:], 1):
                        if f'source = "git+{bump.IR_URL}?' in block:
                            blocks[index] = block.replace(f'version = "{previous}"',
                                                          f'version = "{following}"')
                    data = "[[package]]".join(blocks)
                    for name in ("trust-ir", "trust-ir-build", "trust-ir-giveback", "trust-ir-conformance"):
                        data = data.replace(f'"{name} {previous} (git+{bump.IR_URL}',
                                            f'"{name} {following} (git+{bump.IR_URL}')
                if self.ay_version_move is not None:
                    previous, following = self.ay_version_move
                    data = data.replace('version = "' + previous + '"', 'version = "' + following + '"')
                if self.clean_version_move is not None:
                    previous, following = self.clean_version_move
                    blocks = data.split("[[package]]")
                    for index, block in enumerate(blocks[1:], 1):
                        if f'source = "git+{bump.CLEAN_URL}?' in block:
                            blocks[index] = block.replace(f'version = "{previous}"',
                                                          f'version = "{following}"')
                    data = "[[package]]".join(blocks)
                    for name in ("clean-kernel", "clean-olean", "clean-verify"):
                        data = data.replace(f'"{name} {previous} (git+{bump.CLEAN_URL}',
                                            f'"{name} {following} (git+{bump.CLEAN_URL}')
                lock.write_text(data)
        elif args[:2] != ["--unverified", "test"]:
            raise AssertionError(f"unsupported frontend lane: {args}")
        if self.mutate is not None:
            self.mutate(step, self.root)
        if step == self.fail_step:
            if self.interruption is not None:
                raise self.interruption
            raise bump.Refusal(f"synthetic frontend failure at {step}")
        if args[:2] == ["--unverified", "test"]:
            self.guard_environments.append(dict(env or {}))
            names = bump.GUARD_TEST_NAMES[args[args.index("-p") + 1], args[args.index("--test") + 1]]
            return (f"running {len(names)} tests\n"
                    + "".join(f"test {name} ... ok\n" for name in names)
                    + f"test result: ok. {len(names)} passed; 0 failed; 0 ignored; "
                    "0 measured; 0 filtered out; finished in 0.01s\n")
        return ""

    def git_command(self, args, cwd):
        if args[:1] == ["ls-files"]:
            return "\n".join(bump.OWNED)
        if args[:1] == ["status"]:
            self.status_reads += 1
            if self.preinstall_change and self.status_reads == 2:
                (self.root / bump.CACHE).write_text("concurrent source edit")
            return self.dirty
        if args == ["rev-parse", "--git-path", "compiler-pin-transaction.lock"]:
            return str(self.root / "git-private" / "compiler-pin-transaction.lock")
        if args == ["init", "--bare", "--quiet", "--template=", "--object-format=sha1"]:
            if cwd == self.root:
                raise AssertionError("authority fetch must not mutate the consumer Git repository")
            return ""
        if args[:2] == ["config", "--get-regexp"]:
            return self.rewrite
        if "fetch" in args:
            raise AssertionError("GitHub authority fetch bypassed Agh")
        if args[:2] == ["rev-parse", "--verify"]:
            return "f" * 40 if self.wrong_fetch else self.fetched[cwd][1]
        if args[:2] == ["merge-base", "--is-ancestor"]:
            if args[2:] != [self.fetched[cwd][1], "refs/agh/fetched-main"]:
                raise bump.Refusal("requested revision is not on routed main")
            return ""
        if args[:2] == ["ls-tree", "-z"]:
            url, fetched = self.fetched[cwd]
            if len(args) != 5 or args[2] != fetched or args[3] != "--":
                raise AssertionError("tree admission must name exact immutable path")
            relative = args[4]
            return self.tree_entries.get((url, relative),
                f"100644 blob {blob_oid(self.documents[url, relative].encode())}\t{relative}\0" if (url, relative) in self.documents else "")
        if args[:1] == ["show"]:
            revision, relative = args[1].split(":", 1)
            url, fetched = self.fetched[cwd]
            if revision != fetched:
                raise AssertionError("manifest read must name the fetched immutable commit")
            try:
                return self.documents[url, relative]
            except KeyError as error:
                raise bump.Refusal("synthetic immutable manifest missing") from error
        raise AssertionError(f"unexpected Git operation: {args}")


class TransactionTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="test-compiler-pin-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        (self.root / "git-private").mkdir()
        self.write("Cargo.toml", '[workspace.package]\nversion = "0.6.0"\n'
                   '[workspace.dependencies]\n'
                   f'trust-ir = {dep(bump.IR_URL, OLD_IR)}\n'
                   f'trust-ir-build = {dep(bump.IR_URL, OLD_IR)}\n'
                   f'trust-ir-conformance = {dep(bump.IR_URL, OLD_IR)[:-1]}, '
                   'default-features = false, features = ["must-refuse"] }\n'
                   '# unrelated bytes stay put\n')
        self.write(bump.MANIFESTS[1], '[package]\nname = "bridge"\nversion = "0.1.0"\n'
                   '[dependencies]\n' + f'trust-ir = {dep(bump.IR_URL, OLD_IR)}\n'
                   '[dev-dependencies]\n' + f'trust-ir-build = {dep(bump.IR_URL, OLD_IR)}\n')
        self.write(bump.VERIFY, '[features]\noriginal-i128-cic = ["dep:clean-kernel", "dep:clean-olean"]\ncore-byte-replay = ["dep:clean-kernel", "dep:clean-verify", "dep:trust-ir-build"]\n'
                   '[dependencies]\n' + '\n'.join(
                       f'{name} = {dep(bump.CLEAN_URL, OLD_CLEAN, CLEAN_CURRENT)[:-1]}, optional = true }}'
                       for name in ("clean-kernel", "clean-verify")) + '\n'
                   + f'clean-olean = {dep(bump.CLEAN_URL, OLD_CLEAN, CLEAN_CURRENT)[:-1]}, optional = true, default-features = false }}\n')
        self.write(bump.REGALLOC, '[features]\ndefault = []\n'
                   'ay-regalloc = ["dep:ay-pb", "dep:ay-sat", "dep:trust-cg-process-env"]\n'
                   '[dependencies]\n'
                   f'ay-pb = {dep(bump.AY_URL, AY, "0.26.0")[:-1]}, optional = true, default-features = false }}\n'
                   f'ay-sat = {dep(bump.AY_URL, AY, "0.26.0")[:-1]}, optional = true, default-features = false, features = ["raw-pointer-bcp"] }}\n')
        self.write(bump.CACHE, '// an unrelated cache constant\n'
                   f'pub const {bump.CACHE_NAME}: &str =\n    "trust_ir:{OLD_IR}";\n'
                   f'pub const {bump.AY_CACHE_NAME}: &str =\n    "ay:{AY}";\n')
        self.write(bump.GUARD, "// independent Rust authority guard remains unchanged\n")
        self.write(bump.CORPUS_GUARD, "// must-refuse corpus guard remains unchanged\n")
        for relative, _, _ in bump.INVENTORY_GUARDS:
            self.write(relative, "// TrustIR-derived inventory guard remains unchanged\n")
        for relative, _, _, _ in bump.FIXTURE_GUARDS:
            self.write(relative, f"// conformance fixture guard {relative} remains unchanged\n")
        for relative in VENDORED:
            self.write(f"{bump.VENDORED_FIXTURES}/{relative}", f"vendored {relative}\n")
        self.write("SOUNDNESS_CHECK.md", "untouched gate documentation\n")
        self.write("publish/DECISIONS.md", "untouched publication boundary\n")
        self.write("unrelated-user-work.txt", "unrelated dirty user work\n")
        for lock in bump.LOCKS:
            text = "# retain this original lock comment on rollback\nversion = 4\n"
            for name in ["trust-ir", "trust-ir-build", "trust-ir-giveback"]:
                text += package(name, TRUST_IR_CURRENT, bump.source(bump.IR_URL, OLD_IR))
            if lock == "Cargo.lock":
                # The corpus runner is a dev-dependency of the root workspace only.
                text += package("trust-ir-conformance", TRUST_IR_CURRENT,
                                bump.source(bump.IR_URL, OLD_IR))
            for name in ("clean-kernel", "clean-olean"):
                text += package(name, CLEAN_CURRENT, bump.source(bump.CLEAN_URL, OLD_CLEAN))
            if lock != "fuzz/Cargo.lock":
                for name in ["ay-pb", "ay-sat"]:
                    text += package(name, "0.26.0", bump.source(bump.AY_URL, AY))
            text += package("third-party", "1.0.0", "registry+https://example.invalid/index")
            text += package("consumer", "0.6.0", dependencies=["trust-ir"])
            self.write(lock, text)
            (self.root / lock).chmod(0o640)
        self.commands = SyntheticCommands(self.root)
        self.original = bump.snapshot(self.root)
        self.output = io.StringIO()

    def write(self, relative, text):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def invoke(self, ay_revision=None, admit=(), admit_ay=(), drop=(), ay_version=None,
               clean_version=None, ir_version=None):
        with redirect_stdout(self.output), redirect_stderr(self.output):
            bump.transaction(self.root, NEW_IR, self.commands, ay_revision, admit, admit_ay, drop, ay_version,
                             clean_version=clean_version,
                             ir_version=ir_version)

    def assert_restored(self):
        self.assertEqual(bump.snapshot(self.root), self.original)
        self.assertEqual((self.root / "SOUNDNESS_CHECK.md").read_text(), "untouched gate documentation\n")
        self.assertEqual((self.root / "publish/DECISIONS.md").read_text(), "untouched publication boundary\n")
        self.assertEqual((self.root / "unrelated-user-work.txt").read_text(), "unrelated dirty user work\n")

    def coordinated(self):
        self.commands = SyntheticCommands(self.root)
        self.commands.ay_revision = NEW_AY
        docs = self.commands.documents
        docs[bump.CLEAN_URL, "Cargo.toml"] = docs[bump.CLEAN_URL, "Cargo.toml"].replace(AY, NEW_AY)
        docs[bump.IR_URL, "crates/trust-ir-ay/Cargo.toml"] = '[dependencies]\n' + '\n'.join(
            f'{name} = {dep(bump.AY_URL, NEW_AY, "0.26.0")}' for name in ("ay", "ay-proof"))
        # Deliberately nested paths: package names are not directory names.
        docs[bump.AY_URL, "Cargo.toml"] = ('[workspace]\nmembers = ["solver/pb", "solver/sat"]\n'
                                                   '[workspace.package]\nversion = "0.26.0"\n')
        for name, path in (("ay-pb", "solver/pb"), ("ay-sat", "solver/sat")):
            docs[bump.AY_URL, path + "/Cargo.toml"] = f'[package]\nname = "{name}"\nversion.workspace = true\n'

    def trust_ir_version_migration(self):
        key = bump.IR_URL, "Cargo.toml"
        self.commands.documents[key] = self.commands.documents[key].replace(
            TRUST_IR_CURRENT, TRUST_IR_TARGET)
        self.commands.ir_version_move = bump.IR_VERSION_MIGRATION

    def test_explicit_trust_ir_minor_move_preserves_roster_edges_and_runs_all_guards(self):
        self.trust_ir_version_migration()
        old_edge = (f'trust-ir {TRUST_IR_CURRENT} '
                    f'({bump.source(bump.IR_URL, OLD_IR)})')
        for lock in bump.LOCKS:
            path = self.root / lock
            path.write_text(path.read_text().replace(
                'dependencies = ["trust-ir"]',
                f'dependencies = ["{old_edge}"]'))
        self.original = bump.snapshot(self.root)
        self.invoke(ir_version=TRUST_IR_TARGET)
        state = bump.current(self.root, bump.snapshot(self.root))
        self.assertEqual(set(state.ir_packages.values()), {TRUST_IR_TARGET})
        guards = [call for call in self.commands.calls if "--test" in call[0]]
        self.assertEqual(len(guards), len(bump.GUARD_TEST_NAMES))
        for lock in bump.LOCKS:
            rows = bump.packages((self.root / lock).read_bytes(), lock)
            consumer = next(row for row in rows if row["name"] == "consumer")
            self.assertEqual(consumer["dependencies"], [
                f'trust-ir {TRUST_IR_TARGET} ({bump.source(bump.IR_URL, NEW_IR)})'])

    def test_combined_clean_and_trust_ir_version_move_is_one_atomic_transaction(self):
        self.trust_ir_version_migration()
        self.clean_version_migration()
        self.invoke(clean_version=CLEAN_TARGET, ir_version=TRUST_IR_TARGET)
        state = bump.current(self.root, bump.snapshot(self.root))
        self.assertEqual(set(state.ir_packages.values()), {TRUST_IR_TARGET})
        self.assertEqual(set(state.clean_packages.values()), {CLEAN_TARGET})
        guards = [call for call in self.commands.calls if "--test" in call[0]]
        self.assertEqual(len(guards), len(bump.GUARD_TEST_NAMES))

    def clean_version_migration(self):
        self.commands.documents = {
            key: text.replace(CLEAN_CURRENT, CLEAN_TARGET)
            for key, text in self.commands.documents.items()}
        self.commands.clean_version_move = bump.CLEAN_VERSION_MIGRATION

    def test_explicit_clean_patch_move_runs_all_original_named_guards(self):
        self.clean_version_migration()
        self.invoke(clean_version=CLEAN_TARGET)
        state = bump.current(self.root, bump.snapshot(self.root))
        self.assertEqual(set(state.clean_packages.values()), {CLEAN_TARGET})
        self.assertEqual((state.ir, state.clean, state.ay), (NEW_IR, NEW_CLEAN, AY))
        guards = [call for call in self.commands.calls if "--test" in call[0]]
        self.assertEqual(len(guards), len(bump.GUARD_TEST_NAMES))
        text = (self.root / bump.VERIFY).read_text()
        self.assertEqual(text.count(f'version = "{CLEAN_TARGET}"'), 3)
        self.assertEqual(text.count('optional = true'), 3)
        self.assertIn('default-features = false', text)
        self.assertEqual((self.root / "unrelated-user-work.txt").read_text(), "unrelated dirty user work\n")

    def test_clean_patch_move_preserves_disambiguated_edges_and_registry_versions(self):
        self.clean_version_migration()
        old_edge = f'clean-kernel {CLEAN_CURRENT} ({bump.source(bump.CLEAN_URL, OLD_CLEAN)})'
        for lock in bump.LOCKS:
            path = self.root / lock
            text = path.read_text().replace('dependencies = ["trust-ir"]',
                                            f'dependencies = ["trust-ir", "{old_edge}"]')
            text += package("unchanged-registry-owner", "0.9.0", "registry+https://example.invalid/index")
            path.write_text(text)
        self.invoke(clean_version=CLEAN_TARGET)
        for lock in bump.LOCKS:
            rows = bump.packages((self.root / lock).read_bytes(), lock)
            same_version = next(row for row in rows if row["name"] == "unchanged-registry-owner")
            self.assertEqual(same_version["version"], "0.9.0")
            consumer = next(row for row in rows if row["name"] == "consumer")
            self.assertIn(f'clean-kernel {CLEAN_TARGET} ({bump.source(bump.CLEAN_URL, NEW_CLEAN)})',
                          consumer["dependencies"])

    def test_clean_patch_move_preserves_versionless_exact_revision_requirements(self):
        self.clean_version_migration()
        path = self.root / bump.VERIFY
        path.write_text(path.read_text().replace(f'version = "{CLEAN_CURRENT}", ', ''))
        self.invoke(clean_version=CLEAN_TARGET)
        doc = bump.document(path.read_bytes(), bump.VERIFY)
        for name in ("clean-kernel", "clean-olean", "clean-verify"):
            self.assertNotIn("version", doc["dependencies"][name])
            self.assertEqual(bump.pin(doc["dependencies"][name], bump.CLEAN_URL, name), NEW_CLEAN)
        self.assertEqual(set(bump.current(self.root, bump.snapshot(self.root)).clean_packages.values()),
                         {CLEAN_TARGET})

    def test_wrong_direct_clean_requirement_refuses_before_install(self):
        self.clean_version_migration()
        path = self.root / bump.VERIFY
        path.write_text(path.read_text().replace(f'version = "{CLEAN_CURRENT}"',
                                                f'version = "{CLEAN_UNSUPPORTED}"', 1))
        self.original = bump.snapshot(self.root)
        with self.assertRaisesRegex(bump.Refusal, "locked Clean authority"):
            self.invoke(clean_version=CLEAN_TARGET)
        self.assert_restored()

    def test_clean_move_requires_explicit_review_and_exact_immutable_versions(self):
        for defect in ("missing", "wrong_option", "root", "member", "ir_requirement"):
            with self.subTest(defect=defect):
                self.clean_version_migration()
                clean_version = None if defect == "missing" else CLEAN_TARGET
                if defect == "wrong_option": clean_version = CLEAN_UNSUPPORTED
                docs = self.commands.documents
                if defect == "root":
                    docs[bump.CLEAN_URL, "Cargo.toml"] = docs[bump.CLEAN_URL, "Cargo.toml"].replace(
                        CLEAN_TARGET, CLEAN_UNSUPPORTED)
                if defect == "member":
                    docs[bump.CLEAN_URL, "crates/clean-kernel/Cargo.toml"] = (
                        f'[package]\nname = "clean-kernel"\nversion = "{CLEAN_UNSUPPORTED}"\n')
                if defect == "ir_requirement":
                    key = bump.IR_URL, "crates/trust-ir/Cargo.toml"
                    docs[key] = docs[key].replace(CLEAN_TARGET, CLEAN_UNSUPPORTED)
                with self.assertRaises(bump.Refusal): self.invoke(clean_version=clean_version)
                self.assert_restored()
                self.commands = SyntheticCommands(self.root)

    def test_clean_patch_move_keeps_all_guard_rollbacks_byte_exact(self):
        for step in GUARD_STEPS.values():
            with self.subTest(step=step):
                self.commands = SyntheticCommands(self.root)
                self.clean_version_migration()
                self.commands.fail_step = step
                with self.assertRaises(bump.Refusal): self.invoke(clean_version=CLEAN_TARGET)
                self.assert_restored()

    def test_clean_patch_move_refuses_resolver_version_membership_and_edge_changes(self):
        def corrupt(kind, root):
            path = root / "Cargo.lock"
            text = path.read_text()
            if kind == "version":
                text = text.replace(f'name = "clean-kernel"\nversion = "{CLEAN_TARGET}"',
                                    f'name = "clean-kernel"\nversion = "{CLEAN_UNSUPPORTED}"')
            if kind == "membership":
                text += package("clean-forged", CLEAN_TARGET,
                                bump.source(bump.CLEAN_URL, NEW_CLEAN))
            if kind == "edge": text = text.replace('dependencies = ["trust-ir"]',
                                                     'dependencies = ["clean-kernel"]')
            if kind == "third_party": text = text.replace('version = "1.0.0"', 'version = "1.0.1"')
            path.write_text(text)
        for kind in ("version", "membership", "edge", "third_party"):
            with self.subTest(kind=kind):
                self.commands = SyntheticCommands(self.root)
                self.clean_version_migration()
                self.commands.mutate = lambda step, root: corrupt(kind, root) if step == 5 else None
                with self.assertRaises(bump.Refusal): self.invoke(clean_version=CLEAN_TARGET)
                self.assert_restored()

    def version_migration(self):
        self.coordinated()
        for relative in bump.OWNED:
            path = self.root / relative
            path.write_bytes(path.read_bytes().replace(b"0.26.0", b"0.27.0"))
        self.original = bump.snapshot(self.root)
        self.commands.documents = {
            key: text.replace("0.26.0", "0.28.0")
            for key, text in self.commands.documents.items()}
        self.commands.ay_version_move = ("0.27.0", "0.28.0")

    def test_explicit_version_migration_runs_the_same_complete_named_guards(self):
        self.version_migration()
        self.invoke(NEW_AY, ay_version="0.28.0")
        selected = bump.current(self.root, bump.snapshot(self.root))
        self.assertEqual((selected.ir, selected.clean, selected.ay, selected.ay_version),
                         (NEW_IR, NEW_CLEAN, NEW_AY, "0.28.0"))
        guards = [call for call in self.commands.calls if "--test" in call[0]]
        self.assertEqual(len(guards), len(bump.GUARD_TEST_NAMES))
        regalloc = (self.root / bump.REGALLOC).read_text()
        self.assertEqual(regalloc.count('version = "0.28.0"'), 2)
        self.assertIn('default-features = false', regalloc)
        self.assertIn('features = ["raw-pointer-bcp"]', regalloc)

    def test_version_migration_cannot_be_inferred_from_the_target_revision(self):
        self.version_migration()
        with self.assertRaises(bump.Refusal):
            self.invoke(NEW_AY)
        self.assert_restored()
        self.assertEqual(self.commands.frontend_count, 0)

    def test_explicit_version_migration_requires_every_immutable_coowner_and_member(self):
        for url, path in ((bump.CLEAN_URL, "Cargo.toml"),
                          (bump.IR_URL, "crates/trust-ir-ay/Cargo.toml"),
                          (bump.AY_URL, "Cargo.toml"),
                          (bump.AY_URL, "solver/sat/Cargo.toml")):
            with self.subTest(owner=url, path=path):
                self.version_migration()
                if path == "solver/sat/Cargo.toml":
                    self.commands.documents[url, path] = '[package]\nname = "ay-sat"\nversion = "0.27.0"\n'
                else:
                    self.commands.documents[url, path] = self.commands.documents[url, path].replace(
                        "0.28.0", "0.27.0", 1)
                with self.assertRaises(bump.Refusal):
                    self.invoke(NEW_AY, ay_version="0.28.0")
                self.assert_restored()

    def test_unknown_backward_or_unselected_version_migration_refuses_before_resolver(self):
        for requested, revision in (("0.29.0", NEW_AY), ("0.28", NEW_AY),
                                    ("^0.28.0", NEW_AY), ("0.27.0", NEW_AY),
                                    ("0.28.0", None)):
            with self.subTest(version=requested):
                self.version_migration()
                with self.assertRaises(bump.Refusal):
                    self.invoke(revision, ay_version=requested)
                self.assert_restored()
                self.assertEqual(self.commands.frontend_count, 0)

    def test_version_migration_preserves_non_ay_nodes_and_source_qualified_edges(self):
        self.version_migration()
        state = bump.current(self.root, self.original)
        with tempfile.TemporaryDirectory() as temporary:
            target = bump.target_cohort(self.commands, Path(temporary), state, NEW_IR, NEW_AY,
                                        ay_version="0.28.0")
        before = self.original["Cargo.lock"].data.decode()
        before = before.replace(package("consumer", "0.6.0", dependencies=["trust-ir"]),
            package("consumer", "0.6.0", dependencies=["trust-ir",
                    f"ay-sat 0.27.0 (git+{bump.AY_URL}?rev={AY})"]))
        after = before.replace(OLD_IR, NEW_IR).replace(OLD_CLEAN, NEW_CLEAN).replace(AY, NEW_AY)
        after = after.replace('version = "0.27.0"', 'version = "0.28.0"').replace(
            "ay-sat 0.27.0", "ay-sat 0.28.0")
        bump.validate_graph(before.encode(), after.encode(), "Cargo.lock", state,
                            NEW_IR, NEW_CLEAN, NEW_AY, target.ay)
        changes = (
            after.replace('third-party"\nversion = "1.0.0"', 'third-party"\nversion = "2.0.0"'),
            after.replace('version = "0.28.0"', 'version = "0.27.0"', 1),
            after.replace("ay-sat 0.28.0", "ay-sat 0.27.0"),
            after + package("foreign", "1.0.0", bump.source(bump.AY_URL, NEW_AY)),
        )
        for index, changed in enumerate(changes):
            with self.subTest(mutation=index), self.assertRaises(bump.Refusal):
                bump.validate_graph(before.encode(), changed.encode(), "Cargo.lock", state,
                                    NEW_IR, NEW_CLEAN, NEW_AY, target.ay)

    def test_version_migration_failures_restore_all_original_bytes_and_modes(self):
        for step in (0, 2, 6, 8):
            with self.subTest(step=step):
                self.version_migration()
                self.commands.fail_step = step
                with self.assertRaises(bump.Refusal):
                    self.invoke(NEW_AY, ay_version="0.28.0")
                self.assert_restored()

    def test_explicit_registry_source_gain_keeps_all_other_graph_owners_exact(self):
        from dataclasses import replace
        self.version_migration()
        state = bump.current(self.root, self.original)
        with tempfile.TemporaryDirectory() as temporary:
            target = bump.target_cohort(self.commands, Path(temporary), state, NEW_IR, NEW_AY,
                                       ay_version="0.28.0")
        registry = bump.registry_owner
        checksum = "a" * 64
        captured = registry.Owner(NEW_AY, registry.WAIT_NAME, registry.WAIT_VERSION,
            checksum, {"libc": [{"version": "0.2.56"}]}, frozenset({"libc"}))
        authority = replace(target.ay,
            declarations={**target.ay.declarations, "ay-sys": {
                registry.WAIT_NAME: [{"version": "0.2.1"}]}},
            required={**target.ay.required, "ay-sys": {registry.WAIT_NAME}},
            registry_owners={(registry.WAIT_NAME, registry.WAIT_VERSION): captured})
        old = self.original["Cargo.lock"].data.decode()
        old += package("ay-sys", "0.27.0", bump.source(bump.AY_URL, AY))
        old += package("libc", "0.2.177", bump.REGISTRY)
        new = old.replace(OLD_IR, NEW_IR).replace(OLD_CLEAN, NEW_CLEAN).replace(AY, NEW_AY)
        new = new.replace('version = "0.27.0"', 'version = "0.28.0"')
        new = new.replace(package("ay-sys", "0.28.0", bump.source(bump.AY_URL, NEW_AY)),
            package("ay-sys", "0.28.0", bump.source(bump.AY_URL, NEW_AY), [registry.WAIT_NAME]))
        new += package(registry.WAIT_NAME, registry.WAIT_VERSION, bump.REGISTRY, ["libc"])
        new += f'checksum = "{checksum}"\n'
        check = lambda data, selected: bump.validate_graph(old.encode(), data.encode(),
            "registry gain", state, NEW_IR, NEW_CLEAN, NEW_AY, selected)
        check(new, authority)
        for data, selected in (
            (new, replace(authority, registry_owners=None)),
            (new.replace(checksum, "b" * 64), authority),
            (new.replace('dependencies = ["wait-timeout"]', 'dependencies = []'), authority),
            (new.replace('libc"\nversion = "0.2.177"', 'libc"\nversion = "0.2.178"'), authority),
            (new + package("other", "1.0.0", bump.REGISTRY), authority),
        ):
            with self.subTest(data=data[-160:]), self.assertRaises(bump.Refusal):
                check(data, selected)

    def test_named_registry_source_gain_requires_an_actual_ay_move(self):
        with tempfile.TemporaryDirectory() as temporary, self.assertRaises(bump.Refusal):
            bump.target_cohort(self.commands, Path(temporary),
                bump.current(self.root, self.original), NEW_IR,
                admit_registry=(bump.registry_owner.WAIT_SELECTION,))
        self.assertEqual(self.commands.frontend_count, 0)

    def test_optional_excluded_vendor_declaration_does_not_activate_it(self):
        self.coordinated()
        docs = self.commands.documents
        docs[bump.AY_URL, "Cargo.toml"] = docs[bump.AY_URL, "Cargo.toml"].replace(
            '[workspace]\n', '[workspace]\nexclude = ["vendor/veripb"]\n')
        docs[bump.AY_URL, "solver/pb/Cargo.toml"] += (
            '\n[dependencies]\nveripb = { path = "../../vendor/veripb", optional = true }\n')
        docs[bump.AY_URL, "vendor/veripb/Cargo.toml"] = (
            '[package]\nname = "veripb"\nversion = "1.0.0"\n[workspace]\n')
        self.invoke(NEW_AY)
        for relative in bump.LOCKS:
            self.assertNotIn('name = "veripb"', (self.root / relative).read_text())

    def test_workspace_vendor_template_requires_optional_member_use(self):
        for optional in (True, False):
            with self.subTest(optional=optional):
                self.coordinated()
                docs = self.commands.documents
                docs[bump.AY_URL, "Cargo.toml"] = docs[bump.AY_URL, "Cargo.toml"].replace(
                    '[workspace]\n', '[workspace]\nexclude = ["vendor/veripb"]\n') + (
                    '\n[workspace.dependencies]\nay-veripb = { package = "veripb", path = "vendor/veripb" }\n')
                docs[bump.AY_URL, "solver/pb/Cargo.toml"] += (
                    '\n[dependencies]\nay-veripb = { workspace = true, optional = '
                    + str(optional).lower() + ' }\n')
                docs[bump.AY_URL, "vendor/veripb/Cargo.toml"] = (
                    '[package]\nname = "veripb"\nversion = "1.0.0"\n[workspace]\n')
                if optional:
                    self.invoke(NEW_AY)
                    # Restore the synthetic consumer for the independent required-use case.
                    for relative, saved in self.original.items():
                        (self.root / relative).write_bytes(saved.data)
                else:
                    with self.assertRaises(bump.Refusal):
                        self.invoke(NEW_AY)
                    self.assert_restored()

    def test_non_ay_vendor_activation_under_ay_source_refuses_and_restores(self):
        self.coordinated()
        def activate(step, root):
            if step == 0:
                lock = root / "Cargo.lock"
                lock.write_text(lock.read_text() + package(
                    "veripb", "1.0.0", f"git+{bump.AY_URL}?rev={NEW_AY}#{NEW_AY}"))
        self.commands.mutate = activate
        with self.assertRaises(bump.Refusal):
            self.invoke(NEW_AY)
        self.assert_restored()

    def unselected_required_vendor(self):
        self.coordinated()
        docs = self.commands.documents
        docs[bump.AY_URL, "Cargo.toml"] = docs[bump.AY_URL, "Cargo.toml"].replace(
            '[workspace]\n', '[workspace]\nexclude = ["vendor/veripb"]\n').replace(
            '"solver/pb", "solver/sat"', '"solver/pb", "solver/sat", "solver/cli-core"') + (
            '\n[workspace.dependencies]\nay-veripb = { package = "veripb", path = "vendor/veripb" }\n')
        docs[bump.AY_URL, "solver/cli-core/Cargo.toml"] = (
            '[package]\nname = "ay-cli-core"\nversion.workspace = true\n'
            '[dependencies]\nay-veripb.workspace = true\n')
        docs[bump.AY_URL, "vendor/veripb/Cargo.toml"] = (
            '[package]\nname = "veripb"\nversion = "1.0.0"\n[workspace]\n')

    def test_unselected_member_dependency_discovery_does_not_activate_its_graph(self):
        self.unselected_required_vendor()
        self.invoke(NEW_AY)
        for relative in bump.LOCKS:
            for name in ("ay-cli-core", "veripb"):
                self.assertNotIn('name = "' + name + '"', (self.root / relative).read_text())

    def test_discovered_unselected_vendor_still_cannot_enter_a_locked_graph(self):
        self.unselected_required_vendor()
        def activate(step, root):
            if step == 0:
                lock = root / "Cargo.lock"
                lock.write_text(lock.read_text() + package(
                    "veripb", "1.0.0", bump.source(bump.AY_URL, NEW_AY)))
        self.commands.mutate = activate
        with self.assertRaises(bump.Refusal):
            self.invoke(NEW_AY)
        self.assert_restored()

    def test_explicit_new_member_admission_cannot_borrow_unselected_vendor_discovery(self):
        self.unselected_required_vendor()
        self.commands.documents[bump.AY_URL, "solver/pb/Cargo.toml"] += (
            '\n[dependencies]\nay-cli-core = { path = "../cli-core" }\n')
        with self.assertRaisesRegex(bump.Refusal, "required vendor"):
            self.invoke(NEW_AY, admit_ay=("ay-cli-core",))
        self.assert_restored()
        self.assertEqual(self.commands.frontend_count, 0)

    def selected_dev_vendor(self):
        self.coordinated()
        docs = self.commands.documents
        docs[bump.AY_URL, "Cargo.toml"] = docs[bump.AY_URL, "Cargo.toml"].replace(
            '[workspace]\n', '[workspace]\nexclude = ["vendor/veripb"]\n') + (
            '\n[workspace.dependencies]\nay-veripb = { package = "veripb", path = "vendor/veripb" }\n')
        docs[bump.AY_URL, "solver/pb/Cargo.toml"] += (
            '\n[dev-dependencies]\nay-veripb.workspace = true\n')
        docs[bump.AY_URL, "vendor/veripb/Cargo.toml"] = (
            '[package]\nname = "veripb"\nversion = "1.0.0"\n[workspace]\n')

    def test_selected_dependency_dev_suite_is_discovered_without_graph_admission(self):
        self.selected_dev_vendor()
        self.invoke(NEW_AY)
        for relative in bump.LOCKS:
            self.assertNotIn('name = "veripb"', (self.root / relative).read_text())

    def test_selected_dev_vendor_discovery_cannot_excuse_runtime_or_locked_activation(self):
        for kind in ("runtime", "locked"):
            with self.subTest(kind=kind):
                self.selected_dev_vendor()
                if kind == "runtime":
                    key = bump.AY_URL, "solver/pb/Cargo.toml"
                    self.commands.documents[key] = self.commands.documents[key].replace(
                        '[dev-dependencies]', '[dependencies]')
                else:
                    def activate(step, root):
                        if step == 0:
                            lock = root / "Cargo.lock"
                            lock.write_text(lock.read_text() + package(
                                "veripb", "1.0.0", bump.source(bump.AY_URL, NEW_AY)))
                    self.commands.mutate = activate
                with self.assertRaises(bump.Refusal):
                    self.invoke(NEW_AY)
                self.assert_restored()

    def test_excluded_vendor_requires_optional_owned_literal_identity(self):
        for change in ("required", "unexcluded", "wrong-name", "inherited-version", "alternate"):
            with self.subTest(change=change):
                self.coordinated()
                docs = self.commands.documents
                docs[bump.AY_URL, "Cargo.toml"] = docs[bump.AY_URL, "Cargo.toml"].replace(
                    '[workspace]\n', '[workspace]\nexclude = ["vendor/veripb"]\n'
                    if change != "unexcluded" else '[workspace]\n')
                docs[bump.AY_URL, "solver/pb/Cargo.toml"] += (
                    '\n[dependencies]\nveripb = { path = "../../vendor/veripb", optional = '
                    + ('false' if change == "required" else 'true') + ' }\n')
                docs[bump.AY_URL, "vendor/veripb/Cargo.toml"] = (
                    '[package]\nname = "' + ('foreign' if change == "wrong-name" else 'veripb')
                    + '"\n' + ('version.workspace = true' if change == "inherited-version" else 'version = "1.0.0"') + '\n[workspace]\n')
                if change == "alternate":
                    docs[bump.AY_URL, "vendor/veripb/Targo.toml"] = '[package]\nname = "veripb"\n'
                with self.assertRaises(bump.Refusal):
                    self.invoke(NEW_AY)
                self.assert_restored()

    def test_coordinated_move_binds_eight_files_both_salts_and_exact_authorities(self):
        self.coordinated()
        self.invoke(NEW_AY)
        actual = bump.current(self.root, bump.snapshot(self.root))
        self.assertEqual((actual.ir, actual.clean, actual.ay), (NEW_IR, NEW_CLEAN, NEW_AY))
        self.assertEqual(len(bump.OWNED), 8)
        fetches = list(self.commands.fetched.values())
        self.assertEqual(fetches, [(bump.IR_URL, NEW_IR), (bump.CLEAN_URL, NEW_CLEAN), (bump.AY_URL, NEW_AY)])
        manifest = (self.root / bump.REGALLOC).read_text()
        self.assertEqual(manifest.count(NEW_AY), 2)
        self.assertEqual(manifest.replace(NEW_AY, AY).encode(), self.original[bump.REGALLOC].data)
        cache = (self.root / bump.CACHE).read_text()
        self.assertIn('"ay:' + NEW_AY + '"', cache)
        self.assertNotIn(AY, cache)
        self.assertEqual(self.commands.frontend_count, FRONTEND_STEPS)

    def test_direct_clean_replay_pins_move_atomically_and_preserve_feature_bytes(self):
        self.invoke()
        before = self.original[bump.VERIFY].data
        after = (self.root / bump.VERIFY).read_bytes()
        self.assertEqual(after, before.replace(OLD_CLEAN.encode(), NEW_CLEAN.encode()))
        self.assertEqual(after.count(NEW_CLEAN.encode()), 3)

    def test_direct_clean_pin_drift_and_lost_optionality_refuse_before_mutation(self):
        for old, new in [(OLD_CLEAN, NEW_CLEAN), ('optional = true', 'optional = false'),
                         ('"dep:clean-verify"', '"clean-verify"')]:
            with self.subTest(mutation=new):
                self.write(bump.VERIFY, self.original[bump.VERIFY].data.decode().replace(old, new, 1))
                before = bump.snapshot(self.root)
                with self.assertRaises(bump.Refusal):
                    self.invoke()
                self.assertEqual(bump.snapshot(self.root), before)
                self.assertEqual(self.commands.frontend_count, 0)
        self.write(bump.VERIFY, self.original[bump.VERIFY].data.decode())

    def test_olean_context_pin_and_feature_changes_refuse_without_mutation(self):
        original = self.original[bump.VERIFY].data.decode()
        for old, new in [
                ('clean-olean = ' + dep(bump.CLEAN_URL, OLD_CLEAN, CLEAN_CURRENT)[:-1],
                 'clean-olean = ' + dep(bump.CLEAN_URL, NEW_CLEAN, CLEAN_CURRENT)[:-1]),
                ('default-features = false', 'default-features = true'),
                ('["dep:clean-kernel", "dep:clean-olean"]', '["dep:clean-kernel"]')]:
            with self.subTest(mutation=new):
                self.write(bump.VERIFY, original.replace(old, new, 1))
                before = bump.snapshot(self.root)
                with self.assertRaises(bump.Refusal):
                    self.invoke()
                self.assertEqual(bump.snapshot(self.root), before)
                self.assertEqual(self.commands.frontend_count, 0)
        self.write(bump.VERIFY, original)

    def test_coordinated_target_never_selects_ay_without_explicit_revision(self):
        self.coordinated()
        with self.assertRaisesRegex(bump.Refusal, "requested AY"):
            self.invoke()
        self.assert_restored()
        self.assertEqual(self.commands.frontend_count, 0)

    def test_coordinated_move_restores_all_files_at_every_resolver_and_guard_failure(self):
        for step in range(FRONTEND_STEPS):
            with self.subTest(step=step):
                self.coordinated()
                self.commands.fail_step = step
                with self.assertRaisesRegex(bump.Refusal, "synthetic frontend failure"):
                    self.invoke(NEW_AY)
                self.assert_restored()

    def test_coordinated_target_requires_clean_and_ir_ay_agreement(self):
        for key in ((bump.CLEAN_URL, "Cargo.toml"), (bump.IR_URL, "crates/trust-ir-ay/Cargo.toml")):
            for old, new in ((NEW_AY, AY), ('0.26.0', '0.27.0')):
                with self.subTest(key=key, mutation=new):
                    self.coordinated()
                    self.commands.documents[key] = self.commands.documents[key].replace(old, new, 1)
                    with self.assertRaisesRegex(bump.Refusal, "AY"):
                        self.invoke(NEW_AY)
                    self.assert_restored()
                    self.assertEqual(self.commands.frontend_count, 0)

    def test_coordinated_immutable_ay_membership_and_version_refusals(self):
        mutations = [
            ('Cargo.toml', '0.26.0', '0.27.0'),
            ('Cargo.toml', '"solver/sat"', '"solver/pb"'),
            ('Cargo.toml', '"solver/sat"', '"../solver/sat"'),
            ('Cargo.toml', '"solver/sat"', '"solver/*"'),
            ('Cargo.toml', '"solver/sat"', '{path = "solver/sat"}'),
            ('solver/sat/Cargo.toml', 'ay-sat', 'ay-pb'),
            ('solver/sat/Cargo.toml', 'ay-sat', 'unrelated'),
            ('solver/sat/Cargo.toml', 'version.workspace = true', 'version = "0.27.0"'),
            ('solver/sat/Cargo.toml', 'version.workspace = true', 'version.workspace = true\nworkspace = "../foreign"'),
        ]
        for path, old, new in mutations:
            with self.subTest(path=path, mutation=new):
                self.coordinated()
                key = bump.AY_URL, path
                self.commands.documents[key] = self.commands.documents[key].replace(old, new)
                with self.assertRaises(bump.Refusal):
                    self.invoke(NEW_AY)
                self.assert_restored()
                self.assertEqual(self.commands.frontend_count, 0)

    def test_every_immutable_authority_requires_one_exact_regular_blob(self):
        targets = [(bump.IR_URL, "Cargo.toml"), (bump.CLEAN_URL, "Cargo.toml"),
                   (bump.IR_URL, "crates/trust-ir-build/Cargo.toml"),
                   (bump.AY_URL, "Cargo.toml"), (bump.AY_URL, "solver/pb/Cargo.toml")]
        for key in targets:
            path = key[1]
            entries = ["", f"120000 blob {'a' * 40}\t{path}\0",
                       f"160000 commit {'a' * 40}\t{path}\0",
                       f"040000 tree {'a' * 40}\t{path}\0",
                       f"100644 blob {'a' * 40}\twrong/Cargo.toml\0",
                       f"100644 blob invalid\t{path}\0",
                       (f"100644 blob {'a' * 40}\t{path}\0") * 2]
            for entry in entries:
                with self.subTest(key=key, entry=entry):
                    self.coordinated()
                    self.commands.tree_entries[key] = entry
                    with self.assertRaises(bump.Refusal):
                        self.invoke(NEW_AY)
                    self.assert_restored()
                    self.assertEqual(self.commands.frontend_count, 0)

    def test_immutable_authority_refuses_unsafe_paths_before_git(self):
        with tempfile.TemporaryDirectory() as temporary:
            authority = bump.Authority(self.commands, Path(temporary) / "ay", bump.AY_URL, AY)
            count = len(self.commands.calls)
            for path in ["", "/Cargo.toml", "../Cargo.toml", "a/../Cargo.toml", "a//Cargo.toml",
                         "./Cargo.toml", "a/*/Cargo.toml", "a\\Cargo.toml", ":(top)Cargo.toml"]:
                with self.subTest(path=path), self.assertRaisesRegex(bump.Refusal, "unsafe"):
                    authority.read(path)
            self.assertEqual(len(self.commands.calls), count)

    def test_nested_member_admits_exact_workspace_path_alias_and_executable_blob(self):
        self.coordinated()
        key = bump.AY_URL, "Cargo.toml"
        self.commands.documents[key] += '\n[workspace.dependencies]\nrenamed = { package = "ay-sat", path = "solver/sat", version = "0.26" }\n'
        self.commands.documents[bump.AY_URL, "solver/pb/Cargo.toml"] += '\n[dependencies]\nrenamed = { workspace = true, optional = true }\n'
        self.commands.tree_entries[bump.AY_URL, "solver/pb/Cargo.toml"] = f"100755 blob {blob_oid(self.commands.documents[bump.AY_URL, 'solver/pb/Cargo.toml'].encode())}\tsolver/pb/Cargo.toml\0"
        self.invoke(NEW_AY)
        self.assertEqual(self.commands.frontend_count, FRONTEND_STEPS)

    def excluded_vendor(self):
        self.coordinated()
        key = bump.AY_URL, "Cargo.toml"
        self.commands.documents[key] = self.commands.documents[key].replace(
            "[workspace]\n", '[workspace]\nexclude = ["vendor/veripb"]\n')
        self.commands.documents[key] += (
            '\n[workspace.dependencies]\n'
            'ay-veripb = { package = "veripb", path = "vendor/veripb" }\n')
        self.commands.documents[bump.AY_URL, "solver/pb/Cargo.toml"] += (
            '\n[dependencies]\nay-veripb = { workspace = true, optional = true }\n')
        self.commands.documents[bump.AY_URL, "vendor/veripb/Cargo.toml"] = (
            '[workspace]\n[package]\nname = "veripb"\nversion = "3.0.2"\n')

    def test_optional_excluded_vendor_declaration_keeps_the_selected_cohort(self):
        self.excluded_vendor()
        self.invoke(NEW_AY)
        self.assertEqual(self.commands.frontend_count, FRONTEND_STEPS)
        for lock in bump.LOCKS:
            self.assertFalse(any(row["name"] == "veripb" for row in
                                 bump.packages((self.root / lock).read_bytes(), lock)))

    def test_excluded_vendor_requires_optional_exact_excluded_owning_workspace(self):
        changes = [
            ("solver/pb/Cargo.toml", ", optional = true", ""),
            ("Cargo.toml", 'exclude = ["vendor/veripb"]', 'exclude = []'),
            ("Cargo.toml", 'path = "vendor/veripb"', 'path = "vendor/veripb/child"'),
            ("Cargo.toml", 'path = "vendor/veripb"', 'path = "../vendor/veripb"'),
            ("vendor/veripb/Cargo.toml", 'name = "veripb"', 'name = "other"'),
            ("vendor/veripb/Cargo.toml", 'version = "3.0.2"', 'version.workspace = true'),
            ("vendor/veripb/Cargo.toml", '[workspace]\n', ''),
            ("vendor/veripb/Cargo.toml", '[package]\n', '[package]\nworkspace = "../../"\n'),
        ]
        for path, old, new in changes:
            with self.subTest(path=path, mutation=new):
                self.excluded_vendor()
                key = bump.AY_URL, path
                self.commands.documents[key] = self.commands.documents[key].replace(old, new)
                with self.assertRaises(bump.Refusal):
                    self.invoke(NEW_AY)
                self.assert_restored()
                self.assertEqual(self.commands.frontend_count, 0)

    def test_excluded_vendor_retains_exact_regular_manifest_and_targo_precedence(self):
        for entry in ["", f"120000 blob {'a' * 40}\tvendor/veripb/Cargo.toml\0",
                      f"160000 commit {'a' * 40}\tvendor/veripb/Cargo.toml\0"]:
            with self.subTest(entry=entry):
                self.excluded_vendor()
                self.commands.tree_entries[bump.AY_URL, "vendor/veripb/Cargo.toml"] = entry
                with self.assertRaises(bump.Refusal):
                    self.invoke(NEW_AY)
                self.assert_restored()
                self.assertEqual(self.commands.frontend_count, 0)
        self.excluded_vendor()
        self.commands.documents[bump.AY_URL, "vendor/veripb/Targo.toml"] = '[workspace]\n'
        with self.assertRaisesRegex(bump.Refusal, "Targo"):
            self.invoke(NEW_AY)
        self.assert_restored()

    def test_excluded_vendor_cannot_impersonate_an_ay_member(self):
        self.excluded_vendor()
        key = bump.AY_URL, "Cargo.toml"
        self.commands.documents[key] = self.commands.documents[key].replace(
            'package = "veripb"', 'package = "ay-hidden"')
        self.commands.documents[bump.AY_URL, "vendor/veripb/Cargo.toml"] = (
            '[workspace]\n[package]\nname = "ay-hidden"\nversion = "0.26.0"\n')
        with self.assertRaises(bump.Refusal):
            self.invoke(NEW_AY)
        self.assert_restored()

    def test_valid_vendor_declaration_does_not_admit_foreign_graph_activation(self):
        self.excluded_vendor()
        state, authority = self.graph_authority()
        before, after = self.graph_pair()
        after += package("veripb", "3.0.2", bump.source(bump.AY_URL, NEW_AY)).encode()
        with self.assertRaisesRegex(bump.Refusal, "unexpected package name"):
            bump.validate_graph(before, after, "vendor activation", state,
                                NEW_IR, NEW_CLEAN, NEW_AY, authority)

    def test_workspace_discovery_refuses_nested_owner_default_excluded_and_hidden_members(self):
        cases = [
            ("solver/Cargo.toml", '[workspace]\nmembers = ["pb", "sat"]\n'),
            ("solver/Cargo.toml", '[package]\nname = "parent"\nworkspace = "../elsewhere"\n'),
            ("solver/Cargo.toml", '[project]\nname = "legacy-parent"\nworkspace = "../elsewhere"\n'),
            ("solver/Cargo.toml", 'package = "malformed"\n'),
            ("solver/Cargo.toml", 'project = ["malformed"]\n'),
            ("solver/Cargo.toml", '[broken = [\n'),
            ("Cargo.toml", '\n[package]\nname = "ay-root"\nversion = "0.26.0"\n'),
            ("solver/pb/Cargo.toml", '\n[workspace]\n'),
            ("solver/pb/Cargo.toml", '\n[dev-dependencies]\nhidden = { package = "ay-hidden", path = "../hidden" }\n'),
            ("solver/pb/Cargo.toml", '\n[target.\'cfg(any())\'.dependencies]\nay-sat = { path = "../wrong", version = "0.26" }\n'),
            ("Cargo.toml", '\n[workspace.dependencies]\nay-hidden = { path = "solver/hidden" }\n'),
            ("solver/pb/Cargo.toml", '\n[dependencies]\nay-sat = { path = "../redirect/../sat" }\n'),
            ("solver/pb/Cargo.toml", '\n[dependencies]\nay-sat = { path = ".././sat" }\n'),
            ("solver/pb/Cargo.toml", '\n[dependencies]\nay-sat = { path = "../../../solver/sat" }\n'),
            ("solver/pb/Cargo.toml", '\n[dependencies]\nay-sat = { path = "..//sat" }\n'),
        ]
        for path, text in cases:
            with self.subTest(path=path, text=text):
                self.coordinated()
                key = bump.AY_URL, path
                self.commands.documents[key] = self.commands.documents.get(key, "") + text
                with self.assertRaises(bump.Refusal):
                    self.invoke(NEW_AY)
                self.assert_restored()
                self.assertEqual(self.commands.frontend_count, 0)
        for declaration in ['exclude = ["solver"]', 'exclude = ["solver/sat"]',
                            'exclude = ["unrelated", "unrelated"]',
                            'default-members = ["solver/missing"]', 'default-members = ["solver/pb", "solver/pb"]']:
            with self.subTest(declaration=declaration):
                self.coordinated()
                key = bump.AY_URL, "Cargo.toml"
                self.commands.documents[key] = self.commands.documents[key].replace("[workspace]\n", "[workspace]\n" + declaration + "\n")
                with self.assertRaises(bump.Refusal):
                    self.invoke(NEW_AY)
                self.assert_restored()

    def test_intermediate_manifest_symlink_is_not_an_absent_workspace(self):
        self.coordinated()
        self.commands.tree_entries[bump.AY_URL, "solver/Cargo.toml"] = f"120000 blob {'a' * 40}\tsolver/Cargo.toml\0"
        with self.assertRaisesRegex(bump.Refusal, "regular blob"):
            self.invoke(NEW_AY)
        self.assert_restored()
        self.assertEqual(self.commands.frontend_count, 0)

    def test_targo_precedence_refuses_root_member_and_intermediate_authorities(self):
        for url, relative in [(bump.IR_URL, "Targo.toml"), (bump.CLEAN_URL, "Targo.toml"),
                              (bump.AY_URL, "Targo.toml"), (bump.AY_URL, "solver/Targo.toml"),
                              (bump.AY_URL, "solver/pb/Targo.toml")]:
            with self.subTest(url=url, relative=relative):
                self.coordinated()
                self.commands.documents[url, relative] = '[workspace]\n'
                with self.assertRaisesRegex(bump.Refusal, "Targo manifest precedence"):
                    self.invoke(NEW_AY)
                self.assert_restored()
                self.assertEqual(self.commands.frontend_count, 0)

    def test_semantic_ay_alias_census_cannot_hide_extra_or_renamed_authority(self):
        for key in [(bump.CLEAN_URL, "Cargo.toml"), (bump.IR_URL, "crates/trust-ir-ay/Cargo.toml")]:
            for declaration in [f'extra = {{ package = "ay-core", git = "{bump.AY_URL}", rev = "{NEW_AY}", version = "0.26.0" }}\n',
                                f'extra = {{ git = "{bump.AY_URL}", rev = "{NEW_AY}", version = "0.26.0" }}\n']:
                with self.subTest(key=key, declaration=declaration):
                    self.coordinated()
                    self.commands.documents[key] += "\n" + declaration
                    with self.assertRaisesRegex(bump.Refusal, "AY"):
                        self.invoke(NEW_AY)
                    self.assert_restored()
            self.coordinated()
            self.commands.documents[key] = self.commands.documents[key].replace('ay = {', 'ay = { package = "ay-core",', 1)
            with self.assertRaisesRegex(bump.Refusal, "renamed AY"):
                self.invoke(NEW_AY)
            self.assert_restored()

    def graph_authority(self):
        state = bump.current(self.root, self.original)
        with tempfile.TemporaryDirectory() as temporary:
            target = bump.target_cohort(self.commands, Path(temporary), state, NEW_IR, NEW_AY)
        self.assertEqual(target.clean, NEW_CLEAN)
        self.assertEqual(target.ay.revision, NEW_AY)
        return state, target.ay

    def graph_pair(self, extra="", before_edges=(), after_edges=()):
        before = self.original[bump.LOCKS[0]].data.decode() + extra
        before = before.replace(package("ay-pb", "0.26.0", bump.source(bump.AY_URL, AY)),
                                package("ay-pb", "0.26.0", bump.source(bump.AY_URL, AY), before_edges))
        after = (self.original[bump.LOCKS[0]].data.decode() + extra).replace(
            OLD_IR, NEW_IR).replace(OLD_CLEAN, NEW_CLEAN).replace(AY, NEW_AY)
        after = after.replace(package("ay-pb", "0.26.0", bump.source(bump.AY_URL, NEW_AY)),
                              package("ay-pb", "0.26.0", bump.source(bump.AY_URL, NEW_AY), after_edges))
        return before.encode(), after.encode()

    def test_changed_ay_edge_is_bound_to_actual_admitted_member_manifest(self):
        self.coordinated()
        self.commands.documents[bump.AY_URL, "solver/pb/Cargo.toml"] += '\n[dependencies]\nrenamed = { package = "ay-sat", path = "../sat", version = "0.26" }\n'
        def add_required_edge(step, root):
            if step == 5:
                for relative in bump.LOCKS:
                    lock = root / relative
                    lock.write_text(lock.read_text().replace(
                        package("ay-pb", "0.26.0", bump.source(bump.AY_URL, NEW_AY)),
                        package("ay-pb", "0.26.0", bump.source(bump.AY_URL, NEW_AY), ["ay-sat"])))
        self.commands.mutate = add_required_edge
        self.invoke(NEW_AY)
        self.assertEqual(self.commands.frontend_count, FRONTEND_STEPS)
        self.assertEqual(bump.current(self.root, bump.snapshot(self.root)).ay, NEW_AY)

    def test_ay_required_edge_cannot_disappear_and_undeclared_edge_cannot_appear(self):
        for declaration, edges, expected in [
            ('\n[dependencies]\nay-sat = { path = "../sat" }\n', (), "missing required"),
            ("", ("ay-sat",), "absent from immutable"),
            ('\n[dev-dependencies]\nay-sat = { path = "../sat" }\n', ("ay-sat",), "absent from immutable"),
        ]:
            with self.subTest(declaration=declaration, edges=edges):
                self.coordinated()
                self.commands.documents[bump.AY_URL, "solver/pb/Cargo.toml"] += declaration
                state, authority = self.graph_authority()
                before, after = self.graph_pair(after_edges=edges)
                with self.assertRaisesRegex(bump.Refusal, expected):
                    bump.validate_graph(before, after, "graph", state, NEW_IR, NEW_CLEAN, NEW_AY, authority)

    def test_registry_alias_and_optional_platform_omissions_are_manifest_bound(self):
        self.coordinated()
        self.commands.documents[bump.AY_URL, "solver/pb/Cargo.toml"] += (
            '\n[dependencies]\nrenamed = { package = "helper", version = "1" }\n'
            'ay-sat = { path = "../sat", optional = true }\n'
            '[target.\'cfg(any())\'.build-dependencies]\nplatform = { package = "helper", version = "^1.2" }\n')
        state, authority = self.graph_authority()
        before, after = self.graph_pair(extra=package("helper", "1.2.3", bump.REGISTRY), after_edges=("helper",))
        bump.validate_graph(before, after, "graph", state, NEW_IR, NEW_CLEAN, NEW_AY, authority)
        # Canonically qualified references select the very same admitted edge.
        qualified = after.replace(b'dependencies = ["helper"]',
                                  f'dependencies = ["helper 1.2.3 ({bump.REGISTRY})"]'.encode())
        self.assertNotEqual(qualified, after)
        bump.validate_graph(before, qualified, "graph", state, NEW_IR, NEW_CLEAN, NEW_AY, authority)

    def test_manifest_edge_rejects_wrong_source_version_and_conflicting_optional_alias(self):
        for declaration, identity in [
            ('\n[dependencies]\nhelper = "2"\n', bump.REGISTRY),
            ('\n[dependencies]\nhelper = "1"\n', 'registry+https://wrong.invalid/index'),
            ('\n[dependencies]\nhelper = "1"\nweaker = { package = "helper", version = "2", optional = true }\n', bump.REGISTRY),
            ('\n[dependencies]\nhelper = "*"\n', bump.REGISTRY),
        ]:
            with self.subTest(declaration=declaration, identity=identity):
                self.coordinated()
                self.commands.documents[bump.AY_URL, "solver/pb/Cargo.toml"] += declaration
                state, authority = self.graph_authority()
                before, after = self.graph_pair(extra=package("helper", "1.2.3", identity), after_edges=("helper",))
                with self.assertRaises(bump.Refusal):
                    bump.validate_graph(before, after, "graph", state, NEW_IR, NEW_CLEAN, NEW_AY, authority)

    def test_graph_requires_retained_exact_target_and_preserves_ay_non_edge_fields(self):
        self.coordinated()
        state, authority = self.graph_authority()
        before, after = self.graph_pair()
        for candidate in [None, bump.AyTarget(AY, authority.version, authority.declarations, authority.required)]:
            with self.subTest(candidate=candidate), self.assertRaisesRegex(bump.Refusal, "graph authority"):
                bump.validate_graph(before, after, "graph", state, NEW_IR, NEW_CLEAN, NEW_AY, candidate)
        after = after.replace(b'name = "ay-pb"', b'name = "ay-pb"\nnote = "unowned mutation"')
        with self.assertRaisesRegex(bump.Refusal, "outside the admitted"):
            bump.validate_graph(before, after, "graph", state, NEW_IR, NEW_CLEAN, NEW_AY, authority)

    def test_only_exact_dependency_identities_are_normalized_not_inert_metadata(self):
        for insertion in [
            'name = "third-party"\nnote = "' + bump.source(bump.AY_URL, AY) + '"',
            'name = "third-party"\nchecksum = "' + bump.source(bump.IR_URL, OLD_IR) + '"',
            'name = "ay-pb"\nmetadata = { nested = ["' + bump.source(bump.AY_URL, AY) + '"] }',
        ]:
            with self.subTest(insertion=insertion):
                self.coordinated()
                state, authority = self.graph_authority()
                before, after = self.graph_pair()
                original = insertion.split("\n", 1)[0].encode()
                before = before.replace(original, insertion.encode())
                after = after.replace(original, insertion.replace(AY, NEW_AY).replace(OLD_IR, NEW_IR).encode())
                with self.assertRaisesRegex(bump.Refusal, "outside the admitted"):
                    bump.validate_graph(before, after, "graph", state, NEW_IR, NEW_CLEAN, NEW_AY, authority)
        self.coordinated()
        state, authority = self.graph_authority()
        before, after = self.graph_pair()
        before += ('\n[metadata]\nauthority_note = "' + bump.source(bump.AY_URL, AY) + '"\n').encode()
        after += ('\n[metadata]\nauthority_note = "' + bump.source(bump.AY_URL, NEW_AY) + '"\n').encode()
        with self.assertRaisesRegex(bump.Refusal, "lock metadata"):
            bump.validate_graph(before, after, "graph", state, NEW_IR, NEW_CLEAN, NEW_AY, authority)

    def test_default_ay_exact_ir_clean_dependency_references_remap_without_ay_fetch(self):
        for lock in bump.LOCKS:
            path = self.root / lock
            original = path.read_text()
            updated = original.replace('["trust-ir"]',
                '["trust-ir 0.14.0 (' + bump.source(bump.IR_URL, OLD_IR) + ')", "clean-kernel"]')
            self.assertNotEqual(updated, original)
            path.write_text(updated)
        self.original = bump.snapshot(self.root)
        self.invoke()
        self.assertEqual(self.commands.frontend_count, FRONTEND_STEPS)
        self.assertEqual({url for url, _ in self.commands.fetched.values()}, {bump.IR_URL, bump.CLEAN_URL})

    def test_external_exact_ay_reference_remaps_without_rewriting_inert_fields(self):
        self.coordinated()
        state, authority = self.graph_authority()
        before, after = self.graph_pair()
        note = ('\n[metadata]\nunchanged = "' + bump.source(bump.AY_URL, AY) + '"\n').encode()
        original_before, original_after = before, after
        before = before.replace(b'dependencies = ["trust-ir"]',
                                f'dependencies = ["ay-pb 0.26.0 ({bump.source(bump.AY_URL, AY)})"]'.encode())
        after = after.replace(b'dependencies = ["trust-ir"]', b'dependencies = ["ay-pb"]')
        self.assertNotEqual(before, original_before)
        self.assertNotEqual(after, original_after)
        bump.validate_graph(before + note, after + note, "graph", state, NEW_IR, NEW_CLEAN, NEW_AY, authority)

    def test_fragmentless_git_edges_keep_resolved_commits_in_graph_comparisons(self):
        state = bump.current(self.root, self.original)
        qualifier = "git+https://example.invalid/helper.git?rev=" + "a" * 40
        resolved = qualifier + "#" + "b" * 40
        extra = package("git-helper", "1.0.0", resolved)
        extra += package("downstream", "1.0.0", dependencies=[
            f"git-helper 1.0.0 ({qualifier})"])
        before = self.original[bump.LOCKS[0]].data + extra.encode()
        after = before.replace(OLD_IR.encode(), NEW_IR.encode()).replace(
            OLD_CLEAN.encode(), NEW_CLEAN.encode())
        bump.validate_graph(before, after, "graph", state, NEW_IR, NEW_CLEAN, AY)
        # The abbreviated dependency is unchanged, but the actual selected
        # commit changed. Resolving is not permission to erase that identity.
        changed = after.replace(resolved.encode(), (qualifier + "#" + "c" * 40).encode())
        self.assertNotEqual(changed, after)
        with self.assertRaisesRegex(bump.Refusal, "outside the admitted"):
            bump.validate_graph(before, changed, "graph", state, NEW_IR, NEW_CLEAN, AY)

    def test_dangling_ambiguous_and_duplicate_dependency_identities_refuse(self):
        for extra, edges in [("", ("missing",)), ("", ("ay-sat", "ay-sat 0.26.0")),
                             (package("helper", "1.0.0", bump.REGISTRY) + package("helper", "2.0.0", bump.REGISTRY), ("helper",))]:
            with self.subTest(extra=extra, edges=edges):
                self.coordinated()
                state, authority = self.graph_authority()
                before, after = self.graph_pair(extra=extra, after_edges=edges)
                with self.assertRaises(bump.Refusal):
                    bump.validate_graph(before, after, "graph", state, NEW_IR, NEW_CLEAN, NEW_AY, authority)

    def test_coordinated_lock_cannot_split_add_remove_or_version_ay(self):
        mutations = [
            lambda text: text.replace(NEW_AY, AY, 2),
            lambda text: text + package('ay-extra', '0.26.0', bump.source(bump.AY_URL, NEW_AY)),
            lambda text: text.replace('name = "ay-sat"', 'name = "unrelated-sat"'),
            lambda text: text.replace('name = "ay-sat"\nversion = "0.26.0"', 'name = "ay-sat"\nversion = "0.27.0"'),
            lambda text: text.replace('name = "third-party"\nversion = "1.0.0"', 'name = "third-party"\nversion = "2.0.0"'),
        ]
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                self.coordinated()
                def mutate(step, root):
                    if step == 5:
                        path = root / bump.LOCKS[0]
                        path.write_text(mutation(path.read_text()))
                self.commands.mutate = mutate
                with self.assertRaises(bump.Refusal):
                    self.invoke(NEW_AY)
                self.assert_restored()

    CDCLT = "ay-cdclt"

    def admittable_ay(self, requirer_section="dependencies", row_version="0.26.0",
                      row_edges=(), cdclt_manifest=""):
        """A coordinated move whose AY target adds `ay-cdclt`, which ay-pb requires."""
        self.coordinated()
        docs = self.commands.documents
        docs[bump.AY_URL, "Cargo.toml"] = docs[bump.AY_URL, "Cargo.toml"].replace(
            'members = ["solver/pb", "solver/sat"]', 'members = ["solver/pb", "solver/sat", "solver/cdclt"]')
        docs[bump.AY_URL, "solver/cdclt/Cargo.toml"] = (
            f'[package]\nname = "{self.CDCLT}"\nversion.workspace = true\n' + cdclt_manifest)
        if requirer_section is not None:
            docs[bump.AY_URL, "solver/pb/Cargo.toml"] += (
                f'\n[{requirer_section}]\n{self.CDCLT} = {{ path = "../cdclt" }}\n')

        def gain(step, root):
            if step == 5:
                for relative in bump.LOCKS:
                    lock = root / relative
                    text = lock.read_text()
                    pb = package("ay-pb", "0.26.0", bump.source(bump.AY_URL, NEW_AY))
                    if pb not in text:
                        continue
                    text = text.replace(pb, package("ay-pb", "0.26.0", bump.source(bump.AY_URL, NEW_AY),
                                                    [self.CDCLT]))
                    text += package(self.CDCLT, row_version, bump.source(bump.AY_URL, NEW_AY), row_edges)
                    lock.write_text(text)
        self.commands.mutate = gain

    def test_named_ay_package_is_admitted_where_its_requirer_resolves(self):
        self.admittable_ay()
        self.invoke(NEW_AY, admit_ay=(self.CDCLT,))
        self.assertEqual(self.commands.frontend_count, FRONTEND_STEPS)
        self.assertEqual(bump.current(self.root, bump.snapshot(self.root)).ay, NEW_AY)
        self.assertIn(f"admitted {self.CDCLT}", self.output.getvalue())
        for relative in bump.LOCKS:
            text = (self.root / relative).read_text()
            self.assertEqual(f'name = "{self.CDCLT}"' in text, relative != "fuzz/Cargo.lock", relative)

    def test_unnamed_gained_ay_package_still_refuses_and_restores(self):
        self.admittable_ay()
        with self.assertRaisesRegex(bump.Refusal, "AY cohort is unsupported"):
            self.invoke(NEW_AY)
        self.assert_restored()

    def test_admitted_ay_row_is_held_to_cohort_version_and_its_manifest(self):
        for kwargs, expected in [
            ({"row_version": "0.27.0"}, "AY version drift|AY cohort is unsupported"),
            ({"row_edges": ("ay-sat",)}, "absent from immutable"),
            ({"cdclt_manifest": '\n[dependencies]\nay-sat = { path = "../sat" }\n'}, "missing required"),
            # A third-party package the lock did not already resolve cannot enter with it.
            ({"cdclt_manifest": '\n[dependencies]\nhelper = "1"\n', "row_edges": ("helper",)},
             "unresolved/ambiguous dependency|outside the admitted"),
        ]:
            with self.subTest(kwargs=kwargs):
                self.admittable_ay(**kwargs)
                with self.assertRaisesRegex(bump.Refusal, expected):
                    self.invoke(NEW_AY, admit_ay=(self.CDCLT,))
                self.assert_restored()

    def test_ay_admission_refuses_unbound_names_before_mutation(self):
        cases = [
            ("not a member", ("ay-ghost",), "dependencies"),
            ("already in the AY cohort", ("ay-sat",), "dependencies"),
            ("only a named ay-", ("third-party",), "dependencies"),
            ("only a named ay-", ("ay",), "dependencies"),
            ("duplicate", (self.CDCLT, self.CDCLT), "dependencies"),
            ("no AY cohort package requires", (self.CDCLT,), None),
            ("no AY cohort package requires", (self.CDCLT,), "dev-dependencies"),
        ]
        for expected, names, section in cases:
            with self.subTest(names=names, section=section):
                self.admittable_ay(requirer_section=section)
                with self.assertRaisesRegex(bump.Refusal, expected):
                    self.invoke(NEW_AY, admit_ay=names)
                self.assert_restored()
                self.assertEqual(self.commands.frontend_count, 0)
        self.commands = SyntheticCommands(self.root)
        with self.assertRaisesRegex(bump.Refusal, "needs an AY move"):
            self.invoke(admit_ay=(self.CDCLT,))
        self.assert_restored()
        self.assertEqual(self.commands.frontend_count, 0)

    MACROS = "tok-macros"

    def droppable(self, also=None):
        """Every lock resolves `tok` 1.0.0 -> `tok-macros`; the move's resolution drops the macros.

        The shape of Clean `d618ceed7` (LD-PIN2A43-1): the target stops enabling
        Tokio's macros, so `tokio-macros` and tokio's edge to it leave the locks.
        `also` makes one more change beside the drop.
        """
        tok = lambda edges: package("tok", "1.0.0", bump.REGISTRY, edges)
        macros = package(self.MACROS, "2.0.0", bump.REGISTRY)
        for relative in bump.LOCKS:
            lock = self.root / relative
            if macros not in lock.read_text():
                lock.write_text(lock.read_text() + tok([self.MACROS]) + macros)
        self.original = bump.snapshot(self.root)
        self.commands.frontend_count = 0

        def drop(step, root):
            if step == 5:
                for relative in bump.LOCKS:
                    lock = root / relative
                    text = lock.read_text().replace(tok([self.MACROS]), tok(()))
                    if also == "macros-stay":
                        text = text.replace(tok(()), tok([self.MACROS]))
                    else:
                        text = text.replace(macros, "")
                    if also == "version":
                        text = text.replace(package("third-party", "1.0.0", "registry+https://example.invalid/index"),
                                            package("third-party", "1.0.1", "registry+https://example.invalid/index"))
                    lock.write_text(text)
        self.commands.mutate = drop

    def test_named_dropped_package_leaves_where_the_resolver_drops_it(self):
        self.droppable()
        self.invoke(drop=(self.MACROS,))
        self.assertEqual(self.commands.frontend_count, FRONTEND_STEPS)
        self.assertIn(f"dropped {self.MACROS}", self.output.getvalue())
        for relative in bump.LOCKS:
            text = (self.root / relative).read_text()
            self.assertNotIn(f'name = "{self.MACROS}"', text, relative)
            self.assertIn(package("tok", "1.0.0", bump.REGISTRY), text, relative)

    def test_unnamed_dropped_package_still_refuses_and_restores(self):
        self.droppable()
        with self.assertRaisesRegex(bump.Refusal, "outside the admitted source cohort"):
            self.invoke()
        self.assert_restored()

    def test_a_drop_admits_no_other_change(self):
        for also, expected in [("version", "outside the admitted source cohort"),
                               ("macros-stay", "drops it from no lock")]:
            with self.subTest(also=also):
                self.droppable(also)
                with self.assertRaisesRegex(bump.Refusal, expected):
                    self.invoke(drop=(self.MACROS,))
                self.assert_restored()

    def test_drop_admission_refuses_unbound_names_before_mutation(self):
        self.droppable()
        for names, expected in [(("trust-ir-build",), "only a third-party"),
                                (("clean-kernel",), "only a third-party"),
                                (("ay-sat",), "only a third-party"),
                                (("ghost",), "no current lock resolves"),
                                (("third-party",), "only a registry package"),
                                ((self.MACROS, self.MACROS), "duplicate")]:
            with self.subTest(names=names):
                self.commands.frontend_count = 0
                with self.assertRaisesRegex(bump.Refusal, expected):
                    self.invoke(drop=names)
                self.assert_restored()
                self.assertEqual(self.commands.frontend_count, 0)

    def test_existing_ay_in_fuzz_must_match_manifest_authority(self):
        path = self.root / 'fuzz/Cargo.lock'
        saved = path.read_text()
        path.write_text(saved + package('ay-sat', '0.26.0', bump.source(bump.AY_URL, NEW_AY)))
        with self.assertRaisesRegex(bump.Refusal, 'wrong dependency revision'):
            bump.current(self.root, bump.snapshot(self.root))
        path.write_text(saved + package('ay-sat', '0.26.0', bump.source(bump.AY_URL, AY)))
        self.original = bump.snapshot(self.root)
        self.coordinated()
        self.invoke(NEW_AY)
        self.assertEqual(bump.current(self.root, bump.snapshot(self.root)).ay, NEW_AY)

    def test_optional_fuzz_graph_cannot_gain_ay_during_coordinated_move(self):
        self.coordinated()
        def mutate(step, root):
            if step == 5:
                path = root / 'fuzz/Cargo.lock'
                path.write_text(path.read_text() + package('ay-sat', '0.26.0', bump.source(bump.AY_URL, NEW_AY)))
        self.commands.mutate = mutate
        with self.assertRaisesRegex(bump.Refusal, 'missing ay package cohort'):
            self.invoke(NEW_AY)
        self.assert_restored()

    def test_current_ay_cache_manifest_features_and_version_must_agree(self):
        for path, old, new in [(bump.CACHE, 'ay:' + AY, 'ay:' + NEW_AY),
                               (bump.REGALLOC, 'optional = true', 'optional = false'),
                               (bump.REGALLOC, 'default-features = false', 'default-features = true'),
                               (bump.REGALLOC, 'raw-pointer-bcp', 'jit'),
                               (bump.REGALLOC, 'default = []', 'default = ["ay-regalloc"]'),
                               (bump.REGALLOC, 'dep:trust-cg-process-env', 'dep:other'),
                               (bump.REGALLOC, '0.26.0', '0.27.0')]:
            with self.subTest(path=path, mutation=new):
                original = self.original[path]
                self.write(path, original.data.decode().replace(old, new, 1))
                with self.assertRaises(bump.Refusal):
                    bump.current(self.root, bump.snapshot(self.root))
                self.write(path, original.data.decode())

    def test_success_binds_all_seven_files_and_exact_frontend_lanes(self):
        self.invoke()
        after = bump.current(self.root, bump.snapshot(self.root))
        self.assertEqual((after.ir, after.clean, after.ay), (NEW_IR, NEW_CLEAN, AY))
        actual = [argv for argv, _, _, git, _ in self.commands.calls if not git]
        expected = []
        for lock in bump.LOCKS:
            manifest = str(self.root / Path(lock).with_name("Cargo.toml"))
            expected.extend([
                [str(self.commands.targo), "metadata", "--format-version", "1", "--manifest-path", manifest],
                [str(self.commands.targo), "update", "--manifest-path", manifest, "-p",
                 "trust-ir@0.14.0", "--precise", NEW_IR],
            ])
        for lock in bump.LOCKS:
            manifest = str(self.root / Path(lock).with_name("Cargo.toml"))
            expected.append([str(self.commands.targo), "metadata", "--locked", "--format-version", "1",
                             "--manifest-path", manifest])
        expected.append([str(self.commands.targo), "--unverified", "test", "--locked", "-p",
                         "trust-cg-test", "--test", "dependency_authority",
                         "--", "--test-threads=1"])
        # The TrustIR-derived inventories are re-derived against the target.
        expected.append([str(self.commands.targo), "--unverified", "test", "--locked", "-p",
                         "trust-cg-verify", "--test", "fsym_layout", "--", "--test-threads=1"])
        expected.append([str(self.commands.targo), "--unverified", "test", "--locked", "-p",
                         "trust-cg-verify", "--test", "fsym_ub_map", "--", "--test-threads=1"])
        expected.append([str(self.commands.targo), "--unverified", "test", "--locked", "-p",
                         "trust-cg-lower", "--test", "trust_ir_construct_inventory",
                         "--", "--test-threads=1"])
        # The conformance fixture guards: the census, then the vendored fixtures.
        for package, target in [("trust-cg-codegen", "trust_ir_corpus_roundtrip"),
                                ("trust-cg-codegen", "trust_ir_binary_container"),
                                ("trust-cg-cli", "trust_ir_binary_container")]:
            expected.append([str(self.commands.targo), "--unverified", "test", "--locked", "-p",
                             package, "--test", target, "--", "--test-threads=1"])
        # The must-refuse corpus guard closes the transaction (KIND 4).
        expected.append([str(self.commands.targo), "--unverified", "test", "--locked", "-p",
                         "trust-cg-codegen", "--test", "must_refuse_corpus",
                         "--", "--test-threads=1"])
        self.assertEqual(actual, expected)
        self.assertEqual(self.commands.status_reads, 2)
        for relative in bump.OWNED:
            self.assertEqual((self.root / relative).stat().st_mode & 0o777, self.original[relative].mode)
        self.assertIn("Git index untouched", self.output.getvalue())

    def test_every_metadata_update_and_guard_failure_restores_every_leg(self):
        for step in range(FRONTEND_STEPS - 1):
            with self.subTest(step=step):
                self.commands = SyntheticCommands(self.root)
                self.commands.fail_step = step
                with self.assertRaisesRegex(bump.Refusal, "synthetic frontend failure"):
                    self.invoke()
                self.assert_restored()
                self.assertEqual(self.commands.frontend_count, step + 1)

    def test_all_dirty_owned_legs_refuse_before_remote_or_frontend(self):
        for relative in bump.OWNED:
            with self.subTest(relative=relative):
                self.commands.dirty = f" M {relative}\n"
                with self.assertRaisesRegex(bump.Refusal, "dirty"):
                    self.invoke()
                self.assert_restored()
                self.assertFalse(self.commands.fetched)
                self.assertEqual(self.commands.frontend_count, 0)

    def test_nonblocking_exclusive_lock_refuses_concurrent_transaction(self):
        lock = self.root / "git-private/compiler-pin-transaction.lock"
        with lock.open("w") as handle:
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
            with self.assertRaisesRegex(bump.Refusal, "another compiler-pin transaction"):
                self.invoke()
        self.assert_restored()
        self.assertFalse(self.commands.fetched)

    def test_interruption_restores_every_leg(self):
        for interruption in [KeyboardInterrupt(), InterruptedError("SIGTERM"), SystemExit(7)]:
            with self.subTest(interruption=type(interruption).__name__):
                self.commands = SyntheticCommands(self.root)
                self.commands.fail_step = 3
                self.commands.interruption = interruption
                with self.assertRaises(type(interruption)):
                    self.invoke()
                self.assert_restored()

    def test_deleted_lock_is_recreated_byte_exactly_during_rollback(self):
        self.commands.fail_step = 0
        self.commands.mutate = lambda step, root: (root / bump.LOCKS[0]).unlink() if step == 0 else None
        with self.assertRaisesRegex(bump.Refusal, "synthetic frontend failure"):
            self.invoke()
        self.assert_restored()

    def test_replaced_lock_symlink_is_removed_without_writing_referent(self):
        outside = self.write("outside.txt", "never touch this\n")

        def replace(step, root):
            if step == 0:
                lock = root / bump.LOCKS[0]
                lock.unlink()
                lock.symlink_to(outside)

        self.commands.fail_step = 0
        self.commands.mutate = replace
        with self.assertRaises(bump.Refusal):
            self.invoke()
        self.assertEqual(outside.read_text(), "never touch this\n")
        self.assert_restored()

    def test_partial_install_failure_rolls_back(self):
        real = bump.install

        def fail_cache(root, relative, data, mode, **kwargs):
            if relative == bump.CACHE and not kwargs.get("recovery"):
                raise OSError("synthetic install failure")
            return real(root, relative, data, mode, **kwargs)

        with patch.object(bump, "install", side_effect=fail_cache):
            with self.assertRaisesRegex(OSError, "synthetic install failure"):
                self.invoke()
        self.assert_restored()

    def test_rollback_failure_reports_retained_original_bytes(self):
        real = bump.install

        def fail_restore(root, relative, data, mode, **kwargs):
            if relative == bump.CACHE and kwargs.get("recovery"):
                raise OSError("synthetic restore failure")
            return real(root, relative, data, mode, **kwargs)

        self.commands.fail_step = 0
        with patch.object(bump, "install", side_effect=fail_restore):
            with self.assertRaisesRegex(bump.Refusal, "ROLLBACK INCOMPLETE") as raised:
                self.invoke()
        message = str(raised.exception)
        backup = Path(message.split("original-byte recovery files: ", 1)[1].split(";", 1)[0])
        self.addCleanup(bump.shutil.rmtree, backup)
        for relative, saved in self.original.items():
            self.assertEqual((backup / relative).read_bytes(), saved.data)
        self.assertIn("original failure", message)

    def test_immutable_remote_revision_mismatch_refuses_before_changes(self):
        self.commands.wrong_fetch = True
        with self.assertRaisesRegex(bump.Refusal, "different commit"):
            self.invoke()
        self.assert_restored()
        self.assertEqual(self.commands.frontend_count, 0)

    def test_raw_blob_identity_preserves_transport_bytes_and_rejects_changes(self):
        original = b'title = "raw"\r\n# bytes\x00\xff'
        oid = blob_oid(original)
        self.assertEqual(bump.checked_git_blob(original, oid), original)
        for altered in [original[:-1], original + b"x", original.replace(b"\r\n", b"\n"),
                        original.decode("latin1"), b""]:
            with self.subTest(altered=altered), self.assertRaises(bump.Refusal):
                bump.checked_git_blob(altered, oid)

    def test_authority_rejects_wrong_blob_before_toml_parser(self):
        key = bump.IR_URL, "Cargo.toml"
        self.commands.tree_entries[key] = f"100644 blob {'a' * 40}\tCargo.toml\0"
        with patch.object(bump, "document") as parse, tempfile.TemporaryDirectory() as temporary:
            authority = bump.Authority(self.commands, Path(temporary) / "ir", bump.IR_URL, NEW_IR)
            with self.assertRaisesRegex(bump.Refusal, "authenticated Git tree"):
                authority.read("Cargo.toml")
            parse.assert_not_called()
        self.assert_restored()

    def test_authority_never_reads_blobs_through_git_show(self):
        self.invoke()
        self.assertFalse(any(argv[0] == self.commands.git and "show" in argv
                             for argv, _, _, _, _ in self.commands.calls))
        ancestors = [argv for argv, _, _, _, _ in self.commands.calls
                     if argv[0] == self.commands.git and argv[1:3] == ["merge-base", "--is-ancestor"]]
        self.assertEqual(len(ancestors), 2)

    def test_authority_uses_exact_agh_namespace_and_no_fetch_head(self):
        self.invoke()
        calls = [argv for argv, _, _, _, _ in self.commands.calls
                 if argv[0] == self.commands.agh and argv[1] == "repo"]
        self.assertEqual([argv[3] for argv in calls],
                         ["alabsystems/trust-ir", "alabsystems/clean"])
        self.assertTrue(all(argv[1:3] == ["repo", "fetch-main"] and argv[-1] == "--blobless" for argv in calls))
        self.assertFalse(any("FETCH_HEAD" in arg for argv, _, _, _, _ in self.commands.calls
                             for arg in argv))

    def test_missing_agh_refuses_without_fallback_or_pin_changes(self):
        self.commands.agh = None
        with self.assertRaisesRegex(bump.Refusal, "Agh is required"):
            self.invoke()
        self.assertFalse(self.commands.fetched)
        self.assertEqual(self.commands.frontend_count, 0)
        self.assert_restored()

    def test_refused_agh_fetch_cannot_install_pins(self):
        self.commands.fail_agh = True
        with self.assertRaisesRegex(bump.Refusal, "Agh operation refused"):
            self.invoke()
        self.assertFalse(self.commands.fetched)
        self.assertEqual(self.commands.frontend_count, 0)
        self.assert_restored()

    def test_git_remote_rewrite_refuses_before_fetch(self):
        self.commands.rewrite = "url.file:///wrong/.insteadof https://github.com/alabsystems/trust-ir\n"
        with self.assertRaisesRegex(bump.Refusal, "URL rewrite"):
            self.invoke()
        self.assertFalse(self.commands.fetched)
        self.assert_restored()

    def test_missing_agh_has_no_raw_git_fallback(self):
        commands = bump.Commands(self.root, self.commands.targo)
        with patch.object(commands, "agh", None), \
                patch.object(commands, "run") as execute:
            with self.assertRaisesRegex(bump.Refusal, "Agh is required"):
                commands.fetch_github(self.root, bump.IR_URL, NEW_IR)
        execute.assert_not_called()
        self.assert_restored()

    def test_unrouted_source_url_refuses_before_network(self):
        for url in ["https://example.invalid/ay.git", "https://github.com/unreviewed/ay.git"]:
            with self.subTest(url=url), tempfile.TemporaryDirectory() as temporary:
                with self.assertRaisesRegex(bump.Refusal, "no routed authority"):
                    bump.Authority(self.commands, Path(temporary) / "objects", url, AY)
        self.assertFalse(self.commands.fetched)
        self.assert_restored()

    def test_target_workspace_version_changes_refuse(self):
        for url, old, new in [(bump.IR_URL, "0.14.0", "0.15.0"),
                              (bump.CLEAN_URL, CLEAN_CURRENT, "0.10.0")]:
            with self.subTest(url=url):
                self.commands = SyntheticCommands(self.root)
                key = url, "Cargo.toml"
                self.commands.documents[key] = self.commands.documents[key].replace(old, new)
                with self.assertRaisesRegex(bump.Refusal, "version move"):
                    self.invoke()
                self.assert_restored()

    def test_target_package_name_and_version_are_checked_in_immutable_source(self):
        key = bump.IR_URL, "crates/trust-ir-giveback/Cargo.toml"
        for old, new in [('name = "trust-ir-giveback"', 'name = "wrong"'),
                         ('version.workspace = true', 'version = "0.15.0"')]:
            with self.subTest(new=new):
                self.commands = SyntheticCommands(self.root)
                self.commands.documents[key] = self.commands.documents[key].replace(old, new)
                with self.assertRaises(bump.Refusal):
                    self.invoke()
                self.assert_restored()

    def test_target_clean_ay_source_version_and_cohort_moves_refuse(self):
        key = bump.CLEAN_URL, "Cargo.toml"
        for old, new in [(AY, "6" * 40), ("0.26.0", "0.27.0"), ("ay-translate", "ay-new")]:
            with self.subTest(new=new):
                self.commands = SyntheticCommands(self.root)
                self.commands.documents[key] = self.commands.documents[key].replace(old, new)
                with self.assertRaisesRegex(bump.Refusal, "AY"):
                    self.invoke()
                self.assert_restored()

    def test_mixed_target_clean_selectors_refuse(self):
        key = bump.IR_URL, "crates/trust-ir/Cargo.toml"
        self.commands.documents[key] = self.commands.documents[key].replace(
            f'rev = "{NEW_CLEAN}"', f'rev = "{NEW_CLEAN}", path = "../clean"')
        with self.assertRaisesRegex(bump.Refusal, "mixed or mutable"):
            self.invoke()
        self.assert_restored()

    def test_unsupported_resolver_package_moves_restore_all_files(self):
        mutations = [
            lambda text: text.replace('name = "third-party"\nversion = "1.0.0"',
                                      'name = "third-party"\nversion = "2.0.0"'),
            lambda text: text + package("new-crate", "1.0.0", "registry+https://example.invalid/index"),
            lambda text: text.replace('name = "trust-ir"\nversion = "0.14.0"',
                                      'name = "trust-ir"\nversion = "0.15.0"'),
            lambda text: text.replace(AY, "6" * 40),
            lambda text: text + package("clean-new", CLEAN_CURRENT,
                                        bump.source(bump.CLEAN_URL, NEW_CLEAN)),
            lambda text: text.replace('source = "' + bump.source(bump.IR_URL, NEW_IR) + '"\n', "", 1),
        ]
        for mutation in mutations:
            with self.subTest(mutation=mutation):
                self.commands = SyntheticCommands(self.root)

                def mutate(step, root):
                    if step == 5:
                        lock = root / bump.LOCKS[0]
                        lock.write_text(mutation(lock.read_text()))

                self.commands.mutate = mutate
                with self.assertRaises(bump.Refusal):
                    self.invoke()
                self.assert_restored()
                self.assertEqual(self.commands.frontend_count, 6)

    def test_guard_and_resolver_cannot_alter_staged_source(self):
        for step in [5, 9, 10, 12, 13, 14, 15]:
            with self.subTest(step=step):
                self.commands = SyntheticCommands(self.root)

                def mutate(actual, root):
                    if actual == step:
                        (root / bump.CACHE).write_text("altered cache authority")

                self.commands.mutate = mutate
                with self.assertRaisesRegex(bump.Refusal, "staged source"):
                    self.invoke()
                self.assert_restored()

    def test_missing_independent_rust_guard_refuses_before_authority_fetch(self):
        (self.root / bump.GUARD).unlink()
        with self.assertRaisesRegex(bump.Refusal, "missing regular file"):
            self.invoke()
        self.assertFalse(self.commands.fetched)
        self.assert_restored()

    def test_missing_inventory_guard_refuses_before_authority_fetch(self):
        for relative, _, _ in bump.INVENTORY_GUARDS:
            with self.subTest(relative=relative):
                self.setUp()
                (self.root / relative).unlink()
                with self.assertRaisesRegex(bump.Refusal, "missing regular file"):
                    self.invoke()
                self.assertFalse(self.commands.fetched)
                self.assert_restored()

    def test_inventory_guard_source_cannot_change_during_the_transaction(self):
        relative = bump.INVENTORY_GUARDS[0][0]

        def mutate(step, root):
            if step == 10:
                (root / relative).write_text("// rewritten while the pins moved\n")

        self.commands.mutate = mutate
        with self.assertRaisesRegex(bump.Refusal, "TrustIR-derived inventory guard changed"):
            self.invoke()
        self.assert_restored()

    def test_missing_must_refuse_corpus_guard_refuses_before_authority_fetch(self):
        (self.root / bump.CORPUS_GUARD).unlink()
        with self.assertRaisesRegex(bump.Refusal, "missing regular file"):
            self.invoke()
        self.assertFalse(self.commands.fetched)
        self.assert_restored()

    def test_corpus_guard_runs_last_on_the_locked_codegen_target(self):
        self.invoke()
        frontend = [argv for argv, _, _, git, _ in self.commands.calls if not git]
        tests = [argv for argv in frontend if argv[1:3] == ["--unverified", "test"]]
        self.assertEqual([argv[3:8] for argv in tests], [
            ["--locked", "-p", "trust-cg-test", "--test", "dependency_authority"],
            ["--locked", "-p", "trust-cg-verify", "--test", "fsym_layout"],
            ["--locked", "-p", "trust-cg-verify", "--test", "fsym_ub_map"],
            ["--locked", "-p", "trust-cg-lower", "--test", "trust_ir_construct_inventory"],
            ["--locked", "-p", "trust-cg-codegen", "--test", "trust_ir_corpus_roundtrip"],
            ["--locked", "-p", "trust-cg-codegen", "--test", "trust_ir_binary_container"],
            ["--locked", "-p", "trust-cg-cli", "--test", "trust_ir_binary_container"],
            ["--locked", "-p", "trust-cg-codegen", "--test", "must_refuse_corpus"],
        ])
        # The roster's order is the run order, so the receipts are read in it.
        self.assertEqual([tuple(argv[5:8:2]) for argv in tests], list(bump.GUARD_TEST_NAMES))
        # The corpus guard is the LAST frontend command of the transaction:
        # nothing runs after it that could move a pin a red corpus refused.
        self.assertEqual(frontend[-1], tests[-1])

    def test_red_corpus_guard_rolls_every_owned_file_back(self):
        self.commands.fail_step = GUARD_STEPS["trust-cg-codegen", "must_refuse_corpus"]
        with self.assertRaisesRegex(bump.Refusal, f"synthetic frontend failure at {self.commands.fail_step}"):
            self.invoke()
        self.assert_restored()
        self.assertEqual(self.commands.frontend_count, FRONTEND_STEPS)

    def test_corpus_guard_source_cannot_change_during_the_transaction(self):
        def mutate(step, root):
            if step == 9:
                (root / bump.CORPUS_GUARD).write_text("// rewritten while the pins moved\n")

        self.commands.mutate = mutate
        with self.assertRaisesRegex(bump.Refusal, "must-refuse corpus guard changed"):
            self.invoke()
        self.assert_restored()

    # --- The conformance fixture guards (LD-84) ----------
    # The moves to 8d304e36 and dc2b8073 completed green while the corpus
    # census and the vendored container fixtures were still cb639776's, and the
    # Linux floor went red (LD-77, LD-81). Each is now a guard of the move.

    def red_guard(self, selected, failing):
        """libtest's exit 101 for one (package, target), as the real runner refuses it."""
        names = bump.GUARD_TEST_NAMES[selected]
        transcript = (f"running {len(names)} tests\n"
                      + "".join(f"test {name} ... {'FAILED' if name == failing else 'ok'}\n"
                                for name in names)
                      + f"\nfailures:\n    {failing}\n\n"
                      f"test result: FAILED. {len(names) - 1} passed; 1 failed; 0 ignored; "
                      "0 measured; 0 filtered out; finished in 0.01s\n")
        self.commands = SyntheticCommands(self.root)
        original = self.commands.run

        def run(argv, **kwargs):
            output = original(argv, **kwargs)
            if "--test" in argv and (argv[argv.index("-p") + 1],
                                     argv[argv.index("--test") + 1]) == selected:
                print(transcript, end="")
                raise bump.Refusal(f"command failed (101): {' '.join(argv)}")
            return output

        self.commands.run = run

    def test_stale_census_or_vendored_fixture_rolls_the_move_back_and_names_the_update(self):
        cases = [
            # LD-77: the target corpus gained a golden; the census still counts the old one.
            (("trust-cg-codegen", "trust_ir_corpus_roundtrip"),
             "corpus_census_and_exception_tables_are_exact", "CENSUS"),
            # A vendored golden the target regenerated (LD-81's certificate_binding).
            (("trust-cg-codegen", "trust_ir_binary_container"),
             "the_vendored_conformance_fixtures_are_the_pinned_corpus_bytes",
             "re-vendor tests/fixtures/trust_ir_binary_container/conformance"),
            # LD-81: the stale certificate_binding bytes no longer compile.
            (("trust-cg-cli", "trust_ir_binary_container"),
             "bare_trust_ir_binary_compiles_like_its_json_twin", "NAMED_REFUSALS"),
        ]
        self.assertEqual([selected for selected, _, _ in cases],
                         [(package, target) for _, package, target, _ in bump.FIXTURE_GUARDS])
        for (selected, failing, hint), (_, _, _, update) in zip(cases, bump.FIXTURE_GUARDS):
            with self.subTest(selected=selected):
                self.output = io.StringIO()
                self.red_guard(selected, failing)
                package, target = selected
                with self.assertRaisesRegex(
                        bump.Refusal, rf"{package} --test {target} is red at the target: "
                        r"command failed \(101\)") as raised:
                    self.invoke()
                message = str(raised.exception)
                self.assertIn(f"update {update}, then re-run the transaction", message)
                self.assertIn(hint, message)
                self.assert_restored()
                output = self.output.getvalue()
                self.assertIn(f"test {failing} ... FAILED", output)
                self.assertIn("restored all eight original files and modes", output)
                self.assertNotIn("Updated TrustIR", output)
                # Nothing after the red guard ran, the must-refuse corpus guard included.
                self.assertEqual(self.commands.frontend_count, GUARD_STEPS[selected] + 1)

    def test_fixture_guard_sources_cannot_change_during_the_transaction(self):
        for relative, package, target, _ in bump.FIXTURE_GUARDS:
            for step in [GUARD_STEPS["trust-cg-test", "dependency_authority"],
                         GUARD_STEPS[package, target]]:
                with self.subTest(relative=relative, step=step):
                    self.setUp()

                    def mutate(actual, root, step=step, relative=relative):
                        if actual == step:
                            (root / relative).write_text("// rewritten while the pins moved\n")

                    self.commands.mutate = mutate
                    with self.assertRaisesRegex(bump.Refusal, "conformance fixture guard changed"):
                        self.invoke()
                    self.assert_restored()
                    self.assertLessEqual(self.commands.frontend_count, GUARD_STEPS[package, target] + 1)

    def test_vendored_fixture_tree_cannot_change_during_the_transaction(self):
        base = Path(bump.VENDORED_FIXTURES)

        def changed(root):
            (root / base / "conformance/b1_scalars.json").write_text("re-vendored mid-run\n")

        def added(root):
            (root / base / "conformance/new_golden.tmbc").write_text("vendored mid-run\n")

        def removed(root):
            (root / base / "pinned_writer/crystal_lane_v49.tmbc").unlink()

        def linked(root):
            path = root / base / "conformance/b1_scalars.tmbc"
            path.unlink()
            path.symlink_to(root / "unrelated-user-work.txt")

        selected = [*(GUARD_STEPS[package, target] for _, package, target, _ in bump.FIXTURE_GUARDS),
                    GUARD_STEPS["trust-cg-codegen", "must_refuse_corpus"]]
        for change in [changed, added, removed, linked]:
            for step in selected:
                with self.subTest(change=change.__name__, step=step):
                    self.setUp()
                    self.commands.mutate = (lambda actual, root, step=step, change=change:
                                            change(root) if actual == step else None)
                    with self.assertRaisesRegex(bump.Refusal,
                                                "vendored conformance fixtures changed|symlink"):
                        self.invoke()
                    self.assert_restored()
                    self.assertNotIn("Updated TrustIR", self.output.getvalue())

    def test_missing_or_linked_fixture_guard_data_refuses_before_authority_fetch(self):
        base = Path(bump.VENDORED_FIXTURES)

        def unlink(relative):
            return lambda: (self.root / relative).unlink()

        def symlinked_file():
            path = self.root / base / "conformance/b1_scalars.json"
            path.unlink()
            path.symlink_to(self.root / "unrelated-user-work.txt")

        def symlinked_directory():
            (self.root / base / "pinned_writer").rename(self.root / "elsewhere")
            (self.root / base / "pinned_writer").symlink_to(self.root / "elsewhere",
                                                              target_is_directory=True)

        def hard_linked():
            os.link(self.root / base / "SOURCE.txt", self.root / "source-alias")

        cases = [*((f"missing {relative}", unlink(relative), "missing regular file")
                   for relative, _, _, _ in bump.FIXTURE_GUARDS),
                 ("missing tree", lambda: (self.root / base).rename(self.root / "moved-away"),
                  "missing guard data directory"),
                 ("symlinked file", symlinked_file, "symlink"),
                 ("symlinked directory", symlinked_directory, "symlink in guard data"),
                 ("hard-linked file", hard_linked, "singly linked")]
        for label, change, message in cases:
            with self.subTest(label=label):
                self.setUp()
                change()
                with self.assertRaisesRegex(bump.Refusal, message):
                    self.invoke()
                self.assertFalse(self.commands.fetched)
                self.assertEqual(self.commands.frontend_count, 0)
                self.assert_restored()

    def test_preinstall_concurrent_source_edit_is_preserved_and_refused(self):
        self.commands.preinstall_change = True
        with self.assertRaisesRegex(bump.Refusal, "changed while"):
            self.invoke()
        self.assertEqual((self.root / bump.CACHE).read_text(), "concurrent source edit")
        self.assertEqual(self.commands.frontend_count, 0)

    def test_owned_parent_symlink_and_file_hardlink_are_refused(self):
        original = self.root / "crates"
        moved = self.root / "elsewhere"
        original.rename(moved)
        original.symlink_to(moved, target_is_directory=True)
        with self.assertRaisesRegex(bump.Refusal, "symlink"):
            self.invoke()
        original.unlink()
        moved.rename(original)
        alias = self.root / "lock-alias"
        os.link(self.root / bump.LOCKS[0], alias)
        with self.assertRaisesRegex(bump.Refusal, "singly linked"):
            self.invoke()
        alias.unlink()
        self.assert_restored()

    def test_no_git_index_or_consumer_repository_mutation_commands(self):
        self.invoke()
        for argv, cwd, _, git, _ in self.commands.calls:
            if git and cwd == self.root:
                self.assertIn(argv[1], ["rev-parse", "ls-files", "status"])
        fetches = list(self.commands.fetched.values())
        self.assertEqual(fetches, [(bump.IR_URL, NEW_IR), (bump.CLEAN_URL, NEW_CLEAN)])

    # --- Named admission of a new TrustIR workspace crate -------------------
    # trust-ir 794227ad added `trust-ir-laws` as a non-dev dependency of
    # trust-ir-build; the unwidened transaction refused that move at the lock
    # cohort check (measured: "Cargo.lock: adding/removing/versioning the
    # trust-ir cohort is unsupported").

    LAWS = "trust-ir-laws"

    def admission_target(self, skip_locks=(), laws_dependencies=("trust-ir",)):
        """A target whose trust-ir-build requires trust-ir-laws; resolver adds the row."""
        self.commands = SyntheticCommands(self.root)
        docs = self.commands.documents
        docs[bump.IR_URL, "Cargo.toml"] = (
            '[workspace]\nmembers = ["crates/trust-ir", "crates/trust-ir-build", '
            '"crates/trust-ir-giveback", "crates/trust-ir-conformance", "crates/trust-ir-laws"]\n'
            '[workspace.package]\nversion = "0.14.0"\n'
            '[workspace.dependencies]\ntrust-ir = { path = "crates/trust-ir" }\n'
            'trust-ir-laws = { path = "crates/trust-ir-laws" }\n')
        key = bump.IR_URL, "crates/trust-ir-build/Cargo.toml"
        docs[key] = docs[key].replace("\n[dev-dependencies]",
                                      "\ntrust-ir-laws = { workspace = true }\n[dev-dependencies]")
        docs[bump.IR_URL, f"crates/{self.LAWS}/Cargo.toml"] = (
            f'[package]\nname = "{self.LAWS}"\nversion.workspace = true\n'
            '[dependencies]\ntrust-ir = { workspace = true }\n')
        lock_at_update = {1: bump.LOCKS[0], 3: bump.LOCKS[1], 5: bump.LOCKS[2]}

        def mutate(step, root):
            lock = lock_at_update.get(step)
            if lock is not None and lock not in skip_locks:
                path = root / lock
                path.write_text(path.read_text() + package(
                    self.LAWS, "0.14.0", bump.source(bump.IR_URL, NEW_IR), laws_dependencies))

        self.commands.mutate = mutate
        return docs

    def test_named_admission_joins_every_requiring_lock_at_the_target_source(self):
        self.admission_target()
        self.invoke(admit=(self.LAWS,))
        after = bump.snapshot(self.root)
        state = bump.current(self.root, after)
        self.assertEqual(state.ir, NEW_IR)
        self.assertEqual(state.ir_packages[self.LAWS], "0.14.0")
        for lock in bump.LOCKS:
            rows = bump.packages(after[lock].data, lock)
            self.assertEqual(bump.cohort(rows, "trust-ir", bump.IR_URL, NEW_IR)[self.LAWS], "0.14.0")
        self.assertIn(f"admitted {self.LAWS}", self.output.getvalue())

    def test_unnamed_new_trust_ir_package_still_refuses_and_restores(self):
        self.admission_target()
        with self.assertRaisesRegex(bump.Refusal, "trust-ir cohort is unsupported"):
            self.invoke()
        self.assert_restored()

    def test_admission_is_bound_to_the_immutable_target_before_any_mutation(self):
        laws = bump.IR_URL, f"crates/{self.LAWS}/Cargo.toml"
        build = bump.IR_URL, "crates/trust-ir-build/Cargo.toml"
        root = bump.IR_URL, "Cargo.toml"
        cases = [
            ("not trust-ir family", ("serde",), None, None, None),
            ("bare trust-ir", ("trust-ir",), None, None, None),
            ("already admitted", ("trust-ir-build",), None, None, None),
            ("duplicate", (self.LAWS, self.LAWS), None, None, None),
            ("not a member", (self.LAWS,), root, '"crates/trust-ir-laws"]', '"crates/other"]'),
            ("renamed", (self.LAWS,), laws, 'name = "trust-ir-laws"', 'name = "other"'),
            ("version move", (self.LAWS,), laws, "version.workspace = true", 'version = "0.15.0"'),
            ("registry edge", (self.LAWS,), laws, "trust-ir = { workspace = true }",
             'trust-ir = { workspace = true }\nrayon = "1.8"'),
            ("git edge", (self.LAWS,), laws, "trust-ir = { workspace = true }",
             f'trust-ir = {dep(bump.CLEAN_URL, NEW_CLEAN, CLEAN_CURRENT)}'),
            ("outside cohort", (self.LAWS,), laws, "trust-ir = { workspace = true }",
             'trust-ir-contract = { path = "../trust-ir-contract" }'),
            ("aliased workspace path", (self.LAWS,), root, 'trust-ir = { path = "crates/trust-ir" }',
             'trust-ir = { path = "crates/elsewhere" }'),
            ("renamed edge", (self.LAWS,), laws, "trust-ir = { workspace = true }",
             'trust-ir = { workspace = true, package = "other" }'),
            ("unrequired", (self.LAWS,), build, "trust-ir-laws = { workspace = true }\n", ""),
            ("dev-only requirement", (self.LAWS,), build,
             "trust-ir-laws = { workspace = true }\n[dev-dependencies]",
             "[dev-dependencies]\ntrust-ir-laws = { workspace = true }"),
        ]
        for label, admit, key, old, new in cases:
            with self.subTest(label=label):
                docs = self.admission_target()
                if key is not None:
                    self.assertIn(old, docs[key])
                    docs[key] = docs[key].replace(old, new, 1)
                with self.assertRaises(bump.Refusal):
                    self.invoke(admit=admit)
                self.assert_restored()
                self.assertEqual(self.commands.frontend_count, 0)

    def test_admitted_lock_rows_are_exact_and_restore_every_file(self):
        cases = [
            ("a requiring lock does not gain it", dict(skip_locks=(bump.LOCKS[1],)),
             "trust-ir cohort is unsupported"),
            ("its lock edge leaves the cohort", dict(laws_dependencies=("third-party",)),
             "depends outside the TrustIR cohort"),
        ]
        for label, options, message in cases:
            with self.subTest(label=label):
                self.admission_target(**options)
                with self.assertRaisesRegex(bump.Refusal, message):
                    self.invoke(admit=(self.LAWS,))
                self.assert_restored()
                self.assertEqual(self.commands.frontend_count, 6)


class DependencyEdgeTests(unittest.TestCase):
    def test_git_qualifier_selects_the_complete_row_and_distinguishes_registry(self):
        qualifier = "git+https://example.invalid/helper.git?rev=" + "a" * 40
        resolved = qualifier + "#" + "b" * 40
        git_row = {"name": "helper", "version": "1.0.0", "source": resolved}
        registry_row = {"name": "helper", "version": "1.0.0", "source": bump.REGISTRY}
        index = bump.package_index([git_row, registry_row])
        for edge in [f"helper 1.0.0 ({qualifier})", f"helper ({qualifier})",
                     f"helper 1.0.0 ({resolved})"]:
            with self.subTest(edge=edge):
                self.assertIs(bump.resolve_edge(edge, index, "graph"), git_row)
                self.assertEqual(git_row["source"], resolved)
        self.assertIs(bump.resolve_edge(f"helper 1.0.0 ({bump.REGISTRY})", index, "graph"),
                      registry_row)
        with self.assertRaisesRegex(bump.Refusal, "ambiguous"):
            bump.resolve_edge("helper 1.0.0", index, "graph")

    def test_git_qualifier_refuses_wrong_fragments_queries_and_ambiguous_commits(self):
        qualifier = "git+https://example.invalid/helper.git?rev=" + "a" * 40
        resolved = qualifier + "#" + "b" * 40
        row = {"name": "helper", "version": "1.0.0", "source": resolved}
        index = bump.package_index([row])
        for requested in [qualifier + "#" + "c" * 40,
                          qualifier.replace("a" * 40, "c" * 40),
                          qualifier.replace("?rev=", "?branch="),
                          qualifier.replace("https://", "ssh://"), bump.REGISTRY]:
            with self.subTest(requested=requested), self.assertRaises(bump.Refusal):
                bump.resolve_edge(f"helper 1.0.0 ({requested})", index, "graph")
        for precise in ["", "b" * 39, "b" * 41, "B" * 40, "b" * 40 + "\n",
                        "b" * 40 + "#" + "c" * 40]:
            with self.subTest(precise=precise), self.assertRaises(bump.Refusal):
                malformed = dict(row, source=qualifier + "#" + precise)
                bump.resolve_edge(f"helper 1.0.0 ({qualifier})",
                                  bump.package_index([malformed]), "graph")
        duplicate_query = dict(row, source=qualifier + "#" + "c" * 40)
        with self.assertRaisesRegex(bump.Refusal, "ambiguous"):
            bump.resolve_edge(f"helper 1.0.0 ({qualifier})",
                              bump.package_index([row, duplicate_query]), "graph")
        registry_with_fragment = dict(row, source=bump.REGISTRY + "#" + "b" * 40)
        with self.assertRaises(bump.Refusal):
            bump.resolve_edge(f"helper 1.0.0 ({bump.REGISTRY})",
                              bump.package_index([registry_with_fragment]), "graph")

    def test_every_actual_owned_lock_dependency_resolves_without_external_commands(self):
        # Three independent locks belong to the eight-file transaction. The
        # report-only historical lock is not a live resolver input or an owner.
        expected = ("Cargo.lock", "crates/rustc-codegen-trust-cg/Cargo.lock", "fuzz/Cargo.lock")
        self.assertEqual(bump.LOCKS, expected)
        root = Path(__file__).resolve().parents[2]
        with patch.object(subprocess, "Popen", side_effect=AssertionError("no external commands")):
            for relative in expected:
                with self.subTest(lock=relative):
                    path = root / relative
                    before = path.read_bytes()
                    rows = bump.packages(before, relative)
                    index = bump.package_index(rows)
                    count = 0
                    for row in rows:
                        for edge in row.get("dependencies", []):
                            selected = bump.resolve_edge(edge, index, relative)
                            self.assertTrue(any(selected is candidate for candidate in index[selected["name"]]))
                            count += 1
                    self.assertGreater(count, 0, "the actual lock must exercise dependency resolution")
                    self.assertEqual(path.read_bytes(), before)


class DriverTests(unittest.TestCase):
    def test_original_fixed_descriptor_and_ancestor_advertisement_survive_the_child(self):
        # Transport DATA only: the child is plain Python, never Targo or an
        # admission consumer. No fixed claim is constructed by this test.
        read_fd, write_fd = os.pipe()
        try:
            commands = bump.Commands(Path("/"), Path("/chosen/targo"))
            with patch.dict(os.environ, {
                "TRUST_FIXED_ADMISSION_FD_V1": str(read_fd),
                "TRUST_FIXED_CLAIM_HANDOFF_V1": "retained ancestor advertisement",
            }, clear=True):
                output = commands.run([sys.executable, "-c",
                    "import os; os.fstat(int(os.environ['TRUST_FIXED_ADMISSION_FD_V1'])); "
                    "print(os.environ['TRUST_FIXED_CLAIM_HANDOFF_V1'])"],
                    cwd=Path("/"), capture=True)
            self.assertEqual(output, "retained ancestor advertisement\n")
        finally:
            os.close(read_fd)
            os.close(write_fd)

    def test_native_nested_fixed_marker_retains_its_opaque_ancestor_data(self):
        # Exact native routing shape, plain Python child only; the original
        # Targo owner remains responsible for authenticating the opaque locator.
        environment = {"TRUST_FIXED_ADMISSION_FD_V1": "requires-live-ancestor-v1",
                       "TRUST_FIXED_CLAIM_HANDOFF_V1": "opaque original ancestor locator"}
        commands = bump.Commands(Path("/"), Path("/chosen/targo"))
        with patch.dict(os.environ, environment, clear=True):
            output = commands.run([sys.executable, "-c",
                "import os,json; print(json.dumps({k:os.environ[k] for k in "
                "('TRUST_FIXED_ADMISSION_FD_V1','TRUST_FIXED_CLAIM_HANDOFF_V1')}))"],
                cwd=Path("/"), capture=True)
        self.assertEqual(json.loads(output), environment)
        for ancestor in [None, ""]:
            invalid = {"TRUST_FIXED_ADMISSION_FD_V1": "requires-live-ancestor-v1"}
            if ancestor is not None:
                invalid["TRUST_FIXED_CLAIM_HANDOFF_V1"] = ancestor
            with self.subTest(ancestor=ancestor), patch.dict(os.environ, invalid, clear=True), \
                    patch.object(subprocess, "Popen") as child:
                with self.assertRaises(bump.Refusal):
                    commands.run([sys.executable, "-c", "raise AssertionError('must not start')"],
                                 cwd=Path("/"))
                child.assert_not_called()

    def test_fixed_descriptor_malformed_or_closed_refuses_before_child(self):
        read_fd, write_fd = os.pipe()
        os.close(read_fd)
        os.close(write_fd)
        for value in ["-1", "not-a-descriptor", "requires-live-ancestor-v2", str(read_fd)]:
            with self.subTest(value=value), patch.dict(os.environ, {
                "TRUST_FIXED_ADMISSION_FD_V1": value,
            }, clear=True), patch.object(subprocess, "Popen") as child:
                with self.assertRaises(bump.Refusal):
                    bump.Commands(Path("/"), Path("/chosen/targo")).run(
                        [sys.executable, "-c", "raise AssertionError('must not start')"], cwd=Path("/"))
                child.assert_not_called()

    def test_isolated_cli_loads_its_exact_sibling_owner_guard(self):
        result = subprocess.run(
            [sys.executable, "-I", "-B", str(Path(bump.__file__).resolve()), "--help"],
            cwd="/", text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("--stage-qualification-ir-source", result.stdout)
        self.assertIn("--qualification-receipt", result.stdout)

    def test_exact_immutable_revision_only(self):
        for value in ["main", NEW_IR[:8], NEW_IR.upper().replace("2", "A"), NEW_IR + "\n", ""]:
            with self.subTest(value=value):
                with self.assertRaises(bump.Refusal):
                    bump.exact_sha(value)
        self.assertEqual(bump.exact_sha(NEW_IR), NEW_IR)

    def test_explicit_targo_selection_has_no_stock_or_path_fallback(self):
        with tempfile.TemporaryDirectory(prefix="test-targo-selection-") as temporary:
            root = Path(temporary)
            targo = root / "targo"
            targo.write_text("synthetic executable, never invoked\n")
            targo.chmod(0o700)
            self.assertEqual(bump.selected_targo(str(targo)), targo.resolve())
            for path in ["targo", str(root / "cargo"), str(root / "missing" / "targo")]:
                with self.subTest(path=path):
                    with self.assertRaises(bump.Refusal):
                        bump.selected_targo(path)
            targo.chmod(0o600)
            with self.assertRaises(bump.Refusal):
                bump.selected_targo(str(targo))
            targo.unlink()
            cargo = root / "cargo"
            cargo.write_text("stock cargo, never invoked\n")
            cargo.chmod(0o700)
            targo.symlink_to(cargo)
            with self.assertRaisesRegex(bump.Refusal, "different executable name"):
                bump.selected_targo(str(targo))

    def test_real_command_runner_preserves_failure_and_cleans_git_routing(self):
        child = Mock(returncode=23)
        child.communicate.return_value = ("misleading success output", None)
        commands = bump.Commands(Path("/tmp"), Path("/chosen/targo"))
        with patch.dict(os.environ, {"GIT_DIR": "/wrong", "GIT_INDEX_FILE": "/wrong-index",
                                     "GIT_CONFIG_COUNT": "1", "GIT_CONFIG_KEY_0": "bad"}):
            with patch.object(subprocess, "Popen", return_value=child) as popen:
                with self.assertRaisesRegex(bump.Refusal, "command failed \\(23\\)"):
                    commands.run(["/chosen/git", "show", "immutable:Cargo.toml"],
                                 cwd=Path("/tmp"), capture=True, git=True)
        environment = popen.call_args.kwargs["env"]
        self.assertNotIn("GIT_DIR", environment)
        self.assertNotIn("GIT_INDEX_FILE", environment)
        self.assertEqual(environment["GIT_CONFIG_GLOBAL"], os.devnull)
        self.assertEqual(environment["GIT_CONFIG_NOSYSTEM"], "1")
        self.assertFalse(any(key.startswith("GIT_CONFIG") and key not in
                             {"GIT_CONFIG_GLOBAL", "GIT_CONFIG_NOSYSTEM"} for key in environment))
        self.assertEqual(environment["GIT_NO_REPLACE_OBJECTS"], "1")
        self.assertEqual(environment["GIT_TERMINAL_PROMPT"], "0")
        self.assertEqual(popen.call_args.args[0][0], "/chosen/git")

    def test_command_interruption_stops_child_before_returning(self):
        child = Mock(pid=424242)
        child.communicate.side_effect = KeyboardInterrupt()
        commands = bump.Commands(Path("/tmp"), Path("/chosen/targo"))
        with patch.object(subprocess, "Popen", return_value=child), patch.object(os, "killpg") as kill:
            with self.assertRaises(KeyboardInterrupt):
                commands.frontend(["metadata", "--format-version", "1"])
        kill.assert_called_once_with(424242, signal.SIGTERM)
        child.wait.assert_called_once_with(timeout=5)

    def test_metadata_discards_json_but_guard_and_update_preserve_stdout(self):
        commands = bump.Commands(Path("/tmp"), Path("/chosen/targo"))
        for args, expected in [(["metadata", "--format-version", "1"], subprocess.DEVNULL),
                               (["update", "-p", "trust-ir"], None),
                               (["--unverified", "test", "--test", "dependency_authority"], None)]:
            with self.subTest(args=args):
                child = Mock(returncode=0)
                child.communicate.return_value = (None, None)
                with patch.object(subprocess, "Popen", return_value=child) as popen:
                    commands.frontend(args)
                self.assertEqual(popen.call_args.kwargs["stdout"], expected)
                self.assertNotIn("stderr", popen.call_args.kwargs)
                self.assertEqual(popen.call_args.args[0], ["/chosen/targo", *args])


class ModuleSurfaceTests(unittest.TestCase):
    def test_every_defined_function_has_a_caller_in_the_transaction(self):
        # The script is a CLI, not a library: nothing outside it imports its
        # functions. A superseded wrapper kept "for compatibility" is an
        # unexercised second admission path, so it is deleted, not retained.
        tree = ast.parse(Path(bump.__file__).read_text())
        defined = {node.name for node in tree.body if isinstance(node, ast.FunctionDef)}
        defined |= {member.name for node in tree.body if isinstance(node, ast.ClassDef)
                    for member in node.body if isinstance(member, ast.FunctionDef)
                    and not member.name.startswith("__")}
        used = {node.id for node in ast.walk(tree) if isinstance(node, ast.Name)}
        used |= {node.attr for node in ast.walk(tree) if isinstance(node, ast.Attribute)}
        self.assertEqual(sorted(defined - used), [])


class SourceCacheAuthorityTests(unittest.TestCase):
    """Real Git objects, mocked Agh responses, no compiler or remote request."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="compiler-pin-cache-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.cache = self.root / "cache"
        self.cache.mkdir()
        self.git("init", "--quiet")
        self.git("config", "user.name", "cache test")
        self.git("config", "user.email", "cache@example.invalid")
        (self.cache / "crates/pkg").mkdir(parents=True)
        (self.cache / "crates/pkg/Cargo.toml").write_bytes(b'[package]\r\nname="pkg"\r\n')
        (self.cache / "link").symlink_to("crates/pkg", target_is_directory=True)
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", "source")
        self.revision = self.git("rev-parse", "HEAD").strip()
        self.commands = bump.Commands(self.root, Path("/unused/targo"), {bump.IR_URL: self.cache})
        self.commands.agh = "/mocked/agh"
        self.real_run = self.commands.run
        self.remote = self.revision
        self.calls = []

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.cache), *args], text=True)

    def intercept(self, argv, **kwargs):
        if argv[0] == self.commands.agh:
            self.calls.append(argv)
            if argv[1:3] == ["repo", "check-local"]:
                return "{}"
            self.assertEqual(argv[1:], ["rev", "alabsystems/trust-ir@" + self.revision,
                                        "--jq", ".sha"])
            return self.remote + "\n"
        return self.real_run(argv, **kwargs)

    def authority(self, label="authority"):
        return bump.Authority(self.commands, self.root / label, bump.IR_URL, self.revision)

    def test_cached_source_is_freshly_authenticated_binary_exact_and_read_only(self):
        refs = self.git("show-ref")
        with patch.object(self.commands, "run", side_effect=self.intercept):
            authority = self.authority()
            self.assertEqual(authority.read("crates/pkg/Cargo.toml")["package"]["name"], "pkg")
            self.assertIsNone(authority.read_optional("absent/Cargo.toml"))
        self.assertEqual(len(self.calls), 2)
        self.assertEqual(self.git("show-ref"), refs)
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_wrong_remote_commit_cannot_authorize_cached_bytes(self):
        self.remote = "0" * 40
        with patch.object(self.commands, "run", side_effect=self.intercept):
            with self.assertRaisesRegex(bump.Refusal, "different source-cache commit"):
                self.authority()

    def test_unavailable_remote_cannot_fall_back_to_cache(self):
        def unavailable(argv, **kwargs):
            if argv[:2] == [self.commands.agh, "rev"]:
                raise bump.Refusal("remote refused")
            return self.intercept(argv, **kwargs)
        with patch.object(self.commands, "run", side_effect=unavailable):
            with self.assertRaisesRegex(bump.Refusal, "remote refused"):
                self.authority()
        self.assertEqual(self.calls[0][1:3], ["repo", "check-local"])

    def test_cached_symlink_ancestor_remains_refused(self):
        with patch.object(self.commands, "run", side_effect=self.intercept):
            authority = self.authority()
            with self.assertRaisesRegex(bump.Refusal, "non-tree ancestor"):
                authority.read("link/Cargo.toml")

    def test_cached_targo_precedence_remains_refused(self):
        (self.cache / "crates/pkg/Targo.toml").write_text('[package]\nname="other"\n')
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", "alternate")
        self.revision = self.git("rev-parse", "HEAD").strip()
        self.remote = self.revision
        with patch.object(self.commands, "run", side_effect=self.intercept):
            authority = self.authority()
            with self.assertRaisesRegex(bump.Refusal, "Targo manifest precedence"):
                authority.read("crates/pkg/Cargo.toml")

    def test_every_consumed_object_kind_is_hash_checked(self):
        real_bytes = self.commands.git_bytes
        for kind in ("commit", "tree", "blob"):
            def changed(args, *, cwd):
                raw = real_bytes(args, cwd=cwd)
                return raw + b"changed" if args[1] == kind else raw
            with self.subTest(kind=kind), patch.object(self.commands, "run", side_effect=self.intercept), \
                    patch.object(self.commands, "git_bytes", side_effect=changed):
                with self.assertRaisesRegex(bump.Refusal, "does not match its immutable identity"):
                    self.authority(kind).read("crates/pkg/Cargo.toml")

    def test_qualification_source_is_exact_read_only_data_without_remote_authority(self):
        refs = self.git("show-ref")
        with patch.object(self.commands, "run", side_effect=self.intercept):
            source = bump.QualificationIrSource(self.commands, self.root / "candidate",
                                                self.cache, self.revision)
            self.assertEqual(source.read("crates/pkg/Cargo.toml")["package"]["name"], "pkg")
        self.assertEqual(self.calls, [])
        self.assertEqual(self.git("show-ref"), refs)
        self.assertEqual(self.git("status", "--porcelain"), "")

    def test_qualification_missing_selected_blob_refuses(self):
        oid = self.git("rev-parse", self.revision + ":crates/pkg/Cargo.toml").strip()
        (self.cache / ".git/objects" / oid[:2] / oid[2:]).unlink()
        with self.assertRaisesRegex(bump.Refusal, "selected source closure is incomplete"):
            bump.QualificationIrSource(self.commands, self.root / "missing",
                                       self.cache, self.revision)
        self.assertEqual(self.calls, [])

    def test_qualification_does_not_require_unselected_historical_blobs(self):
        old = self.git("rev-parse", self.revision + ":crates/pkg/Cargo.toml").strip()
        (self.cache / "crates/pkg/Cargo.toml").write_text('[package]\nname="next"\n')
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", "next")
        self.revision = self.git("rev-parse", "HEAD").strip()
        (self.cache / ".git/objects" / old[:2] / old[2:]).unlink()
        source = bump.QualificationIrSource(self.commands, self.root / "selected-only",
                                            self.cache, self.revision)
        self.assertEqual(source.read("crates/pkg/Cargo.toml")["package"]["name"], "next")

    def test_qualification_missing_commit_ancestry_refuses(self):
        parent = self.revision
        (self.cache / "next").write_text("next")
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", "next")
        self.revision = self.git("rev-parse", "HEAD").strip()
        (self.cache / ".git/objects" / parent[:2] / parent[2:]).unlink()
        with self.assertRaises(bump.Refusal):
            bump.QualificationIrSource(self.commands, self.root / "missing-parent",
                                       self.cache, self.revision)

    def test_qualification_consumed_object_hash_mismatch_refuses(self):
        real_bytes = self.commands.git_bytes
        for kind in ("commit", "tree", "blob"):
            def changed(args, *, cwd):
                raw = real_bytes(args, cwd=cwd)
                return raw + b"changed" if args[1] == kind else raw
            with self.subTest(kind=kind), patch.object(self.commands, "git_bytes", side_effect=changed):
                with self.assertRaisesRegex(bump.Refusal, "does not match its immutable identity"):
                    bump.QualificationIrSource(self.commands, self.root / ("bad-" + kind),
                                               self.cache, self.revision).read("crates/pkg/Cargo.toml")


class QualificationStageTests(unittest.TestCase):
    setUp = TransactionTests.setUp
    write = TransactionTests.write
    assert_restored = TransactionTests.assert_restored
    def test_candidate_stage_retains_every_original_and_makes_no_guard_or_publication_claim(self):
        receipt = self.root / "external-evidence" / "stage.json"
        candidate = self.root / "candidate-ir"
        target = bump.Target(NEW_CLEAN, None, {}, qualification_ir_tree="a" * 40)
        with patch.object(bump, "target_cohort", return_value=target) as prepare, \
                redirect_stdout(self.output), redirect_stderr(self.output):
            bump.transaction(self.root, NEW_IR, self.commands,
                             qualification_ir_source=candidate, qualification_receipt=receipt)
        self.assertEqual(prepare.call_args.kwargs["qualification_ir_source"], candidate)
        # The three locked metadata calls run; none of the eight Rust guards does.
        self.assertEqual(self.commands.frontend_count, 9)
        frontend = [argv for argv, *_ in self.commands.calls
                    if argv[0] == str(self.commands.targo)]
        self.assertEqual(len(frontend), 9)
        self.assertTrue(all("--offline" in argv for argv in frontend))
        record = json.loads(receipt.read_text())
        self.assertFalse(record["publication_authority"])
        self.assertEqual(record["source_role"], "untrusted-candidate-data")
        self.assertEqual(record["rust_guards"], "NOT RUN")
        self.assertIn("QUALIFICATION ONLY", self.output.getvalue())
        self.assertNotIn("All eight files, the Rust authority guard", self.output.getvalue())
        for path, saved in self.original.items():
            original = Path(record["originals"]) / path
            self.assertEqual(original.read_bytes(), saved.data)
            self.assertEqual(original.stat().st_mode & 0o777, saved.mode)

    def test_candidate_source_and_receipt_must_be_explicitly_paired(self):
        with self.assertRaisesRegex(bump.Refusal, "explicitly selected together"):
            bump.transaction(self.root, NEW_IR, self.commands,
                             qualification_ir_source=self.root / "candidate")
        self.assert_restored()

    def test_candidate_stage_cli_exits_three_not_successful_adoption(self):
        with patch.object(bump, "transaction") as transaction, \
                patch.object(bump, "selected_targo", return_value=Path("/chosen/targo")), \
                patch.object(bump, "Commands"):
            status = bump.main([NEW_IR, "--targo", "/chosen/targo",
                                "--stage-qualification-ir-source", str(self.root / "candidate"),
                                "--qualification-receipt", str(self.root / "stage.json")])
        self.assertEqual(status, 3)
        self.assertEqual(transaction.call_args.kwargs["qualification_ir_source"],
                         self.root / "candidate")


class IrVersionMigrationTests(unittest.TestCase):
    setUp = TransactionTests.setUp
    write = TransactionTests.write
    assert_restored = TransactionTests.assert_restored

    def select_minor_release(self):
        self.commands.documents[bump.IR_URL, "Cargo.toml"] = '[workspace.package]\nversion = "0.15.0"\n'
        self.commands.ir_version_move = ("0.14.0", "0.15.0")

    def test_target_version_requires_explicit_selection_before_install(self):
        self.select_minor_release()
        with self.assertRaisesRegex(bump.Refusal, "matching explicit selection"):
            bump.transaction(self.root, NEW_IR, self.commands)
        self.assert_restored()
        self.assertEqual(self.commands.frontend_count, 0)

    def test_explicit_minor_move_preserves_roster_and_all_eight_original_guards(self):
        self.select_minor_release()
        with redirect_stdout(self.output), redirect_stderr(self.output):
            bump.transaction(self.root, NEW_IR, self.commands, ir_version="0.15.0")
        after = bump.current(self.root, bump.snapshot(self.root))
        before = bump.current(self.root, self.original)
        self.assertEqual(set(after.ir_packages), set(before.ir_packages))
        self.assertEqual(set(after.ir_packages.values()), {"0.15.0"})
        self.assertEqual(self.commands.frontend_count, FRONTEND_STEPS)
        updates = [argv for argv, *_ in self.commands.calls if "--precise" in argv]
        self.assertEqual(len(updates), 3)
        self.assertTrue(all(argv[argv.index("-p") + 1] == "trust-ir@0.15.0" for argv in updates))
        guards = [argv for argv, *_ in self.commands.calls if argv[1:3] == ["--unverified", "test"]]
        self.assertEqual([(argv[argv.index("-p") + 1], argv[argv.index("--test") + 1])
                          for argv in guards], list(GUARD_STEPS))

    def test_wrong_workspace_or_member_version_refuses_before_install(self):
        self.select_minor_release()
        for path, text in (("Cargo.toml", '[workspace.package]\nversion = "0.16.0"\n'),
                           ("crates/trust-ir-build/Cargo.toml",
                            '[package]\nname = "trust-ir-build"\nversion = "0.14.0"\n'
                            '[dependencies]\nclean-kernel = ' + dep(
                                bump.CLEAN_URL, NEW_CLEAN, CLEAN_CURRENT))):
            with self.subTest(path=path), patch.dict(self.commands.documents, {(bump.IR_URL, path): text}):
                with self.assertRaises(bump.Refusal):
                    bump.transaction(self.root, NEW_IR, self.commands, ir_version="0.15.0")
                self.assert_restored()
                self.assertEqual(self.commands.frontend_count, 0)

    def test_explicit_manifest_requirements_move_with_the_cohort(self):
        self.select_minor_release()
        for relative in bump.MANIFESTS:
            text = (self.root / relative).read_text().replace(
                f'git = "{bump.IR_URL}"', f'version = "0.14.0", git = "{bump.IR_URL}"')
            self.write(relative, text)
        self.original = bump.snapshot(self.root)
        with redirect_stdout(self.output), redirect_stderr(self.output):
            bump.transaction(self.root, NEW_IR, self.commands, ir_version="0.15.0")
        root = bump.document((self.root / bump.MANIFESTS[0]).read_bytes(), "root")
        bridge = bump.document((self.root / bump.MANIFESTS[1]).read_bytes(), "bridge")
        selected = [root["workspace"]["dependencies"][name]
                    for name in ("trust-ir", "trust-ir-build", "trust-ir-conformance")]
        selected += [bridge[section][name] for section, name in
                     (("dependencies", "trust-ir"), ("dev-dependencies", "trust-ir-build"))]
        self.assertTrue(all(dep["version"] == "0.15.0" and dep["rev"] == NEW_IR
                            for dep in selected))

    def test_unsupported_version_or_split_current_version_refuses(self):
        state = bump.current(self.root, self.original)
        with self.assertRaisesRegex(bump.Refusal, "unsupported TrustIR package-version migration"):
            bump.selected_ir_version(state, "0.16.0")
        split = bump.Current(state.ir, state.clean, state.ay, state.ay_version,
                             {**state.ir_packages, "trust-ir-build": "0.15.0"},
                             state.clean_packages, state.ay_packages)
        with self.assertRaisesRegex(bump.Refusal, "versions disagree"):
            bump.selected_ir_version(split, "0.15.0")

    def test_foreign_same_version_is_not_remapped_and_graph_changes_rollback(self):
        self.select_minor_release()
        for lock in bump.LOCKS:
            with (self.root / lock).open("a") as output:
                output.write(package("foreign-version-peer", "0.14.0", bump.REGISTRY))
        self.original = bump.snapshot(self.root)
        with redirect_stdout(self.output), redirect_stderr(self.output):
            bump.transaction(self.root, NEW_IR, self.commands, ir_version="0.15.0")
        for lock in bump.LOCKS:
            foreign = next(row for row in bump.packages((self.root / lock).read_bytes(), lock)
                           if row["name"] == "foreign-version-peer")
            self.assertEqual(foreign["version"], "0.14.0")
        bump.restore(self.root, self.original)
        self.commands.mutate = lambda _step, _root: (self.root / "Cargo.lock").write_text(
            (self.root / "Cargo.lock").read_text().replace(
                'name = "foreign-version-peer"\nversion = "0.14.0"',
                'name = "foreign-version-peer"\nversion = "0.15.0"'))
        with self.assertRaisesRegex(bump.Refusal, "outside the admitted source cohort"):
            bump.transaction(self.root, NEW_IR, self.commands, ir_version="0.15.0")
        self.assert_restored()

    def test_last_original_guard_failure_restores_every_original_file(self):
        self.select_minor_release()
        self.commands.fail_step = GUARD_STEPS["trust-cg-codegen", "must_refuse_corpus"]
        with self.assertRaises(bump.Refusal):
            bump.transaction(self.root, NEW_IR, self.commands, ir_version="0.15.0")
        self.assert_restored()
        self.assertEqual(self.commands.frontend_count, FRONTEND_STEPS)


class CleanVersionMigrationTests(unittest.TestCase):
    setUp = TransactionTests.setUp
    write = TransactionTests.write
    assert_restored = TransactionTests.assert_restored

    def select_patch_release(self):
        for (url, path), text in list(self.commands.documents.items()):
            if url == bump.CLEAN_URL and path == "Cargo.toml":
                self.commands.documents[url, path] = text.replace(
                    f'version = "{CLEAN_CURRENT}"', f'version = "{CLEAN_TARGET}"')
            elif url == bump.IR_URL:
                self.commands.documents[url, path] = text.replace(CLEAN_CURRENT, CLEAN_TARGET)
        self.commands.clean_version_move = bump.CLEAN_VERSION_MIGRATION

    def test_patch_release_requires_explicit_selection_before_any_install(self):
        self.select_patch_release()
        with self.assertRaisesRegex(bump.Refusal, "Clean version differs from explicit selection"):
            bump.transaction(self.root, NEW_IR, self.commands)
        self.assert_restored()
        self.assertEqual(self.commands.frontend_count, 0)

    def test_explicit_patch_release_preserves_roster_and_runs_all_original_guards(self):
        self.select_patch_release()
        with redirect_stdout(self.output), redirect_stderr(self.output):
            bump.transaction(self.root, NEW_IR, self.commands, clean_version=CLEAN_TARGET)
        result = bump.current(self.root, bump.snapshot(self.root))
        self.assertEqual(set(result.clean_packages), set(bump.current(self.root, self.original).clean_packages))
        self.assertEqual(set(result.clean_packages.values()), {CLEAN_TARGET})
        self.assertEqual(self.commands.frontend_count, FRONTEND_STEPS)
        self.assertIn(f'version = "{CLEAN_TARGET}"', (self.root / bump.VERIFY).read_text())

    def test_wrong_target_patch_version_refuses_despite_explicit_flag(self):
        self.select_patch_release()
        self.commands.documents[bump.CLEAN_URL, "Cargo.toml"] = self.commands.documents[
            bump.CLEAN_URL, "Cargo.toml"].replace(CLEAN_TARGET, CLEAN_UNSUPPORTED)
        with self.assertRaisesRegex(bump.Refusal, "Clean package version move"):
            bump.transaction(self.root, NEW_IR, self.commands, clean_version=CLEAN_TARGET)
        self.assert_restored()

    def test_unsupported_patch_selection_and_foreign_graph_change_refuse(self):
        state = bump.current(self.root, self.original)
        with self.assertRaisesRegex(bump.Refusal, "unsupported Clean package-version migration"):
            bump.selected_clean_version(state, CLEAN_UNSUPPORTED)
        self.select_patch_release()
        self.commands.mutate = lambda _step, _root: (self.root / "Cargo.lock").write_text(
            (self.root / "Cargo.lock").read_text().replace('version = "1.0.0"', 'version = "1.0.1"'))
        with self.assertRaises(bump.Refusal):
            bump.transaction(self.root, NEW_IR, self.commands, clean_version=CLEAN_TARGET)
        self.assert_restored()


class HostileGitAuthorityTests(unittest.TestCase):
    """Actual local Git ancestry, simulated authenticated metadata; no network."""

    def test_grafts_templates_and_namespace_cannot_authorize_an_unrelated_commit(self):
        base = Path(tempfile.gettempdir()) / ".ubd"
        base.mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=base, prefix="pin-hostile-git-") as temporary:
            root = Path(temporary)
            objects = []
            def obj(kind, data):
                raw = kind.encode() + b" " + str(len(data)).encode() + b"\0" + data
                identity = bump.hashlib.sha1(raw).hexdigest()
                objects.append((identity, zlib.compress(raw)))
                return identity
            tree = obj("tree", b"")
            def commit(message):
                return obj("commit", (f"tree {tree}\nauthor Fixture <fixture@example.invalid> 1 +0000\n"
                    f"committer Fixture <fixture@example.invalid> 1 +0000\n\n{message}\n").encode())
            main, unrelated = commit("main"), commit("unrelated")
            template = root / "template"
            (template / "info").mkdir(parents=True)
            graft = template / "info/grafts"
            graft.write_text(f"{main} {unrelated}\n")
            global_config = root / "global-config"
            global_config.write_text(f"[init]\n templateDir = {template}\n")
            class MetadataCommands(bump.Commands):
                def fetch_github(self, directory, url, revision):
                    for identity, data in objects:
                        target = directory / "objects" / identity[:2] / identity[2:]
                        target.parent.mkdir(exist_ok=True)
                        target.write_bytes(data)
                    self.git_run(["update-ref", "refs/agh/fetched-main", main], cwd=directory)
                    self.git_run(["update-ref", "refs/namespaces/evil/refs/agh/fetched-main", unrelated], cwd=directory)
            commands = MetadataCommands(root, root / "unused-targo")
            poisoned = {"GIT_GRAFT_FILE": str(graft), "GIT_TEMPLATE_DIR": str(template),
                        "GIT_CONFIG_GLOBAL": str(global_config), "GIT_NAMESPACE": "evil",
                        "GIT_NO_REPLACE_OBJECTS": "1"}
            with patch.dict(os.environ, poisoned):
                with self.assertRaisesRegex(bump.Refusal, "command failed"):
                    bump.Authority(commands, root / "authority", bump.IR_URL, unrelated)
            self.assertFalse((root / "authority/info/grafts").exists())
            # NO_REPLACE alone is not the protection. The same real Git accepts
            # the forged ancestry when its graft input is explicitly restored.
            control = subprocess.run([commands.git, "merge-base", "--is-ancestor", unrelated,
                                      "refs/agh/fetched-main"], cwd=root / "authority",
                                     env={**os.environ, "GIT_GRAFT_FILE": str(graft),
                                          "GIT_NO_REPLACE_OBJECTS": "1"},
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            self.assertEqual(control.returncode, 0, control.stderr)

    def test_all_git_template_graft_shallow_and_format_inputs_are_scrubbed(self):
        child = Mock(returncode=0)
        child.communicate.return_value = ("", None)
        commands = bump.Commands(Path("/tmp"), Path("/chosen/targo"))
        names = {"GIT_GRAFT_FILE", "GIT_SHALLOW_FILE", "GIT_TEMPLATE_DIR", "GIT_NAMESPACE",
                 "GIT_DEFAULT_HASH", "GIT_DEFAULT_REF_FORMAT", "GIT_CONFIG_SYSTEM"}
        with patch.dict(os.environ, {name: "poison" for name in names}), \
                patch.object(subprocess, "Popen", return_value=child) as popen:
            commands.git_run(["rev-parse", "HEAD"])
        env = popen.call_args.kwargs["env"]
        self.assertFalse(names.intersection(env))
        self.assertEqual(env["GIT_CONFIG_GLOBAL"], os.devnull)
        self.assertEqual(env["GIT_CONFIG_NOSYSTEM"], "1")


class CliRegistryAdmissionTests(unittest.TestCase):
    def test_reviewed_trust_ir_and_clean_versions_reach_transaction_unchanged(self):
        with patch.object(bump, "selected_targo", return_value=Path("/selected/targo")), \
                patch.object(bump, "Commands", return_value=object()), \
                patch.object(bump, "transaction") as transaction:
            result = bump.main([NEW_IR, "--targo", "/selected/targo",
                                "--ir-version", TRUST_IR_TARGET,
                                "--clean-version", CLEAN_TARGET])
        self.assertEqual(result, 0)
        self.assertEqual(transaction.call_args.kwargs["ir_version"], TRUST_IR_TARGET)
        self.assertEqual(transaction.call_args.kwargs["clean_version"], CLEAN_TARGET)

    def test_unreviewed_trust_ir_and_clean_versions_refuse_at_cli_boundary(self):
        for option, version in (("--ir-version", TRUST_IR_UNSUPPORTED),
                                ("--clean-version", CLEAN_UNSUPPORTED)):
            with self.subTest(option=option), patch.object(bump, "transaction") as transaction, \
                    redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as refused:
                bump.main([NEW_IR, "--targo", "/selected/targo", option, version])
            self.assertEqual(refused.exception.code, 2)
            transaction.assert_not_called()

    def test_explicit_guard_interface_reaches_commands_without_fallback(self):
        for selection in ["ordinary", "native-worker", "original-fixed-v1"]:
            with self.subTest(selection=selection), \
                    patch.object(bump, "selected_targo", return_value=Path("/selected/targo")), \
                    patch.object(bump, "Commands") as commands, \
                    patch.object(bump, "transaction") as transaction:
                self.assertEqual(bump.main([NEW_IR, "--targo", "/selected/targo",
                                            "--guard-admission", selection]), 0)
                self.assertEqual(commands.call_args.kwargs, {"guard_admission": selection})
                transaction.assert_called_once()
        for selection in ["fixed", "legacy", "sdk", "", "original-fixed-v2"]:
            with self.subTest(selection=selection), patch.object(bump, "Commands") as commands, \
                    patch.object(bump, "transaction") as transaction, redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as error:
                    bump.main([NEW_IR, "--targo", "/selected/targo", "--guard-admission", selection])
                self.assertEqual(error.exception.code, 2)
                commands.assert_not_called()
                transaction.assert_not_called()

    """Exercise the real main/parser boundary without starting a transaction."""

    def test_named_cfg_aliases_versions_reach_transaction_unchanged(self):
        for selection in ["cfg_aliases@0.2.1", "cfg_aliases@0.2.2"]:
            with self.subTest(selection=selection), \
                    patch.object(bump, "selected_targo", return_value=Path("/selected/targo")), \
                    patch.object(bump, "Commands", return_value=object()), \
                    patch.object(bump, "transaction") as transaction, \
                    patch.object(subprocess, "Popen", side_effect=AssertionError("no external commands")):
                result = bump.main([NEW_IR, "--targo", "/selected/targo",
                                    "--ay-revision", NEW_AY, "--ay-version", "0.28.0",
                                    "--admit-registry-package", "nix@0.29.0",
                                    "--admit-registry-package", selection])
                self.assertEqual(result, 0)
                transaction.assert_called_once()
                self.assertEqual(transaction.call_args.args[-1], ("nix@0.29.0", selection))
                self.assertEqual(transaction.call_args.args[3], NEW_AY)

    def test_unknown_registry_versions_refuse_before_transaction(self):
        for selection in ["cfg_aliases@0.2.3", "cfg_aliases@0.2.20", "nix@0.30.0",
                          "wait-timeout@0.2.2", "foreign@0.2.2"]:
            with self.subTest(selection=selection), \
                    patch.object(bump, "selected_targo") as frontend, \
                    patch.object(bump, "Commands") as commands, \
                    patch.object(bump, "transaction") as transaction, \
                    patch.object(subprocess, "Popen", side_effect=AssertionError("no external commands")), \
                    redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit) as refused:
                    bump.main([NEW_IR, "--targo", "/selected/targo",
                               "--admit-registry-package", selection])
                self.assertEqual(refused.exception.code, 2)
                frontend.assert_not_called()
                commands.assert_not_called()
                transaction.assert_not_called()


if __name__ == "__main__":
    unittest.main()
