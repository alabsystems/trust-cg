"""Committed-source, no-clobber and real compiler controls for VT table export."""

import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "export_vt_tables.py"
SPEC = importlib.util.spec_from_file_location("export_vt_tables", SCRIPT)
EXPORT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(EXPORT)
try:
    # The installed Trust package's trustc; the exporter has no stock default.
    TRUSTC = EXPORT.trust_compiler()
except ValueError:
    TRUSTC = "trustc"


class VtExportTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.directory = Path(self.temporary.name)
        self.repo = self.directory / "repo"
        self.repo.mkdir()
        self.git("init", "--quiet")
        self.git("config", "user.name", "VT export test")
        self.git("config", "user.email", "vt-export@example.invalid")
        sources = {
            "aterm/state.rs": (
                "#[derive(Clone, Copy)] #[repr(u8)] pub enum State { Next = 1 }\n"
                "impl State { pub const COUNT: usize = 14; }\n"
            ),
            "aterm/table/types.rs": (
                "#[derive(Clone, Copy)] #[repr(u8)] pub enum Action { Emit = 7 }\n"
                "#[derive(Clone, Copy)] pub struct Transition {"
                " pub next_state: crate::state::State, pub action: Action }\n"
            ),
            "aterm/table/dcs_osc.rs": "pub const BYTES: usize = 256;\n",
            "aterm/table/mod.rs": (
                "mod types; mod dcs_osc;\n"
                "pub const TRANSITIONS: [[types::Transition; dcs_osc::BYTES]; 14] =\n"
                " [[types::Transition { next_state: crate::state::State::Next,"
                " action: types::Action::Emit }; dcs_osc::BYTES]; 14];\n"
            ),
            "aterm/width.rs": (
                "pub fn char_width(c: char) -> usize { match c as u32 {"
                " 0..=31 => 0, 0x4e00..=0x9fff => 2, _ => 1 } }\n"
            ),
        }
        for source, destination in EXPORT.SOURCES.items():
            path = self.repo / source
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(sources[destination])
        self.commit()

    def git(self, *args):
        return subprocess.run(["git", "-C", str(self.repo), *args], check=True,
                              capture_output=True, text=True).stdout.strip()

    def commit(self):
        self.git("add", ".")
        self.git("-c", "core.hooksPath=/dev/null", "commit", "--quiet", "-m", "fixture")
        self.revision = self.git("rev-parse", "HEAD")

    def test_snapshot_uses_committed_bytes_despite_dirty_worktree(self):
        path = next(iter(EXPORT.SOURCES))
        original = (self.repo / path).read_bytes()
        (self.repo / path).write_text("uncommitted invalid Rust")
        directory = self.directory / "snapshot"
        directory.mkdir()
        commit, evidence = EXPORT.snapshot(self.repo, "HEAD", directory)
        self.assertEqual(commit, self.revision)
        self.assertEqual((directory / EXPORT.SOURCES[path]).read_bytes(), original)
        self.assertEqual(evidence[path]["sha256"], hashlib.sha256(original).hexdigest())
        self.assertEqual((self.repo / path).read_text(), "uncommitted invalid Rust")

    def test_missing_or_symlinked_source_is_rejected(self):
        source = self.repo / next(iter(EXPORT.SOURCES))
        source.unlink()
        self.commit()
        with self.assertRaisesRegex(ValueError, "lacks"):
            EXPORT.snapshot(self.repo, self.revision, self.directory / "missing")
        source.symlink_to("/unavailable/fixture.rs")
        self.commit()
        with self.assertRaisesRegex(ValueError, "ordinary source"):
            EXPORT.snapshot(self.repo, self.revision, self.directory / "symlink")

    def test_revision_must_resolve_to_a_commit(self):
        for revision in ("--help", "missing", "HEAD:crates/aterm-parser/src/state.rs"):
            with self.subTest(revision=revision), self.assertRaises(subprocess.CalledProcessError):
                EXPORT.snapshot(self.repo, revision, self.directory / "invalid")

    def test_real_rust_export_compiles_sources_and_covers_all_inputs(self):
        output = self.directory / "tables.json"
        report = EXPORT.export(self.repo, self.revision, output, TRUSTC)
        value = json.loads(output.read_bytes())
        self.assertEqual(report["aterm_commit"], self.revision)
        self.assertEqual(report["vt_cells"], 14 * 256)
        self.assertEqual(report["tables_sha256"], hashlib.sha256(output.read_bytes()).hexdigest())
        self.assertEqual(value["vt"], [[[1, 7]] * 256] * 14)
        self.assertEqual(value["width_runs"], [
            [0, 31, 0], [32, 0x4dff, 1], [0x4e00, 0x9fff, 2], [0xa000, 0x10ffff, 1],
        ])
        # A dirty implementation cannot be silently attributed to the commit.
        width = self.repo / "crates/aterm-grapheme/src/tables/width.rs"
        width.write_text("compile_error!(\"dirty worktree must not be compiled\");")
        second = self.directory / "second.json"
        again = EXPORT.export(self.repo, self.revision, second, TRUSTC)
        self.assertEqual(output.read_bytes(), second.read_bytes())
        self.assertEqual(report["sources"], again["sources"])

    def test_export_runs_the_compiler_without_the_gate_controls(self):
        # The soundness gate exports TRUST_CG_* controls for its tests, and the
        # Trust compiler refuses to run under any of them.
        controls = {"TRUST_CG_RUN_FORMAL_PROOF_TESTS": "1", "TCG_EXPORT_SELF_TEST": "1"}
        with mock.patch.dict("os.environ", controls):
            report = EXPORT.export(self.repo, self.revision, self.directory / "t.json", TRUSTC)
        self.assertEqual(report["vt_cells"], 14 * 256)

    def test_compilation_failure_does_not_publish_a_dump(self):
        width = self.repo / "crates/aterm-grapheme/src/tables/width.rs"
        width.write_text("compile_error!(\"broken committed implementation\");")
        self.commit()
        output = self.directory / "failed.json"
        with self.assertRaises(subprocess.CalledProcessError):
            EXPORT.export(self.repo, self.revision, output, TRUSTC)
        self.assertFalse(output.exists())

    def test_out_of_range_discriminants_are_not_truncated(self):
        for source, before, after in (
            ("crates/aterm-parser/src/state.rs", "Next = 1", "Next = 256"),
            ("crates/aterm-parser/src/table/types.rs", "Emit = 7", "Emit = 256"),
        ):
            with self.subTest(source=source):
                path = self.repo / source
                original = path.read_text()
                path.write_text(original.replace("repr(u8)", "repr(u16)").replace(before, after))
                self.commit()
                output = self.directory / (path.stem + "-invalid.json")
                with self.assertRaises(subprocess.CalledProcessError):
                    EXPORT.export(self.repo, self.revision, output, TRUSTC)
                self.assertFalse(output.exists())
                path.write_text(original)
                self.commit()

    def test_publication_never_replaces_existing_files_or_symlinks(self):
        path = self.directory / "existing.json"
        path.write_bytes(b"prior evidence")
        with self.assertRaises(FileExistsError):
            EXPORT.publish_new(path, b"replacement")
        self.assertEqual(path.read_bytes(), b"prior evidence")
        link = self.directory / "link.json"
        link.symlink_to(self.directory / "missing-target")
        with self.assertRaises(FileExistsError):
            EXPORT.publish_new(link, b"replacement")
        self.assertTrue(link.is_symlink())
        self.assertFalse(link.exists())
        with self.assertRaisesRegex(ValueError, "refusing to replace"):
            EXPORT.export(self.repo, self.revision, link, "nonexistent-rustc")
        new = self.directory / "new.json"
        EXPORT.publish_new(new, b"complete evidence")
        self.assertEqual(new.read_bytes(), b"complete evidence")
        self.assertFalse(list(self.directory.glob(".*.json.*")))

    def test_dump_validator_rejects_domain_and_identity_mutations(self):
        original = {
            "schema": "aterm.vt-islands.tables", "version": 1,
            "aterm_commit": self.revision, "vt": [[[1, 7]] * 256] * 14,
            "width_runs": [[0, 0x10ffff, 1]],
        }
        self.assertEqual(EXPORT.validate_dump(json.dumps(original).encode(), self.revision), original)
        for key, value in (
            ("aterm_commit", "0" * 40), ("version", True), ("vt", []),
            ("vt", [[[14, 7]] * 256] * 14), ("vt", [[[1, True]] * 256] * 14),
            ("width_runs", [[1, 0x10ffff, 1]]), ("width_runs", [[0, 0x10ffff, 2]]),
            ("width_runs", [[0, 0x10fffe, 1]]), ("width_runs", [[0, 0x110000, 1]]),
        ):
            with self.subTest(key=key, value=str(value)[:80]):
                mutated = copy.deepcopy(original)
                mutated[key] = value
                with self.assertRaises(ValueError):
                    EXPORT.validate_dump(json.dumps(mutated).encode(), self.revision)


if __name__ == "__main__":
    unittest.main()
