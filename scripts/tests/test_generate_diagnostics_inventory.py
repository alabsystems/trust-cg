#!/usr/bin/env python3
"""Positive and fail-closed controls for the generated `[TCG-*]` code census.

Each fixture is a synthetic checkout in a temporary directory; only the final
test reads this repository, and it is skipped where docs/ is withheld.
"""

from __future__ import annotations

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))

import check_documentation  # noqa: E402
import generate_diagnostics_inventory as census  # noqa: E402


DIAG = '''\
pub enum DiagCode {
    Ssa,
    Proof,
    Coverage,
}

impl DiagCode {
    pub const fn as_str(self) -> &'static str {
        match self {
            DiagCode::Ssa => "TCG-SSA-071",
            DiagCode::Proof => "TCG-PROOF-465",
            DiagCode::Coverage => "TCG-COVERAGE-068",
        }
    }

    pub const fn gate(self) -> &'static str {
        match self {
            DiagCode::Ssa => "ssa_loop_complete",
            DiagCode::Proof => "proof_certificates",
            DiagCode::Coverage => "coverage_gate",
        }
    }

    pub const fn what(self) -> &'static str {
        "described elsewhere"
    }

    pub fn prefix(self) -> String {
        format!("[{}] ", self.as_str())
    }
}

pub fn json_enabled() -> bool {
    false
}

/// Returns the `[TCG-SSA-071]`-prefixed message (a doc comment, not a site).
pub fn ssa_message(function: &str, why: &str) -> String {
    let _ = function;
    format!("{}{why}", DiagCode::Ssa.prefix())
}

pub fn gate_message_kv(code: DiagCode, function: &str, why: &str) -> String {
    let _ = function;
    format!("{}{why}", code.prefix())
}

#[cfg(test)]
mod tests {
    #[test]
    fn prefix() {
        assert_eq!(super::DiagCode::Ssa.prefix(), "[TCG-SSA-071] ");
    }
}
'''

LIB = '''\
mod helper;
#[cfg(test)]
mod weld;
use trust_cg_verify::diag::DiagCode;

// [TCG-OLD-TAG] a historical fix tag in a comment.
/* nested /* "[TCG-NESTED]" */ still a comment */
#[cfg_attr(test, derive(Debug))]
struct Marker<'a> {
    text: &'a str,
}

fn lower<'a>(value: &'a str) -> Result<(), String> {
    let quote = '"';
    let brace = '{';
    let escaped = b'\\'';
    let hex = '\\x41';
    let wide = '\\u{1F600}';
    let _ = (value, quote, brace, escaped, hex, wide);
    let raw = r#"[TCG-RAW] a "quoted" raw refusal"#;
    eprintln!("TCG-TRACE-X fired at {raw}");
    if value.is_empty() {
        return Err("[TCG-FOO-BAR] refused: \\
                    the continuation line is not context"
            .to_owned());
    }
    Err(trust_cg_verify::diag::ssa_message("f", "why"))
}

fn classify() -> DiagCode {
    DiagCode::Proof
}

fn wrap() -> String {
    trust_cg_verify::diag::gate_message_kv(classify(), "f", "why")
}

#[cfg(test)]
mod tests {
    #[test]
    fn mentions() {
        assert!("[TCG-TEST-ONLY]".contains("TCG"));
    }
}
'''

HELPER = '''\
pub(crate) fn refuse() -> String {
    format!("[TCG-FOO-BAR] second site")
}
'''

WELD = '''\
// A test-only module file: nothing here is an emission site.
pub fn weld() -> &'static str {
    "[TCG-WELD] never emitted"
}
'''

DOC = f'''\
# Codes

| Code | Gate |
| --- | --- |
| `TCG-SSA-071` | `ssa_loop_complete` |
| `TCG-PROOF-465` | `proof_certificates` |
| `TCG-COVERAGE-068` | `coverage_gate` |

The typed module is the single source of truth; `TCG-SSA-071` is cited here.

{census.BEGIN}
{census.END}

## After
'''

INVENTORY = "| `GlobalAsm` | fail-closed | `x` | Refused with `[TCG-FOO-BAR]`. |\n"


class Fixture:
    def __init__(self, root: Path):
        self.root = root
        self.files = {
            census.TYPED_MODULE: DIAG,
            Path("crates/rustc-codegen-trust-cg/src/lib.rs"): LIB,
            Path("crates/rustc-codegen-trust-cg/src/helper.rs"): HELPER,
            Path("crates/rustc-codegen-trust-cg/src/weld.rs"): WELD,
            census.DOC: DOC,
            Path("rustc-mir-coverage-inventory.md"): INVENTORY,
        }
        for path, text in self.files.items():
            self.write(path, text)

    def write(self, path: Path | str, text: str) -> None:
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def edit(self, path: Path | str, old: str, new: str) -> None:
        target = self.root / path
        text = target.read_text()
        assert text.count(old) == 1, (path, old)
        target.write_text(text.replace(old, new))

    def line_of(self, path: str, needle: str) -> int:
        text = (self.root / path).read_text()
        return text[:text.index(needle)].count("\n") + 1


LIB_PATH = "crates/rustc-codegen-trust-cg/src/lib.rs"


class CensusFixtureTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="tcg-census-")
        self.addCleanup(self.temporary.cleanup)
        self.fixture = Fixture(Path(self.temporary.name))
        self.root = self.fixture.root

    def test_clean_source_unit_is_recorded_and_fails_closed(self) -> None:
        lib = self.root / LIB_PATH
        lib.write_text(lib.read_text() + '\n#[path = "proof.lean"] clean mod proof;\n')
        proof = lib.parent / "proof.lean"
        with self.assertRaisesRegex(census.CensusError, "existing file"):
            census.scan(self.root)
        proof.write_text("theorem identity (n : Nat) : n = n := rfl\n")
        result = census.scan(self.root)
        self.assertEqual(len(result.clean_units), 1)
        self.assertIn("proof.lean", census.render(result))
        digest = result.clean_units[0][2]
        proof.write_text(proof.read_text() + "-- changed\n")
        self.assertNotEqual(digest, census.scan(self.root).clean_units[0][2])
        for text in ["import Hidden\n", '-- [TCG-HIDDEN]\n', '@[extern "hidden"] def hidden : Nat\n']:
            proof.write_text(text)
            with self.assertRaisesRegex(census.CensusError, "unmodeled diagnostic"):
                census.scan(self.root)
        lib.write_text(lib.read_text().replace('proof.lean', '../../../../../../escape.lean'))
        with self.assertRaisesRegex(census.CensusError, "inside the repository"):
            census.scan(self.root)

    def written_block(self) -> str:
        self.assertEqual(census.write_document(self.root), [])
        return census.split_document((self.root / census.DOC).read_text())[1]

    def assert_census_error(self, pattern: str) -> None:
        with self.assertRaisesRegex(census.CensusError, pattern):
            census.scan(self.root)

    # ---- positive controls

    def test_write_then_check_is_current(self) -> None:
        self.written_block()
        self.assertEqual(census.check_errors(self.root), [])

    def test_string_literal_typed_and_helper_sites_are_located(self) -> None:
        block = self.written_block()
        self.assertIn(
            "| `TCG-FOO-BAR` | — | `helper.rs`, `lib.rs` | — | "
            "`[TCG-FOO-BAR] second site` |", block)
        self.assertIn("| `TCG-RAW` | — | `lib.rs` | — | `[TCG-RAW] a \"quoted\" raw refusal` |", block)
        self.assertIn(
            "| `TCG-SSA-071` | `DiagCode::Ssa` (`diag.rs`) | — | `lib.rs` | "
            "typed gate `ssa_loop_complete` |", block)
        self.assertIn(
            "| `TCG-PROOF-465` | `DiagCode::Proof` (`diag.rs`) | — | `lib.rs` | "
            "typed gate `proof_certificates` |", block)
        self.assertIn("- Typed codes with no site in the scanned source: `TCG-COVERAGE-068`.", block)
        self.assertIn("- Codes with an emission site: 4 — 2 typed `DiagCode` codes and "
                      "2 bridge-local string prefixes.", block)

    def test_comments_tests_and_test_only_files_are_not_sites(self) -> None:
        block = self.written_block()
        table = block.split("| --- |", 1)[1].split("\n\n", 1)[0]
        for code in ("TCG-OLD-TAG", "TCG-NESTED", "TCG-TEST-ONLY", "TCG-WELD"):
            self.assertNotIn(f"`{code}`", table, code)
        mentions = next(line for line in block.splitlines() if line.startswith("Bracketed tags"))
        for code in ("TCG-OLD-TAG", "TCG-NESTED", "TCG-TEST-ONLY", "TCG-WELD"):
            self.assertIn(f"`{code}`", mentions, code)
        # diag.rs's own as_str arms and its test module are definitions, not sites.
        self.assertNotIn("`diag.rs`", table.replace("(`diag.rs`)", ""))

    def test_site_references_are_file_level_with_a_count(self) -> None:
        # Line numbers are deliberately not rendered: an edit above a site must
        # not make the census stale. Distinct lines in one file are counted.
        sites = [census.Site("TCG-X", "lib.rs", line, "emit") for line in (40, 7, 7, 12)]
        sites.append(census.Site("TCG-X", "abi.rs", 3, "emit"))
        self.assertEqual(census.refs(sites), "`abi.rs`, `lib.rs` ×3")
        self.assertEqual(census.refs([]), "—")

    def test_unbracketed_labels_are_listed_separately(self) -> None:
        block = self.written_block()
        self.assertIn("`TCG-TRACE-X` (`lib.rs`)", block)
        self.assertNotIn("`TCG-SSA-071` (`diag.rs", block)

    # ---- drift and document controls

    def test_new_emission_site_is_drift(self) -> None:
        self.written_block()
        self.fixture.edit("crates/rustc-codegen-trust-cg/src/helper.rs",
                          "second site", 'second site")\n    + "[TCG-NEW-CODE] added')
        self.assertEqual(census.check_errors(self.root), [census.STALE])

    def test_edited_generated_block_is_drift(self) -> None:
        self.written_block()
        self.fixture.edit(census.DOC, "`TCG-RAW`", "`TCG-RAW-EDITED`")
        self.assertIn(census.STALE, census.check_errors(self.root))

    def test_handwritten_table_must_equal_the_typed_codes(self) -> None:
        self.fixture.edit(census.DOC, "| `TCG-COVERAGE-068` | `coverage_gate` |\n", "")
        self.fixture.edit(census.DOC, "| --- | --- |\n", "| --- | --- |\n| `TCG-FOO-BAR` | bridge |\n")
        errors = census.write_document(self.root)
        self.assertTrue(any("lacks typed code TCG-COVERAGE-068" in error for error in errors), errors)
        self.assertTrue(any("lists TCG-FOO-BAR, which is not a DiagCode variant" in error
                            for error in errors), errors)

    def test_cited_code_without_emission_site_fails(self) -> None:
        self.fixture.write("rustc-mir-coverage-inventory.md",
                           INVENTORY + "| `X` | fail-closed | `[TCG-OLD-TAG]` | stale |\n")
        errors = census.write_document(self.root)
        self.assertEqual(errors, ["rustc-mir-coverage-inventory.md:2: cites TCG-OLD-TAG, which has "
                                  "no emission site and is not a typed DiagCode code"])

    def test_missing_citing_document_fails(self) -> None:
        (self.root / "rustc-mir-coverage-inventory.md").unlink()
        self.assertIn("rustc-mir-coverage-inventory.md: maintained document is missing",
                      census.write_document(self.root))

    def test_markers_must_appear_exactly_once(self) -> None:
        self.fixture.edit(census.DOC, census.END + "\n", "")
        with self.assertRaisesRegex(census.CensusError, "exactly one"):
            census.check_errors(self.root)
        self.fixture.write(census.DOC, DOC.replace(census.BEGIN, census.BEGIN + "\n" + census.BEGIN))
        with self.assertRaisesRegex(census.CensusError, "exactly one"):
            census.check_errors(self.root)

    # ---- fail-closed source forms

    def test_code_outside_literals_and_comments_fails(self) -> None:
        self.fixture.edit(LIB_PATH, "fn classify()", "const TCG_ALIAS: () = (); // ok\nfn classify()")
        census.scan(self.root)  # an identifier using `TCG_` is not a code token
        self.fixture.edit(LIB_PATH, "fn classify()", "macro_call!(TCG-BARE);\nfn classify()")
        self.assert_census_error("outside every string literal")

    def test_computed_or_unclosed_codes_fail(self) -> None:
        self.fixture.edit("crates/rustc-codegen-trust-cg/src/helper.rs",
                          "[TCG-FOO-BAR] second site", "[TCG-{}] second site")
        self.assert_census_error("malformed or computed")
        self.fixture.edit("crates/rustc-codegen-trust-cg/src/helper.rs",
                          "[TCG-{}] second site", "[TCG-FOO-BAR second site")
        self.assert_census_error("not a closed")

    def test_cfg_predicates_mentioning_test_fail(self) -> None:
        pattern = "only an outer #\\[cfg\\(test\\)\\], spelled exactly, is modeled"
        self.fixture.edit(LIB_PATH, "#[cfg(test)]\nmod tests", '#[cfg(any(test, feature = "x"))]\nmod tests')
        self.assert_census_error(pattern)
        # A spacing variant would otherwise leave the test module classified as live.
        self.fixture.edit(LIB_PATH, '#[cfg(any(test, feature = "x"))]\nmod tests', "#[cfg( test )]\nmod tests")
        self.assert_census_error(pattern)
        # An inner attribute would make the whole file test-only without a mod declaration.
        self.fixture.edit(LIB_PATH, "#[cfg( test )]\nmod tests", "#[cfg(test)]\nmod tests")
        self.fixture.write("crates/rustc-codegen-trust-cg/src/helper.rs", "#![cfg(test)]\n" + HELPER)
        self.assert_census_error(pattern)

    def test_cfg_test_on_a_field_or_arm_fails(self) -> None:
        # Left pending, the attribute would mark the next braced item test-only and
        # hide its live emission sites.
        self.fixture.edit(LIB_PATH, "struct Marker<'a> {\n    text",
                          "struct Marker<'a> {\n    #[cfg(test)]\n    probe: u8,\n    text")
        self.assert_census_error("not followed by a braced or `;`-terminated item")
        self.fixture.write(LIB_PATH, LIB.replace(
            "fn classify() -> DiagCode {\n    DiagCode::Proof\n}",
            "fn classify() -> DiagCode {\n    match 0 {\n        #[cfg(test)]\n        1 => DiagCode::Ssa,\n"
            "        _ => DiagCode::Proof,\n    }\n}"))
        self.assert_census_error("not followed by a braced or `;`-terminated item")

    def test_semicolon_inside_a_test_item_signature_keeps_it_test_only(self) -> None:
        self.fixture.edit(LIB_PATH, "#[cfg(test)]\nmod tests {",
                          "#[cfg(test)]\nfn fixture(_bytes: [u8; 4]) -> &'static str {\n"
                          "    \"[TCG-SIGNATURE-TEST]\"\n}\n\n#[cfg(test)]\nmod tests {")
        sites = census.scan(self.root).sites
        self.assertNotIn("TCG-SIGNATURE-TEST", {site.code for site in sites if site.emits})
        self.assertIn(("TCG-SIGNATURE-TEST", "test"), {(site.code, site.kind) for site in sites})

    def test_path_attribute_and_orphan_files_fail(self) -> None:
        self.fixture.write("crates/rustc-codegen-trust-cg/src/orphan.rs", '"[TCG-ORPHAN]"\n')
        self.assert_census_error("not reachable from a module declaration")
        (self.root / "crates/rustc-codegen-trust-cg/src/orphan.rs").unlink()
        self.fixture.edit(LIB_PATH, "mod helper;", '#[path = "helper.rs"]\nmod helper;')
        self.assert_census_error("#\\[path\\]")

    def test_undeclared_module_file_fails(self) -> None:
        self.fixture.edit(LIB_PATH, "mod helper;", "mod helper;\nmod missing;")
        self.assert_census_error("module missing resolves to no scanned file")

    def test_unread_diag_import_forms_fail(self) -> None:
        self.fixture.edit(LIB_PATH, "use trust_cg_verify::diag::DiagCode;",
                          "use trust_cg_verify::diag::{DiagCode, ssa_message};")
        self.assert_census_error("imports from the diag module")

    def test_grouped_or_unknown_variants_fail(self) -> None:
        self.fixture.edit(LIB_PATH, "    DiagCode::Proof\n", "    DiagCode::Nope\n")
        self.assert_census_error("unknown DiagCode variant Nope")
        self.fixture.edit(LIB_PATH, "    DiagCode::Nope\n", "    use DiagCode::*;\n    DiagCode::Proof\n")
        self.assert_census_error("glob or grouped DiagCode")

    def test_unterminated_literals_and_bad_escapes_fail(self) -> None:
        with self.assertRaisesRegex(census.CensusError, "unterminated string"):
            census.lex('fn f() { let s = "open; }')
        with self.assertRaisesRegex(census.CensusError, "unterminated raw string"):
            census.lex('fn f() { let s = r#"open"; }')
        with self.assertRaisesRegex(census.CensusError, "unrecognised char escape"):
            census.lex("fn f() { let c = '\\x4'; }")

    def test_typed_module_structure_is_required(self) -> None:
        self.fixture.edit(census.TYPED_MODULE, 'DiagCode::Coverage => "coverage_gate",\n', "")
        self.assert_census_error("DiagCode::gate has no arm for Coverage")
        self.fixture.write(census.TYPED_MODULE, "pub enum DiagCode {}\n")
        self.assert_census_error("no DiagCode::as_str arms")
        (self.root / census.TYPED_MODULE).unlink()
        self.assert_census_error("typed diagnostic module .* is missing")

    def test_unclassified_diag_function_call_fails(self) -> None:
        self.fixture.edit(LIB_PATH, 'Err(trust_cg_verify::diag::ssa_message("f", "why"))',
                          'Err(trust_cg_verify::diag::mystery_message("f", "why"))')
        self.assert_census_error("unknown diag function mystery_message")
        # A non-emitting public diag function is known and credits nothing.
        self.fixture.edit(LIB_PATH, "diag::mystery_message(", "diag::json_enabled(")
        self.assertNotIn("TCG-SSA-071",
                         {site.code for site in census.scan(self.root).sites if site.emits})

    def test_helper_passed_as_a_value_is_credited_and_unknown_paths_fail(self) -> None:
        self.fixture.edit(LIB_PATH, 'Err(trust_cg_verify::diag::ssa_message("f", "why"))',
                          'Err(("f", "why")).map_err(|(f, w)| (trust_cg_verify::diag::ssa_message)(f, w))')
        line = self.fixture.line_of(LIB_PATH, "diag::ssa_message)")
        typed = [(site.code, site.line) for site in census.scan(self.root).sites if site.kind == "typed"]
        self.assertIn(("TCG-SSA-071", line), typed)
        self.fixture.edit(LIB_PATH, "diag::ssa_message)", "diag::mystery_message)")
        self.assert_census_error("unknown diag function mystery_message")

    def test_delegating_helper_is_credited(self) -> None:
        self.fixture.edit(census.TYPED_MODULE, "pub fn json_enabled() -> bool {",
                          "pub fn ssa_again(function: &str) -> String {\n"
                          "    ssa_message(function, \"again\")\n}\n\npub fn json_enabled() -> bool {")
        self.fixture.edit(LIB_PATH, 'diag::ssa_message("f", "why")', 'diag::ssa_again("f")')
        line = self.fixture.line_of(LIB_PATH, "diag::ssa_again(")
        typed = [(site.code, site.line) for site in census.scan(self.root).sites if site.kind == "typed"]
        self.assertIn(("TCG-SSA-071", line), typed)

    def test_include_and_aliased_diag_code_fail(self) -> None:
        self.fixture.edit(LIB_PATH, "fn classify()", 'include!("generated.rs");\nfn classify()')
        self.assert_census_error("included source is not scanned")
        self.fixture.edit(LIB_PATH, 'include!("generated.rs");\n', "type Code = DiagCode;\n")
        self.assert_census_error("renamed or aliased DiagCode")

    def test_restricted_visibility_helper_is_credited(self) -> None:
        self.fixture.edit(census.TYPED_MODULE, "pub fn json_enabled() -> bool {",
                          "pub(crate) const fn proof_message() -> DiagCode {\n"
                          "    DiagCode::Proof\n}\n\npub fn json_enabled() -> bool {")
        self.fixture.edit(LIB_PATH, "fn classify() -> DiagCode {\n    DiagCode::Proof\n}",
                          "fn classify() -> DiagCode {\n    trust_cg_verify::diag::proof_message()\n}")
        line = self.fixture.line_of(LIB_PATH, "diag::proof_message(")
        typed = [(site.code, site.line) for site in census.scan(self.root).sites if site.kind == "typed"]
        self.assertIn(("TCG-PROOF-465", line), typed)

    def test_helper_naming_two_variants_fails(self) -> None:
        self.fixture.edit(census.TYPED_MODULE, "    format!(\"{}{why}\", DiagCode::Ssa.prefix())",
                          "    let _ = DiagCode::Proof;\n    format!(\"{}{why}\", DiagCode::Ssa.prefix())")
        self.assert_census_error("helper ssa_message names several DiagCode variants")

    # ---- command-line exit codes

    def run_cli(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, str(SCRIPTS / "generate_diagnostics_inventory.py"),
                               "--root", str(self.root), *args],
                              capture_output=True, text=True, check=False)

    def test_cli_exit_codes(self) -> None:
        self.assertEqual(self.run_cli("--check").returncode, 1)  # empty block: stale
        self.assertEqual(self.run_cli("--write").returncode, 0)
        self.assertEqual(self.run_cli("--check").returncode, 0)
        self.fixture.edit(LIB_PATH, "fn classify()", "macro_call!(TCG-BARE);\nfn classify()")
        result = self.run_cli("--check")
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn("diagnostic census failed", result.stderr)


class DocumentationGateTests(unittest.TestCase):
    def test_gate_is_skipped_only_without_docs_directory(self) -> None:
        with tempfile.TemporaryDirectory(prefix="tcg-census-") as temporary:
            root = Path(temporary)
            self.assertEqual(check_documentation.diagnostics_census_errors(root), [])
            (root / "docs").mkdir()
            with self.assertRaisesRegex(ValueError, "missing"):
                check_documentation.diagnostics_census_errors(root)

    def test_gate_reports_drift(self) -> None:
        with tempfile.TemporaryDirectory(prefix="tcg-census-") as temporary:
            fixture = Fixture(Path(temporary))
            self.assertEqual(check_documentation.diagnostics_census_errors(fixture.root), [census.STALE])
            census.write_document(fixture.root)
            self.assertEqual(check_documentation.diagnostics_census_errors(fixture.root), [])


class RepositoryCensusTests(unittest.TestCase):
    @unittest.skipUnless((census.ROOT / "docs").is_dir(), "docs/ is withheld from public snapshots")
    def test_repository_census_is_current(self) -> None:
        self.assertEqual(census.check_errors(census.ROOT), [])


if __name__ == "__main__":
    unittest.main()
