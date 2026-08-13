#!/usr/bin/env python3
"""Generate the deterministic production panic-family inventory.

The scanner intentionally has no third-party dependencies.  It masks Rust
comments and literals, removes items whose cfg expression cannot be enabled in
a non-test build, and then inventories the five panic-family spellings owned by
the repository ratchet:

    .unwrap(), .expect(...), panic!(...), unreachable!(...), todo!(...)

`trust-cg-verify` is excluded by the crash-free-codegen policy recorded in the
generated audit.  Test modules/items and rustdoc examples are excluded by the
lexical masking/cfg pass rather than by line-number heuristics, so production
items after an inline `#[cfg(test)]` helper remain visible.  Out-of-line
`tests.rs` / `tests/**` module files are excluded by path, matching Rust's
conventional test-module layout and the documented ratchet scope.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import sys
import tempfile
import unittest
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence


REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_BASELINE = REPO_ROOT / "ratchet" / "unwrap_baseline.json"
DEFAULT_AUDIT = REPO_ROOT / "ratchet" / "panic_audit.md"
EXCLUDED_CRATES = frozenset({"trust-cg-verify"})

SITE_PATTERNS: tuple[tuple[str, re.Pattern[str]], ...] = (
    (".unwrap()", re.compile(r"\.\s*unwrap\s*\(\s*\)")),
    (".expect", re.compile(r"\.\s*expect\s*\(")),
    ("panic!", re.compile(r"(?<![A-Za-z0-9_])panic\s*!\s*[({\[]")),
    ("unreachable!", re.compile(r"(?<![A-Za-z0-9_])unreachable\s*!\s*[({\[]")),
    ("todo!", re.compile(r"(?<![A-Za-z0-9_])todo\s*!\s*[({\[]")),
)


@dataclass(frozen=True, order=True)
class Site:
    file: str
    line: int
    column: int
    kind: str
    snippet: str
    crate: str


@dataclass(frozen=True)
class Annotation:
    category: str
    reason: str


def _blank(out: list[str], start: int, end: int) -> None:
    """Blank one source range while preserving line boundaries and offsets."""

    for index in range(start, end):
        if out[index] not in "\r\n":
            out[index] = " "


def _raw_string_end(source: str, start: int) -> int | None:
    """Return the exclusive end of a Rust raw string beginning at *start*."""

    if source.startswith("br", start):
        prefix_len = 2
    elif source.startswith("r", start):
        prefix_len = 1
    else:
        return None

    if start > 0 and (source[start - 1].isalnum() or source[start - 1] == "_"):
        return None

    cursor = start + prefix_len
    hashes = 0
    while cursor < len(source) and source[cursor] == "#":
        hashes += 1
        cursor += 1
    if cursor >= len(source) or source[cursor] != '"':
        return None

    terminator = '"' + ("#" * hashes)
    end = source.find(terminator, cursor + 1)
    return len(source) if end < 0 else end + len(terminator)


def mask_rust_comments_and_literals(source: str) -> str:
    """Mask comments and literals without changing byte/line positions.

    Rust block comments nest.  Raw strings may contain comment delimiters and
    arbitrary quotes, so they are recognized before ordinary strings.
    Lifetimes are left intact; a single quote is treated as a character literal
    only when a closing quote follows one character (or one escape).
    """

    out = list(source)
    length = len(source)
    cursor = 0
    while cursor < length:
        raw_end = _raw_string_end(source, cursor)
        if raw_end is not None:
            _blank(out, cursor, raw_end)
            cursor = raw_end
            continue

        if source.startswith("//", cursor):
            end = source.find("\n", cursor + 2)
            end = length if end < 0 else end
            _blank(out, cursor, end)
            cursor = end
            continue

        if source.startswith("/*", cursor):
            depth = 1
            end = cursor + 2
            while end < length and depth:
                if source.startswith("/*", end):
                    depth += 1
                    end += 2
                elif source.startswith("*/", end):
                    depth -= 1
                    end += 2
                else:
                    end += 1
            _blank(out, cursor, end)
            cursor = end
            continue

        if source[cursor] == '"':
            end = cursor + 1
            escaped = False
            while end < length:
                char = source[end]
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    end += 1
                    break
                end += 1
            _blank(out, cursor, end)
            cursor = end
            continue

        if source[cursor] == "'":
            end = cursor + 1
            if end < length and source[end] == "\\":
                end += 2
            else:
                end += 1
            if end < length and source[end] == "'":
                end += 1
                _blank(out, cursor, end)
                cursor = end
                continue

        cursor += 1

    return "".join(out)


def _matching_delimiter(source: str, opening: int, left: str, right: str) -> int | None:
    depth = 0
    for cursor in range(opening, len(source)):
        char = source[cursor]
        if char == left:
            depth += 1
        elif char == right:
            depth -= 1
            if depth == 0:
                return cursor
    return None


class _CfgParser:
    """Small cfg parser returning values possible in a non-test build.

    Unknown cfg atoms may be either true or false.  `test` and `doctest` are
    fixed false.  This is a conservative abstraction: an item is removed only
    when true is impossible, so unusual cfg syntax cannot hide production code.
    """

    def __init__(self, text: str) -> None:
        self.tokens = re.findall(r"[A-Za-z_][A-Za-z0-9_]*|[(),=!]", text)
        self.cursor = 0

    def parse(self) -> set[bool]:
        values = self._expr()
        return values if values is not None else {False, True}

    def _expr(self) -> set[bool] | None:
        if self.cursor >= len(self.tokens):
            return None
        name = self.tokens[self.cursor]
        self.cursor += 1
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
            return None

        if self.cursor < len(self.tokens) and self.tokens[self.cursor] == "(":
            self.cursor += 1
            children: list[set[bool]] = []
            while self.cursor < len(self.tokens) and self.tokens[self.cursor] != ")":
                child = self._expr()
                children.append(child if child is not None else {False, True})
                if self.cursor < len(self.tokens) and self.tokens[self.cursor] == ",":
                    self.cursor += 1
                elif self.cursor < len(self.tokens) and self.tokens[self.cursor] != ")":
                    self.cursor += 1
            if self.cursor < len(self.tokens) and self.tokens[self.cursor] == ")":
                self.cursor += 1
            if name == "all":
                values = {True}
                for child in children:
                    values = {left and right for left in values for right in child}
                return values
            if name == "any":
                values = {False}
                for child in children:
                    values = {left or right for left in values for right in child}
                return values
            if name == "not" and len(children) == 1:
                return {not value for value in children[0]}
            return {False, True}

        if self.cursor < len(self.tokens) and self.tokens[self.cursor] == "=":
            self.cursor += 1
            if self.cursor < len(self.tokens):
                self.cursor += 1
        if name in {"test", "doctest"}:
            return {False}
        return {False, True}


def _is_test_only_attribute(attribute: str) -> bool:
    compact = re.sub(r"\s+", "", attribute)
    if compact in {"test", "doctest"} or compact.endswith("::test"):
        return True
    if not compact.startswith("cfg(") or not compact.endswith(")"):
        return False
    possibilities = _CfgParser(compact[4:-1]).parse()
    return True not in possibilities


def _skip_attributes(masked: str, cursor: int) -> int:
    while True:
        whitespace = re.match(r"\s*", masked[cursor:])
        cursor += whitespace.end() if whitespace else 0
        match = re.match(r"#\s*\[", masked[cursor:])
        if not match:
            return cursor
        opening = cursor + match.end() - 1
        closing = _matching_delimiter(masked, opening, "[", "]")
        if closing is None:
            return len(masked)
        cursor = closing + 1


def _annotated_item_end(masked: str, cursor: int) -> int:
    """Find the end of an attributed item conservatively."""

    paren_depth = 0
    bracket_depth = 0
    while cursor < len(masked):
        char = masked[cursor]
        if char == "(":
            paren_depth += 1
        elif char == ")" and paren_depth:
            paren_depth -= 1
        elif char == "[":
            bracket_depth += 1
        elif char == "]" and bracket_depth:
            bracket_depth -= 1
        elif char == "{" and paren_depth == 0 and bracket_depth == 0:
            closing = _matching_delimiter(masked, cursor, "{", "}")
            return len(masked) if closing is None else closing + 1
        elif char == ";" and paren_depth == 0 and bracket_depth == 0:
            return cursor + 1
        cursor += 1
    return len(masked)


def test_only_ranges(masked: str) -> list[tuple[int, int]]:
    ranges: list[tuple[int, int]] = []
    for match in re.finditer(r"#\s*\[", masked):
        opening = match.end() - 1
        closing = _matching_delimiter(masked, opening, "[", "]")
        if closing is None:
            continue
        if not _is_test_only_attribute(masked[opening + 1 : closing]):
            continue
        item_start = _skip_attributes(masked, closing + 1)
        ranges.append((match.start(), _annotated_item_end(masked, item_start)))

    if not ranges:
        return []
    ranges.sort()
    merged = [ranges[0]]
    for start, end in ranges[1:]:
        old_start, old_end = merged[-1]
        if start <= old_end:
            merged[-1] = (old_start, max(old_end, end))
        else:
            merged.append((start, end))
    return merged


def file_is_test_only(masked: str) -> bool:
    """Return whether an inner cfg attribute disables the whole source file."""

    cursor = 1 if masked.startswith("\ufeff") else 0
    if masked.startswith("#!", cursor) and not re.match(r"#!\s*\[", masked[cursor:]):
        newline = masked.find("\n", cursor)
        cursor = len(masked) if newline < 0 else newline + 1

    # Inner crate/module attributes are legal only in this leading attribute
    # sequence.  Looking later in the file would mistake an attribute token
    # inside a macro definition for a file-level cfg and hide production code.
    while True:
        whitespace = re.match(r"\s*", masked[cursor:])
        cursor += whitespace.end() if whitespace else 0
        match = re.match(r"#\s*!\s*\[", masked[cursor:])
        if match is None:
            return False
        opening = cursor + match.end() - 1
        closing = _matching_delimiter(masked, opening, "[", "]")
        if closing is None:
            return False
        if _is_test_only_attribute(masked[opening + 1 : closing]):
            return True
        cursor = closing + 1


def _inside_ranges(position: int, ranges: Sequence[tuple[int, int]]) -> bool:
    # The number of test-only ranges per source file is small; a linear walk is
    # clearer and deterministic, and scanning stops as soon as starts pass us.
    for start, end in ranges:
        if position < start:
            return False
        if start <= position < end:
            return True
    return False


def _line_snippet(source: str, position: int) -> str:
    start = source.rfind("\n", 0, position) + 1
    end = source.find("\n", position)
    if end < 0:
        end = len(source)
    snippet = " ".join(source[start:end].strip().split())
    if len(snippet) > 180:
        snippet = snippet[:177] + "..."
    return snippet


def scan_source(relative_file: str, crate: str, source: str) -> list[Site]:
    masked = mask_rust_comments_and_literals(source)
    if file_is_test_only(masked):
        return []
    excluded = test_only_ranges(masked)
    sites: list[Site] = []
    for kind, pattern in SITE_PATTERNS:
        for match in pattern.finditer(masked):
            if _inside_ranges(match.start(), excluded):
                continue
            line = source.count("\n", 0, match.start()) + 1
            line_start = source.rfind("\n", 0, match.start()) + 1
            sites.append(
                Site(
                    file=relative_file,
                    line=line,
                    column=match.start() - line_start + 1,
                    kind=kind,
                    snippet=_line_snippet(source, match.start()),
                    crate=crate,
                )
            )
    return sorted(sites)


def _package_name(crate_dir: Path) -> str:
    cargo_toml = crate_dir / "Cargo.toml"
    if cargo_toml.is_file():
        in_package = False
        for line in cargo_toml.read_text(encoding="utf-8").splitlines():
            stripped = line.strip()
            if stripped.startswith("["):
                in_package = stripped == "[package]"
                continue
            if in_package:
                match = re.match(r'name\s*=\s*"([^"]+)"', stripped)
                if match:
                    return match.group(1)
    return crate_dir.name


def _resolve_module_file(source_file: Path, module: str, explicit_path: str | None) -> Path | None:
    if explicit_path is not None:
        candidate = (source_file.parent / explicit_path).resolve(strict=False)
        return candidate if candidate.is_file() else None
    module_dir = (
        source_file.parent
        if source_file.name in {"lib.rs", "main.rs", "mod.rs"}
        else source_file.parent / source_file.stem
    )
    for candidate in (module_dir / f"{module}.rs", module_dir / module / "mod.rs"):
        if candidate.is_file():
            return candidate.resolve(strict=False)
    return None


def test_only_module_files(src_dir: Path) -> set[Path]:
    """Discover out-of-line modules attached to a test-only declaration."""

    excluded: set[Path] = set()
    for source_file in sorted(src_dir.rglob("*.rs")):
        source = source_file.read_text(encoding="utf-8")
        masked = mask_rust_comments_and_literals(source)
        for match in re.finditer(r"#\s*\[", masked):
            opening = match.end() - 1
            closing = _matching_delimiter(masked, opening, "[", "]")
            if closing is None or not _is_test_only_attribute(masked[opening + 1 : closing]):
                continue
            item_start = _skip_attributes(masked, closing + 1)
            item_end = _annotated_item_end(masked, item_start)
            declaration = re.search(
                r"\bmod\s+([A-Za-z_][A-Za-z0-9_]*)\s*;",
                masked[item_start:item_end],
            )
            if declaration is None:
                continue
            # A path attribute normally follows cfg(test), as in the workspace's
            # scalar-unroll test module.  Its literal was intentionally masked,
            # so recover it from the same original attribute chain.
            attribute_chain = source[closing + 1 : item_start]
            path_matches = list(
                re.finditer(r'#\s*\[\s*path\s*=\s*"([^"]+)"\s*\]', attribute_chain)
            )
            explicit_path = path_matches[-1].group(1) if path_matches else None
            resolved = _resolve_module_file(source_file, declaration.group(1), explicit_path)
            if resolved is not None:
                excluded.add(resolved)
    return excluded


def inventory(repo_root: Path) -> list[Site]:
    sites: list[Site] = []
    crates_dir = repo_root / "crates"
    for crate_dir in sorted(path for path in crates_dir.iterdir() if path.is_dir()):
        if crate_dir.name in EXCLUDED_CRATES:
            continue
        src_dir = crate_dir / "src"
        if not src_dir.is_dir():
            continue
        crate = _package_name(crate_dir)
        out_of_line_tests = test_only_module_files(src_dir)
        for path in sorted(src_dir.rglob("*.rs")):
            relative_to_src = path.relative_to(src_dir)
            if (
                path.resolve(strict=False) in out_of_line_tests
                or path.name == "tests.rs"
                or "tests" in relative_to_src.parts[:-1]
            ):
                continue
            relative = path.relative_to(repo_root).as_posix()
            source = path.read_text(encoding="utf-8")
            sites.extend(scan_source(relative, crate, source))
    return sorted(sites)


def _split_markdown_row(line: str) -> list[str]:
    cells: list[str] = []
    current: list[str] = []
    escaped = False
    for char in line:
        if escaped:
            current.extend(("\\", char))
            escaped = False
        elif char == "\\":
            escaped = True
        elif char == "|":
            cells.append("".join(current).strip())
            current = []
        else:
            current.append(char)
    cells.append("".join(current).strip())
    if cells and not cells[0]:
        cells.pop(0)
    if cells and not cells[-1]:
        cells.pop()
    return cells


def _unquote_code(value: str) -> str:
    value = value.strip()
    if value.startswith("`") and value.endswith("`"):
        value = value[1:-1]
    return value.replace(r"\|", "|").replace(r"\`", "`").replace(r"\\", "\\")


def _fingerprint(value: str) -> str:
    return " ".join(_unquote_code(value).split())


def load_annotations(audit_path: Path) -> dict[tuple[str, str, str], Annotation]:
    if not audit_path.is_file() or audit_path == Path(os.devnull):
        return {}
    annotations: dict[tuple[str, str, str], Annotation] = {}
    current_file: str | None = None
    for line in audit_path.read_text(encoding="utf-8").splitlines():
        header = re.match(r"^### `([^`]+)`", line)
        if header:
            current_file = header.group(1)
            continue
        if current_file is None or not line.startswith("|"):
            continue
        cells = _split_markdown_row(line)
        if len(cells) != 5 or not cells[0].isdigit() or cells[2] not in {"A", "B", "C", "D"}:
            continue
        kind = _unquote_code(cells[1])
        snippet = _fingerprint(cells[4])
        annotations[(current_file, kind, snippet)] = Annotation(cells[2], cells[3])
    return annotations


def _markdown_escape(value: str) -> str:
    return value.replace("\\", r"\\").replace("|", r"\|").replace("`", r"\`")


def _records_digest(sites: Sequence[Site]) -> str:
    records = [
        {
            "column": site.column,
            "file": site.file,
            "kind": site.kind,
            "line": site.line,
            "snippet": site.snippet,
        }
        for site in sites
    ]
    encoded = json.dumps(records, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return "sha256:" + hashlib.sha256(encoded).hexdigest()


def baseline_document(sites: Sequence[Site]) -> dict[str, object]:
    per_file: dict[str, int] = {}
    per_crate: dict[str, int] = {}
    for site in sites:
        per_file[site.file] = per_file.get(site.file, 0) + 1
        per_crate[site.crate] = per_crate.get(site.crate, 0) + 1
    return {
        "schema_version": 1,
        "generator": "scripts/generate_unwrap_audit.py",
        "scope": "crates/*/src/**/*.rs production code",
        "excluded": [
            "#[cfg(test)]/#[test] items",
            "src/**/tests.rs and src/**/tests/**",
            "comments/literals/rustdoc",
            "trust-cg-verify",
        ],
        "site_inventory_sha256": _records_digest(sites),
        "per_crate": dict(sorted(per_crate.items())),
        "per_file": dict(sorted(per_file.items())),
        "total": len(sites),
    }


def audit_document(sites: Sequence[Site], annotations: dict[tuple[str, str, str], Annotation]) -> str:
    by_crate: dict[str, list[Site]] = {}
    by_file: dict[str, list[Site]] = {}
    for site in sites:
        by_crate.setdefault(site.crate, []).append(site)
        by_file.setdefault(site.file, []).append(site)

    lines = [
        "# Panic / Unwrap Production Audit",
        "",
        "**Author:** Andrew Yates <andrewyates.name@gmail.com>",
        "**Generated by:** `python3 scripts/generate_unwrap_audit.py --write` (deterministic; no timestamp)",
        "**Scope:** `crates/*/src/**` production Rust; comments, literals, rustdoc examples, `tests.rs`/`tests/**` modules, and cfg/test-only items are excluded. `trust-cg-verify` is excluded by policy.",
        "**Parent epic:** #372 · **Inventory issue:** #385",
        "",
        "## Summary",
        "",
        "This document inventories every in-scope `.unwrap()`, `.expect(...)`, `panic!`, `unreachable!`, and `todo!` site. The checked-in baseline is a monotonic per-file ratchet: a new site must be paired with a same-file removal or explicitly audited by regenerating this inventory and justifying the increase.",
        "",
        "| Cat | Meaning | Required handling |",
        "|-----|---------|-------------------|",
        "| A | Invariant guarded by a validated precondition. | Keep only with a precise invariant explanation, or return an error. |",
        "| B | Reachable from malformed/external input. | Convert to a typed `Result`/diagnostic. |",
        "| C | Structurally impossible (for example, immediately after `push`). | Keep with a local explanation. |",
        "| D | Test-only or rustdoc. | Out of scope and normally absent from this generated file. |",
        "",
        "**Baseline file:** `ratchet/unwrap_baseline.json`.",
        "**CI checks:** `scripts/check_unwrap_ratchet.sh` and `scripts/check_panic_clippy.sh`.",
        "**Clippy lint set:** `clippy::unwrap_used`, `clippy::expect_used`, `clippy::panic`, `clippy::unreachable`, and `clippy::todo`.",
        "",
        "## Totals",
        "",
        "| Crate | Production sites |",
        "|-------|-----------------:|",
    ]
    for crate in sorted(by_crate):
        lines.append(f"| `{_markdown_escape(crate)}` | {len(by_crate[crate])} |")
    lines.extend((f"| **Total** | **{len(sites)}** |", ""))

    files_by_crate: dict[str, list[str]] = {}
    for file, file_sites in by_file.items():
        files_by_crate.setdefault(file_sites[0].crate, []).append(file)

    for crate in sorted(files_by_crate):
        lines.extend((f"## Crate: `{_markdown_escape(crate)}`", ""))
        for file in sorted(files_by_crate[crate]):
            file_sites = sorted(by_file[file])
            lines.extend(
                (
                    f"### `{_markdown_escape(file)}` ({len(file_sites)})",
                    "",
                    "| Line | Kind | Cat | Reason | Snippet |",
                    "|-----:|------|:---:|--------|---------|",
                )
            )
            for site in file_sites:
                key = (site.file, site.kind, _fingerprint(site.snippet))
                annotation = annotations.get(
                    key, Annotation("A", "unclassified — manual review pending")
                )
                lines.append(
                    f"| {site.line} | `{_markdown_escape(site.kind)}` | {annotation.category} | "
                    f"{_markdown_escape(annotation.reason)} | `{_markdown_escape(site.snippet)}` |"
                )
            lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def _atomic_write(path: Path, content: str) -> None:
    if path == Path(os.devnull):
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    target_mode = stat.S_IMODE(path.stat().st_mode) if path.exists() else 0o644
    temporary: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="w",
            encoding="utf-8",
            dir=path.parent,
            prefix=f".{path.name}.",
            delete=False,
        ) as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
            temporary = Path(handle.name)
        # NamedTemporaryFile is deliberately private (0600).  Replacing a
        # tracked document without restoring its mode would silently make the
        # generated baseline/audit owner-only.
        os.chmod(temporary, target_mode)
        os.replace(temporary, path)
        temporary = None
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def write_outputs(repo_root: Path, baseline_out: Path, audit_out: Path) -> int:
    sites = inventory(repo_root)
    annotations = load_annotations(DEFAULT_AUDIT)
    baseline = json.dumps(baseline_document(sites), indent=2, sort_keys=True) + "\n"
    audit = audit_document(sites, annotations)
    _atomic_write(baseline_out, baseline)
    _atomic_write(audit_out, audit)
    print(
        f"panic audit: {len(sites)} production sites across "
        f"{len({site.file for site in sites})} files",
        file=sys.stderr,
    )
    return 0


class ScannerSelfTests(unittest.TestCase):
    def scan(self, source: str) -> list[Site]:
        return scan_source("crates/example/src/lib.rs", "example", source)

    def test_masks_comments_literals_raw_strings_and_rustdoc(self) -> None:
        sites = self.scan(
            r'''
            /// example.unwrap(); panic!();
            const S: &str = ".expect(\"no\")";
            const R: &str = r#"todo!(); unreachable!()"#;
            /* nested /* panic!() */ todo!() */
            fn live(x: Option<u8>) { x.unwrap(); }
            '''
        )
        self.assertEqual([site.kind for site in sites], [".unwrap()"])

    def test_excludes_test_items_but_keeps_following_production(self) -> None:
        sites = self.scan(
            """
            #[cfg(test)]
            mod tests { fn bad(x: Option<u8>) { x.unwrap(); panic!(); } }
            #[test]
            fn standalone_test() { todo!(); }
            fn production(x: Result<u8, ()>) { x.expect("live"); }
            """
        )
        self.assertEqual([site.kind for site in sites], [".expect"])

    def test_cfg_abstract_interpretation_is_conservative(self) -> None:
        sites = self.scan(
            """
            #[cfg(all(test, unix))]
            fn test_only() { panic!(); }
            #[cfg(any(test, feature = "shipping"))]
            fn maybe_production() { unreachable!(); }
            #[cfg(not(test))]
            fn production() { todo!(); }
            """
        )
        self.assertEqual([site.kind for site in sites], ["unreachable!", "todo!"])

    def test_counts_multiple_sites_and_nested_block_comments(self) -> None:
        sites = self.scan(
            "fn live(a: Option<u8>, b: Result<u8, ()>) { "
            "a.unwrap(); b.expect(\"b\"); panic! {}; unreachable! []; todo! {\"later\"}; }"
        )
        self.assertEqual(
            [site.kind for site in sites],
            [".unwrap()", ".expect", "panic!", "unreachable!", "todo!"],
        )
        self.assertEqual([site.line for site in sites], [1, 1, 1, 1, 1])

    def test_excludes_file_with_inner_test_cfg(self) -> None:
        sites = self.scan(
            "#![cfg(all(test, unix))]\nfn helper(x: Option<u8>) { x.unwrap(); }\n"
        )
        self.assertEqual(sites, [])

        sites = self.scan(
            "fn live(x: Option<u8>) { quote! { #![cfg(test)] }; x.unwrap(); }\n"
        )
        self.assertEqual([site.kind for site in sites], [".unwrap()"])

    def test_baseline_is_sorted_and_digest_is_stable(self) -> None:
        sites = self.scan("fn live(a: Option<u8>) { a.unwrap(); }")
        left = baseline_document(sites)
        right = baseline_document(list(reversed(sites)))
        self.assertEqual(left, right)
        self.assertTrue(str(left["site_inventory_sha256"]).startswith("sha256:"))

    def test_atomic_write_preserves_or_sets_public_file_mode(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            existing = root / "existing.json"
            existing.write_text("old", encoding="utf-8")
            os.chmod(existing, 0o640)
            _atomic_write(existing, "new\n")
            self.assertEqual(stat.S_IMODE(existing.stat().st_mode), 0o640)
            self.assertEqual(existing.read_text(encoding="utf-8"), "new\n")

            created = root / "created.json"
            _atomic_write(created, "created\n")
            self.assertEqual(stat.S_IMODE(created.stat().st_mode), 0o644)

    def test_inventory_excludes_out_of_line_tests_modules(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            crate = root / "crates" / "example"
            (crate / "src" / "feature").mkdir(parents=True)
            (crate / "Cargo.toml").write_text(
                '[package]\nname = "example"\n', encoding="utf-8"
            )
            (crate / "src" / "lib.rs").write_text(
                "#[cfg(test)]\nmod support;\n"
                "fn live(x: Option<u8>) { x.unwrap(); }\n",
                encoding="utf-8",
            )
            (crate / "src" / "support.rs").write_text(
                "fn test_support(x: Option<u8>) { x.unwrap(); }\n", encoding="utf-8"
            )
            (crate / "src" / "feature" / "tests.rs").write_text(
                "fn test_only(x: Option<u8>) { x.unwrap(); }\n", encoding="utf-8"
            )
            sites = inventory(root)
            self.assertEqual(len(sites), 1)
            self.assertEqual(sites[0].file, "crates/example/src/lib.rs")


def run_self_tests() -> int:
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(ScannerSelfTests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="write baseline and audit outputs")
    parser.add_argument("--baseline-out", type=Path, default=DEFAULT_BASELINE)
    parser.add_argument("--audit-out", type=Path, default=DEFAULT_AUDIT)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--self-test", action="store_true", help="run scanner unit tests")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    if args.self_test:
        return run_self_tests()
    if not args.write:
        print("error: pass --write or --self-test", file=sys.stderr)
        return 2
    return write_outputs(args.repo_root.resolve(), args.baseline_out, args.audit_out)


if __name__ == "__main__":
    raise SystemExit(main())
