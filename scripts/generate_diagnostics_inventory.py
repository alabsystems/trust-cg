#!/usr/bin/env python3
"""Generate the source-derived `[TCG-*]` diagnostic-code census in docs/diagnostics.md.

Scans the rustc bridge source and the typed diagnostic module for every stable
diagnostic code and records where non-test code emits it: bracketed `[TCG-*]`
string literals, and typed `DiagCode::<Variant>` / `diag::<helper>` uses whose
code comes from `DiagCode::as_str`. The table is written between BEGIN/END
GENERATED markers; `--check` fails on drift, on a hand-written code table that
disagrees with `DiagCode`, and on a maintained document citing a code that has
no emission site. A source form the bounded lexer cannot classify is an error,
never a silent omission. A census row locates where a code is emitted; it is not
evidence that the gate is correct, complete, or reached by any program.
"""

from __future__ import annotations

import argparse
import bisect
import hashlib
from dataclasses import dataclass
from pathlib import Path
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
DOC = Path("docs/diagnostics.md")
TYPED_MODULE = Path("crates/trust-cg-verify/src/diag.rs")
# Maintained documents whose `TCG-*` citations must name a code with an emission
# site (or a typed `DiagCode` code). The generated block itself is excluded.
CITING_DOCS = (DOC, Path("rustc-mir-coverage-inventory.md"))


@dataclass(frozen=True)
class ScanRoot:
    path: Path
    pattern: str
    # The crate root file under `path`, when the whole module tree is scanned:
    # every scanned file must then be reachable through `mod NAME;` declarations,
    # and a module declared under `#[cfg(test)]` makes its file test-only.
    crate_root: str | None


# A site's label is its path relative to its scan root; labels must be unique
# across roots so a file reference is unambiguous.
SCAN_ROOTS = (
    ScanRoot(Path("crates/rustc-codegen-trust-cg/src"), "**/*.rs", "lib.rs"),
    ScanRoot(Path("crates/trust-cg-verify/src"), "diag*.rs", None),
)
BEGIN = ("<!-- BEGIN GENERATED diagnostic code census: "
         "python3 scripts/generate_diagnostics_inventory.py --write -->")
END = "<!-- END GENERATED diagnostic code census -->"
CODE = r"TCG-[A-Z0-9][A-Z0-9_-]*"
BRACKETED = re.compile(rf"\[({CODE})\]")
TOKEN = re.compile(r"TCG-[A-Z0-9_-]*")
CITED = re.compile(rf"\b({CODE})")
TYPED_ARM = re.compile(rf'DiagCode::(\w+)\s*=>\s*"({CODE})"')
GATE_ARM = re.compile(r'DiagCode::(\w+)\s*=>\s*"([^"]+)"')
TYPED_USE = re.compile(r"\bDiagCode::(\w+)")
TYPED_GLOB = re.compile(r"\bDiagCode::\s*[{*]")
# Every `diag::NAME` path in scanned code: `DiagCode` is read by TYPED_USE; any
# other name must be a function of the typed module, whether it is called or
# passed as a value (`map_err(diag::ssa_message)`).
DIAG_PATH = re.compile(r"\bdiag::(\w+)")
HELPER_DEF = re.compile(r"(?ms)^pub(?:\([^)]*\))?[ \t]+(?:const[ \t]+)?fn[ \t]+(\w+)\s*\((.*?)^\}")
USE_DIAG = re.compile(r"\buse\s+[^;]*\bdiag\b[^;]*;")
USE_DIAG_ALLOWED = re.compile(
    r"use\s+(?:crate::|::)?(?:\w+::)*diag(?:::DiagCode|::\{\s*DiagCode\s*,?\s*\})?\s*;")
MOD_DECL = re.compile(r"(?m)^[ \t]*(?:pub(?:\([^)]*\))?[ \t]+)?mod[ \t]+(\w+)[ \t]*;")
PATH_ATTR = re.compile(r"#\s*\[\s*path\b")
# `#[cfg_attr(test, …)]` changes attributes, not which code exists, so only
# `#[cfg(…)]` predicates are policed.
CFG_ATTR = re.compile(r"#\s*(!?)\s*\[\s*cfg\s*\(([^\]]*)\)\s*\]")
# Forms that would hide code from the scan or rename the typed enum.
INCLUDE_MACRO = re.compile(r"\binclude(?:_str|_bytes)?\s*!")
DIAGCODE_ALIAS = re.compile(r"\bDiagCode\s+as\b|\btype\s+\w+[^;=]*=[^;]*\bDiagCode\b")
RAW_STRING_OPEN = re.compile(r'[bc]?r(#*)"')
CFG_TEST = "#[cfg(test)]"
CONTEXT_WIDTH = 100
STALE = (f"{DOC} diagnostic code census is stale; run "
         "python3 scripts/generate_diagnostics_inventory.py --write")


class CensusError(ValueError):
    """The census cannot be computed or the document cannot hold it (exit 2)."""


@dataclass(frozen=True)
class Span:
    start: int
    end: int
    kind: str  # "string" | "comment" | "test"
    close: int = 0  # length of a string literal's closing delimiter


@dataclass(frozen=True)
class Site:
    code: str
    label: str
    line: int
    kind: str  # "emit" (string literal) | "typed" (DiagCode use) | "comment" | "test"
    message: str = ""  # an emit site's literal, first physical line from the code onward

    @property
    def emits(self) -> bool:
        return self.kind in ("emit", "typed")


@dataclass(frozen=True)
class Lexed:
    text: str
    code: str  # `text` with every string literal and comment blanked (newlines kept)
    spans: list[Span]
    starts: list[int]
    tests: list[Span]  # `#[cfg(test)]` items, including `;`-terminated ones
    newlines: list[int]

    def span_at(self, position: int) -> Span | None:
        index = bisect.bisect_right(self.starts, position) - 1
        if index >= 0 and self.spans[index].start <= position < self.spans[index].end:
            return self.spans[index]
        return None

    def in_test(self, position: int) -> bool:
        return any(span.start <= position < span.end for span in self.tests)

    def line(self, position: int) -> int:
        return bisect.bisect_left(self.newlines, position) + 1

    def depth(self, position: int) -> int:
        return self.code.count("{", 0, position) - self.code.count("}", 0, position)


def _ident_before(text: str, i: int) -> bool:
    return i > 0 and (text[i - 1].isalnum() or text[i - 1] == "_")


def lex(text: str, label: str = "<source>") -> Lexed:
    """Classify Rust source into string/comment spans and `#[cfg(test)]` items.

    A bounded lexer: plain/byte/C/raw strings, char literals (with `\\x`, `\\u{}`
    and one-character escapes) distinguished from lifetimes, line and nested
    block comments, and brace depth so the item that follows a `#[cfg(test)]`
    attribute (a `mod tests { … }` block, a test-only fn, or a `;`-terminated
    `mod name;`) is spanned. `(`/`[` nesting is tracked too, so a `;` inside a
    test item's signature or type (`fn t(x: [u8; 4]) { … }`) does not end it.
    A cfg or path attribute it cannot interpret is an error rather than a guess.
    """
    spans: list[Span] = []
    tests: list[Span] = []
    i, n = 0, len(text)
    depth = 0
    nest = 0  # `(` / `[` nesting outside literals and comments
    canonical: set[int] = set()  # offsets of the exact `#[cfg(test)]` spelling
    pending: tuple[int, int, int] | None = None  # (depth, attribute start, nest) awaiting its item
    open_test: tuple[int, int] | None = None  # (start, depth) of an open braced test item

    def unattached(attribute: int) -> None:
        # A #[cfg(test)] on a field, match arm, parameter or expression ends at a `,`
        # or a closing brace; left pending it would claim the next braced item.
        # Inside an already test-only item it changes nothing.
        if open_test is None:
            raise CensusError(f"{label}:{text.count(chr(10), 0, attribute) + 1}: #[cfg(test)] "
                              "is not followed by a braced or `;`-terminated item; the census "
                              "does not model it on a field, arm or expression")
    while i < n:
        c = text[i]
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            spans.append(Span(i, j, "comment"))
            i = j
            continue
        if text.startswith("/*", i):
            j, level = i + 2, 1
            while j < n and level:
                if text.startswith("/*", j):
                    level, j = level + 1, j + 2
                elif text.startswith("*/", j):
                    level, j = level - 1, j + 2
                else:
                    j += 1
            spans.append(Span(i, j, "comment"))
            i = j
            continue
        start, quote = i, c
        if c in "bcr" and not _ident_before(text, i):
            raw = RAW_STRING_OPEN.match(text, i)
            if raw:
                close = '"' + raw.group(1)
                j = text.find(close, raw.end())
                if j < 0:
                    raise CensusError(f"{label}:{text.count(chr(10), 0, i) + 1}: unterminated raw string")
                spans.append(Span(i, j + len(close), "string", len(close)))
                i = j + len(close)
                continue
            if i + 1 < n and (text[i + 1] == '"' and c in "bc" or text[i + 1] == "'" and c == "b"):
                i += 1
                quote = text[i]
        if quote == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            if j >= n:
                raise CensusError(f"{label}:{text.count(chr(10), 0, start) + 1}: unterminated string")
            spans.append(Span(start, j + 1, "string", 1))
            i = j + 1
            continue
        if quote == "'":
            j = i + 1
            if text.startswith("\\", j):
                if text.startswith("u{", j + 1):
                    j = text.find("}", j) + 1
                elif text.startswith("x", j + 1):
                    j += 4
                else:
                    j += 2
                if 0 < j < n and text[j] == "'":
                    spans.append(Span(start, j + 1, "string", 1))
                    i = j + 1
                    continue
                raise CensusError(f"{label}:{text.count(chr(10), 0, start) + 1}: unrecognised char escape")
            if i + 2 < n and text[i + 2] == "'" and text[i + 1] not in "'\n":
                spans.append(Span(start, i + 3, "string", 1))
                i += 3
                continue
            if start != i:
                raise CensusError(f"{label}:{text.count(chr(10), 0, start) + 1}: malformed byte literal")
            i += 1  # a lifetime or label
            continue
        if text.startswith(CFG_TEST, i):
            canonical.add(i)
            if pending is None:
                pending = (depth, i, nest)
            i += len(CFG_TEST)
            continue
        if c in "([":
            nest += 1
        elif c in ")]":
            nest -= 1
        elif c == "{":
            if pending is not None and pending[0] == depth and pending[2] == nest:
                if open_test is None:
                    open_test = (pending[1], depth)
                pending = None
            depth += 1
        elif c == "}":
            depth -= 1
            if open_test is not None and depth == open_test[1]:
                tests.append(Span(open_test[0], i + 1, "test"))
                open_test = None
                pending = None
            elif pending is not None and depth < pending[0]:
                unattached(pending[1])
                pending = None
        elif c == ";" and pending is not None and pending[0] == depth and pending[2] == nest:
            if open_test is None:
                tests.append(Span(pending[1], i + 1, "test"))
            pending = None
        elif c == "," and pending is not None and pending[0] == depth and pending[2] == nest:
            unattached(pending[1])
            pending = None
        i += 1
    if pending is not None:
        unattached(pending[1])
    if open_test is not None:
        raise CensusError(f"{label}: unbalanced braces after a #[cfg(test)] item")
    chars = list(text)
    for span in spans:
        for k in range(span.start, span.end):
            if chars[k] != "\n":
                chars[k] = " "
    code = "".join(chars)
    newlines = [index for index, char in enumerate(text) if char == "\n"]
    lexed = Lexed(text, code, spans, [span.start for span in spans], tests, newlines)
    for match in PATH_ATTR.finditer(code):
        if re.match(r'#\s*\[\s*path\s*=\s*"[A-Za-z0-9_./-]+\.lean"\s*\]\s*clean\s+mod\s+[A-Za-z_]\w*\s*;', text[match.start():]):
            continue
        raise CensusError(f"{label}:{lexed.line(match.start())}: #[path] module attributes are "
                          "not modeled by the census")
    for match in CFG_ATTR.finditer(code):
        inner, predicate = match.group(1), " ".join(match.group(2).split())
        if not re.search(r"\btest\b", predicate):
            continue
        if inner or predicate != "test" or match.start() not in canonical:
            spelling = " ".join(match.group(0).split())
            raise CensusError(f"{label}:{lexed.line(match.start())}: cfg attribute `{spelling}` "
                              "mentions test; only an outer #[cfg(test)], spelled exactly, "
                              "is modeled")
    return lexed


@dataclass(frozen=True)
class TypedModule:
    codes: dict[str, tuple[str, int]]  # code -> (variant, line of its as_str arm)
    gates: dict[str, str]  # variant -> DiagCode::gate
    helpers: dict[str, str]  # single-code helper fn -> variant
    functions: frozenset[str]  # every top-level public fn (helpers, generic, non-emitting)
    arms: frozenset[int]  # offsets of the as_str arm code strings (definitions, not sites)


def parameter_list_end(after_open_paren: str) -> int:
    """Offset of the `)` closing a parameter list whose `(` was just consumed."""
    depth = 1
    for offset, char in enumerate(after_open_paren):
        depth += {"(": 1, ")": -1}.get(char, 0)
        if depth == 0:
            return offset
    raise CensusError(f"{TYPED_MODULE}: unbalanced parameter list")


def typed_module(text: str) -> TypedModule:
    """Read `diag.rs`: its `DiagCode::as_str` codes, gates and single-code helpers.

    Test code and comments are ignored. A helper is a top-level `pub fn` that
    does not take a `DiagCode` argument and names exactly one variant, directly
    or by delegating to other helpers; generic helpers (`gate_message_kv`, …)
    are credited through their `DiagCode::X` argument at the call site instead.
    """
    lexed = lex(text, str(TYPED_MODULE))
    codes: dict[str, tuple[str, int]] = {}
    variants: dict[str, str] = {}
    arms: set[int] = set()
    for match in TYPED_ARM.finditer(text):
        if lexed.in_test(match.start()) or lexed.span_at(match.start()) is not None:
            continue
        variant, code = match.group(1), match.group(2)
        arms.add(match.start(2))
        if code in codes or variant in variants:
            raise CensusError(f"{TYPED_MODULE}:{lexed.line(match.start())}: {code} / "
                              f"DiagCode::{variant} is mapped twice")
        codes[code] = (variant, lexed.line(match.start()))
        variants[variant] = code
    if not codes:
        raise CensusError(f"{TYPED_MODULE}: no DiagCode::as_str arms were found")
    gate_start = text.find("fn gate(self)")
    gate_end = text.find("fn what(self)", gate_start)
    if gate_start < 0 or gate_end < 0:
        raise CensusError(f"{TYPED_MODULE}: DiagCode::gate / DiagCode::what were not found")
    gates = {match.group(1): match.group(2)
             for match in GATE_ARM.finditer(text, gate_start, gate_end)}
    missing = sorted(set(variants) - set(gates))
    if missing:
        raise CensusError(f"{TYPED_MODULE}: DiagCode::gate has no arm for {', '.join(missing)}")
    helpers: dict[str, str] = {}
    functions: set[str] = set()
    undecided: dict[str, tuple[str, int]] = {}  # fn naming no variant -> (body, line)
    for match in HELPER_DEF.finditer(lexed.code):
        if lexed.in_test(match.start()):
            continue
        name, body = match.group(1), match.group(2)
        functions.add(name)
        if "DiagCode" in body[:parameter_list_end(body)]:
            continue  # generic: the call site's DiagCode::X argument is the site
        named = {use.group(1) for use in TYPED_USE.finditer(body)}
        if len(named) > 1:
            raise CensusError(f"{TYPED_MODULE}:{lexed.line(match.start())}: helper {name} names "
                              f"several DiagCode variants ({', '.join(sorted(named))})")
        if named:
            variant = named.pop()
            if variant not in variants:
                raise CensusError(f"{TYPED_MODULE}: helper {name} names unknown DiagCode::{variant}")
            helpers[name] = variant
        else:
            undecided[name] = (body, lexed.line(match.start()))
    # A function that names no variant but calls (or passes) a single-code helper
    # emits that helper's code; resolve delegation chains to a fixed point.
    changed = True
    while changed:
        changed = False
        for name, (body, line) in sorted(undecided.items()):
            if name in helpers:
                continue
            delegated = {helpers[word] for word in re.findall(r"\b(\w+)\b", body)
                         if word in helpers and word != name}
            if len(delegated) > 1:
                raise CensusError(f"{TYPED_MODULE}:{line}: helper {name} delegates to several "
                                  f"DiagCode variants ({', '.join(sorted(delegated))})")
            if delegated:
                helpers[name] = delegated.pop()
                changed = True
    return TypedModule(codes, gates, helpers, frozenset(functions), frozenset(arms))


def module_file(directory: Path, name: str, files: dict[Path, object]) -> Path | None:
    for candidate in (directory / f"{name}.rs", directory / name / "mod.rs"):
        if candidate in files:
            return candidate
    return None


def test_only_files(root: ScanRoot, lexed: dict[Path, Lexed]) -> set[Path]:
    """Walk `mod NAME;` from the crate root; every scanned file must be reached."""
    crate_root = root.path / root.crate_root
    if crate_root not in lexed:
        raise CensusError(f"crate root {crate_root} is missing")
    test_only: set[Path] = set()
    reached = {crate_root}
    queue = [(crate_root, False)]
    while queue:
        path, parent_test = queue.pop()
        if parent_test:
            test_only.add(path)
        source = lexed[path]
        is_mod_rs = path.name in ("lib.rs", "main.rs", "mod.rs")
        directory = path.parent if is_mod_rs else path.parent / path.stem
        for match in MOD_DECL.finditer(source.code):
            if source.depth(match.start()) != 0:
                raise CensusError(f"{path}:{source.line(match.start())}: an out-of-line module "
                                  "declared inside an inline module is not modeled by the census")
            child = module_file(directory, match.group(1), lexed)
            if child is None:
                raise CensusError(f"{path}:{source.line(match.start())}: module "
                                  f"{match.group(1)} resolves to no scanned file")
            if child in reached:
                continue
            reached.add(child)
            queue.append((child, parent_test or source.in_test(match.start())))
    orphans = sorted(str(path) for path in set(lexed) - reached)
    if orphans:
        raise CensusError("scanned files not reachable from a module declaration: "
                          + ", ".join(orphans))
    return test_only


def scan_file(source: Lexed, label: str, test_only: bool, typed: TypedModule,
              defines: bool) -> tuple[list[Site], list[Site]]:
    """Return (code sites, unbracketed `TCG-` label sites) for one file.

    `defines` marks the typed module itself: its `DiagCode::X` references define
    the codes rather than emit them, and its `as_str` arm strings are the
    definitions the "Typed variant" column already cites.
    """
    variants = {variant: code for code, (variant, _) in typed.codes.items()}
    sites: list[Site] = []
    labels: list[Site] = []
    text = source.text
    for match in TOKEN.finditer(text):
        position = match.start()
        line = source.line(position)
        bracketed = position > 0 and text[position - 1] == "[" and text.startswith("]", match.end())
        test = test_only or source.in_test(position)
        span = source.span_at(position)
        if span is None:
            if test:
                continue  # an identifier or macro token in test code emits nothing
            raise CensusError(f"{label}:{line}: {match.group(0)} is outside every string literal "
                              "and comment; the census lexer cannot classify it")
        if span.kind == "comment" or test:
            if bracketed and BRACKETED.fullmatch(text, position - 1, match.end() + 1):
                sites.append(Site(match.group(0), label, line, "test" if test else "comment"))
            continue
        if not re.fullmatch(CODE, match.group(0)):
            raise CensusError(f"{label}:{line}: string literal holds a malformed or computed "
                              f"code `{match.group(0)}`")
        if position > 0 and text[position - 1] == "[" and not bracketed:
            raise CensusError(f"{label}:{line}: `[{match.group(0)}` is not a closed [CODE] prefix")
        if not bracketed:
            if defines and position in typed.arms:
                continue
            labels.append(Site(match.group(0), label, line, "label"))
            continue
        content_end = span.end - span.close
        newline = text.find("\n", position - 1, content_end)
        message = text[position - 1:content_end if newline < 0 else newline].rstrip("\\ ")
        sites.append(Site(match.group(0), label, line, "emit", message))

    def live(position: int) -> bool:
        return not (test_only or source.in_test(position))

    for match in USE_DIAG.finditer(source.code):
        statement = " ".join(match.group(0).split())
        if live(match.start()) and not USE_DIAG_ALLOWED.fullmatch(statement):
            raise CensusError(f"{label}:{source.line(match.start())}: `{statement}` imports from the "
                              "diag module in a form the census does not read")
    for pattern, what in ((INCLUDE_MACRO, "included source is not scanned by the census"),
                          (DIAGCODE_ALIAS, "a renamed or aliased DiagCode is not read by the census")):
        for match in pattern.finditer(source.code):
            if live(match.start()):
                raise CensusError(f"{label}:{source.line(match.start())}: {what}")
    if defines:
        return sites, labels
    helpers = typed.helpers
    for match in TYPED_USE.finditer(source.code):
        if not live(match.start()):
            continue
        name = match.group(1)
        if name not in variants:
            raise CensusError(f"{label}:{source.line(match.start())}: unknown DiagCode variant {name}")
        sites.append(Site(variants[name], label, source.line(match.start()), "typed"))
    for match in DIAG_PATH.finditer(source.code):
        name = match.group(1)
        if name == "DiagCode" or not live(match.start()):
            continue  # `diag::DiagCode::X` is read by TYPED_USE above
        if name in helpers:
            sites.append(Site(variants[helpers[name]], label, source.line(match.start()), "typed"))
        elif name not in typed.functions:
            raise CensusError(f"{label}:{source.line(match.start())}: unknown diag function {name}")
        # else: a generic or non-emitting diag function (gate_message_kv, set_json_enabled, …);
        # a generic one is credited through its DiagCode::X argument.
    for match in TYPED_GLOB.finditer(source.code):
        if live(match.start()):
            raise CensusError(f"{label}:{source.line(match.start())}: glob or grouped DiagCode "
                              "variants are not read by the census")
    return sites, labels


@dataclass(frozen=True)
class Census:
    sites: list[Site]
    labels: list[Site]
    typed: dict[str, tuple[str, int]]
    gates: dict[str, str]
    paths: dict[str, str]  # label -> repo-relative path
    clean_units: tuple[tuple[str, str, str], ...] = ()


def scan(root: Path) -> Census:
    typed_path = root / TYPED_MODULE
    if not typed_path.is_file():
        raise CensusError(f"typed diagnostic module {TYPED_MODULE} is missing")
    typed = typed_module(typed_path.read_text())
    sites: list[Site] = []
    labels: list[Site] = []
    paths: dict[str, str] = {}
    clean_units = []
    for scan_root in SCAN_ROOTS:
        base = root / scan_root.path
        files = sorted(path for path in base.glob(scan_root.pattern) if path.is_file())
        if not files:
            raise CensusError(f"scan root {scan_root.path}/{scan_root.pattern} matched no files")
        lexed = {}
        for path in files:
            relative = path.relative_to(root)
            source = lex(path.read_text(), relative.as_posix())
            lexed[relative] = source
            for attr in PATH_ATTR.finditer(source.code):
                declaration = re.match(r'#\s*\[\s*path\s*=\s*"([A-Za-z0-9_./-]+\.lean)"\s*\]\s*clean\s+mod\s+[A-Za-z_]\w*\s*;', source.text[attr.start():])
                assert declaration is not None  # lex rejects every other path form
                unit = (path.parent / declaration.group(1)).resolve()
                if not unit.is_relative_to(root.resolve()) or not unit.is_file():
                    raise CensusError(f"{relative}: Clean source must be an existing file inside the repository")
                content = unit.read_text()
                if re.search(r"TCG-|\bDiagCode\b|\bdiag\s*::|^\s*(?:public\s+)?import\b|\bextern\b", content, re.MULTILINE):
                    raise CensusError(f"{relative}: Clean source has unmodeled diagnostic vocabulary or dependencies")
                clean_units.append((f"{relative}:{source.line(attr.start())}", unit.relative_to(root.resolve()).as_posix(), hashlib.sha256(unit.read_bytes()).hexdigest()))
        test_only = test_only_files(scan_root, lexed) if scan_root.crate_root else set()
        for relative, source in lexed.items():
            label = relative.relative_to(scan_root.path).as_posix()
            if label in paths:
                raise CensusError(f"scan label {label} names both {paths[label]} and {relative}")
            paths[label] = relative.as_posix()
            file_sites, file_labels = scan_file(source, label, relative in test_only, typed,
                                                relative == TYPED_MODULE)
            sites.extend(file_sites)
            labels.extend(file_labels)
    sites.sort(key=lambda site: (site.label, site.line, site.code))
    labels.sort(key=lambda site: (site.code, site.label, site.line))
    return Census(sites, labels, typed.codes, typed.gates, paths, tuple(sorted(clean_units)))


def cell(text: str) -> str:
    text = " ".join(text.split()).replace("`", "'").replace("|", "\\|")
    if len(text) > CONTEXT_WIDTH:
        text = text[:CONTEXT_WIDTH - 1] + "…"
    return f"`{text}`"


def refs(sites: list[Site]) -> str:
    """File labels with a site count; line numbers would churn on every edit above a site."""
    counts: dict[str, int] = {}
    for label, _ in {(site.label, site.line) for site in sites}:
        counts[label] = counts.get(label, 0) + 1
    return ", ".join(f"`{label}`" + (f" ×{count}" if count > 1 else "")
                     for label, count in sorted(counts.items())) or "—"


def emitted_codes(census: Census) -> set[str]:
    return {site.code for site in census.sites if site.emits}


def render(census: Census) -> str:
    by_code: dict[str, list[Site]] = {}
    for site in census.sites:
        by_code.setdefault(site.code, []).append(site)
    emitted = emitted_codes(census)
    codes = sorted(emitted | set(census.typed))
    typed_emitted = sorted(code for code in census.typed if code in emitted)
    typed_silent = sorted(code for code in census.typed if code not in emitted)
    bridge_local = sorted(code for code in emitted if code not in census.typed)
    mention_only = sorted(set(by_code) - emitted - set(census.typed))
    emit_sites = [site for site in census.sites if site.kind == "emit"]
    typed_sites = [site for site in census.sites if site.kind == "typed"]
    files = sorted({site.label for site in emit_sites + typed_sites})
    roots = ", ".join(f"`{root.path}/{root.pattern}`" for root in SCAN_ROOTS)
    lines = [
        BEGIN, "",
        "Generated by `python3 scripts/generate_diagnostics_inventory.py --write` from",
        "this checkout; `--check` (also run by `python3 scripts/check_documentation.py",
        "--check`) fails on drift. Scope: non-test code under " + roots + ".",
        "A string-literal site is any `[TCG-*]` literal: most are refusal messages, a few are",
        "knob-gated traces, batch-ineligibility reasons or tag constants. A typed site is a",
        f"`DiagCode::<Variant>` use or a use of a single-code `diag::<helper>` of `{TYPED_MODULE}`,",
        "whose `DiagCode::as_str` arm supplies the code. Comment mentions and `#[cfg(test)]` code",
        "are not sites. Codes emitted by other crates (for example `trust-cg-codegen` and",
        "the `trust-cg-verify` post-register-allocation checkers) are outside this scan and",
        "can appear inside a typed gate's message. A row locates where a code is emitted; it",
        "is not evidence that the gate is correct, complete, or reached by any program.", "",
        f"- Codes with an emission site: {len(emitted)} — {len(typed_emitted)} typed `DiagCode` "
        f"codes and {len(bridge_local)} bridge-local string prefixes.",
        f"- Typed codes with no site in the scanned source: "
        + (", ".join(f"`{code}`" for code in typed_silent) or "none") + ".",
        f"- Emission sites: {len(emit_sites)} string-literal and {len(typed_sites)} typed, "
        f"in {len(files)} files.",
        "- File labels: " + "; ".join(f"`{label}` = `{census.paths[label]}`" for label in files) + ".",
        "",
        "| Code | Typed variant | String-literal sites | Typed sites | Context |",
        "| --- | --- | --- | --- | --- |",
    ]
    if census.clean_units:
        lines[lines.index("| Code | Typed variant | String-literal sites | Typed sites | Context |"):lines.index("| Code | Typed variant | String-literal sites | Typed sites | Context |")] = [
            "Clean compilation units referenced by scanned Rust modules are recorded separately;",
            "imports, extern declarations and diagnostic vocabulary in these units are rejected",
            "until modeled by this census. These are source identities, not emission sites.", "",
            *[f"- `{unit}` from `{owner}`; SHA-256 `{digest}`." for owner, unit, digest in census.clean_units], "",
        ]
    typed_label = TYPED_MODULE.name
    for code in codes:
        group = by_code.get(code, [])
        literal = [site for site in group if site.kind == "emit"]
        typed = [site for site in group if site.kind == "typed"]
        if code in census.typed:
            variant, _ = census.typed[code]
            variant_cell = f"`DiagCode::{variant}` (`{typed_label}`)"
            context = f"typed gate `{census.gates[variant]}`"
        else:
            variant_cell = "—"
            # Prefer the first site whose literal continues past the bare code.
            primary = next((site for site in literal if len(site.message) > len(code) + 2), literal[0])
            context = cell(primary.message)
        lines.append(f"| `{code}` | {variant_cell} | {refs(literal)} | {refs(typed)} | {context} |")
    if mention_only:
        mentions = []
        for code in mention_only:
            group = by_code[code]
            first = group[0]
            mentions.append(f"`{code}` ({len(group)}, first in `{first.label}`)")
        lines.extend(["", "Bracketed tags that appear only in comments or `#[cfg(test)]` code, with no "
                      "emission site (count of mentions, file of the first mention): " + "; ".join(mentions) + "."])
    if census.labels:
        grouped: dict[str, list[Site]] = {}
        for site in census.labels:
            grouped.setdefault(site.code, []).append(site)
        labels = [f"`{code}` ({refs(group)})" for code, group in grouped.items()]
        lines.extend(["", "Unbracketed `TCG-*` labels in non-test string literals (trace output, not "
                      "diagnostic codes): " + "; ".join(labels) + "."])
    lines.extend(["", END])
    return "\n".join(lines)


def split_document(text: str) -> tuple[str, str, str]:
    """Return (before, generated block, after); the markers must appear exactly once."""
    for marker in (BEGIN, END):
        if text.count(marker) != 1:
            raise CensusError(f"{DOC} must contain exactly one `{marker}` line")
    begin, end = text.index(BEGIN), text.index(END) + len(END)
    if end < begin:
        raise CensusError(f"{DOC} has the END marker before the BEGIN marker")
    return text[:begin], text[begin:end], text[end:]


HANDWRITTEN_ROW = re.compile(rf"^\| `({CODE})`\s*\|")


def handwritten_table_errors(before: str, after: str, typed: dict[str, tuple[str, int]]) -> list[str]:
    """The hand-written code table is the typed-code table: it must match diag.rs exactly."""
    documented = {match.group(1) for line in (before + after).splitlines()
                  for match in [HANDWRITTEN_ROW.match(line)] if match}
    errors = []
    for code in sorted(set(typed) - documented):
        errors.append(f"{DOC}: hand-written code table lacks typed code {code} "
                      f"(DiagCode::{typed[code][0]}, {TYPED_MODULE}:{typed[code][1]})")
    for code in sorted(documented - set(typed)):
        errors.append(f"{DOC}: hand-written code table lists {code}, which is not a "
                      f"DiagCode variant in {TYPED_MODULE}")
    return errors


def citation_errors(root: Path, census: Census, doc_outside_block: str) -> list[str]:
    """Every `TCG-*` code a maintained document cites must exist in the census."""
    known = emitted_codes(census) | set(census.typed)
    errors = []
    for path in CITING_DOCS:
        if path == DOC:
            text = doc_outside_block
        else:
            if not (root / path).is_file():
                errors.append(f"{path}: maintained document is missing")
                continue
            text = (root / path).read_text()
        for number, line in enumerate(text.splitlines(), 1):
            for match in CITED.finditer(line):
                if match.group(1) not in known:
                    errors.append(f"{path}:{number}: cites {match.group(1)}, which has no emission "
                                  "site and is not a typed DiagCode code")
    return errors


def generate(root: Path) -> str:
    return render(scan(root))


def read_document(root: Path) -> str:
    path = root / DOC
    if not path.is_file():
        raise CensusError(f"{DOC} is missing")
    return path.read_text()


def check_errors(root: Path) -> list[str]:
    """Drift, hand-written-table and citation errors for a checkout (empty when current)."""
    before, block, after = split_document(read_document(root))
    census = scan(root)
    errors = [] if block == render(census) else [STALE]
    errors += handwritten_table_errors(before, after, census.typed)
    return errors + citation_errors(root, census, before + after)


def write_document(root: Path) -> list[str]:
    """Rewrite the generated block; returns the table and citation errors that remain."""
    before, _, after = split_document(read_document(root))
    census = scan(root)
    (root / DOC).write_text(before + render(census) + after)
    return (handwritten_table_errors(before, after, census.typed)
            + citation_errors(root, census, before + after))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="checkout to scan (default: this repository)")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true", help=f"regenerate the census block in {DOC}")
    mode.add_argument("--print", action="store_true", help="print the regenerated census block")
    mode.add_argument("--check", action="store_true", help="fail when the census block is stale (default)")
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        if args.print:
            print(generate(root))
            return 0
        if args.write:
            errors = write_document(root)
            print(f"Regenerated the diagnostic code census in {DOC}.")
        else:
            errors = check_errors(root)
    except (OSError, ValueError) as error:
        print(f"diagnostic census failed: {error}", file=sys.stderr)
        return 2
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    if not args.write:
        print(f"Diagnostic code census in {DOC} is current.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
