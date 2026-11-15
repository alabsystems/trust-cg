// Symbolic execution: pins the fsym UB obligation map to trust-ir's reference interpreter
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The fsym UB map (`fsym_ub_map`) is DERIVED from trust-ir's reference
//! interpreter; this test re-derives it from the interpreter's source at the
//! pinned rev and fails on any difference.
//!
//! * `interpreter_ub_sites_are_exactly_the_map`: every place the interpreter's
//!   non-test code constructs an `UndefinedBehavior` error (a call to its
//!   `ub(..)` helper or an `InterpretErrorCode::UndefinedBehavior` literal),
//!   keyed by (enclosing function, start of the message literal), is an entry
//!   of `FSYM_INTERPRETER_UB_SITES`, and nothing else is. A new interpreter UB
//!   fails here until it is mapped.
//! * `each_site_is_raised_by_exactly_the_mapped_instructions`: a call graph over
//!   the interpreter's functions (an edge per call of a known function name —
//!   an over-approximation), rooted at each arm of `execute_node` (one per
//!   `Inst` variant), at `execute_function` (`<entry>`) and at
//!   `execute_function_inner` (`<walk>`), with a callee's execution
//!   (`execute_callee`) a pseudo-site of its own. The instructions that reach
//!   each site must equal the union of the site's mapped raisers. A UB newly
//!   reachable from an instruction fails here until its stance is stated.
//! * `classes_table_agrees_with_the_map`: `FSYM_TRUST_IR_UB_CLASSES` is checked
//!   against the map, so it cannot claim a class unchecked while an admitted
//!   instruction raises it.
//! * `admission_gate_follows_the_map`: a catalog of instances of every `Inst`
//!   variant is put through the admission gate; an admitted instance must owe
//!   (`fsym_owed_kinds`, which the scan-time coverage invariant enforces) the
//!   kind of every site it can raise, and never be the raiser of a site the map
//!   refuses. A newly admitted instruction fails here until it owes its UB.
//! * `every_restricted_owed_shape_accepts_an_admitted_instance`: an `Owed`
//!   stance's shape predicate must accept some admitted instance of each of
//!   its raisers (a vacuous predicate is an unreviewed "never raised").
//! * `every_owed_kind_is_its_class_kind_or_a_pinned_exception`: the verdict
//!   kind a stance owes is DERIVED from its site's class, or pinned with why.
//! * `every_hand_stated_stance_is_confirmed_or_reviewed`: every stance that is
//!   a claim is confirmed mechanically at its site (the integer-switch claim
//!   only where `Switch` reaches the site through its case constants alone),
//!   or listed as reviewed, keyed on its site, raiser group and stance kind, so
//!   a new claim or one moved to another site or raiser group fails until it
//!   is reviewed.
//!
//! * `every_raise_the_interpreter_shows_is_owed_by_its_stance`: each
//!   predicate's raiser set is taken from the interpreter by EXECUTION — a
//!   catalog of one-instruction triggers over every op, scalar type, edge
//!   value and pointer kind (a forged entry pointer included) at both
//!   pointer widths — and every UB raised at an admitted instance must be
//!   owed by its stance: a predicate narrowed below what the interpreter
//!   raises, or a `NotRaised` it refutes, fails here whatever the review
//!   list says.
//!
//! `tests/fsym_interpreter_oracle.rs` holds the map to the interpreter by
//! OBSERVATION as well: every UB it attributes to its raising instruction
//! must be one the map's stance owes there.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use trust_cg_verify::fsym_trust_ir::{
    FSYM_TRUST_IR_UB_CLASSES, FsymTrustIrDiagnosticKind, FsymTrustIrSkipReason, FsymUbClassStatus,
    fsym_owed_kinds, scan_function_in_module,
};
use trust_cg_verify::fsym_ub_map::{
    CALLEE_BODY, CALLEE_FUNCTION, FORGED_ENTRY_POINTER, FSYM_INST_VARIANTS,
    FSYM_INTERPRETER_UB_SITES, FsymUbStance, RAISER_ENTRY, RAISER_WALK, fsym_inst_variant_name,
    fsym_site_message_matches,
};
use trust_ir::inst::{AllocOrigin, BindingFrameDef, BindingSlot};
use trust_ir::value::{BindingFrameId, GlobalId};
use trust_ir::{
    AtomicRMWOp, BinOp, Block, BlockId, CastOp, Constant, DialectInst, EnumDef, EnumId,
    EnumVariant, FCmpOp, FatPtrKind, FuncId, FuncTy, FuncTyId, Function, ICmpOp, Inst, InstrNode,
    InterpretValue, InterpretValueKind, Module, Ordering, OverflowOp, SwitchCase, Ty, TyId, UnOp,
    ValueId,
};

/// The number of leading characters of a message literal that key a site.
const MESSAGE_KEY_CHARS: usize = 50;

// ---------------------------------------------------------------------------
// Locating the interpreter's source at the pinned rev
// ---------------------------------------------------------------------------

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("crates/<crate> sits two levels below the workspace root")
        .to_path_buf()
}

/// The trust-ir rev `Cargo.lock` pins.
fn pinned_trust_ir_rev() -> String {
    let lock = std::fs::read_to_string(workspace_root().join("Cargo.lock"))
        .expect("read the workspace Cargo.lock");
    let mut in_trust_ir = false;
    for line in lock.lines() {
        if line.starts_with("[[package]]") {
            in_trust_ir = false;
        } else if line == "name = \"trust-ir\"" {
            in_trust_ir = true;
        } else if in_trust_ir && line.starts_with("source = ") {
            let rev = line
                .rsplit('#')
                .next()
                .expect("a git source ends in #<rev>")
                .trim_end_matches('"');
            return rev.to_string();
        }
    }
    panic!("Cargo.lock pins no trust-ir source");
}

/// The reference interpreter's source at the pinned rev, as the census and
/// the call graph read it: `interpret.rs` ([`interpreter_entry`]) followed by
/// every production module of it that constructs an `UndefinedBehavior`
/// (trust-ir v68's `interpret/tensor_region.rs`, v69's
/// `interpret/tensor_gather_scatter.rs`), so UB raised in a submodule is in
/// the census. The production modules that construct none (the rope, byte
/// image and array-value layers) are leaves, left out of the call graph
/// because their generic names (`new`, `err`, `fill`) would merge with the
/// interpreter's and reach every site from every instruction;
/// `leaf_interpreter_modules_reach_no_ub_site` proves leaving them out drops
/// no raiser. The path is `interpret.rs`'s.
fn interpreter_source() -> (PathBuf, String) {
    let (path, mut source, modules) = interpreter_modules();
    for (_, text) in modules.iter().filter(|(_, text)| !is_leaf_module(text)) {
        source.push('\n');
        source.push_str(text);
    }
    (path, source)
}

/// Whether a production module constructs no `UndefinedBehavior` in its
/// non-test code (a leaf of the census's call graph).
fn is_leaf_module(text: &str) -> bool {
    let code = lex(&non_test_source(text)).code;
    ub_points(&code, 0, code.len()).is_empty()
}

/// `interpret.rs` (path and source) and every production module it
/// declares, recursively ([`production_modules`]), less the
/// [`UNCENSUSED_MODULES`], each of which must still be declared.
fn interpreter_modules() -> (PathBuf, String, Vec<(PathBuf, String)>) {
    let (path, source) = interpreter_entry();
    let mut excluded = BTreeSet::new();
    let modules = production_modules(&path, &source, &mut excluded);
    for (name, why) in UNCENSUSED_MODULES {
        assert!(
            excluded.contains(name),
            "{}: UNCENSUSED_MODULES names `{name}` ({why}), which the interpreter no longer declares: remove the row",
            path.display()
        );
    }
    (path, source, modules)
}

/// Production modules of the interpreter the census does not read, with
/// why. Every row must still be declared ([`interpreter_source`] fails
/// otherwise), so a rename cannot move a module out of the census unseen.
const UNCENSUSED_MODULES: &[(&str, &str)] = &[
    (
        "observed",
        "the resource-observed executor (`ObservedSession`): a separate engine with its own public entry, not reached from `execute_function` or `execute_node`, whose UB is not the reference interpreter's",
    ),
    (
        "observed_impl",
        "the observed engine's byte-image and rope support (`byte_image_observed.rs`, `rope_observed.rs`)",
    ),
];

/// The production (non-`#[cfg(test)]`) file modules `text` (the source of
/// `file`) declares, recursively, as `(path, source)`, skipping and
/// recording the [`UNCENSUSED_MODULES`]. Every file here is a non-`mod.rs`
/// file, so `mod name;` is `<file stem>/name.rs` and a `#[path]` is relative
/// to the file's own directory. A declared module whose file cannot be read
/// FAILS: a census that silently skips one is the false green this exists
/// to prevent.
fn production_modules(
    file: &Path,
    text: &str,
    excluded: &mut BTreeSet<&'static str>,
) -> Vec<(PathBuf, String)> {
    let lexed = lex(&non_test_source(text));
    let code = &lexed.code;
    let dir = file.parent().expect("a source file has a directory");
    let own_dir = file.with_extension("");
    let mut out = Vec::new();
    let mut depth = 0i64;
    let mut item_start = 0;
    let mut i = 0;
    while i < code.len() {
        match code[i] {
            b'{' => {
                depth += 1;
                item_start = i + 1;
            }
            b'}' => {
                depth -= 1;
                item_start = i + 1;
            }
            b';' => item_start = i + 1,
            b'm' if code[i..].starts_with(b"mod ") && is_word_start(code, i) => {
                let mut at = i + 4;
                while code.get(at).is_some_and(u8::is_ascii_whitespace) {
                    at += 1;
                }
                let (name, mut end) = identifier_at(code, at).expect("a module name");
                while code.get(end).is_some_and(u8::is_ascii_whitespace) {
                    end += 1;
                }
                if code.get(end) == Some(&b';') {
                    assert_eq!(
                        depth,
                        0,
                        "{}: file module `{name}` declared inside an inline module: the census cannot place it",
                        file.display()
                    );
                    if let Some((row, _)) = UNCENSUSED_MODULES.iter().find(|(row, _)| *row == name)
                    {
                        excluded.insert(row);
                    } else {
                        let attributes = &code[item_start..i];
                        let path = if find(attributes, b"#[path", 0).is_some() {
                            let literal = lexed
                                .strings
                                .iter()
                                .find(|(at, _)| (item_start..i).contains(at))
                                .unwrap_or_else(|| {
                                    panic!(
                                        "{}: `#[path]` of `{name}` has no literal",
                                        file.display()
                                    )
                                });
                            dir.join(&literal.1)
                        } else {
                            own_dir.join(format!("{name}.rs"))
                        };
                        let source = std::fs::read_to_string(&path).unwrap_or_else(|error| {
                            panic!(
                                "{}: production module `{name}` is unreadable at {}: {error}",
                                file.display(),
                                path.display()
                            )
                        });
                        let nested = production_modules(&path, &source, excluded);
                        out.push((path, source));
                        out.extend(nested);
                    }
                }
                i = end;
                continue;
            }
            _ => {}
        }
        i += 1;
    }
    out
}

/// `trust-ir/src/interpret.rs` at the pinned rev: `FSYM_TRUST_IR_INTERPRET_RS`
/// when set (a `[patch]`ed or vendored trust-ir), else Cargo's git checkout of
/// the pinned rev, else what `targo metadata` resolves `trust-ir` to. Absent
/// all three the test FAILS — the map cannot be checked against nothing.
fn interpreter_entry() -> (PathBuf, String) {
    if let Some(path) = std::env::var_os("FSYM_TRUST_IR_INTERPRET_RS") {
        let path = PathBuf::from(path);
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
        return (path, text);
    }
    let rev = pinned_trust_ir_rev();
    let cargo_home = std::env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".cargo")))
        .expect("CARGO_HOME or HOME");
    let checkouts = cargo_home.join("git").join("checkouts");
    if let Ok(entries) = std::fs::read_dir(&checkouts) {
        for entry in entries.flatten() {
            if !entry.file_name().to_string_lossy().starts_with("trust-ir-") {
                continue;
            }
            let candidate = entry
                .path()
                .join(&rev[..7])
                .join("crates/trust-ir/src/interpret.rs");
            if let Ok(text) = std::fs::read_to_string(&candidate) {
                return (candidate, text);
            }
        }
    }
    // The build tool that compiled this test (targo, under the Trust
    // toolchain); `targo metadata` takes no lane. No stock fallback.
    let cargo = option_env!("CARGO").unwrap_or("targo");
    if let Ok(output) = std::process::Command::new(cargo)
        .args(["metadata", "--format-version", "1", "--offline", "--locked"])
        .current_dir(workspace_root())
        .output()
    {
        let json = String::from_utf8_lossy(&output.stdout);
        for chunk in json.split("\"manifest_path\":\"").skip(1) {
            let manifest = chunk.split('"').next().unwrap_or_default();
            if manifest.ends_with("/trust-ir/Cargo.toml") {
                let candidate = Path::new(manifest)
                    .parent()
                    .expect("a manifest has a parent directory")
                    .join("src/interpret.rs");
                if let Ok(text) = std::fs::read_to_string(&candidate) {
                    return (candidate, text);
                }
            }
        }
    }
    panic!(
        "cannot find trust-ir's interpret.rs at the pinned rev {rev} (looked in {} and asked targo metadata); set FSYM_TRUST_IR_INTERPRET_RS",
        checkouts.display()
    );
}

// ---------------------------------------------------------------------------
// A lexer just good enough to read the interpreter's structure
// ---------------------------------------------------------------------------

/// `code` is the source with comments and string contents blanked (same byte
/// length, newlines kept); `strings` are the string literals by start offset.
struct Lexed {
    code: Vec<u8>,
    strings: Vec<(usize, String)>,
}

fn lex(source: &str) -> Lexed {
    let bytes = source.as_bytes();
    let n = bytes.len();
    let mut code = bytes.to_vec();
    let mut strings = Vec::new();
    let blank = |code: &mut Vec<u8>, from: usize, to: usize| {
        for byte in &mut code[from..to] {
            if *byte != b'\n' {
                *byte = b' ';
            }
        }
    };
    let ident = |byte: u8| byte.is_ascii_alphanumeric() || byte == b'_';
    let mut i = 0;
    while i < n {
        if bytes[i..].starts_with(b"//") {
            let end = bytes[i..]
                .iter()
                .position(|byte| *byte == b'\n')
                .map_or(n, |offset| i + offset);
            blank(&mut code, i, end);
            i = end;
            continue;
        }
        if bytes[i..].starts_with(b"/*") {
            let mut depth = 0;
            let mut j = i;
            while j < n {
                if bytes[j..].starts_with(b"/*") {
                    depth += 1;
                    j += 2;
                } else if bytes[j..].starts_with(b"*/") {
                    depth -= 1;
                    j += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    j += 1;
                }
            }
            blank(&mut code, i, j);
            i = j;
            continue;
        }
        if bytes[i] == b'r' && (i == 0 || !ident(bytes[i - 1])) {
            let hashes = bytes[i + 1..].iter().take_while(|b| **b == b'#').count();
            if bytes.get(i + 1 + hashes) == Some(&b'"') {
                let open = i + 2 + hashes;
                let mut close = open;
                loop {
                    if bytes[close] == b'"'
                        && bytes[close + 1..].iter().take(hashes).all(|b| *b == b'#')
                        && bytes.len() >= close + 1 + hashes
                    {
                        break;
                    }
                    close += 1;
                }
                strings.push((i, source[open..close].to_string()));
                blank(&mut code, open, close);
                i = close + 1 + hashes;
                continue;
            }
        }
        if bytes[i] == b'"' {
            let mut j = i + 1;
            while bytes[j] != b'"' {
                j += if bytes[j] == b'\\' { 2 } else { 1 };
            }
            strings.push((i, source[i + 1..j].to_string()));
            blank(&mut code, i + 1, j);
            i = j + 1;
            continue;
        }
        if bytes[i] == b'\'' {
            // A char literal ('x', '\n', '\'', '\u{..}', a multi-byte char);
            // anything else is a lifetime.
            if bytes.get(i + 1) == Some(&b'\\') {
                if let Some(offset) = bytes[i + 3..].iter().position(|b| *b == b'\'') {
                    let end = i + 3 + offset + 1;
                    blank(&mut code, i + 1, end - 1);
                    i = end;
                    continue;
                }
            } else if let Some(ch) = source[i + 1..].chars().next() {
                let after = i + 1 + ch.len_utf8();
                if bytes.get(after) == Some(&b'\'') {
                    blank(&mut code, i + 1, after);
                    i = after + 1;
                    continue;
                }
            }
        }
        i += 1;
    }
    Lexed { code, strings }
}

struct FnItem {
    name: String,
    body_start: usize,
    body_end: usize,
}

fn identifier_at(code: &[u8], at: usize) -> Option<(String, usize)> {
    let start = at;
    let mut end = at;
    while end < code.len() && (code[end].is_ascii_alphanumeric() || code[end] == b'_') {
        end += 1;
    }
    (end > start).then(|| (String::from_utf8_lossy(&code[start..end]).to_string(), end))
}

fn is_word_start(code: &[u8], at: usize) -> bool {
    at == 0 || !(code[at - 1].is_ascii_alphanumeric() || code[at - 1] == b'_')
}

fn matching_brace(code: &[u8], open: usize) -> usize {
    let mut depth = 0i64;
    for (offset, byte) in code[open..].iter().enumerate() {
        match byte {
            b'{' => depth += 1,
            b'}' => {
                depth -= 1;
                if depth == 0 {
                    return open + offset;
                }
            }
            _ => {}
        }
    }
    panic!("unbalanced braces from {open}");
}

/// Every `fn` item with a body.
fn functions(code: &[u8]) -> Vec<FnItem> {
    let mut items = Vec::new();
    let mut at = 0;
    while let Some(offset) = find(code, b"fn ", at) {
        at = offset + 3;
        if !is_word_start(code, offset) {
            continue;
        }
        let mut name_at = at;
        while code.get(name_at) == Some(&b' ') {
            name_at += 1;
        }
        let Some((name, mut j)) = identifier_at(code, name_at) else {
            continue;
        };
        // The body is the first `{` outside the signature's brackets (the
        // signature's `->` / generics may unbalance `<>`: the depth is only a
        // heuristic, exactly as it needs to be for this file); a `;` first
        // means no body.
        let mut depth = 0i64;
        let mut body = None;
        while j < code.len() {
            match code[j] {
                b'(' | b'<' | b'[' => depth += 1,
                b')' | b'>' | b']' => depth -= 1,
                b';' if depth <= 0 => break,
                b'{' if depth <= 0 => {
                    body = Some(j);
                    break;
                }
                _ => {}
            }
            j += 1;
        }
        if let Some(open) = body {
            items.push(FnItem {
                name,
                body_start: open,
                body_end: matching_brace(code, open),
            });
        }
    }
    items
}

fn find(haystack: &[u8], needle: &[u8], from: usize) -> Option<usize> {
    haystack[from.min(haystack.len())..]
        .windows(needle.len())
        .position(|window| window == needle)
        .map(|offset| from + offset)
}

/// The names of known functions called in `code[from..to]` (an identifier,
/// an optional turbofish, then `(`).
fn calls_in(code: &[u8], from: usize, to: usize, known: &BTreeSet<String>) -> BTreeSet<String> {
    let mut calls = BTreeSet::new();
    let mut i = from;
    while i < to {
        if (code[i].is_ascii_lowercase() || code[i] == b'_') && is_word_start(code, i) {
            let (name, mut j) = identifier_at(code, i).expect("an identifier starts here");
            while j < to && code[j] == b' ' {
                j += 1;
            }
            if code[j..].starts_with(b"::<") {
                let mut depth = 0i64;
                j += 2;
                while j < to {
                    match code[j] {
                        b'<' => depth += 1,
                        b'>' => {
                            depth -= 1;
                            if depth == 0 {
                                j += 1;
                                break;
                            }
                        }
                        _ => {}
                    }
                    j += 1;
                }
                while j < to && code[j] == b' ' {
                    j += 1;
                }
            }
            if j < to && code[j] == b'(' && known.contains(&name) {
                calls.insert(name.clone());
            }
            i += name.len();
            continue;
        }
        i += 1;
    }
    calls
}

/// The UB construction points in `code[from..to]`: `ub(` and
/// `InterpretErrorCode::UndefinedBehavior`.
fn ub_points(code: &[u8], from: usize, to: usize) -> Vec<usize> {
    let mut points = Vec::new();
    for needle in [&b"ub("[..], &b"InterpretErrorCode::UndefinedBehavior"[..]] {
        let mut at = from;
        while let Some(offset) = find(code, needle, at) {
            if offset >= to {
                break;
            }
            if needle.starts_with(b"ub(") && !is_word_start(code, offset) {
                at = offset + 1;
                continue;
            }
            points.push(offset + needle.len());
            at = offset + needle.len();
        }
    }
    points
}

type SiteKey = (String, String);

struct Derived {
    /// Every UB site, with the set of raisers that reach it.
    raisers: BTreeMap<SiteKey, BTreeSet<String>>,
    /// The call graph (same-named functions merged).
    edges: BTreeMap<String, BTreeSet<String>>,
    /// The sites each function raises in its own body.
    sites_by_fn: BTreeMap<String, BTreeSet<SiteKey>>,
    /// Per `Inst` variant: the known functions its `execute_node` arm calls
    /// directly, and the sites the arm raises in its own body.
    arms: BTreeMap<String, (BTreeSet<String>, BTreeSet<SiteKey>)>,
}

impl Derived {
    /// The sites reachable from `start` through the call graph, not
    /// descending into `cut` (reaching `execute_callee` yields its
    /// pseudo-site).
    fn reach(&self, start: &BTreeSet<String>, cut: &[&str]) -> BTreeSet<SiteKey> {
        let callee_key = (CALLEE_FUNCTION.to_string(), CALLEE_BODY.to_string());
        let mut seen = BTreeSet::new();
        let mut stack = start.iter().cloned().collect::<Vec<_>>();
        let mut found = BTreeSet::new();
        while let Some(name) = stack.pop() {
            if cut.contains(&name.as_str()) {
                if name == CALLEE_FUNCTION {
                    found.insert(callee_key.clone());
                }
                continue;
            }
            if !seen.insert(name.clone()) {
                continue;
            }
            if let Some(sites) = self.sites_by_fn.get(&name) {
                found.extend(sites.iter().cloned());
            }
            if let Some(next) = self.edges.get(&name) {
                stack.extend(next.iter().cloned());
            }
        }
        found
    }

    /// The sites `variant`'s `execute_node` arm reaches when the calls in
    /// `cut` (beyond `execute_node` and `execute_callee`) are not followed.
    fn arm_reach(&self, variant: &str, cut: &[&str]) -> BTreeSet<SiteKey> {
        let Some((direct, own)) = self.arms.get(variant) else {
            return BTreeSet::new();
        };
        let mut all_cut = vec!["execute_node", CALLEE_FUNCTION];
        all_cut.extend_from_slice(cut);
        let start = direct
            .iter()
            .filter(|name| !cut.contains(&name.as_str()))
            .cloned()
            .collect();
        let mut found = self.reach(&start, &all_cut);
        found.extend(own.iter().cloned());
        found
    }
}

fn message_after(lexed: &Lexed, at: usize) -> String {
    // A normative interpreter UB message may be a named string constant.
    // Resolve that exact argument, never an unrelated later TypeError literal.
    if let Some(comma) = lexed.code[at..].iter().position(|&byte| byte == b',') {
        let mut argument = at + comma + 1;
        while lexed
            .code
            .get(argument)
            .is_some_and(u8::is_ascii_whitespace)
        {
            argument += 1;
        }
        if let Some((name, end)) = identifier_at(&lexed.code, argument) {
            let tail = &lexed.code[end..];
            if name
                .bytes()
                .all(|byte| byte.is_ascii_uppercase() || byte == b'_')
                && tail
                    .iter()
                    .copied()
                    .find(|byte| !byte.is_ascii_whitespace())
                    == Some(b')')
            {
                let declaration = format!("const {name}:");
                let start = find(&lexed.code, declaration.as_bytes(), 0)
                    .unwrap_or_else(|| panic!("unresolved UB message constant {name}"));
                assert!(
                    find(
                        &lexed.code,
                        declaration.as_bytes(),
                        start + declaration.len()
                    )
                    .is_none(),
                    "UB message constant {name} must have one unambiguous declaration"
                );
                let end = start
                    + lexed.code[start..]
                        .iter()
                        .position(|&byte| byte == b';')
                        .expect("message constant has a complete declaration");
                let equals = start
                    + lexed.code[start..end]
                        .iter()
                        .position(|&byte| byte == b'=')
                        .expect("message constant has an initializer");
                assert!(
                    lexed.code[equals + 1..end]
                        .iter()
                        .copied()
                        .filter(|byte| !byte.is_ascii_whitespace())
                        .eq(b"\"\"".iter().copied()),
                    "UB message constant {name} must be one literal"
                );
                let literals: Vec<_> = lexed
                    .strings
                    .iter()
                    .filter(|(at, _)| *at > equals && *at < end)
                    .collect();
                assert_eq!(
                    literals.len(),
                    1,
                    "UB message constant {name} must be one literal"
                );
                return literals[0].1.chars().take(MESSAGE_KEY_CHARS).collect();
            }
        }
    }
    lexed
        .strings
        .iter()
        .find(|(start, _)| *start >= at && *start < at + 400)
        .map(|(_, text)| text.chars().take(MESSAGE_KEY_CHARS).collect())
        .unwrap_or_default()
}

#[test]
fn named_ub_message_is_resolved_before_an_unrelated_later_literal() {
    let source = "const MESSAGE: &str = \"the actual normative UB\"; fn evaluate() { ub(block, MESSAGE); type_error(block, \"unrelated later error\"); }";
    let lexed = lex(source);
    let at = find(&lexed.code, b"ub(", 0).expect("UB call") + 3;
    assert_eq!(message_after(&lexed, at), "the actual normative UB");
}

/// Remove each top-level test module, preserving production items on either side.
/// A test-only external module may precede the interpreter implementation;
/// truncating at its attribute would silently discard the production census.
/// Unexpected test-item syntax refuses rather than guessing its extent.
fn non_test_source(source: &str) -> String {
    let code = lex(source).code;
    let mut result = source.as_bytes().to_vec();
    let mut from = 0;
    while let Some(start) = find(&code, b"#[cfg(test)]", from) {
        let depth = code[..start].iter().fold(0i64, |depth, byte| match byte {
            b'{' => depth + 1,
            b'}' => depth - 1,
            _ => depth,
        });
        if depth != 0 {
            // Keep nested test helpers in the conservative census, as before.
            // Only complete top-level test modules are excluded here.
            from = start + b"#[cfg(test)]".len();
            continue;
        }
        let mut at = start + b"#[cfg(test)]".len();
        loop {
            while at < code.len() && code[at].is_ascii_whitespace() {
                at += 1;
            }
            if code.get(at..at + 2) != Some(b"#[") {
                break;
            }
            at += code[at..]
                .iter()
                .position(|&byte| byte == b']')
                .expect("unterminated test-module attribute")
                + 1;
        }
        let (keyword, end) = identifier_at(&code, at).expect("test item declaration");
        let end = match keyword.as_str() {
            "mod" => {
                at = end;
                while at < code.len() && code[at].is_ascii_whitespace() {
                    at += 1;
                }
                let (_, end) = identifier_at(&code, at).expect("test module name");
                at = end;
                while at < code.len() && code[at].is_ascii_whitespace() {
                    at += 1;
                }
                match code.get(at) {
                    Some(b';') => at,
                    Some(b'{') => matching_brace(&code, at),
                    _ => panic!("unsupported test-module body in interpreter census"),
                }
            }
            // A test-only impl block (trust-ir's `Rope` invariant checker in
            // `interpret/rope.rs`): an impl header holds no brace or `;`, so
            // its body is the first `{` after the keyword.
            "impl" => {
                let open = find(&code, b"{", end).expect("a test-only impl has a body");
                assert!(
                    !code[end..open].contains(&b';'),
                    "unsupported test-only impl header in interpreter census"
                );
                matching_brace(&code, open)
            }
            _ => panic!("unsupported test-only item `{keyword}` in interpreter census"),
        };
        for byte in &mut result[start..=end] {
            if *byte != b'\n' {
                *byte = b' ';
            }
        }
        from = end + 1;
    }
    String::from_utf8(result).expect("blanking whole module spans preserves UTF-8")
}

#[test]
fn non_test_census_preserves_production_after_test_modules() {
    let source = r#"
#[cfg(test)]
mod early;
fn first() { ub("production before inline tests"); }
impl Dummy {
    #[cfg(test)]
    fn legacy_helper() {}
}
#[cfg(test)]
mod inline_tests {
    fn excluded() { let text = "} #[cfg(test)]"; ub(text); }
}
fn last() { ub("production after inline tests"); }
#[cfg(test)]
#[path = "another_test.rs"]
mod late;
#[cfg(test)]
impl<T: Elem> Dummy<T> {
    fn invariant_checker() { ub("test-only impl"); }
}
fn after_impl() { ub("production after a test-only impl"); }
"#;
    let kept = lex(&non_test_source(source));
    let names = functions(&kept.code)
        .into_iter()
        .map(|item| item.name)
        .collect::<Vec<_>>();
    assert_eq!(names, ["first", "legacy_helper", "last", "after_impl"]);
    assert_eq!(ub_points(&kept.code, 0, kept.code.len()).len(), 3);
    assert!(std::panic::catch_unwind(|| non_test_source("#[cfg(test)] fn unknown() {}")).is_err());
}

fn derive(source: &str) -> Derived {
    let lexed = lex(&non_test_source(source));
    let code = &lexed.code;
    let items = functions(code);
    let known = items
        .iter()
        .map(|item| item.name.clone())
        .collect::<BTreeSet<_>>();
    let innermost = |at: usize| {
        items
            .iter()
            .filter(|item| item.body_start <= at && at <= item.body_end)
            .max_by_key(|item| item.body_start)
    };

    // Sites, by the innermost enclosing function.
    let mut sites_by_fn: BTreeMap<String, BTreeSet<SiteKey>> = BTreeMap::new();
    let mut raisers: BTreeMap<SiteKey, BTreeSet<String>> = BTreeMap::new();
    for point in ub_points(code, 0, code.len()) {
        let Some(item) = innermost(point) else {
            continue;
        };
        if item.name == "ub" || item.name == "as_str" {
            continue;
        }
        let key = (item.name.clone(), message_after(&lexed, point));
        sites_by_fn
            .entry(item.name.clone())
            .or_default()
            .insert(key.clone());
        raisers.entry(key).or_default();
    }
    raisers
        .entry((CALLEE_FUNCTION.to_string(), CALLEE_BODY.to_string()))
        .or_default();

    // Call edges (all same-named functions merge: an over-approximation).
    let mut edges: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for item in &items {
        let mut calls = calls_in(code, item.body_start, item.body_end, &known);
        calls.remove(&item.name);
        edges.entry(item.name.clone()).or_default().extend(calls);
    }
    let mut derived = Derived {
        raisers,
        edges,
        sites_by_fn,
        arms: BTreeMap::new(),
    };
    let item = |name: &str| {
        items
            .iter()
            .find(|item| item.name == name)
            .unwrap_or_else(|| panic!("the interpreter has no `{name}`"))
    };

    // One root per arm of `execute_node`'s `match &node.inst`.
    let execute_node = item("execute_node");
    let open = find(code, b"match &node.inst {", execute_node.body_start)
        .expect("execute_node matches on &node.inst")
        + b"match &node.inst ".len();
    let close = matching_brace(code, open);
    let mut i = open + 1;
    let mut pattern_start = i;
    let mut depth = 0i64;
    let mut arms = 0;
    while i < close {
        if depth == 0 && code[i..].starts_with(b"=>") {
            let pattern = String::from_utf8_lossy(&code[pattern_start..i]).to_string();
            let mut j = i + 2;
            while code[j].is_ascii_whitespace() {
                j += 1;
            }
            let (body_from, body_to) = if code[j] == b'{' {
                let end = matching_brace(code, j);
                (j, end + 1)
            } else {
                let mut k = j;
                let mut inner = 0i64;
                loop {
                    match code[k] {
                        b'(' | b'{' | b'[' => inner += 1,
                        b')' | b'}' | b']' => inner -= 1,
                        b',' if inner == 0 => break,
                        _ => {}
                    }
                    if inner < 0 {
                        break;
                    }
                    k += 1;
                }
                (j, k)
            };
            let variants = pattern
                .split("Inst::")
                .skip(1)
                .map(|rest| {
                    rest.chars()
                        .take_while(|c| c.is_ascii_alphanumeric())
                        .collect::<String>()
                })
                .collect::<Vec<_>>();
            let direct = calls_in(code, body_from, body_to, &known);
            let mut found = derived.reach(&direct, &["execute_node", CALLEE_FUNCTION]);
            let own = ub_points(code, body_from, body_to)
                .into_iter()
                .map(|point| ("execute_node".to_string(), message_after(&lexed, point)))
                .collect::<BTreeSet<_>>();
            found.extend(own.iter().cloned());
            for variant in &variants {
                let arm = derived.arms.entry(variant.clone()).or_default();
                arm.0.extend(direct.iter().cloned());
                arm.1.extend(own.iter().cloned());
            }
            for key in found {
                derived
                    .raisers
                    .entry(key)
                    .or_default()
                    .extend(variants.iter().cloned());
            }
            arms += 1;
            i = body_to;
            while i < close && (code[i].is_ascii_whitespace() || code[i] == b',') {
                i += 1;
            }
            pattern_start = i;
            continue;
        }
        match code[i] {
            b'(' | b'{' | b'[' => depth += 1,
            b')' | b'}' | b']' => depth -= 1,
            _ => {}
        }
        i += 1;
    }
    assert!(
        arms > 40,
        "execute_node has only {arms} arms: the parse is off"
    );

    // `<entry>` and `<walk>`.
    for (raiser, root, cut) in [
        (
            RAISER_ENTRY,
            "execute_function",
            &["execute_function_inner"][..],
        ),
        (
            RAISER_WALK,
            "execute_function_inner",
            &["execute_node", CALLEE_FUNCTION][..],
        ),
    ] {
        let root = item(root);
        let direct = calls_in(code, root.body_start, root.body_end, &known);
        let mut found = derived.reach(&direct, cut);
        if let Some(own) = derived.sites_by_fn.get(&root.name) {
            found.extend(own.iter().cloned());
        }
        for key in found {
            derived
                .raisers
                .entry(key)
                .or_default()
                .insert(raiser.to_string());
        }
    }
    derived
}

fn map_keys() -> BTreeMap<SiteKey, BTreeSet<String>> {
    let mut map = BTreeMap::new();
    for site in FSYM_INTERPRETER_UB_SITES {
        let key = (site.function.to_string(), site.message.to_string());
        let by = site
            .raisers
            .iter()
            .flat_map(|raise| raise.by.iter().map(|name| name.to_string()))
            .collect::<BTreeSet<_>>();
        assert!(
            map.insert(key.clone(), by).is_none(),
            "the map lists {key:?} twice"
        );
    }
    map
}

#[test]
fn interpreter_ub_sites_are_exactly_the_map() {
    let (path, source) = interpreter_source();
    let derived = derive(&source);
    let map = map_keys();
    let derived_sites = derived.raisers.keys().cloned().collect::<BTreeSet<_>>();
    let map_sites = map.keys().cloned().collect::<BTreeSet<_>>();
    let unmapped = derived_sites.difference(&map_sites).collect::<Vec<_>>();
    let stale = map_sites.difference(&derived_sites).collect::<Vec<_>>();
    assert!(
        unmapped.is_empty() && stale.is_empty(),
        "{}: interpreter UB sites not in FSYM_INTERPRETER_UB_SITES: {unmapped:#?}\nmapped sites the interpreter no longer has: {stale:#?}",
        path.display()
    );
    assert!(
        derived_sites.len() >= 60,
        "only {} UB sites derived: the parse is off",
        derived_sites.len()
    );
}

#[test]
fn each_site_is_raised_by_exactly_the_mapped_instructions() {
    let (path, source) = interpreter_source();
    let derived = derive(&source);
    let map = map_keys();
    let mut mismatches = Vec::new();
    for (key, raisers) in &derived.raisers {
        let Some(mapped) = map.get(key) else {
            continue; // reported by `interpreter_ub_sites_are_exactly_the_map`
        };
        if raisers != mapped {
            mismatches.push(format!(
                "{key:?}: the interpreter is reached from {:?} but the map names {:?} (missing {:?}, extra {:?})",
                raisers,
                mapped,
                raisers.difference(mapped).collect::<Vec<_>>(),
                mapped.difference(raisers).collect::<Vec<_>>()
            ));
        }
    }
    assert!(
        mismatches.is_empty(),
        "{}: {} site(s) whose raisers drifted:\n{}",
        path.display(),
        mismatches.len(),
        mismatches.join("\n")
    );
}

/// Leaf calls the name-merged call graph cannot place, reviewed: (leaf file,
/// called name, the receivers every such call must be spelled on, why no
/// such call reaches the interpreter's function of that name). Every call
/// of the name in the leaf's non-test code must end one of the receivers, and
/// a row the leaf no longer exercises fails as stale.
const REVIEWED_LEAF_CALLS: &[(&str, &str, &[&str], &str)] = &[(
    "byte_image.rs",
    "fill",
    &["Image::", "]."],
    "the byte-image layer calls its own constructor `Image::fill(byte, len)` and the slice method `<[u8]>::fill`; the interpreter's `fill` is `MemoryState::fill`, the MemSet store, a method of the memory state this layer sits below and never holds",
)];

/// The byte offsets of each `name(` call in `code` (an identifier at a word
/// start, directly followed by `(`, and not the name of a `fn` item).
fn call_sites(code: &[u8], name: &str) -> Vec<usize> {
    let needle = format!("{name}(");
    let mut sites = Vec::new();
    let mut at = 0;
    while let Some(offset) = find(code, needle.as_bytes(), at) {
        if is_word_start(code, offset) && !code[..offset].ends_with(b"fn ") {
            sites.push(offset);
        }
        at = offset + needle.len();
    }
    sites
}

/// The leaf modules [`interpreter_source`] leaves out of the call graph
/// construct no UB of their own (that is what makes them leaves), and every
/// interpreter function name any of them calls (an over-approximation: a
/// leaf's own `new` counts as the interpreter's) reaches no UB site, the
/// callee pseudo-site included. A leaf therefore reaches no site, directly or
/// through another leaf, so leaving the leaves out of the graph drops no
/// raiser of any site.
#[test]
fn leaf_interpreter_modules_reach_no_ub_site() {
    let (path, _, modules) = interpreter_modules();
    let derived = derive(&interpreter_source().1);
    let known = derived.edges.keys().cloned().collect::<BTreeSet<_>>();
    let mut leaves = 0;
    let mut failures = Vec::new();
    let mut reviewed = BTreeSet::new();
    for (module, text) in modules.iter().filter(|(_, text)| is_leaf_module(text)) {
        leaves += 1;
        let code = lex(&non_test_source(text)).code;
        let file = module
            .file_name()
            .expect("a module file has a name")
            .to_string_lossy()
            .to_string();
        for name in calls_in(&code, 0, code.len(), &known) {
            let reached = derived.reach(&BTreeSet::from([name.clone()]), &[]);
            if reached.is_empty() {
                continue;
            }
            match REVIEWED_LEAF_CALLS
                .iter()
                .find(|(row_file, row_name, ..)| *row_file == file && *row_name == name)
            {
                Some((_, _, prefixes, _)) => {
                    reviewed.insert((file.clone(), name.clone()));
                    for at in call_sites(&code, &name) {
                        if !prefixes
                            .iter()
                            .any(|prefix| code[..at].ends_with(prefix.as_bytes()))
                        {
                            failures.push(format!(
                                "{}: a `{name}(` call at byte {at} has none of the reviewed receivers {prefixes:?}, and `{name}` reaches {reached:?}",
                                module.display()
                            ));
                        }
                    }
                }
                None => failures.push(format!(
                    "{}: calls `{name}`, which reaches {reached:?}",
                    module.display()
                )),
            }
        }
    }
    for (file, name, _, why) in REVIEWED_LEAF_CALLS {
        if !reviewed.contains(&(file.to_string(), name.to_string())) {
            failures.push(format!(
                "REVIEWED_LEAF_CALLS ({file}, {name}) is stale: the leaf no longer makes a call of `{name}` that reaches a site ({why})"
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "{}: a leaf module reaches a UB site, so the census must graph it:\n{}",
        path.display(),
        failures.join("\n")
    );
    assert!(
        leaves >= 1 && modules.len() > leaves,
        "{}: {} production module(s), {leaves} leaf/leaves: the module walk is off",
        path.display(),
        modules.len()
    );
}

#[test]
fn every_raiser_is_an_inst_variant_or_a_pseudo_raiser() {
    let variants = FSYM_INST_VARIANTS
        .iter()
        .map(|(name, _)| *name)
        .collect::<BTreeSet<_>>();
    for site in FSYM_INTERPRETER_UB_SITES {
        for raise in site.raisers {
            for name in raise.by {
                assert!(
                    variants.contains(name) || *name == RAISER_ENTRY || *name == RAISER_WALK,
                    "{}: raiser `{name}` is neither an Inst variant nor a pseudo-raiser",
                    site.message
                );
            }
        }
    }
}

#[test]
fn classes_table_agrees_with_the_map() {
    let mut failures = Vec::new();
    let checked_kinds = FSYM_TRUST_IR_UB_CLASSES
        .iter()
        .filter_map(|class| match class.status {
            FsymUbClassStatus::Checked(kind) => Some(kind),
            FsymUbClassStatus::NotChecked => None,
        })
        .collect::<Vec<_>>();
    let names = FSYM_TRUST_IR_UB_CLASSES
        .iter()
        .map(|class| class.name)
        .collect::<Vec<_>>();
    for (index, name) in names.iter().enumerate() {
        if names[..index].contains(name) {
            failures.push(format!("class `{name}` is listed twice"));
        }
    }
    for site in FSYM_INTERPRETER_UB_SITES {
        let Some(class) = FSYM_TRUST_IR_UB_CLASSES
            .iter()
            .find(|class| class.name == site.class)
        else {
            failures.push(format!(
                "site `{}` ({}) names class `{}`, which FSYM_TRUST_IR_UB_CLASSES does not list",
                site.message, site.function, site.class
            ));
            continue;
        };
        for raise in site.raisers {
            let owed = match raise.stance {
                FsymUbStance::Owed { kind, .. } | FsymUbStance::AtSource { kind, .. } => Some(kind),
                FsymUbStance::Refused | FsymUbStance::NotRaised(_) | FsymUbStance::Outside(_) => {
                    None
                }
            };
            match (owed, class.status) {
                (Some(kind), FsymUbClassStatus::NotChecked) => failures.push(format!(
                    "site `{}` is owed a {kind:?} verdict (raised by {:?}) but its class `{}` claims NotChecked",
                    site.message, raise.by, class.name
                )),
                (Some(kind), FsymUbClassStatus::Checked(_)) if !checked_kinds.contains(&kind) => {
                    failures.push(format!(
                        "site `{}` is owed a {kind:?} verdict, which no Checked class names",
                        site.message
                    ))
                }
                _ => {}
            }
        }
    }
    for class in FSYM_TRUST_IR_UB_CLASSES {
        let sites = FSYM_INTERPRETER_UB_SITES
            .iter()
            .filter(|site| site.class == class.name)
            .collect::<Vec<_>>();
        match class.status {
            FsymUbClassStatus::Checked(_) if sites.is_empty() => failures.push(format!(
                "class `{}` is Checked but no interpreter UB site belongs to it",
                class.name
            )),
            FsymUbClassStatus::NotChecked
                if sites.is_empty()
                    && !class.detail.starts_with("no interpreter UB")
                    && !class.detail.starts_with("not UB in trust-ir") =>
            {
                failures.push(format!(
                        "class `{}` has no interpreter UB site; its detail must say so (\"no interpreter UB\" / \"not UB in trust-ir\")",
                        class.name
                    ));
            }
            _ => {}
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

// ---------------------------------------------------------------------------
// The admission gate against the map
// ---------------------------------------------------------------------------

/// A module with the types the catalog's instances use.
fn catalog_module() -> Module {
    let mut module = Module::new("fsym_ub_map_catalog");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: "x86_64-unknown-linux-gnu".to_string(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::default(),
    });
    module.types = vec![Ty::I32, Ty::Bool];
    module.enums.push(EnumDef::new(
        EnumId::new(0),
        "E",
        vec![
            EnumVariant {
                name: "A".to_string(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "B".to_string(),
                fields: vec![Ty::I32],
                field_names: vec![],
            },
        ],
    ));
    module.globals.push(trust_ir::Global {
        name: "G".to_string(),
        ty: Ty::I64,
        mutable: true,
        initializer: Some(Constant::Int(0)),
        linkage: trust_ir::Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    });
    module
}

/// Parameters every catalog function takes, by name.
fn params() -> Vec<(&'static str, Ty)> {
    vec![
        ("i64", Ty::I64),
        ("u64", Ty::U64),
        ("u8", Ty::U8),
        ("ptr", Ty::Ptr),
        ("bool", Ty::Bool),
        ("f64", Ty::F64),
        ("vec", Ty::Vector(Box::new(Ty::I32), 4)),
        ("enum", Ty::Enum(EnumId::new(0))),
        ("tuple", Ty::Tuple(vec![Ty::I32, Ty::I64])),
        ("usize", Ty::Usize),
        ("seq", Ty::Sequence(TyId::new(0))),
        ("fat", Ty::FatPtr(FatPtrKind::Str)),
        ("i32", Ty::I32),
    ]
}

/// The `k`th tensor parameter [`tensor_params`] appends after [`params`].
fn tensor_param(k: u32) -> ValueId {
    ValueId::new(params().len() as u32 + k)
}

/// The tensor parameters a catalog function for `inst` takes after
/// [`params`], in order: each tensor instruction reads only these and the
/// scalar parameters.
fn tensor_params(inst: &Inst) -> Vec<Ty> {
    let tensor = |rank| Ty::Tensor(Box::new(Ty::I64), rank);
    match inst {
        Inst::TensorContract { ty, .. } => vec![ty.clone()],
        Inst::TensorMap { .. } => vec![tensor(1)],
        Inst::TensorReduce { .. } | Inst::TensorView { .. } => vec![tensor(2)],
        Inst::TensorGather { .. } => vec![tensor(1), tensor(1)],
        Inst::TensorScatter { .. } => vec![tensor(1), tensor(1), tensor(1)],
        _ => vec![],
    }
}

fn p(name: &str) -> ValueId {
    ValueId::new(
        params()
            .iter()
            .position(|(param, _)| *param == name)
            .unwrap_or_else(|| panic!("no catalog parameter `{name}`")) as u32,
    )
}

/// Instances of every `Inst` variant, covering the shapes the map's `applies`
/// predicates distinguish. `(inst, results, terminator)`.
fn catalog() -> Vec<(Inst, usize, bool)> {
    let mut out = Vec::new();
    let mut value = |inst: Inst| out.push((inst, 1, false));
    for op in [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::UDiv,
        BinOp::SDiv,
        BinOp::URem,
        BinOp::SRem,
        BinOp::Shl,
        BinOp::LShr,
        BinOp::AShr,
        BinOp::And,
        BinOp::RotL,
    ] {
        for ty in [Ty::I64, Ty::U64] {
            value(Inst::BinOp {
                op,
                ty: ty.clone(),
                lhs: p("i64"),
                rhs: p("i64"),
            });
        }
        value(Inst::BinOp {
            op,
            ty: Ty::Vector(Box::new(Ty::I32), 4),
            lhs: p("vec"),
            rhs: p("vec"),
        });
    }
    for op in [BinOp::FAdd, BinOp::FDiv, BinOp::FRem] {
        value(Inst::BinOp {
            op,
            ty: Ty::F64,
            lhs: p("f64"),
            rhs: p("f64"),
        });
    }
    for op in [UnOp::Neg, UnOp::Not, UnOp::CtLz, UnOp::FNeg] {
        value(Inst::UnOp {
            op,
            ty: Ty::I64,
            operand: p("i64"),
        });
    }
    value(Inst::ICmp {
        op: ICmpOp::Ult,
        ty: Ty::U64,
        lhs: p("u64"),
        rhs: p("u64"),
    });
    value(Inst::ICmp {
        op: ICmpOp::Eq,
        ty: Ty::Ptr,
        lhs: p("ptr"),
        rhs: p("ptr"),
    });
    value(Inst::FCmp {
        op: FCmpOp::OLt,
        ty: Ty::F64,
        lhs: p("f64"),
        rhs: p("f64"),
    });
    for (op, src, dst, operand) in [
        (CastOp::Trunc, Ty::I64, Ty::U8, "i64"),
        (CastOp::ZExt, Ty::Bool, Ty::U64, "bool"),
        (CastOp::SExt, Ty::U8, Ty::I64, "u8"),
        (CastOp::FPToSI, Ty::F64, Ty::I64, "f64"),
        (CastOp::FPToUI, Ty::F64, Ty::U8, "f64"),
        (CastOp::FPToSISat, Ty::F64, Ty::I64, "f64"),
        (CastOp::SIToFP, Ty::I64, Ty::F64, "i64"),
        (CastOp::PtrToInt, Ty::Ptr, Ty::U64, "ptr"),
        (CastOp::IntToPtr, Ty::U64, Ty::Ptr, "u64"),
        (CastOp::Bitcast, Ty::U64, Ty::Ptr, "u64"),
        (CastOp::Bitcast, Ty::U64, Ty::I64, "u64"),
        (CastOp::PtrToPtr, Ty::Ptr, Ty::Ptr, "ptr"),
        (CastOp::Transmute, Ty::Ptr, Ty::U64, "ptr"),
    ] {
        value(Inst::Cast {
            op,
            src_ty: src,
            dst_ty: dst,
            operand: p(operand),
        });
    }
    for (ty, volatile) in [(Ty::I64, false), (Ty::Ptr, true)] {
        value(Inst::Load {
            ty,
            ptr: p("ptr"),
            volatile,
            align: None,
        });
    }
    for (ty, stored) in [
        (Ty::I64, "i64"),
        (Ty::Ptr, "ptr"),
        (Ty::Tuple(vec![Ty::I32, Ty::I64]), "tuple"),
        (Ty::FatPtr(FatPtrKind::Str), "fat"),
    ] {
        out.push((
            Inst::Store {
                ty,
                ptr: p("ptr"),
                value: p(stored),
                volatile: false,
                align: Some(8),
            },
            0,
            false,
        ));
    }
    let mut value = |inst: Inst| out.push((inst, 1, false));
    for (count, align) in [
        (None, None),
        (Some(p("u64")), None),
        (None, Some(1u64 << 20)),
        (Some(p("usize")), Some(16)),
    ] {
        value(Inst::Alloca {
            ty: Ty::I64,
            count,
            align,
        });
        value(Inst::HeapAlloc {
            ty: Ty::I64,
            count,
            align,
            origin: AllocOrigin::CMalloc,
        });
    }
    value(Inst::GEP {
        pointee_ty: Ty::I64,
        base: p("ptr"),
        indices: vec![p("i64")],
        inbounds: true,
    });
    value(Inst::PtrData {
        ptr_ty: Ty::FatPtr(FatPtrKind::Str),
        ptr: p("fat"),
    });
    value(Inst::PtrMetadata {
        ptr_ty: Ty::FatPtr(FatPtrKind::Str),
        metadata_ty: Ty::Usize,
        ptr: p("fat"),
    });
    value(Inst::PtrFromParts {
        ptr_ty: Ty::FatPtr(FatPtrKind::Str),
        metadata_ty: Ty::Usize,
        data: p("ptr"),
        metadata: p("usize"),
    });
    value(Inst::AtomicLoad {
        ty: Ty::I64,
        ptr: p("ptr"),
        ordering: Ordering::SeqCst,
    });
    for (ty, stored) in [(Ty::I64, "i64"), (Ty::Ptr, "ptr")] {
        out.push((
            Inst::AtomicStore {
                ty: ty.clone(),
                ptr: p("ptr"),
                value: p(stored),
                ordering: Ordering::SeqCst,
            },
            0,
            false,
        ));
        out.push((
            Inst::AtomicRMW {
                op: AtomicRMWOp::Xchg,
                ty: ty.clone(),
                ptr: p("ptr"),
                value: p(stored),
                ordering: Ordering::SeqCst,
            },
            1,
            false,
        ));
        for weak in [false, true] {
            out.push((
                Inst::CmpXchg {
                    ty: ty.clone(),
                    ptr: p("ptr"),
                    expected: p(stored),
                    desired: p(stored),
                    success: Ordering::SeqCst,
                    failure: Ordering::SeqCst,
                    weak,
                },
                2,
                false,
            ));
        }
        // v47: a drop through a pointer (refused at admission).
        out.push((Inst::Drop { ty, ptr: p("ptr") }, 0, false));
    }
    out.push((
        Inst::Fence {
            ordering: Ordering::SeqCst,
        },
        0,
        false,
    ));
    out.push((
        Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::I64,
            lhs: p("i64"),
            rhs: p("i64"),
        },
        2,
        false,
    ));
    // A bodied callee, an external, and a bulk-memory symbol declared with
    // C's prototype (checked as the MemSet it lowers to, not as a callee).
    for (callee, args, results) in [
        (FuncId::new(1), vec![p("ptr")], 0),
        (FuncId::new(2), vec![], 0),
        (FuncId::new(3), vec![p("ptr"), p("i32"), p("usize")], 1),
    ] {
        out.push((Inst::Call { callee, args }, results, false));
    }
    out.push((
        Inst::CallIndirect {
            callee: p("ptr"),
            sig: FuncTyId::new(1),
            args: vec![],
            calling_conv: trust_ir::CallingConv::default(),
        },
        0,
        false,
    ));
    // v53: the non-propagating call boundaries (refused at admission).
    out.push((
        Inst::CallCannotUnwind {
            callee: FuncId::new(1),
            args: vec![p("ptr")],
        },
        0,
        false,
    ));
    out.push((
        Inst::CallIndirectCannotUnwind {
            callee: p("ptr"),
            sig: FuncTyId::new(1),
            args: vec![],
            calling_conv: trust_ir::CallingConv::default(),
        },
        0,
        false,
    ));
    // v54: a sited check (refused at admission; its unsited twin is in the
    // value-free list below, admitted).
    out.push((sited_assert(), 0, false));
    let mut value = |inst: Inst| out.push((inst, 1, false));
    value(Inst::ExtractField {
        ty: Ty::I32,
        aggregate: p("enum"),
        field: 1,
    });
    value(Inst::ExtractField {
        ty: Ty::I64,
        aggregate: p("tuple"),
        field: 1,
    });
    value(Inst::InsertField {
        ty: Ty::Enum(EnumId::new(0)),
        aggregate: p("enum"),
        field: 0,
        value: p("u8"),
    });
    value(Inst::InsertField {
        ty: Ty::Tuple(vec![Ty::I32, Ty::I64]),
        aggregate: p("tuple"),
        field: 0,
        value: p("i32"),
    });
    value(Inst::ExtractElement {
        ty: Ty::I32,
        array: p("vec"),
        index: p("i64"),
    });
    value(Inst::InsertElement {
        ty: Ty::Vector(Box::new(Ty::I32), 4),
        array: p("vec"),
        index: p("u64"),
        value: p("i32"),
    });
    value(Inst::Const {
        ty: Ty::I64,
        value: Constant::Int(1),
    });
    value(Inst::Const {
        ty: Ty::Enum(EnumId::new(0)),
        value: Constant::Aggregate(vec![Constant::Int(0)]),
    });
    value(Inst::Const {
        ty: Ty::Ptr,
        value: Constant::SymbolAddr {
            symbol: "G".to_string(),
            addend: 0,
        },
    });
    value(Inst::NullPtr);
    value(Inst::GlobalAddr {
        global: GlobalId::new(0),
    });
    value(Inst::Undef { ty: Ty::I64 });
    value(Inst::Copy {
        ty: Ty::I64,
        operand: p("i64"),
    });
    value(Inst::Select {
        ty: Ty::I64,
        cond: p("bool"),
        then_val: p("i64"),
        else_val: p("i64"),
    });
    value(Inst::SeqMapAddK {
        ty: Ty::Sequence(TyId::new(0)),
        seq: p("seq"),
        k: 1,
    });
    value(Inst::SeqMapNot {
        ty: Ty::Sequence(TyId::new(1)),
        seq: p("seq"),
    });
    value(Inst::SeqMap {
        ty: Ty::Sequence(TyId::new(0)),
        seq: p("seq"),
        fwd: FuncId::new(1),
    });
    value(Inst::TensorContract {
        ty: Ty::Tensor(Box::new(Ty::I64), 2),
        lhs: tensor_param(0),
        rhs: tensor_param(0),
        batch: vec![],
        contract: vec![(1, 0)],
    });
    // trust-ir v68/v69 tensor regions, gather and scatter: each reads the
    // tensor parameters `tensor_params` appends for it.
    value(Inst::TensorMap {
        ty: Ty::Tensor(Box::new(Ty::I64), 1),
        args: vec![tensor_param(0), p("i64")],
        body: vec![trust_ir::TensorMapNode::BinOp {
            op: BinOp::SDiv,
            ty: Ty::I64,
            lhs: 0,
            rhs: 1,
        }],
    });
    value(Inst::TensorReduce {
        ty: Ty::Tensor(Box::new(Ty::I64), 1),
        src: tensor_param(0),
        op: trust_ir::TensorReduceOp::Add,
        axes: vec![1],
        order: trust_ir::TensorReduceOrder::RowMajor,
    });
    value(Inst::TensorView {
        ty: Ty::Tensor(Box::new(Ty::I64), 2),
        src: tensor_param(0),
        params: vec![p("usize")],
        exprs: vec![
            trust_ir::TensorIndexExpr::Param(0),
            trust_ir::TensorIndexExpr::SrcExtent(0),
            trust_ir::TensorIndexExpr::Coord(1),
            trust_ir::TensorIndexExpr::Coord(0),
        ],
        shape: vec![0, 1],
        index: vec![2, 3],
        fill: Some(p("i64")),
    });
    value(Inst::TensorGather {
        ty: Ty::Tensor(Box::new(Ty::I64), 1),
        data: tensor_param(0),
        coords: vec![tensor_param(1)],
    });
    value(Inst::TensorScatter {
        ty: Ty::Tensor(Box::new(Ty::I64), 1),
        init: tensor_param(0),
        src: tensor_param(1),
        coords: vec![tensor_param(2)],
    });
    value(Inst::Borrow { ptr: p("ptr") });
    value(Inst::BorrowMut { ptr: p("ptr") });
    value(Inst::IsUnique { ptr: p("ptr") });
    value(Inst::MakeAggregate {
        ty: Ty::Tuple(vec![Ty::I32, Ty::I64]),
        variant: None,
        fields: vec![p("i32"), p("i64")],
    });
    value(Inst::MakeClosure {
        ty: trust_ir::ClosureTyId::new(0),
        func: FuncId::new(1),
        captures: vec![p("ptr")],
    });
    // v50: `[x; n]` over the catalog's `i32` element type (`types[0]`), at a
    // small and a huge lane count (the map's stances never read `n`).
    for len in [2, 1 << 40] {
        value(Inst::ArraySplat {
            ty: Ty::Array(TyId::new(0), len),
            value: p("i32"),
        });
    }
    value(Inst::OpenFrame {
        def: BindingFrameDef::new(
            BindingFrameId::new(0),
            "frame",
            vec![BindingSlot::new("x", Ty::I64)],
        ),
    });
    value(Inst::LoadSlot {
        frame: p("ptr"),
        slot: 0,
        ty: Ty::I64,
    });
    value(Inst::BindSlot {
        frame: p("ptr"),
        slot: 0,
        value: p("i64"),
    });
    // This catalog probes the named opcode gate, not malformed result metadata.
    // `value` binds one SSA lane, so declare its actual type as well.
    value(Inst::DialectOp(Box::new(
        DialectInst::new("verif", "op").with_result_ty(Ty::I64),
    )));
    for inst in [
        Inst::Assume { cond: p("bool") },
        Inst::Assert {
            cond: p("bool"),
            kind: trust_ir::AssertKind::Unspecified,
            site: None,
        },
        Inst::EndBorrow {
            borrow_ptr: p("ptr"),
        },
        Inst::Retain { ptr: p("ptr") },
        Inst::Release { ptr: p("ptr") },
        Inst::Dealloc { ptr: p("ptr") },
        Inst::MemCopy {
            dst: p("ptr"),
            src: p("ptr"),
            bytes: p("usize"),
            overlap: false,
        },
        Inst::MemCopy {
            dst: p("ptr"),
            src: p("ptr"),
            bytes: p("usize"),
            overlap: true,
        },
        Inst::MemSet {
            dst: p("ptr"),
            byte: p("u8"),
            bytes: p("usize"),
        },
        Inst::CloseFrame { frame: p("ptr") },
    ] {
        out.push((inst, 0, false));
    }
    out.push((
        Inst::LandingPad {
            is_cleanup: true,
            catch_type_indices: vec![],
        },
        2,
        false,
    ));
    // Terminators (each ends the catalog function's entry block).
    for inst in [
        Inst::Return {
            values: vec![p("i64")],
        },
        Inst::Unreachable,
        Inst::Br {
            target: BlockId::new(1),
            args: vec![],
        },
        Inst::CondBr {
            cond: p("bool"),
            then_target: BlockId::new(1),
            then_args: vec![],
            else_target: BlockId::new(1),
            else_args: vec![],
        },
        Inst::Switch {
            value: p("u64"),
            default: BlockId::new(1),
            default_args: vec![],
            cases: vec![SwitchCase {
                value: Constant::Int(3),
                target: BlockId::new(1),
                args: vec![],
            }],
            exhaustive_enum_unreachable: false,
        },
        Inst::CoroSuspend {
            frame: p("ptr"),
            state_slot: 0,
            next_state: 1,
            value: p("i64"),
        },
        Inst::Invoke {
            callee: FuncId::new(2),
            args: vec![],
            normal_dest: BlockId::new(1),
            normal_args: vec![],
            unwind_dest: BlockId::new(1),
        },
        Inst::Resume { exn: p("ptr") },
        assert_invoke(),
        drop_invoke(),
        invoke_indirect(),
    ] {
        out.push((inst, 0, true));
    }
    out
}

/// v55 (amendment D): a drop with an unwind edge through the `ptr` parameter.
fn drop_invoke() -> Inst {
    Inst::DropInvoke {
        ty: Ty::I64,
        ptr: p("ptr"),
        normal_dest: BlockId::new(1),
        normal_args: vec![],
        unwind_dest: BlockId::new(1),
    }
}

/// v56 (amendment D Part 2): an indirect call with an unwind edge.
fn invoke_indirect() -> Inst {
    Inst::InvokeIndirect {
        callee: p("ptr"),
        sig: FuncTyId::new(1),
        args: vec![],
        calling_conv: trust_ir::CallingConv::default(),
        normal_dest: BlockId::new(1),
        normal_args: vec![],
        unwind_dest: BlockId::new(1),
    }
}

/// v54 (amendment P): the site the catalog's sited checks name — the bodied
/// callee `g: (ptr) -> ()` (the signature a zero-operand kind's entry must
/// have) with the `ptr` parameter as the run-time location.
fn catalog_panic_site() -> trust_ir::PanicSite {
    trust_ir::PanicSite {
        entry: FuncId::new(1),
        location: trust_ir::PanicLocation::Value(p("ptr")),
    }
}

fn sited_assert() -> Inst {
    Inst::Assert {
        cond: p("bool"),
        kind: trust_ir::AssertKind::DivByZero,
        site: Some(catalog_panic_site()),
    }
}

fn assert_invoke() -> Inst {
    Inst::AssertInvoke {
        cond: p("bool"),
        kind: trust_ir::AssertKind::DivByZero,
        site: catalog_panic_site(),
        normal_dest: BlockId::new(1),
        normal_args: vec![],
        unwind_dest: BlockId::new(1),
    }
}

/// A module holding one catalog function `f` whose entry block runs `inst`
/// (then returns, unless `inst` is the terminator), plus a bodied callee
/// `g(ptr)`, an external `ext()` and the bulk-memory symbol `memset`.
fn catalog_case(inst: &Inst, results: usize, terminator: bool) -> Module {
    let mut module = catalog_module();
    let mut params = params();
    params.extend(tensor_params(inst).into_iter().map(|ty| ("tensor", ty)));
    module.func_types.push(FuncTy {
        params: params.iter().map(|(_, ty)| ty.clone()).collect(),
        returns: vec![Ty::I64],
        abi: None,
        is_vararg: false,
    });
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![],
        abi: None,
        is_vararg: false,
    });
    module.func_types.push(FuncTy {
        params: vec![],
        returns: vec![],
        abi: None,
        is_vararg: false,
    });
    if matches!(inst, Inst::MakeClosure { .. }) {
        module.closure_types.push(trust_ir::ClosureTy {
            func: FuncTyId::new(2),
            captures: vec![Ty::Ptr],
        });
    }
    let mut f = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
    let mut entry = Block {
        id: BlockId::new(0),
        params: params
            .iter()
            .enumerate()
            .map(|(index, (_, ty))| (ValueId::new(index as u32), ty.clone()))
            .collect(),
        body: Vec::new(),
    };
    let first_result = params.len() as u32;
    entry.body.push(
        InstrNode::new(inst.clone())
            .with_results((0..results as u32).map(|offset| ValueId::new(first_result + offset))),
    );
    if !terminator {
        entry.body.push(InstrNode::new(Inst::Return {
            values: vec![p("i64")],
        }));
    }
    let exit = Block {
        id: BlockId::new(1),
        params: vec![],
        body: vec![InstrNode::new(Inst::Return {
            values: vec![p("i64")],
        })],
    };
    f.blocks = vec![entry, exit];
    module.functions.push(f);
    let mut g = Function::new(FuncId::new(1), "g", FuncTyId::new(1), BlockId::new(0));
    g.blocks = vec![Block {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body: vec![InstrNode::new(Inst::Return { values: vec![] })],
    }];
    module.functions.push(g);
    module.functions.push(Function::new(
        FuncId::new(2),
        "ext",
        FuncTyId::new(2),
        BlockId::new(0),
    ));
    // C's `memset(void *, int, size_t) -> void *`: only with it does the
    // lowering read a call of `memset` as the library routine.
    module.func_types.push(FuncTy {
        params: vec![Ty::Ptr, Ty::I32, Ty::Usize],
        returns: vec![Ty::Ptr],
        abi: None,
        is_vararg: false,
    });
    module.functions.push(Function::new(
        FuncId::new(3),
        "memset",
        FuncTyId::new(3),
        BlockId::new(0),
    ));
    module
}

/// Each catalog instance in its module, and whether the admission gate
/// admits it (`Err` when the function is skipped for a reason other than
/// the gate's).
fn gated_catalog() -> Vec<(Inst, Module, Result<bool, String>)> {
    catalog()
        .into_iter()
        .map(|(inst, results, terminator)| {
            let module = catalog_case(&inst, results, terminator);
            let report = scan_function_in_module(&module, &module.functions[0]);
            let admitted = match report.skipped_functions.first() {
                None => Ok(true),
                Some(skip)
                    if matches!(
                        skip.reason,
                        FsymTrustIrSkipReason::UnsupportedInstruction
                            | FsymTrustIrSkipReason::UnsupportedTerminator
                    ) =>
                {
                    Ok(false)
                }
                Some(skip) => Err(format!(
                    "{inst:?}: skipped for a reason other than the gate: {:?} {}",
                    skip.reason, skip.detail
                )),
            };
            (inst, module, admitted)
        })
        .collect()
}

/// trust-ir v53: a non-propagating call boundary (`Inst::CallCannotUnwind`,
/// `Inst::CallIndirectCannotUnwind`) is refused by name before any verdict:
/// fsym models no host unwinding (the reference interpreter refuses both), and
/// scanning either as an ordinary call would erase the boundary.
#[test]
fn v53_call_unwind_boundaries_are_refused_before_any_verdict() {
    let boundaries = [
        Inst::CallCannotUnwind {
            callee: FuncId::new(1),
            args: vec![p("ptr")],
        },
        Inst::CallIndirectCannotUnwind {
            callee: p("ptr"),
            sig: FuncTyId::new(1),
            args: vec![],
            calling_conv: trust_ir::CallingConv::default(),
        },
    ];
    for inst in &boundaries {
        let module = catalog_case(inst, 0, false);
        let report = scan_function_in_module(&module, &module.functions[0]);
        let skip = report
            .skipped_functions
            .first()
            .unwrap_or_else(|| panic!("{inst:?} must be refused at admission"));
        assert_eq!(skip.reason, FsymTrustIrSkipReason::UnsupportedInstruction);
        assert!(
            skip.detail.contains("non-propagating call boundary"),
            "{}",
            skip.detail
        );
    }
}

/// trust-ir v54 (amendment P): a panic site is refused by name before any
/// verdict. fsym scans the reference semantics, where a failed check is a
/// terminal panic, and owes no verdict on the panic-entry call compiled code
/// makes instead; `AssertInvoke` adds an unwind edge fsym does not model. The
/// same check WITHOUT a site is still admitted: the refusal is the site.
#[test]
fn v54_panic_sites_are_refused_before_any_verdict() {
    for (inst, terminator, reason, needle) in [
        (
            sited_assert(),
            false,
            FsymTrustIrSkipReason::UnsupportedInstruction,
            "sited check",
        ),
        (
            assert_invoke(),
            true,
            FsymTrustIrSkipReason::UnsupportedTerminator,
            "AssertInvoke",
        ),
    ] {
        let module = catalog_case(&inst, 0, terminator);
        let report = scan_function_in_module(&module, &module.functions[0]);
        let skip = report
            .skipped_functions
            .first()
            .unwrap_or_else(|| panic!("{inst:?} must be refused at admission"));
        assert_eq!(skip.reason, reason, "{}", skip.detail);
        assert!(skip.detail.contains(needle), "{}", skip.detail);
        assert!(skip.detail.contains("panic-entry"), "{}", skip.detail);
    }
    let unsited = Inst::Assert {
        cond: p("bool"),
        kind: trust_ir::AssertKind::DivByZero,
        site: None,
    };
    let module = catalog_case(&unsited, 0, false);
    let report = scan_function_in_module(&module, &module.functions[0]);
    assert!(
        report.skipped_functions.is_empty(),
        "the unsited twin must stay admitted: {:?}",
        report.skipped_functions
    );
}

/// trust-ir v55 / v56 (amendment D): the unwinding twins of a drop and of an
/// indirect call are refused by name before any verdict (fsym models no
/// destructor, no indirect callee and no unwinding), and a run under
/// `PanicStrategy::Unwind` is outside the run model, which the map's
/// `UNWIND_RAISE_ONLY` / `PAD_BINDS_ONLY_UNDER_UNWIND` stances rest on.
#[test]
fn v55_v56_unwinding_twins_are_refused_before_any_verdict() {
    for (inst, needle) in [
        (drop_invoke(), "DropInvoke"),
        (invoke_indirect(), "InvokeIndirect"),
    ] {
        let module = catalog_case(&inst, 0, true);
        let report = scan_function_in_module(&module, &module.functions[0]);
        let skip = report
            .skipped_functions
            .first()
            .unwrap_or_else(|| panic!("{inst:?} must be refused at admission"));
        assert_eq!(
            skip.reason,
            FsymTrustIrSkipReason::UnsupportedTerminator,
            "{}",
            skip.detail
        );
        assert!(skip.detail.contains(needle), "{}", skip.detail);
        assert!(skip.detail.contains("unwind"), "{}", skip.detail);
    }
    let unwind = trust_ir::InterpretOptions {
        panic_strategy: trust_ir::interpret::PanicStrategy::Unwind,
        ..trust_ir::InterpretOptions::default()
    };
    let breach = trust_cg_verify::fsym_trust_ir::FSYM_RUN_MODEL
        .breach(&unwind, &[])
        .expect("a run under PanicStrategy::Unwind is outside the run model");
    assert!(breach.contains("panic=abort"), "{breach}");
    assert_eq!(
        trust_cg_verify::fsym_trust_ir::FSYM_RUN_MODEL
            .breach(&trust_ir::InterpretOptions::default(), &[]),
        None,
        "the default Abort run is inside the run model"
    );
}

/// trust-ir v47-v49 (the crystal lane): fsym refuses what its model — the
/// reference interpreter's — does not step (`Inst::Drop`, a WEAK
/// `Inst::CmpXchg`) and every function of a module that spells an unwritten
/// aggregate lane anywhere, and a run handed one is outside the run model:
/// the `not-raised` stances of the v49 sites rest on exactly this.
/// trust-ir v68-v70: every tensor-region instruction and a `Const` of a
/// `Constant::TensorBlob` (whole or nested) are refused by name before any
/// verdict: fsym has no bounded model of tensor values, extents or the
/// module's weight-blob table.
#[test]
fn v68_v70_tensor_constructs_are_refused_before_any_verdict() {
    let skip = |module: &Module| {
        scan_function_in_module(module, &module.functions[0])
            .skipped_functions
            .first()
            .map(|skip| (skip.reason, skip.detail.clone()))
    };
    let mut refused = 0;
    for (inst, results, terminator) in catalog() {
        let name = fsym_inst_variant_name(&inst);
        if !matches!(
            inst,
            Inst::TensorMap { .. }
                | Inst::TensorReduce { .. }
                | Inst::TensorView { .. }
                | Inst::TensorGather { .. }
                | Inst::TensorScatter { .. }
        ) {
            continue;
        }
        let (reason, detail) = skip(&catalog_case(&inst, results, terminator))
            .unwrap_or_else(|| panic!("{name} is admitted"));
        assert_eq!(
            reason,
            FsymTrustIrSkipReason::UnsupportedInstruction,
            "{name}"
        );
        assert!(
            detail.contains(&format!("{name} requires "))
                && detail.contains("semantics outside bounded fsym support"),
            "{name}: {detail}"
        );
        refused += 1;
    }
    assert_eq!(
        refused, 5,
        "the catalog holds one instance of each v68/v69 instruction"
    );

    let blob = Constant::TensorBlob {
        digest: trust_ir::blob::BlobDigest::of(&[1, 0, 0, 0, 0, 0, 0, 0]),
        dims: vec![1],
    };
    for (ty, value) in [
        (Ty::Tensor(Box::new(Ty::I64), 1), blob.clone()),
        (
            Ty::Tuple(vec![Ty::I64, Ty::Tensor(Box::new(Ty::I64), 1)]),
            Constant::Aggregate(vec![Constant::Int(0), blob]),
        ),
    ] {
        let mut module = catalog_case(&Inst::Const { ty, value }, 1, false);
        module.intern_blob(vec![1, 0, 0, 0, 0, 0, 0, 0]);
        let (reason, detail) = skip(&module).expect("a weight-blob constant is refused");
        assert_eq!(reason, FsymTrustIrSkipReason::UnsupportedInstruction);
        assert!(detail.contains("Constant::TensorBlob"), "{detail}");
    }
}

#[test]
fn v47_v49_constructs_are_refused_before_any_verdict() {
    let skip_detail = |module: &Module| {
        let report = scan_function_in_module(module, &module.functions[0]);
        report
            .skipped_functions
            .first()
            .map(|skip| (skip.reason, skip.detail.clone()))
    };
    let cmpxchg = |weak| Inst::CmpXchg {
        ty: Ty::I64,
        ptr: p("ptr"),
        expected: p("i64"),
        desired: p("i64"),
        success: Ordering::SeqCst,
        failure: Ordering::SeqCst,
        weak,
    };

    let drop = catalog_case(
        &Inst::Drop {
            ty: Ty::I64,
            ptr: p("ptr"),
        },
        0,
        false,
    );
    let (reason, detail) = skip_detail(&drop).expect("a drop is refused");
    assert_eq!(reason, FsymTrustIrSkipReason::UnsupportedInstruction);
    assert!(detail.contains("destructor"), "{detail}");

    let (reason, detail) =
        skip_detail(&catalog_case(&cmpxchg(true), 2, false)).expect("a weak CAS is refused");
    assert_eq!(reason, FsymTrustIrSkipReason::UnsupportedInstruction);
    assert!(detail.contains("weak CmpXchg"), "{detail}");
    assert_eq!(
        skip_detail(&catalog_case(&cmpxchg(false), 2, false)),
        None,
        "the strong CAS stays admitted"
    );

    // The scanned function is clean; the lane is spelled elsewhere in its
    // module — in another function's `Const`, then in a global initializer.
    let lane = Constant::Aggregate(vec![Constant::Int(1), Constant::Uninit]);
    let clean = Inst::Const {
        ty: Ty::I64,
        value: Constant::Int(1),
    };
    let mut elsewhere = catalog_case(&clean, 1, false);
    assert_eq!(
        skip_detail(&elsewhere),
        None,
        "control: the clean module scans"
    );
    elsewhere.functions[1].blocks[0].body.insert(
        0,
        InstrNode::new(Inst::Const {
            ty: Ty::Tuple(vec![Ty::I64, Ty::I64]),
            value: lane.clone(),
        })
        .with_result(ValueId::new(1)),
    );
    let (reason, detail) = skip_detail(&elsewhere).expect("an unwritten lane anywhere refuses");
    assert_eq!(reason, FsymTrustIrSkipReason::UnsupportedInstruction);
    assert!(
        detail.contains("unwritten aggregate lane") && detail.contains("function `g` bb0"),
        "{detail}"
    );
    let mut global = catalog_case(&clean, 1, false);
    global.globals[0].ty = Ty::Tuple(vec![Ty::I64, Ty::I64]);
    global.globals[0].initializer = Some(lane.clone());
    let (_, detail) = skip_detail(&global).expect("an unwritten lane in a global refuses");
    assert!(detail.contains("global `G`"), "{detail}");

    let options = trust_ir::InterpretOptions::default();
    let clean_arg = InterpretValue {
        ty: Ty::Tuple(vec![Ty::Bool]),
        kind: InterpretValueKind::Aggregate(vec![InterpretValue {
            ty: Ty::Bool,
            kind: InterpretValueKind::Bool(true),
        }]),
    };
    assert_eq!(
        trust_cg_verify::fsym_trust_ir::FSYM_RUN_MODEL.breach(&options, &[clean_arg]),
        None
    );
    let unwritten_arg = InterpretValue {
        ty: Ty::Tuple(vec![Ty::Bool]),
        kind: InterpretValueKind::Aggregate(vec![InterpretValue {
            ty: Ty::Bool,
            kind: InterpretValueKind::Uninit,
        }]),
    };
    let breach = trust_cg_verify::fsym_trust_ir::FSYM_RUN_MODEL
        .breach(&options, &[unwritten_arg])
        .expect("an entry argument carrying an unwritten lane is outside the run model");
    assert!(breach.contains("unwritten aggregate lane"), "{breach}");
}

#[test]
fn dialect_gate_preserves_char_and_unresolved_result_refusals() {
    use trust_cg_verify::fsym_trust_ir::FSYM_CHAR_BINDING_REFUSAL;

    let dialect_detail = "bb0 inst0 unsupported: DialectOp `verif.op` requires dialect-specific semantics before fsym";
    let malformed_detail = "bb0 inst0: result typing unresolved or arity mismatch; cannot establish absence of Char bindings";
    for (label, result_types, result_count, reason, detail) in [
        (
            "effect-only dialect",
            vec![],
            0,
            FsymTrustIrSkipReason::UnsupportedInstruction,
            dialect_detail,
        ),
        (
            "typed dialect value",
            vec![Ty::I64],
            1,
            FsymTrustIrSkipReason::UnsupportedInstruction,
            dialect_detail,
        ),
        (
            "missing result metadata",
            vec![],
            1,
            FsymTrustIrSkipReason::MalformedCfg,
            malformed_detail,
        ),
        (
            "discarded non-Char result",
            vec![Ty::I64],
            0,
            FsymTrustIrSkipReason::MalformedCfg,
            malformed_detail,
        ),
        (
            "extra SSA result",
            vec![Ty::I64],
            2,
            FsymTrustIrSkipReason::MalformedCfg,
            malformed_detail,
        ),
        (
            "Char result",
            vec![Ty::Char],
            1,
            FsymTrustIrSkipReason::UnsupportedInstruction,
            FSYM_CHAR_BINDING_REFUSAL,
        ),
        (
            "discarded Char result",
            vec![Ty::Char],
            0,
            FsymTrustIrSkipReason::UnsupportedInstruction,
            FSYM_CHAR_BINDING_REFUSAL,
        ),
    ] {
        let inst = Inst::DialectOp(Box::new(
            DialectInst::new("verif", "op").with_result_tys(result_types.clone()),
        ));
        let module = catalog_case(&inst, result_count, false);
        let node = &module.functions[0].blocks[0].body[0];
        assert_eq!(node.result_tys(&module), result_types, "{label}");
        assert_eq!(node.results.len(), result_count, "{label}");
        let report = scan_function_in_module(&module, &module.functions[0]);
        assert_eq!(report.scanned_functions, 0, "{label}: {report:?}");
        let [skip] = report.skipped_functions.as_slice() else {
            panic!("{label}: {report:?}");
        };
        assert_eq!(skip.reason, reason, "{label}: {report:?}");
        assert_eq!(skip.detail, detail, "{label}: {report:?}");
    }
}

#[test]
fn admission_gate_follows_the_map() {
    let mut failures = Vec::new();
    let mut admitted_variants = BTreeSet::new();
    let mut seen_variants = BTreeSet::new();
    for (inst, module, admitted) in gated_catalog() {
        let name = fsym_inst_variant_name(&inst);
        seen_variants.insert(name);
        match admitted {
            Ok(true) => {}
            Ok(false) => continue,
            Err(why) => {
                failures.push(why);
                continue;
            }
        }
        admitted_variants.insert(name);
        let owed = fsym_owed_kinds(&module, &inst);
        for site in FSYM_INTERPRETER_UB_SITES {
            for raise in site.raisers.iter().filter(|raise| raise.by.contains(&name)) {
                match raise.stance {
                    FsymUbStance::Refused => failures.push(format!(
                        "{inst:?} is ADMITTED but raises `{}` ({}), which the map refuses",
                        site.message, site.function
                    )),
                    FsymUbStance::Owed { kind, applies, .. }
                        if applies(&module, &inst) && !owed.contains(&kind) =>
                    {
                        failures.push(format!(
                            "{inst:?} is ADMITTED, raises `{}` ({}), and owes no {kind:?} verdict (owes {owed:?})",
                            site.message, site.function
                        ))
                    }
                    _ => {}
                }
            }
        }
    }
    for (name, admitted) in FSYM_INST_VARIANTS {
        if !seen_variants.contains(name) {
            failures.push(format!("the catalog has no instance of `{name}`"));
        } else if admitted_variants.contains(name) != *admitted {
            failures.push(format!(
                "FSYM_INST_VARIANTS says `{name}` admitted={admitted}, the gate admits {} catalog instance(s) of it",
                if admitted_variants.contains(name) { "some" } else { "no" }
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// An `Owed` stance restricted by a shape predicate (`applies`, with an
/// `otherwise` saying why the other shapes cannot raise the site) is a
/// derivation only if the predicate accepts the shapes that DO raise it: a
/// predicate no admitted instance of a raiser satisfies says, unreviewed,
/// that the site never arises from that raiser (a predicate rejecting
/// every materializing `GlobalAddr` would silently drop the owed placement
/// verdict). Each (restricted Owed stance, admitted raiser) pair
/// must have a catalog instance the gate admits and the predicate accepts.
#[test]
fn every_restricted_owed_shape_accepts_an_admitted_instance() {
    let catalog = gated_catalog();
    let mut failures = Vec::new();
    let mut pairs = 0usize;
    for site in FSYM_INTERPRETER_UB_SITES {
        for raise in site.raisers {
            let FsymUbStance::Owed {
                applies, otherwise, ..
            } = raise.stance
            else {
                continue;
            };
            if otherwise.is_empty() {
                continue; // owed at every instance
            }
            for name in raise.by {
                let admitted = FSYM_INST_VARIANTS
                    .iter()
                    .any(|(variant, admitted)| variant == name && *admitted);
                if !admitted {
                    continue;
                }
                pairs += 1;
                let accepted = catalog.iter().any(|(inst, module, gate)| {
                    fsym_inst_variant_name(inst) == *name
                        && gate == &Ok(true)
                        && applies(module, inst)
                });
                if !accepted {
                    failures.push(format!(
                        "{} `{}`: the Owed stance for {name} accepts no admitted catalog instance of it (add the raising shape to the catalog, or the predicate is vacuous)",
                        site.function, site.message
                    ));
                }
            }
        }
    }
    assert!(
        pairs >= 20,
        "only {pairs} restricted (stance, raiser) pairs"
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The verdict kinds an `Owed` / `AtSource` stance names that are NOT its
/// site's class kind: `(site function, site message, raiser group, kind,
/// why)`. Every other owed kind is DERIVED: it must be the kind its site's
/// class is `Checked` with in `FSYM_TRUST_IR_UB_CLASSES` (the class says what
/// the site's UB is; the kind is the verdict fsym owes for it). An entry no
/// stance matches fails too.
const OWED_KIND_EXCEPTIONS: &[(&str, &str, &[&str], FsymTrustIrDiagnosticKind, &str)] = &[
    (
        "expect_pointer",
        "{op}: null pointer dereference",
        &["Dealloc"],
        FsymTrustIrDiagnosticKind::InvalidFree,
        "`Dealloc` of null is the free's own obligation: fsym's Dealloc check records it as an invalid free, not a dereference",
    ),
    (
        "expect_pointer",
        "{op}: pointer value {addr} has no allocation prove",
        &["Dealloc"],
        FsymTrustIrDiagnosticKind::InvalidFree,
        "`Dealloc` of an address naming no allocation frees nothing fsym tracks: an invalid free",
    ),
];

#[test]
fn every_owed_kind_is_its_class_kind_or_a_pinned_exception() {
    let mut failures = Vec::new();
    let mut used = BTreeSet::new();
    let mut derived = 0usize;
    for site in FSYM_INTERPRETER_UB_SITES {
        let class_kind = FSYM_TRUST_IR_UB_CLASSES
            .iter()
            .find(|class| class.name == site.class)
            .and_then(|class| match class.status {
                FsymUbClassStatus::Checked(kind) => Some(kind),
                FsymUbClassStatus::NotChecked => None,
            });
        for raise in site.raisers {
            let kind = match raise.stance {
                FsymUbStance::Owed { kind, .. } | FsymUbStance::AtSource { kind, .. } => kind,
                FsymUbStance::Refused | FsymUbStance::NotRaised(_) | FsymUbStance::Outside(_) => {
                    continue;
                }
            };
            if class_kind == Some(kind) {
                derived += 1;
                continue;
            }
            match OWED_KIND_EXCEPTIONS.iter().position(|(function, message, by, k, _)| {
                *function == site.function && *message == site.message && *by == raise.by && *k == kind
            }) {
                Some(index) => {
                    used.insert(index);
                }
                None => failures.push(format!(
                    "{} `{}` by {:?}: owes a {kind:?} verdict, but its class `{}` is checked as {class_kind:?} (fix the stance, or pin the exception with why)",
                    site.function, site.message, raise.by, site.class
                )),
            }
        }
    }
    for (index, entry) in OWED_KIND_EXCEPTIONS.iter().enumerate() {
        if !used.contains(&index) {
            failures.push(format!(
                "OWED_KIND_EXCEPTIONS entry {:?} matches no stance",
                (entry.0, entry.1, entry.2, entry.3)
            ));
        }
    }
    assert!(
        derived >= 50,
        "only {derived} owed kinds derived from their class"
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

// ---------------------------------------------------------------------------
// Hand-stated stances: each is confirmed mechanically, or reviewed
// ---------------------------------------------------------------------------

/// FNV-1a, 64 bits: a fingerprint of a ported function's source.
fn fingerprint(text: &str) -> u64 {
    text.bytes().fold(0xcbf2_9ce4_8422_2325, |hash, byte| {
        (hash ^ u64::from(byte)).wrapping_mul(0x0100_0000_01b3)
    })
}

/// The interpreter's non-test source, lexed.
fn interpreter_non_test() -> Lexed {
    let (_, source) = interpreter_source();
    lex(&non_test_source(&source))
}

/// Whether the gate refuses a `Switch` whose case constant is not a
/// `Constant::Int` (the only switch shape that could materialize a global).
fn gate_refuses_non_int_switch_cases() -> bool {
    let mut module = catalog_module();
    module.func_types.push(FuncTy {
        params: vec![Ty::U64],
        returns: vec![Ty::I64],
        abi: None,
        is_vararg: false,
    });
    let mut f = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
    let ret = |id: u32| Block {
        id: BlockId::new(id),
        params: vec![],
        body: vec![InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        })],
    };
    f.blocks = vec![
        Block {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::U64)],
            body: vec![InstrNode::new(Inst::Switch {
                value: ValueId::new(0),
                default: BlockId::new(1),
                default_args: vec![],
                cases: vec![SwitchCase {
                    value: Constant::SymbolAddr {
                        symbol: "G".to_string(),
                        addend: 0,
                    },
                    target: BlockId::new(2),
                    args: vec![],
                }],
                exhaustive_enum_unreachable: false,
            })],
        },
        ret(1),
        ret(2),
    ];
    module.functions.push(f);
    let report = scan_function_in_module(&module, &module.functions[0]);
    report.skipped_functions.len() == 1
}

/// Confirm a claim mechanically, when its reason is one this test can check
/// at the claimed site: `Some(Ok)` confirmed, `Some(Err)` refuted, `None`
/// not mechanically checkable (it must then be reviewed).
fn confirm_claim(
    lexed: &Lexed,
    derived: &Derived,
    site: &trust_cg_verify::fsym_ub_map::FsymInterpreterUbSite,
    by: &[&str],
    kind: &str,
    reason: &str,
) -> Option<Result<(), String>> {
    // Where the interpreter removes an allocation record (a pointer the run
    // made could then name an unknown allocation).
    let removes = || {
        [
            "allocations.remove(",
            "allocations.retain(",
            "allocations.clear(",
            "allocations.drain(",
            "allocations.split_off(",
            "allocations.pop_first(",
            "allocations.pop_last(",
            "allocations.extract_if(",
            ".allocations =",
        ]
        .into_iter()
        .filter(|needle| find(&lexed.code, needle.as_bytes(), 0).is_some())
        .collect::<Vec<_>>()
    };
    let pseudo = |raiser: &&str| *raiser == RAISER_ENTRY || *raiser == RAISER_WALK;
    if kind == "outside" {
        if reason == FORGED_ENTRY_POINTER {
            // An instruction's `unknown allocation` UB, only on a pointer no
            // run makes: the embedder's forgery is outside the run model.
            return Some(
                match (
                    site.message.contains("unknown allocation"),
                    by.iter().any(pseudo),
                    removes().as_slice(),
                ) {
                    (false, _, _) => {
                        Err("the reason speaks for an `unknown allocation` site only".to_string())
                    }
                    (true, true, _) => Err(format!(
                        "the reason speaks for instructions, and {by:?} names a pseudo-raiser"
                    )),
                    (true, false, []) => Ok(()),
                    (true, false, found) => Err(format!("the interpreter now does {found:?}")),
                },
            );
        }
        // Otherwise only a pseudo-raiser (the harness's entry, the block
        // walk) can be outside a scanned body.
        return Some(if by.iter().all(pseudo) {
            Ok(())
        } else {
            Err(format!(
                "Outside names instructions {by:?}; an instruction's UB is outside a scanned body only in a run outside the run model (FORGED_ENTRY_POINTER)"
            ))
        });
    }
    if kind != "not-raised" {
        return None;
    }
    if reason.starts_with("the interpreter never removes an allocation record") {
        // True of the pointers a global's materialization makes and encodes
        // itself; any other raiser takes a pointer operand from the program,
        // which may be an entry argument the embedder forged.
        let run_made = by
            .iter()
            .all(|raiser| ["Const", "GlobalAddr"].contains(raiser));
        return Some(
            match (
                site.message.contains("unknown allocation"),
                run_made,
                removes().as_slice(),
            ) {
                (false, _, _) => {
                    Err("the reason speaks for an `unknown allocation` site only".to_string())
                }
                (true, false, _) => Err(format!(
                    "{by:?} take a pointer operand from the program, which may be an entry argument the embedder forged (an allocation the run never made): state it Outside(FORGED_ENTRY_POINTER), or owe it"
                )),
                (true, true, []) => Ok(()),
                (true, true, found) => Err(format!("the interpreter now does {found:?}")),
            },
        );
    }
    if reason.starts_with("the interpreter runs on a 64-bit host") {
        return Some(
            match (site.message.contains("does not fit usize"), usize::BITS) {
                (true, 64) => Ok(()),
                (false, _) => {
                    Err("the reason speaks for a `does not fit usize` site only".to_string())
                }
                (true, bits) => Err(format!("this host's usize is {bits} bits")),
            },
        );
    }
    if reason.starts_with("a failed check allocates its exception object") {
        // trust-ir v56: the reason speaks for `Assert` reaching the site ONLY
        // through `raise_exception` (with that call cut, the arm must no
        // longer reach it), and for every `raise_exception` call being
        // guarded by `PanicStrategy::Unwind`, the strategy
        // `FsymRunModel::breach` places outside the run model.
        let key = (site.function.to_string(), site.message.to_string());
        let reached = derived.arm_reach("Assert", &[]).contains(&key);
        let reached_otherwise = derived
            .arm_reach("Assert", &["raise_exception"])
            .contains(&key);
        let unguarded = unwind_unguarded_calls(lexed, b"raise_exception(");
        let outside = trust_cg_verify::fsym_trust_ir::FSYM_RUN_MODEL
            .breach(
                &trust_ir::InterpretOptions {
                    panic_strategy: trust_ir::interpret::PanicStrategy::Unwind,
                    ..trust_ir::InterpretOptions::default()
                },
                &[],
            )
            .is_some();
        return Some(
            match (
                by == ["Assert"],
                reached && !reached_otherwise,
                unguarded.as_slice(),
                outside,
            ) {
                (true, true, [], true) => Ok(()),
                (false, _, _, _) => Err("the reason speaks for `Assert` only".to_string()),
                (true, false, _, _) => Err(format!(
                    "`Assert` reaches this site {}",
                    if reached {
                        "other than through `raise_exception`"
                    } else {
                        "not at all (stale)"
                    }
                )),
                (true, true, found, _) if !found.is_empty() => Err(format!(
                    "`raise_exception` is called without a `PanicStrategy::Unwind` guard at byte(s) {found:?}"
                )),
                (true, true, _, _) => Err(
                    "the run model admits a `PanicStrategy::Unwind` run (`FsymRunModel::breach`)"
                        .to_string(),
                ),
            },
        );
    }
    if reason.starts_with("fsym admits only `Constant::Int` switch cases") {
        // The reason speaks for the sites a `Switch` reaches by converting
        // its case constants (`constant_to_value`, which materializes a
        // symbol's global) and for no other: with that call cut, the arm must
        // no longer reach the site — a site the arm reaches directly (its
        // selector's poison inspection) is not one an integer case avoids.
        let key = (site.function.to_string(), site.message.to_string());
        let reached_otherwise = derived
            .arm_reach("Switch", &["constant_to_value"])
            .contains(&key);
        let reached = derived.arm_reach("Switch", &[]).contains(&key);
        return Some(
            match (
                by == ["Switch"],
                reached && !reached_otherwise,
                gate_refuses_non_int_switch_cases(),
            ) {
                (true, true, true) => Ok(()),
                (false, _, _) => Err("the reason speaks for `Switch` only".to_string()),
                (true, false, _) => Err(format!(
                    "`Switch` reaches this site {}: an integer case constant does not keep it from the site",
                    if reached {
                        "other than by converting its case constants (`constant_to_value`)"
                    } else {
                        "not at all (stale)"
                    }
                )),
                (true, true, false) => {
                    Err("the gate admits a switch case that is not a Constant::Int".to_string())
                }
            },
        );
    }
    None
}

/// The calls to `needle` (`name(`) in the interpreter's non-test code, other
/// than its definition, that no `panic_strategy == PanicStrategy::Unwind`
/// test precedes within the few lines before the call: their byte offsets.
fn unwind_unguarded_calls(lexed: &Lexed, needle: &[u8]) -> Vec<usize> {
    const GUARD: &[u8] = b"panic_strategy == PanicStrategy::Unwind";
    const WINDOW: usize = 240;
    let mut unguarded = Vec::new();
    let mut from = 0;
    while let Some(at) = find(&lexed.code, needle, from) {
        from = at + needle.len();
        if at >= 3 && &lexed.code[at - 3..at] == b"fn " {
            continue;
        }
        let window = &lexed.code[at.saturating_sub(WINDOW)..at];
        if find(window, GUARD, 0).is_none() {
            unguarded.push(at);
        }
    }
    unguarded
}

/// The REVIEWED hand-stated claims: `(site function, site message, raiser
/// group, stance kind)`. Each was checked against the interpreter by reading
/// the code the site's reason names. A claim not listed here (and not
/// confirmed mechanically) fails
/// `every_hand_stated_stance_is_confirmed_or_reviewed`, and so does an entry no
/// claim matches. Moving a claim to another site or raiser group, or changing
/// its stance kind, therefore needs a new review.
const REVIEWED_CLAIMS: &[(&str, &str, &[&str], &str)] = &[
    // v63 flat construction, reviewed against eval_make_closure at 6d2e381:
    // no Char/handle/nested capture is admitted, every source Char binding is
    // refused, and all captures are explicit SSA values. Constant::Uninit is
    // refused module-wide; poison can only originate at an owed Load site.
    (
        "check_char_validity",
        "`char` value {:#x} is not a Unicode scalar value (",
        &["MakeClosure"],
        "not-raised",
    ),
    (
        "reject_partial",
        "{op}: use of an unwritten aggregate lane (uninit) ",
        &["MakeClosure"],
        "not-raised",
    ),
    (
        "reject_partial_error",
        "{op}: use of an uninitialized value — poison (unin",
        &["MakeClosure"],
        "at-source",
    ),
    // trust-ir v56 (amendment D Part 2): the `LandingPad` arm binds its two
    // results (`bind_results`, reaching `check_char_validity`) only under
    // `self.options.panic_strategy == PanicStrategy::Unwind` with an
    // exception in hand; otherwise it refuses (`UnsupportedInstruction`,
    // "landingpad entered without an unwind edge"). Reviewed at 0be81d5c.
    (
        "check_char_validity",
        "`char` value {:#x} is not a Unicode scalar value (",
        &["LandingPad"],
        "not-raised",
    ),
    // v54 (amendment P), reviewed against the interpreter at 6f2dfce6: its
    // Assert arm reaches `resolve_panic_location` only through
    // `assert_panic`'s `Some(site)` arm (an unsited check resolves no
    // location), and the admission gate refuses every sited Assert by name
    // (`unsupported_nonterminator_detail`), so no scanned Assert raises it.
    (
        "resolve_panic_location",
        "assert: panic location is null or dangling",
        &["Assert"],
        "not-raised",
    ),
    (
        "check_char_validity",
        "`char` value {:#x} is not a Unicode scalar value (",
        trust_cg_verify::fsym_ub_map::CHAR_BINDING_RAISERS,
        "not-raised",
    ),
    (
        "eval_alloca",
        "Alloca: count must be positive",
        &["Alloca", "HeapAlloc"],
        "owed-otherwise",
    ),
    (
        "eval_alloca",
        "Alloca: count {} does not fit u64",
        &["Alloca", "HeapAlloc"],
        "owed-otherwise",
    ),
    (
        "eval_alloca",
        "Alloca: allocation size overflow",
        &["Alloca", "HeapAlloc"],
        "owed-otherwise",
    ),
    (
        "address",
        "{op}: pointer address overflow",
        &["Const", "GlobalAddr"],
        "owed-otherwise",
    ),
    // eval_icmp enters address/check_address ONLY inside its Ty::Ptr arm.
    // The integer/Boolean cases never materialize an operand's address.
    (
        "address",
        "{op}: pointer address overflow",
        &["ICmp"],
        "owed-otherwise",
    ),
    (
        "check_address",
        "{op}: address {address:#x} is outside the target's",
        &["ICmp"],
        "owed-otherwise",
    ),
    (
        "check_address",
        "{op}: address {address:#x} is outside the target's",
        &["Const", "GlobalAddr"],
        "owed-otherwise",
    ),
    (
        "alloc_with_slack",
        "Alloca: allocation id overflow",
        &["Alloca", "HeapAlloc"],
        "not-raised",
    ),
    (
        "alloc_with_slack",
        "Alloca: allocation id overflow",
        &["Const", "GlobalAddr"],
        "not-raised",
    ),
    (
        "eval_mem_copy",
        "MemCopy: source [{}..{}) and destination [{}..{}) ",
        &["MemCopy"],
        "owed-otherwise",
    ),
    (
        "eval_cast",
        "{op}: NaN cannot be converted to integer",
        &["Cast"],
        "owed-otherwise",
    ),
    (
        "eval_cast",
        "{op}: {value} out of range for {dst_ty}",
        &["Cast"],
        "owed-otherwise",
    ),
    (
        "eval_cast",
        "{op}: address {} does not fit u64",
        &["Cast"],
        "owed-otherwise",
    ),
    (
        "check_address",
        "{op}: address {address:#x} is outside the target's",
        &["Cast"],
        "owed-otherwise",
    ),
    (
        "eval_bitcast",
        "Bitcast: address {} does not fit u64",
        &["Cast"],
        "owed-otherwise",
    ),
    (
        "address",
        "{op}: pointer address overflow",
        &["Cast"],
        "owed-otherwise",
    ),
    (
        "address",
        "{op}: pointer address overflow",
        &["Store", "AtomicStore", "AtomicRMW", "CmpXchg"],
        "owed-otherwise",
    ),
    (
        "check_address",
        "{op}: address {address:#x} is outside the target's",
        &["Store", "AtomicStore", "AtomicRMW", "CmpXchg"],
        "owed-otherwise",
    ),
    (
        "checked_access",
        "{op}: use after dealloc",
        &["Const", "GlobalAddr"],
        "not-raised",
    ),
    (
        "checked_access",
        "{op}: pointer address overflow",
        &["Const", "GlobalAddr"],
        "not-raised",
    ),
    (
        "checked_access",
        "{op}: pointer address {address} is not aligned to ",
        &["Const", "GlobalAddr"],
        "not-raised",
    ),
    (
        "checked_access",
        "{op}: access range overflow",
        &["Const", "GlobalAddr"],
        "not-raised",
    ),
    (
        "checked_access",
        "{op}: access [{}..{}) is out of bounds for allocat",
        &["Const", "GlobalAddr"],
        "not-raised",
    ),
    (
        "checked_access",
        "{op}: pointer address {address} is not aligned to ",
        &["MemCopy", "MemSet"],
        "not-raised",
    ),
    (
        "expect_pointer",
        "{op}: pointer value {addr} has no allocation prove",
        &["GEP"],
        "not-raised",
    ),
    (
        "eval_int_binop",
        "unsigned division by zero",
        &["BinOp"],
        "owed-otherwise",
    ),
    (
        "eval_int_binop",
        "unsigned division by zero",
        &["Overflow"],
        "not-raised",
    ),
    (
        "eval_int_binop",
        "unsigned remainder by zero",
        &["Overflow"],
        "not-raised",
    ),
    (
        "eval_int_binop",
        "signed division by zero",
        &["Overflow"],
        "not-raised",
    ),
    (
        "eval_int_binop",
        "signed division overflow",
        &["Overflow"],
        "not-raised",
    ),
    (
        "eval_int_binop",
        "signed remainder by zero",
        &["Overflow"],
        "not-raised",
    ),
    (
        "eval_int_binop",
        "signed remainder overflow",
        &["Overflow"],
        "not-raised",
    ),
    (
        "shift_amount",
        "shift amount {} is out of range for {bits}-bit int",
        &["Overflow"],
        "not-raised",
    ),
    (
        "eval_int_binop",
        "unsigned division by zero",
        &["AtomicRMW"],
        "not-raised",
    ),
    (
        "eval_int_binop",
        "unsigned remainder by zero",
        &["AtomicRMW"],
        "not-raised",
    ),
    (
        "eval_int_binop",
        "signed division by zero",
        &["AtomicRMW"],
        "not-raised",
    ),
    (
        "eval_int_binop",
        "signed division overflow",
        &["AtomicRMW"],
        "not-raised",
    ),
    (
        "eval_int_binop",
        "signed remainder by zero",
        &["AtomicRMW"],
        "not-raised",
    ),
    (
        "eval_int_binop",
        "signed remainder overflow",
        &["AtomicRMW"],
        "not-raised",
    ),
    (
        "shift_amount",
        "shift amount {} is out of range for {bits}-bit int",
        &["AtomicRMW"],
        "not-raised",
    ),
    (
        "eval_int_binop",
        "unsigned remainder by zero",
        &["BinOp"],
        "owed-otherwise",
    ),
    (
        "eval_int_binop",
        "signed division by zero",
        &["BinOp"],
        "owed-otherwise",
    ),
    (
        "eval_int_binop",
        "signed division overflow",
        &["BinOp"],
        "owed-otherwise",
    ),
    (
        "eval_int_binop",
        "signed remainder by zero",
        &["BinOp"],
        "owed-otherwise",
    ),
    (
        "eval_int_binop",
        "signed remainder overflow",
        &["BinOp"],
        "owed-otherwise",
    ),
    (
        "shift_amount",
        "shift amount {} is out of range for {bits}-bit int",
        &["BinOp"],
        "owed-otherwise",
    ),
    (
        "reject_partial_error",
        "{op}: use of an uninitialized value — poison (unin",
        &[
            "<entry>",
            "<walk>",
            "Alloca",
            "ArraySplat",
            "Assert",
            "Assume",
            "AtomicLoad",
            "AtomicRMW",
            "AtomicStore",
            "BinOp",
            "BindSlot",
            "Borrow",
            "BorrowMut",
            "Call",
            "CallIndirect",
            "Cast",
            "CloseFrame",
            "CmpXchg",
            "CondBr",
            "Const",
            "CoroSuspend",
            "Dealloc",
            "DialectOp",
            "ExtractElement",
            "ExtractField",
            "FCmp",
            "GEP",
            "GlobalAddr",
            "HeapAlloc",
            "ICmp",
            "InsertElement",
            "InsertField",
            "Invoke",
            "IsUnique",
            "Load",
            "LoadSlot",
            "MakeAggregate",
            "MemCopy",
            "MemSet",
            "Overflow",
            "PtrData",
            "PtrFromParts",
            "PtrMetadata",
            "Release",
            "Retain",
            "Select",
            "SeqMap",
            "Store",
            "Switch",
            "UnOp",
        ],
        "at-source",
    ),
    (
        "execute_callee",
        "<callee body>",
        &["Call"],
        "owed-otherwise",
    ),
    (
        "decode_image_with_unwritten_lanes",
        "Load: reading uninitialized byte at offset {} of a",
        &["Load", "AtomicLoad", "AtomicRMW", "CmpXchg"],
        "not-raised",
    ),
    (
        "encode_image",
        "encoding an unwritten lane (uninit) of type {} as ",
        &["Store", "AtomicStore", "AtomicRMW", "CmpXchg"],
        "not-raised",
    ),
    (
        "encode_image",
        "encoding an unwritten lane (uninit) of type {} as ",
        &["Const", "GlobalAddr"],
        "not-raised",
    ),
    (
        "encode_image",
        "encoding an unwritten lane (uninit) of type {} as ",
        &["Switch"],
        "not-raised",
    ),
    (
        "eval_extract_field",
        "extract_field: field {field} of {} is an unwritten",
        &["ExtractField"],
        "not-raised",
    ),
    (
        "eval_store",
        "Store (atomic/volatile): the stored aggregate has ",
        &["Store", "AtomicStore", "AtomicRMW", "CmpXchg"],
        "not-raised",
    ),
    (
        "reject_partial",
        "{op}: use of an unwritten aggregate lane (uninit) ",
        &[
            "<walk>",
            "Alloca",
            "ArraySplat",
            "Assert",
            "Assume",
            "AtomicLoad",
            "AtomicRMW",
            "AtomicStore",
            "BinOp",
            "BindSlot",
            "Borrow",
            "BorrowMut",
            "Call",
            "CallIndirect",
            "Cast",
            "CloseFrame",
            "CmpXchg",
            "CondBr",
            "Const",
            "CoroSuspend",
            "Dealloc",
            "DialectOp",
            "ExtractElement",
            "ExtractField",
            "FCmp",
            "GEP",
            "GlobalAddr",
            "HeapAlloc",
            "ICmp",
            "InsertElement",
            "InsertField",
            "Invoke",
            "IsUnique",
            "Load",
            "LoadSlot",
            "MakeAggregate",
            "MemCopy",
            "MemSet",
            "Overflow",
            "PtrData",
            "PtrFromParts",
            "PtrMetadata",
            "Release",
            "Retain",
            "Select",
            "SeqMap",
            "Store",
            "Switch",
            "UnOp",
        ],
        "not-raised",
    ),
    (
        "checked_access",
        "{op}: unknown allocation {}",
        &["Alloca", "HeapAlloc"],
        "not-raised",
    ),
    (
        "checked_access",
        "{op}: use after dealloc",
        &["Alloca", "HeapAlloc"],
        "not-raised",
    ),
    (
        "checked_access",
        "{op}: pointer address overflow",
        &["Alloca", "HeapAlloc"],
        "not-raised",
    ),
    (
        "checked_access",
        "{op}: pointer address {address} is not aligned to ",
        &["Alloca", "HeapAlloc"],
        "not-raised",
    ),
    (
        "checked_access",
        "{op}: access range overflow",
        &["Alloca", "HeapAlloc"],
        "not-raised",
    ),
    (
        "checked_access",
        "{op}: access [{}..{}) is out of bounds for allocat",
        &["Alloca", "HeapAlloc"],
        "not-raised",
    ),
];

/// Every stance that is a CLAIM rather than a derivation — a `NotRaised` /
/// `Outside` reason, an `Owed` stance's `otherwise` (why the site cannot
/// arise from the shapes `applies` rejects), an `AtSource` detail — is either
/// CONFIRMED mechanically (`confirm_claim`) or REVIEWED (`REVIEWED_CLAIMS`,
/// keyed on its site, raiser group and stance kind). A new claim, or one
/// moved to another site or raiser group, fails here on its own: `Retain`
/// admitted with `NotRaised("verifier fake")` does.
#[test]
fn every_hand_stated_stance_is_confirmed_or_reviewed() {
    let lexed = interpreter_non_test();
    let derived = derive(&interpreter_source().1);
    let mut failures = Vec::new();
    let mut used = BTreeSet::new();
    for site in FSYM_INTERPRETER_UB_SITES {
        for raise in site.raisers {
            let (kind, reason) = match raise.stance {
                FsymUbStance::NotRaised(reason) => ("not-raised", reason),
                FsymUbStance::Outside(reason) => ("outside", reason),
                FsymUbStance::Owed { otherwise, .. } if !otherwise.is_empty() => {
                    ("owed-otherwise", otherwise)
                }
                FsymUbStance::AtSource { detail, .. } => ("at-source", detail),
                FsymUbStance::Owed { .. } | FsymUbStance::Refused => continue,
            };
            match confirm_claim(&lexed, &derived, site, raise.by, kind, reason) {
                Some(Ok(())) => continue,
                Some(Err(why)) => {
                    failures.push(format!(
                        "{} `{}` by {:?}: {kind} claim REFUTED: {why}",
                        site.function, site.message, raise.by
                    ));
                    continue;
                }
                None => {}
            }
            match REVIEWED_CLAIMS.iter().position(|(function, message, by, k)| {
                *function == site.function
                    && *message == site.message
                    && *by == raise.by
                    && *k == kind
            }) {
                Some(index) => {
                    used.insert(index);
                }
                None => failures.push(format!(
                    "unreviewed {kind} claim (review it against the interpreter, then list it):\n    ({:?}, {:?}, &{:?}, {kind:?}), // {reason}",
                    site.function, site.message, raise.by
                )),
            }
        }
    }
    for (index, entry) in REVIEWED_CLAIMS.iter().enumerate() {
        if !used.contains(&index) {
            failures.push(format!(
                "REVIEWED_CLAIMS entry {entry:?} matches no claim in the map"
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "{} stance claim(s) neither confirmed nor reviewed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// The interpreter functions `fsym_layout` ports are the pinned rev's, as
/// fingerprinted in `FSYM_LAYOUT_PORTED_FROM`: a trust-ir bump that changes
/// one fails here until the port is re-derived from it.
#[test]
fn the_layout_port_matches_the_pinned_interpreter() {
    let lexed = interpreter_non_test();
    let code = &lexed.code;
    let items = functions(code);
    let mut failures = Vec::new();
    for (name, pinned) in trust_cg_verify::fsym_layout::FSYM_LAYOUT_PORTED_FROM {
        let bodies = items
            .iter()
            .filter(|item| item.name == *name)
            .collect::<Vec<_>>();
        let [item] = bodies.as_slice() else {
            failures.push(format!(
                "`{name}`: {} definition(s) in the interpreter",
                bodies.len()
            ));
            continue;
        };
        let text = String::from_utf8_lossy(&code[item.body_start..=item.body_end])
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        let print = fingerprint(&text);
        if print != *pinned {
            failures.push(format!("(\"{name}\", {print:#018x}),"));
        }
    }
    assert!(
        trust_cg_verify::fsym_layout::FSYM_LAYOUT_PORTED_FROM.len() >= 15,
        "the port names too few interpreter functions"
    );
    assert!(
        failures.is_empty(),
        "interpreter layout functions changed since fsym_layout ported them (re-derive the port, re-run tests/fsym_layout.rs, then pin):\n{}",
        failures.join("\n")
    );
}

// ---------------------------------------------------------------------------
// Observed raisers: every UB the interpreter raises at an admitted instance is
// one the map's stance owes there
// ---------------------------------------------------------------------------

/// A pointer operand a trigger hands its instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PtrKind {
    Null,
    /// A filled 64-byte allocation, at its base.
    Alloc,
    /// That allocation moved `2^64 - 8` bytes by a GEP (64-bit targets): an
    /// offset the interpreter keeps, with no address.
    PastSpace,
    /// An address naming no allocation (`inttoptr`).
    Dangling,
    /// An entry argument naming an allocation the run never made.
    Forged,
    /// An entry argument with no provenance at an address past 2^32 (32-bit
    /// targets).
    ForgedDangling,
}

const PTR_KINDS: [PtrKind; 6] = [
    PtrKind::Null,
    PtrKind::Alloc,
    PtrKind::PastSpace,
    PtrKind::Dangling,
    PtrKind::Forged,
    PtrKind::ForgedDangling,
];

/// Whether `kind` can be built at `pointer_size`-byte pointers: a GEP
/// `2^64 - 8` bytes past an allocation faults at 32 bits, and an address past
/// 2^32 is only unrepresentable there.
fn ptr_kind_at(kind: PtrKind, pointer_size: u32) -> bool {
    match kind {
        PtrKind::PastSpace => pointer_size == 8,
        PtrKind::ForgedDangling => pointer_size == 4,
        _ => true,
    }
}

/// One trigger: `f` builds operands in bb0 and runs ONE instance alone in
/// bb1 (the block an error names is then the instance's), then returns.
struct Trigger {
    what: String,
    module: Module,
    args: Vec<InterpretValue>,
    /// An entry argument is a pointer the embedder forged.
    forged: bool,
    /// A placement as large as the address space: before trust-ir v50 it
    /// faulted as UB past an unbounded memory budget; since v50 it must be
    /// refused `OutOfMemory`.
    past_bounds: bool,
}

struct TriggerBuilder {
    module: Module,
    params: Vec<(ValueId, Ty)>,
    args: Vec<InterpretValue>,
    setup: Vec<InstrNode>,
    next: u32,
    forged: bool,
    past_bounds: bool,
}

impl TriggerBuilder {
    /// A trigger over a module with 8- or 4-byte pointers, the byte type, and
    /// globals `G: i64 = 0`, `H: &i64 = &G` and `B: [u8; 64]`.
    fn new(pointer_size: u32) -> Self {
        let mut module = catalog_module();
        if let Some(target) = &mut module.target_info {
            target.pointer_size = pointer_size;
            if pointer_size == 4 {
                target.triple = "wasm32-unknown-unknown".to_string();
            }
        }
        module.types = vec![Ty::U8];
        module.globals.push(trust_ir::Global {
            name: "H".to_string(),
            ty: Ty::Ref(Box::new(Ty::I64)),
            initializer: Some(Constant::SymbolAddr {
                symbol: "G".to_string(),
                addend: 0,
            }),
            ..module.globals[0].clone()
        });
        module.globals.push(trust_ir::Global {
            name: "B".to_string(),
            ty: Ty::Array(TyId::new(0), 64),
            initializer: None,
            ..module.globals[0].clone()
        });
        Self {
            module,
            params: Vec::new(),
            args: Vec::new(),
            setup: Vec::new(),
            next: 0,
            forged: false,
            past_bounds: false,
        }
    }

    fn fresh(&mut self) -> ValueId {
        self.next += 1;
        ValueId::new(self.next - 1)
    }

    fn value(&mut self, inst: Inst) -> ValueId {
        let result = self.fresh();
        self.setup.push(InstrNode::new(inst).with_result(result));
        result
    }

    fn effect(&mut self, inst: Inst) {
        self.setup.push(InstrNode::new(inst));
    }

    fn constant(&mut self, ty: &Ty, value: Constant) -> ValueId {
        self.value(Inst::Const {
            ty: ty.clone(),
            value,
        })
    }

    fn size_ty(&self) -> Ty {
        Ty::Usize
    }

    fn ptr(&mut self, kind: PtrKind) -> ValueId {
        match kind {
            PtrKind::Null => self.value(Inst::NullPtr),
            PtrKind::Alloc | PtrKind::PastSpace => {
                let size_ty = self.size_ty();
                let count = self.constant(&size_ty, Constant::Int(64));
                let base = self.value(Inst::Alloca {
                    ty: Ty::U8,
                    count: Some(count),
                    align: Some(16),
                });
                let fill = self.constant(&Ty::U8, Constant::Int(1));
                self.effect(Inst::MemSet {
                    dst: base,
                    byte: fill,
                    bytes: count,
                });
                if kind == PtrKind::Alloc {
                    return base;
                }
                let far = self.constant(&Ty::U64, Constant::Int(i128::from(u64::MAX - 7)));
                self.value(Inst::GEP {
                    pointee_ty: Ty::U8,
                    base,
                    indices: vec![far],
                    inbounds: false,
                })
            }
            PtrKind::Dangling => {
                let address = self.constant(&Ty::U64, Constant::Int(0x10_0000));
                self.value(Inst::Cast {
                    op: CastOp::IntToPtr,
                    src_ty: Ty::U64,
                    dst_ty: Ty::Ptr,
                    operand: address,
                })
            }
            PtrKind::Forged | PtrKind::ForgedDangling => {
                let param = self.fresh();
                self.params.push((param, Ty::Ptr));
                self.args.push(InterpretValue {
                    ty: Ty::Ptr,
                    kind: if kind == PtrKind::Forged {
                        InterpretValueKind::Ptr(trust_ir::interpret::InterpretPointer {
                            allocation: 1000,
                            offset: 0,
                        })
                    } else {
                        InterpretValueKind::DanglingPtr(1 << 40)
                    },
                });
                self.forged = true;
                param
            }
        }
    }

    /// One-byte allocations at alignments `2^63 .. 2^lowest`: the bump
    /// pointer then at `2^64 - 2^lowest + 1` (64-bit targets).
    fn exhaust(&mut self, lowest: u32) {
        for shift in (lowest..=63).rev() {
            self.value(Inst::Alloca {
                ty: Ty::U8,
                count: None,
                align: Some(1u64 << shift),
            });
        }
    }

    fn finish(mut self, what: String, instance: Inst, results: usize) -> Trigger {
        let results = (0..results).map(|_| self.fresh()).collect::<Vec<_>>();
        let zero = self.fresh();
        self.module.func_types = vec![FuncTy {
            params: self.params.iter().map(|(_, ty)| ty.clone()).collect(),
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        }];
        let mut setup = self.setup;
        setup.push(InstrNode::new(Inst::Br {
            target: BlockId::new(1),
            args: vec![],
        }));
        let mut f = Function::new(FuncId::new(0), "f", FuncTyId::new(0), BlockId::new(0));
        f.blocks = vec![
            Block {
                id: BlockId::new(0),
                params: self.params,
                body: setup,
            },
            Block {
                id: BlockId::new(1),
                params: vec![],
                body: vec![
                    InstrNode::new(instance).with_results(results),
                    InstrNode::new(Inst::Br {
                        target: BlockId::new(2),
                        args: vec![],
                    }),
                ],
            },
            Block {
                id: BlockId::new(2),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(0),
                    })
                    .with_result(zero),
                    InstrNode::new(Inst::Return { values: vec![zero] }),
                ],
            },
        ];
        self.module.functions = vec![f];
        Trigger {
            what,
            module: self.module,
            args: self.args,
            forged: self.forged,
            past_bounds: self.past_bounds,
        }
    }
}

/// Every `BinOp`, `UnOp` and `CastOp` (EXHAUSTIVE: a new variant fails to
/// compile until the observation catalog runs it).
fn all_binops() -> Vec<BinOp> {
    let ops = [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::UDiv,
        BinOp::SDiv,
        BinOp::URem,
        BinOp::SRem,
        BinOp::FAdd,
        BinOp::FSub,
        BinOp::FMul,
        BinOp::FDiv,
        BinOp::FRem,
        BinOp::FMin,
        BinOp::FMax,
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
        BinOp::Shl,
        BinOp::LShr,
        BinOp::AShr,
        BinOp::BAnd,
        BinOp::BOr,
        BinOp::BXor,
        BinOp::RotL,
        BinOp::RotR,
        BinOp::FCopySign,
    ];
    for op in ops {
        match op {
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::UDiv
            | BinOp::SDiv
            | BinOp::URem
            | BinOp::SRem
            | BinOp::FAdd
            | BinOp::FSub
            | BinOp::FMul
            | BinOp::FDiv
            | BinOp::FRem
            | BinOp::FMin
            | BinOp::FMax
            | BinOp::And
            | BinOp::Or
            | BinOp::Xor
            | BinOp::Shl
            | BinOp::LShr
            | BinOp::AShr
            | BinOp::BAnd
            | BinOp::BOr
            | BinOp::BXor
            | BinOp::RotL
            | BinOp::RotR
            | BinOp::FCopySign => {}
        }
    }
    ops.to_vec()
}

fn all_unops() -> Vec<UnOp> {
    let ops = [
        UnOp::Neg,
        UnOp::FNeg,
        UnOp::FAbs,
        UnOp::FSqrt,
        UnOp::FFloor,
        UnOp::FCeil,
        UnOp::FTrunc,
        UnOp::Not,
        UnOp::CtPop,
        UnOp::CtLz,
        UnOp::CtTz,
        UnOp::BSwap,
        UnOp::BitReverse,
    ];
    for op in ops {
        match op {
            UnOp::Neg
            | UnOp::FNeg
            | UnOp::FAbs
            | UnOp::FSqrt
            | UnOp::FFloor
            | UnOp::FCeil
            | UnOp::FTrunc
            | UnOp::Not
            | UnOp::CtPop
            | UnOp::CtLz
            | UnOp::CtTz
            | UnOp::BSwap
            | UnOp::BitReverse => {}
        }
    }
    ops.to_vec()
}

fn all_castops() -> Vec<CastOp> {
    let ops = [
        CastOp::Trunc,
        CastOp::ZExt,
        CastOp::SExt,
        CastOp::FPTrunc,
        CastOp::FPExt,
        CastOp::FPToUI,
        CastOp::FPToSI,
        CastOp::UIToFP,
        CastOp::SIToFP,
        CastOp::PtrToInt,
        CastOp::IntToPtr,
        CastOp::PtrToPtr,
        CastOp::Bitcast,
        CastOp::Transmute,
        CastOp::ReifyFnPointer,
        CastOp::FPToSISat,
        CastOp::FPToUISat,
    ];
    for op in ops {
        match op {
            CastOp::Trunc
            | CastOp::ZExt
            | CastOp::SExt
            | CastOp::FPTrunc
            | CastOp::FPExt
            | CastOp::FPToUI
            | CastOp::FPToSI
            | CastOp::UIToFP
            | CastOp::SIToFP
            | CastOp::PtrToInt
            | CastOp::IntToPtr
            | CastOp::PtrToPtr
            | CastOp::Bitcast
            | CastOp::Transmute
            | CastOp::ReifyFnPointer
            | CastOp::FPToSISat
            | CastOp::FPToUISat => {}
        }
    }
    ops.to_vec()
}

/// Scalar values of `ty` that reach the interpreter's edges: zero, one, all
/// ones, the signed minimum, 2^32 and 2^64 where they fit; NaN, infinities
/// and out-of-range magnitudes for a float.
fn edge_values(ty: &Ty, pointer_bits: u32) -> Vec<Constant> {
    if ty.is_float() {
        return [f64::NAN, f64::INFINITY, -1.5, 1e30, 3.0, 300.0]
            .into_iter()
            .map(Constant::Float)
            .collect();
    }
    if *ty == Ty::Bool {
        return vec![Constant::Bool(false), Constant::Bool(true)];
    }
    let bits = match ty {
        Ty::Usize | Ty::Isize => pointer_bits,
        ty => ty.bit_width_with(pointer_bits).unwrap_or(64),
    };
    let (min, max) = match (ty.is_signed(), bits) {
        (true, 128..) => (i128::MIN, i128::MAX),
        (true, _) => (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1),
        (false, 127..) => (0, i128::MAX),
        (false, _) => (0, (1i128 << bits) - 1),
    };
    let mut values = vec![0, 1, 3, max, min, 200, i128::from(bits)];
    if ty.is_signed() {
        values.push(-1);
    }
    values.extend([1i128 << 32, 1i128 << 64]);
    values.retain(|value| (min..=max).contains(value));
    values.sort_unstable();
    values.dedup();
    values.into_iter().map(Constant::Int).collect()
}

/// Instances of every raising shape the map's predicates distinguish, each
/// with operands at the interpreter's edges.
fn triggers() -> Vec<Trigger> {
    let mut out = Vec::new();
    let int_tys = [
        Ty::U8,
        Ty::I8,
        Ty::U32,
        Ty::I32,
        Ty::U64,
        Ty::I64,
        Ty::U128,
        Ty::I128,
        Ty::Usize,
        Ty::Isize,
    ];
    let vector = Ty::Vector(Box::new(Ty::I32), 4);
    // Integer, float and vector arithmetic.
    for op in all_binops() {
        for ty in int_tys.iter().chain(&[Ty::F64, Ty::Bool]) {
            let values = edge_values(ty, 64);
            for lhs in &values {
                for rhs in &values {
                    let mut t = TriggerBuilder::new(8);
                    let l = t.constant(ty, lhs.clone());
                    let r = t.constant(ty, rhs.clone());
                    out.push(t.finish(
                        format!("{op:?} {ty:?} {lhs:?} {rhs:?}"),
                        Inst::BinOp {
                            op,
                            ty: ty.clone(),
                            lhs: l,
                            rhs: r,
                        },
                        1,
                    ));
                }
            }
        }
        for (lhs, rhs) in [(7, 0), (i128::from(i32::MIN), -1), (1, 200), (1, 32)] {
            let mut t = TriggerBuilder::new(8);
            let lanes = |v: i128| Constant::Vector(vec![Constant::Int(v); 4]);
            let l = t.constant(&vector, lanes(lhs));
            let r = t.constant(&vector, lanes(rhs));
            out.push(t.finish(
                format!("{op:?} <4 x i32> {lhs} {rhs}"),
                Inst::BinOp {
                    op,
                    ty: vector.clone(),
                    lhs: l,
                    rhs: r,
                },
                1,
            ));
        }
    }
    for op in all_unops() {
        for ty in int_tys.iter().chain(&[Ty::F64]) {
            for value in edge_values(ty, 64) {
                let mut t = TriggerBuilder::new(8);
                let operand = t.constant(ty, value.clone());
                out.push(t.finish(
                    format!("{op:?} {ty:?} {value:?}"),
                    Inst::UnOp {
                        op,
                        ty: ty.clone(),
                        operand,
                    },
                    1,
                ));
            }
        }
    }
    // Casts, at both pointer widths.
    let cast_tys = [
        Ty::Bool,
        Ty::U8,
        Ty::I8,
        Ty::U32,
        Ty::I32,
        Ty::U64,
        Ty::I64,
        Ty::U128,
        Ty::I128,
        Ty::Usize,
        Ty::F32,
        Ty::F64,
        Ty::Ptr,
    ];
    for pointer_size in [8u32, 4] {
        for op in all_castops() {
            for src in &cast_tys {
                for dst in &cast_tys {
                    let operands: Vec<Result<Constant, PtrKind>> = if *src == Ty::Ptr {
                        PTR_KINDS
                            .into_iter()
                            .filter(|kind| ptr_kind_at(*kind, pointer_size))
                            .map(Err)
                            .collect()
                    } else {
                        edge_values(src, pointer_size * 8)
                            .into_iter()
                            .map(Ok)
                            .collect()
                    };
                    for operand in operands {
                        let mut t = TriggerBuilder::new(pointer_size);
                        let value = match &operand {
                            Ok(value) => t.constant(src, value.clone()),
                            Err(kind) => t.ptr(*kind),
                        };
                        out.push(t.finish(
                            format!("{op:?} {src:?} -> {dst:?} of {operand:?} at {pointer_size}-byte pointers"),
                            Inst::Cast {
                                op,
                                src_ty: src.clone(),
                                dst_ty: dst.clone(),
                                operand: value,
                            },
                            1,
                        ));
                    }
                }
            }
        }
    }
    // Exercise both pointer operands at both widths. The source-derived
    // checks decide which address sites the pinned interpreter actually raises.
    for pointer_size in [8u32, 4] {
        for kind in PTR_KINDS {
            if !ptr_kind_at(kind, pointer_size) {
                continue;
            }
            for left in [true, false] {
                let mut t = TriggerBuilder::new(pointer_size);
                let target = t.ptr(kind);
                let other = t.ptr(PtrKind::Alloc);
                let (lhs, rhs) = if left {
                    (target, other)
                } else {
                    (other, target)
                };
                out.push(t.finish(
                    format!("ICmp {kind:?} on left={left} at {pointer_size}-byte pointers"),
                    Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::Ptr,
                        lhs,
                        rhs,
                    },
                    1,
                ));
            }
        }
    }
    // Accesses, address exposures, frees and borrows through every pointer
    // kind, and stores of every pointer kind.
    for pointer_size in [8u32, 4] {
        for kind in PTR_KINDS {
            if !ptr_kind_at(kind, pointer_size) {
                continue;
            }
            let access = |t: &mut TriggerBuilder, target: ValueId| -> Vec<(String, Inst, usize)> {
                let one = t.constant(&Ty::U64, Constant::Int(1));
                let eight = t.constant(&Ty::Usize, Constant::Int(8));
                let other = t.ptr(PtrKind::Alloc);
                vec![
                    (
                        "Load".to_string(),
                        Inst::Load {
                            ty: Ty::U64,
                            ptr: target,
                            volatile: false,
                            align: None,
                        },
                        1,
                    ),
                    (
                        "Store".to_string(),
                        Inst::Store {
                            ty: Ty::U64,
                            ptr: target,
                            value: one,
                            volatile: false,
                            align: None,
                        },
                        0,
                    ),
                    (
                        "AtomicLoad".to_string(),
                        Inst::AtomicLoad {
                            ty: Ty::U64,
                            ptr: target,
                            ordering: Ordering::SeqCst,
                        },
                        1,
                    ),
                    (
                        "AtomicStore".to_string(),
                        Inst::AtomicStore {
                            ty: Ty::U64,
                            ptr: target,
                            value: one,
                            ordering: Ordering::SeqCst,
                        },
                        0,
                    ),
                    (
                        "AtomicRMW".to_string(),
                        Inst::AtomicRMW {
                            op: AtomicRMWOp::Add,
                            ty: Ty::U64,
                            ptr: target,
                            value: one,
                            ordering: Ordering::SeqCst,
                        },
                        1,
                    ),
                    (
                        "CmpXchg".to_string(),
                        Inst::CmpXchg {
                            ty: Ty::U64,
                            ptr: target,
                            expected: one,
                            desired: one,
                            success: Ordering::SeqCst,
                            failure: Ordering::SeqCst,
                            weak: false,
                        },
                        2,
                    ),
                    (
                        "MemSet".to_string(),
                        Inst::MemSet {
                            dst: target,
                            byte: t.constant(&Ty::U8, Constant::Int(0)),
                            bytes: eight,
                        },
                        0,
                    ),
                    (
                        "MemCopy into".to_string(),
                        Inst::MemCopy {
                            dst: target,
                            src: other,
                            bytes: eight,
                            overlap: false,
                        },
                        0,
                    ),
                    (
                        "MemCopy from".to_string(),
                        Inst::MemCopy {
                            dst: other,
                            src: target,
                            bytes: eight,
                            overlap: true,
                        },
                        0,
                    ),
                    ("Dealloc".to_string(), Inst::Dealloc { ptr: target }, 0),
                    ("Borrow".to_string(), Inst::Borrow { ptr: target }, 1),
                    ("BorrowMut".to_string(), Inst::BorrowMut { ptr: target }, 1),
                ]
            };
            // Build once to learn the shapes, then once per shape.
            let shapes = access(&mut TriggerBuilder::new(pointer_size), ValueId::new(0)).len();
            for index in 0..shapes {
                let mut t = TriggerBuilder::new(pointer_size);
                let target = t.ptr(kind);
                let (what, inst, results) = access(&mut t, target).swap_remove(index);
                out.push(t.finish(
                    format!("{what} through {kind:?} at {pointer_size}-byte pointers"),
                    inst,
                    results,
                ));
            }
            // Compare either operand position, including a genuinely
            // unrepresentable allocation offset at 64 bits and an entry
            // dangling address outside the 32-bit target's address space.
            for pointer_on_left in [true, false] {
                let mut t = TriggerBuilder::new(pointer_size);
                let pointer = t.ptr(kind);
                let null = t.ptr(PtrKind::Null);
                let (lhs, rhs) = if pointer_on_left {
                    (pointer, null)
                } else {
                    (null, pointer)
                };
                out.push(t.finish(
                    format!(
                        "ICmp {kind:?}, pointer_on_left {pointer_on_left} at {pointer_size}-byte pointers"
                    ),
                    Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::Ptr,
                        lhs,
                        rhs,
                    },
                    1,
                ));
            }
            for index in [
                Constant::Int(0),
                Constant::Int(1),
                Constant::Int(-1),
                Constant::Int(1 << 40),
            ] {
                for index_ty in [Ty::I64, Ty::U64] {
                    if matches!(index, Constant::Int(-1)) && index_ty == Ty::U64 {
                        continue;
                    }
                    let mut t = TriggerBuilder::new(pointer_size);
                    let base = t.ptr(kind);
                    let index_value = t.constant(&index_ty, index.clone());
                    out.push(t.finish(
                        format!(
                            "GEP {kind:?} by {index_ty:?} {index:?} at {pointer_size}-byte pointers"
                        ),
                        Inst::GEP {
                            pointee_ty: Ty::U8,
                            base,
                            indices: vec![index_value],
                            inbounds: false,
                        },
                        1,
                    ));
                }
            }
            {
                let mut t = TriggerBuilder::new(pointer_size);
                let base = t.ptr(kind);
                out.push(t.finish(
                    format!("GEP {kind:?} with no index at {pointer_size}-byte pointers"),
                    Inst::GEP {
                        pointee_ty: Ty::U8,
                        base,
                        indices: vec![],
                        inbounds: false,
                    },
                    1,
                ));
            }
            // A pointer VALUE stored.
            for (what, store) in [
                ("Store", 0usize),
                ("AtomicStore", 1),
                ("AtomicRMW", 2),
                ("CmpXchg", 3),
            ] {
                let mut t = TriggerBuilder::new(pointer_size);
                let value = t.ptr(kind);
                let slot = t.ptr(PtrKind::Alloc);
                // The slot holds null, so a compare-exchange from null stores.
                let null = t.value(Inst::NullPtr);
                t.effect(Inst::Store {
                    ty: Ty::Ptr,
                    ptr: slot,
                    value: null,
                    volatile: false,
                    align: None,
                });
                let (inst, results) = match store {
                    0 => (
                        Inst::Store {
                            ty: Ty::Ptr,
                            ptr: slot,
                            value,
                            volatile: false,
                            align: None,
                        },
                        0,
                    ),
                    1 => (
                        Inst::AtomicStore {
                            ty: Ty::Ptr,
                            ptr: slot,
                            value,
                            ordering: Ordering::SeqCst,
                        },
                        0,
                    ),
                    2 => (
                        Inst::AtomicRMW {
                            op: AtomicRMWOp::Xchg,
                            ty: Ty::Ptr,
                            ptr: slot,
                            value,
                            ordering: Ordering::SeqCst,
                        },
                        1,
                    ),
                    _ => (
                        Inst::CmpXchg {
                            ty: Ty::Ptr,
                            ptr: slot,
                            expected: null,
                            desired: value,
                            success: Ordering::SeqCst,
                            failure: Ordering::SeqCst,
                            weak: false,
                        },
                        2,
                    ),
                };
                out.push(t.finish(
                    format!("{what} of {kind:?} at {pointer_size}-byte pointers"),
                    inst,
                    results,
                ));
            }
        }
    }
    // Placements (allocations and globals' first materializations), from
    // fresh memory and with the bump pointer near 2^64.
    let materializers = || {
        vec![
            (
                Inst::GlobalAddr {
                    global: GlobalId::new(0),
                },
                "GlobalAddr G",
            ),
            (
                Inst::GlobalAddr {
                    global: GlobalId::new(1),
                },
                "GlobalAddr H",
            ),
            (
                Inst::Const {
                    ty: Ty::Ref(Box::new(Ty::I64)),
                    value: Constant::SymbolAddr {
                        symbol: "G".to_string(),
                        addend: 0,
                    },
                },
                "Const &G",
            ),
            (
                Inst::GlobalAddr {
                    global: GlobalId::new(2),
                },
                "GlobalAddr B",
            ),
            (
                Inst::Const {
                    ty: Ty::Ref(Box::new(Ty::U8)),
                    value: Constant::SymbolAddr {
                        symbol: "B".to_string(),
                        addend: 0,
                    },
                },
                "Const &B",
            ),
            (
                Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(0),
                },
                "Const 0",
            ),
        ]
    };
    for lowest in [None, Some(3u32), Some(4), Some(5), Some(12)] {
        for heap in [false, true] {
            for ty in [Ty::U8, Ty::I64, Ty::Unit] {
                for count in [
                    None,
                    Some((Ty::U64, 0)),
                    Some((Ty::U64, 16)),
                    Some((Ty::I64, -1)),
                    Some((Ty::U64, i128::from(u64::MAX))),
                    Some((Ty::U128, 1i128 << 64)),
                ] {
                    for align in [
                        None,
                        Some(1u64),
                        Some(8),
                        Some(4096),
                        Some(8192),
                        Some(1 << 63),
                    ] {
                        let mut t = TriggerBuilder::new(8);
                        if let Some(lowest) = lowest {
                            t.exhaust(lowest);
                        }
                        let count_value = count
                            .clone()
                            .map(|(ty, value)| t.constant(&ty, Constant::Int(value)));
                        let inst = if heap {
                            Inst::HeapAlloc {
                                ty: ty.clone(),
                                count: count_value,
                                align,
                                origin: AllocOrigin::CMalloc,
                            }
                        } else {
                            Inst::Alloca {
                                ty: ty.clone(),
                                count: count_value,
                                align,
                            }
                        };
                        out.push(t.finish(
                            format!("{} {ty:?} x {count:?} align {align:?} after placements down to {lowest:?}", if heap { "HeapAlloc" } else { "Alloca" }),
                            inst,
                            1,
                        ));
                    }
                }
            }
        }
        for (inst, what) in materializers() {
            let mut t = TriggerBuilder::new(8);
            if let Some(lowest) = lowest {
                t.exhaust(lowest);
            }
            out.push(t.finish(
                format!("{what} after placements down to {lowest:?}"),
                inst,
                1,
            ));
        }
    }
    // A placement as large as the address space exhausts it from fresh memory
    // at both widths, and at 32 bits so does one of 2^63 bytes at alignment
    // 2^63 (whose base is 2^63). Before trust-ir v50 a run with an unbounded
    // memory budget faulted each as UB ("base / next address overflow");
    // since v50 there is no budget and the interpreter refuses each
    // (OutOfMemory) before any host memory is touched.
    for pointer_size in [8u32, 4] {
        let huge = Ty::Array(TyId::new(0), u64::MAX);
        let mut placements = vec![
            (Ty::U8, Some(i128::from(u64::MAX)), Some(1u64), false),
            (Ty::U8, Some(i128::from(u64::MAX)), None, true),
            (huge.clone(), None, None, false),
            (huge.clone(), None, None, true),
        ];
        if pointer_size == 4 {
            placements.push((Ty::U8, Some(1i128 << 63), Some(1 << 63), false));
        }
        for (ty, count, align, heap) in placements {
            let mut t = TriggerBuilder::new(pointer_size);
            t.past_bounds = true;
            let count_value = count.map(|count| t.constant(&Ty::U64, Constant::Int(count)));
            let inst = if heap {
                Inst::HeapAlloc {
                    ty: ty.clone(),
                    count: count_value,
                    align,
                    origin: AllocOrigin::CMalloc,
                }
            } else {
                Inst::Alloca {
                    ty: ty.clone(),
                    count: count_value,
                    align,
                }
            };
            out.push(t.finish(
                format!(
                    "{} {ty:?} x {count:?} align {align:?} at {pointer_size}-byte pointers, as large as the address space",
                    if heap { "HeapAlloc" } else { "Alloca" }
                ),
                inst,
                1,
            ));
        }
        let mut t = TriggerBuilder::new(pointer_size);
        t.past_bounds = true;
        t.module.globals.push(trust_ir::Global {
            name: "Huge".to_string(),
            ty: huge,
            initializer: None,
            ..t.module.globals[0].clone()
        });
        let huge_global = GlobalId::new(t.module.globals.len() as u32 - 1);
        out.push(t.finish(
            format!(
                "GlobalAddr Huge ([u8; 2^64 - 1]) at {pointer_size}-byte pointers, as large as the address space"
            ),
            Inst::GlobalAddr {
                global: huge_global,
            },
            1,
        ));
    }
    // At 32 bits, a global initializer pointing one past a global placed to
    // end exactly at 2^32 (one-byte placements at 2^31 .. 2^12 first).
    for through_const in [false, true] {
        let mut t = TriggerBuilder::new(4);
        t.module.globals.push(trust_ir::Global {
            name: "G1".to_string(),
            ty: Ty::Array(TyId::new(0), 4064),
            initializer: None,
            ..t.module.globals[0].clone()
        });
        t.module.globals.push(trust_ir::Global {
            name: "G2".to_string(),
            ty: Ty::PtrConst(Box::new(Ty::U8)),
            initializer: Some(Constant::SymbolAddr {
                symbol: "G1".to_string(),
                addend: 4064,
            }),
            ..t.module.globals[0].clone()
        });
        for shift in (12..=31).rev() {
            t.value(Inst::Alloca {
                ty: Ty::U8,
                count: None,
                align: Some(1u64 << shift),
            });
        }
        let inst = if through_const {
            Inst::Const {
                ty: Ty::Ref(Box::new(Ty::PtrConst(Box::new(Ty::U8)))),
                value: Constant::SymbolAddr {
                    symbol: "G2".to_string(),
                    addend: 0,
                },
            }
        } else {
            Inst::GlobalAddr {
                global: GlobalId::new(4),
            }
        };
        out.push(t.finish(
            format!("materializing G2 = &G1 + 4064, G1 ending at 2^32 (through a Const: {through_const})"),
            inst,
            1,
        ));
    }
    // memcpy vs memmove over overlapping ranges.
    for overlap in [false, true] {
        let mut t = TriggerBuilder::new(8);
        let base = t.ptr(PtrKind::Alloc);
        let four = t.constant(&Ty::I64, Constant::Int(4));
        let dst = t.value(Inst::GEP {
            pointee_ty: Ty::U8,
            base,
            indices: vec![four],
            inbounds: false,
        });
        let eight = t.constant(&Ty::Usize, Constant::Int(8));
        out.push(t.finish(
            format!("MemCopy overlapping, overlap {overlap}"),
            Inst::MemCopy {
                dst,
                src: base,
                bytes: eight,
                overlap,
            },
            0,
        ));
    }
    out
}

/// Every UB the interpreter raises at an ADMITTED catalog instance (each
/// shape the map's predicates distinguish — every BinOp, UnOp and CastOp at
/// every scalar type and edge value, at both pointer widths; accesses, frees,
/// borrows, GEPs, address exposures and stores through and of every kind of
/// pointer, a forged entry pointer included; placements from fresh memory and
/// with the bump pointer near 2^64) must be one the map's stance for the site
/// and that raiser OWES there: `Owed` with its shape predicate accepting the
/// instance, `AtSource`, `Refused`, or — for an argument the embedder forged —
/// `Outside(FORGED_ENTRY_POINTER)`. A placement as large as the address space
/// (the `past_bounds` triggers) raises no UB since trust-ir v50 deleted the
/// interpreter's memory budget: the interpreter must refuse it `OutOfMemory`
/// at its instance, and fsym must still report the instance (an Unknown
/// naming its 2^62-byte bound, never a verdict). A predicate narrowed
/// below what the interpreter raises (a float-to-int cast, a shift, a
/// pointer/integer cast dropped from it; a placement restricted by
/// alignment), a `NotRaised` the interpreter refutes, or a site with no
/// stance for the raiser fails here, whatever the review list says: the
/// raiser set is the interpreter's, observed. And every restricted `Owed`
/// stance (one whose predicate is not `always`) must be observed at an
/// admitted instance, so the catalog exercises what it guards.
#[test]
fn every_raise_the_interpreter_shows_is_owed_by_its_stance() {
    let mut failures = Vec::new();
    let mut observed = BTreeSet::new();
    let mut raised = 0usize;
    let triggers = triggers();
    let mut past_bounds_refused = 0usize;
    let run = |trigger: &Trigger| {
        trust_ir::Interpreter::with_module(&trigger.module)
            .with_options(trust_ir::InterpretOptions {
                fuel: 10_000,
                max_call_depth: 4,
                panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
            })
            .execute_func(FuncId::new(0), trigger.args.clone())
    };
    let raised_at_instance = |error: &trust_ir::InterpretError| {
        error.code == trust_ir::InterpretErrorCode::UndefinedBehavior
            && error.block == Some(BlockId::new(1))
    };
    for trigger in &triggers {
        let outcome = run(trigger);
        if trigger.past_bounds {
            // trust-ir v50: no memory budget, and exhausting the address
            // space is `OutOfMemory` — an incapacity of the model, not UB.
            match &outcome {
                Err(error)
                    if error.code == trust_ir::InterpretErrorCode::OutOfMemory
                        && error.block == Some(BlockId::new(1)) =>
                {
                    past_bounds_refused += 1;
                }
                other => failures.push(format!(
                    "{}: a placement past the address space must be refused OutOfMemory at its instance, got {other:?}",
                    trigger.what
                )),
            }
            // fsym does not decide it: it reports the instance.
            let report = scan_function_in_module(&trigger.module, &trigger.module.functions[0]);
            let decided = report
                .unknown_obligations
                .iter()
                .any(|u| u.block == 1 && u.inst_index == 0)
                || report
                    .diagnostics
                    .iter()
                    .any(|d| d.block == 1 && d.inst_index == 0);
            if report.skipped_functions.is_empty() && !decided {
                failures.push(format!(
                    "{}: a placement past fsym's 2^62-byte bound, and fsym reports nothing at the instance",
                    trigger.what
                ));
            }
            continue;
        }
        let error = match outcome {
            Err(error) if raised_at_instance(&error) => error,
            _ => continue,
        };
        let report = scan_function_in_module(&trigger.module, &trigger.module.functions[0]);
        if !report.skipped_functions.is_empty() {
            continue; // refused: fsym claims nothing about it
        }
        raised += 1;
        let inst = &trigger.module.functions[0].blocks[1].body[0].inst;
        let name = fsym_inst_variant_name(inst);
        let sites = FSYM_INTERPRETER_UB_SITES
            .iter()
            .filter(|site| {
                site.function != CALLEE_FUNCTION
                    && fsym_site_message_matches(site.message, &error.message)
            })
            .collect::<Vec<_>>();
        let mut owed = false;
        let mut why = Vec::new();
        for site in &sites {
            let raises = site
                .raisers
                .iter()
                .filter(|raise| raise.by.contains(&name))
                .collect::<Vec<_>>();
            if raises.is_empty() {
                why.push(format!(
                    "{} `{}`: no stance for {name}",
                    site.function, site.message
                ));
            }
            for raise in raises {
                match raise.stance {
                    FsymUbStance::Owed {
                        applies, otherwise, ..
                    } => {
                        if applies(&trigger.module, inst) {
                            owed = true;
                            observed.insert((
                                site.function,
                                site.message,
                                name,
                                otherwise.is_empty(),
                            ));
                        } else {
                            why.push(format!(
                                "{} `{}`: the {name} predicate rejects it",
                                site.function, site.message
                            ));
                        }
                    }
                    FsymUbStance::AtSource { .. } | FsymUbStance::Refused => owed = true,
                    FsymUbStance::Outside(reason)
                        if trigger.forged && reason == FORGED_ENTRY_POINTER =>
                    {
                        owed = true;
                    }
                    FsymUbStance::Outside(reason) | FsymUbStance::NotRaised(reason) => {
                        why.push(format!(
                            "{} `{}`: the map says {name} cannot raise it here: {reason}",
                            site.function, site.message
                        ))
                    }
                }
            }
        }
        if sites.is_empty() {
            why.push("no site's message matches".to_string());
        }
        if !owed {
            failures.push(format!(
                "{}: `{}` — {}",
                trigger.what,
                error.message,
                why.join("; ")
            ));
        }
    }
    // Non-vacuity: every restricted Owed stance of an admitted raiser is
    // observed.
    let mut unobserved = Vec::new();
    for site in FSYM_INTERPRETER_UB_SITES {
        for raise in site.raisers {
            let FsymUbStance::Owed { otherwise, .. } = raise.stance else {
                continue;
            };
            if otherwise.is_empty() {
                continue;
            }
            for name in raise.by {
                let admitted = FSYM_INST_VARIANTS
                    .iter()
                    .any(|(variant, admitted)| variant == name && *admitted);
                if admitted
                    && !observed.iter().any(|(function, message, raiser, _)| {
                        *function == site.function && *message == site.message && raiser == name
                    })
                    && !UNOBSERVED_RESTRICTED
                        .iter()
                        .any(|(function, message, raiser, _)| {
                            *function == site.function && *message == site.message && raiser == name
                        })
                {
                    unobserved.push(format!("{} `{}` by {name}", site.function, site.message));
                }
            }
        }
    }
    eprintln!(
        "{} triggers, {raised} raised UB at an admitted instance; {} (site, raiser) pairs observed owed",
        triggers.len(),
        observed.len()
    );
    assert!(raised >= 500, "only {raised} triggers raised UB");
    assert_eq!(
        past_bounds_refused,
        triggers
            .iter()
            .filter(|trigger| trigger.past_bounds)
            .count(),
        "every placement past the address space is refused OutOfMemory at its instance"
    );
    assert!(
        failures.is_empty(),
        "{} observed raise(s) the map does not owe:\n{}",
        failures.len(),
        failures
            .iter()
            .take(40)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert!(
        unobserved.is_empty(),
        "restricted Owed stances no catalog trigger raises (extend `triggers`, or excuse with why):\n{}",
        unobserved.join("\n")
    );
}

/// Restricted `Owed` stances the observation catalog cannot raise at an
/// admitted instance, each with why: `(site function, message, raiser, why)`.
/// The map owes them (a verdict nothing needs is imprecision, never
/// unsoundness); the call graph reaches them, the run does not.
const UNOBSERVED_RESTRICTED: &[(&str, &str, &str, &str)] = &[
    (
        "address",
        "{op}: pointer address overflow",
        "AtomicRMW",
        "eval_atomic_rmw takes integer operands only (expect_int_value): the value it stores is never a pointer",
    ),
    (
        "check_address",
        "{op}: address {address:#x} is outside the target's",
        "AtomicRMW",
        "eval_atomic_rmw takes integer operands only (expect_int_value): the value it stores is never a pointer",
    ),
    (
        "check_address",
        "{op}: address {address:#x} is outside the target's",
        "Const",
        "a global initializer's pointer lanes are null or symbol_pointer windows, never a no-provenance address (a nonzero Int at a pointer type is a type error)",
    ),
    (
        "check_address",
        "{op}: address {address:#x} is outside the target's",
        "GlobalAddr",
        "a global initializer's pointer lanes are null or symbol_pointer windows, never a no-provenance address (a nonzero Int at a pointer type is a type error)",
    ),
    (
        "eval_bitcast",
        "Bitcast: address {} does not fit u64",
        "Cast",
        "a Bitcast needs equal widths, and the interpreter's pointer-like types are one pointer wide (at most 64 bits): the integer it turns into a pointer always fits u64",
    ),
    (
        "execute_callee",
        "<callee body>",
        "Call",
        "a callee's UB is raised in the callee's own blocks, attributed to its own instruction (the oracle's attribution), never at the caller's one-instruction block",
    ),
];
