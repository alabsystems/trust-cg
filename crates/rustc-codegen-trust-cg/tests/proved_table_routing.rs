//! The bridge states no second copy of a trust-ir decision table.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates
//! License: Apache-2.0
//!
//! trust-ir owns three legality tables the bridge consults:
//! `Ordering::is_legal_for_load` (`Relaxed | Acquire | SeqCst`),
//! `Ordering::is_legal_for_store` (`Relaxed | Release | SeqCst`) and
//! `Linkage::is_module_local` (`Internal | Private`). Each is PROVED per cell
//! in trust-ir (gate 13: `trust_ir_laws::laws::atomic_load_*`,
//! `atomic_store_*`, `module_local_*`). A bridge `match` that lists one of
//! those variant sets, or its complement, is a second statement of the same
//! rule that the proof does not cover and that can drift from it.
//!
//! This file scans the bridge's own sources (`src/*.rs`, comments stripped)
//! for an or-pattern (`A | B | ...`) of `Ordering::` or `Linkage::` variants
//! whose set is a table or its complement, and names every one it finds. It is
//! a SOURCE guard (test rung): it proves no copy exists in the scanned text,
//! not that the tables are right — that is trust-ir's gate 13.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

const ORDERINGS: &[&str] = &["Relaxed", "Acquire", "Release", "AcqRel", "SeqCst"];
const LINKAGES: &[&str] = &[
    "External",
    "Internal",
    "Private",
    "Weak",
    "LinkOnce",
    "AvailableExternally",
    "ExternalWeak",
    "WeakOdr",
    "LinkOnceOdr",
];

/// The variant sets that ARE a proved table (or its complement within the
/// enum's closed variant list).
fn forbidden_sets() -> Vec<(&'static str, &'static str, BTreeSet<&'static str>)> {
    let set = |v: &[&'static str]| v.iter().copied().collect::<BTreeSet<_>>();
    let complement = |all: &[&'static str], v: &[&'static str]| {
        all.iter()
            .copied()
            .filter(|x| !v.contains(x))
            .collect::<BTreeSet<_>>()
    };
    let load = ["Relaxed", "Acquire", "SeqCst"];
    let store = ["Relaxed", "Release", "SeqCst"];
    let local = ["Internal", "Private"];
    vec![
        ("Ordering", "Ordering::is_legal_for_load", set(&load)),
        (
            "Ordering",
            "!Ordering::is_legal_for_load",
            complement(ORDERINGS, &load),
        ),
        ("Ordering", "Ordering::is_legal_for_store", set(&store)),
        (
            "Ordering",
            "!Ordering::is_legal_for_store",
            complement(ORDERINGS, &store),
        ),
        ("Linkage", "Linkage::is_module_local", set(&local)),
        (
            "Linkage",
            "!Linkage::is_module_local",
            complement(LINKAGES, &local),
        ),
    ]
}

/// Remove `//` comments (line and doc) so prose that names the sets is not
/// read as code. String literals holding `//` are not a concern here: the
/// patterns this scan looks for never appear inside a string in the bridge.
fn strip_line_comments(src: &str) -> String {
    src.lines()
        .map(|line| match line.find("//") {
            Some(at) => &line[..at],
            None => line,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// Every maximal or-chain `P::A | P::B | ...` of paths ending in
/// `<enum_name>::<Variant>`: `(byte offset, variants)`.
fn or_chains<'a>(code: &'a str, enum_name: &str) -> Vec<(usize, Vec<&'a str>)> {
    let needle = format!("{enum_name}::");
    let bytes = code.as_bytes();
    let mut chains = Vec::new();
    let mut at = 0usize;
    while let Some(found) = code[at..].find(&needle) {
        let start = at + found;
        // A path prefix (`trust_ir::`) is fine; an identifier character right
        // before the enum name means a different name (`MyOrdering::`).
        if start > 0 {
            let prev = bytes[start - 1] as char;
            if prev.is_alphanumeric() || prev == '_' {
                at = start + needle.len();
                continue;
            }
        }
        let mut variants = Vec::new();
        let mut cursor = start;
        loop {
            let name_start = cursor + needle.len();
            let name_end = code[name_start..]
                .find(|c: char| !(c.is_alphanumeric() || c == '_'))
                .map_or(code.len(), |n| name_start + n);
            variants.push(&code[name_start..name_end]);
            // Continue only across `|` (whitespace allowed) to the next
            // `<path>::<enum_name>::Variant`.
            let rest = &code[name_end..];
            let trimmed = rest.trim_start();
            if !trimmed.starts_with('|') || trimmed.starts_with("||") {
                cursor = name_end;
                break;
            }
            let after_bar = trimmed[1..].trim_start();
            let offset = code.len() - after_bar.len();
            // Skip an optional path prefix (`trust_ir::`, `rustc_x::y::`); the
            // prefix must end at a `::`, so `MyOrdering::` is not `Ordering::`.
            let path_len = after_bar
                .find(&needle)
                .filter(|n| {
                    let prefix = &after_bar[..*n];
                    (prefix.is_empty() || prefix.ends_with("::"))
                        && prefix
                            .chars()
                            .all(|c| c.is_alphanumeric() || c == '_' || c == ':')
                })
                .unwrap_or(usize::MAX);
            if path_len == usize::MAX {
                cursor = name_end;
                break;
            }
            cursor = offset + path_len;
        }
        chains.push((start, variants));
        at = cursor.max(start + needle.len());
    }
    chains
}

fn line_of(code: &str, offset: usize) -> usize {
    code[..offset].matches('\n').count() + 1
}

fn respellings_in(path: &Path, code: &str) -> Vec<String> {
    let mut found = Vec::new();
    for (enum_name, table, set) in forbidden_sets() {
        for (offset, variants) in or_chains(code, enum_name) {
            if variants.len() < 2 {
                continue;
            }
            let chain: BTreeSet<&str> = variants.iter().copied().collect();
            if chain == set {
                found.push(format!(
                    "{}:{}: `{}` re-spells `{table}` — call the trust-ir table instead",
                    path.display(),
                    line_of(code, offset),
                    variants
                        .iter()
                        .map(|v| format!("{enum_name}::{v}"))
                        .collect::<Vec<_>>()
                        .join(" | "),
                ));
            }
        }
    }
    found
}

fn bridge_sources() -> Vec<PathBuf> {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&src)
        .unwrap_or_else(|e| panic!("read {src:?}: {e}"))
        .map(|entry| entry.expect("directory entry").path())
        .filter(|p| p.extension().is_some_and(|x| x == "rs"))
        .collect();
    files.sort();
    files
}

#[test]
fn bridge_does_not_respell_trust_ir_decision_tables() {
    let files = bridge_sources();
    assert!(
        files.iter().any(|p| p.ends_with("lib.rs")),
        "the scan must see the bridge's lib.rs: {files:?}"
    );
    let mut found = Vec::new();
    for path in &files {
        let raw = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {path:?}: {e}"));
        found.extend(respellings_in(path, &strip_line_comments(&raw)));
    }
    assert!(
        found.is_empty(),
        "{} re-spelling(s) of a proved trust-ir table:\n  {}",
        found.len(),
        found.join("\n  ")
    );
}

/// The scanner itself: each forbidden spelling is found (the mutation this
/// file exists to catch), and the lowering choice the store path keeps is not.
#[test]
fn the_scan_finds_each_spelling_it_forbids() {
    let p = Path::new("probe.rs");
    let hits = |code: &str| respellings_in(p, &strip_line_comments(code)).len();
    assert_eq!(
        hits(
            "match o { trust_ir::Ordering::Relaxed | trust_ir::Ordering::Acquire | trust_ir::Ordering::SeqCst => {} _ => {} }"
        ),
        1
    );
    assert_eq!(
        hits("matches!(f, Ordering::Release |\n    Ordering::AcqRel)"),
        1
    );
    assert_eq!(
        hits("Ordering::Acquire | Ordering::AcqRel => return Err(e),"),
        1
    );
    assert_eq!(
        hits("Ordering::SeqCst | Ordering::Release | Ordering::Relaxed => {}"),
        1
    );
    assert_eq!(
        hits("!matches!(g.linkage, Linkage::Private | Linkage::Internal)"),
        1
    );
    // Not a table: one variant, a lowering choice, a boolean `||`, prose.
    assert_eq!(
        hits("if ordering == trust_ir::Ordering::SeqCst { xchg }"),
        0
    );
    assert_eq!(
        hits("Ordering::Relaxed | Ordering::Release => plain_store(),"),
        0
    );
    assert_eq!(hits("a == Linkage::Internal || b == Linkage::Private"), 0);
    assert_eq!(
        hits("// a Release | AcqRel failure: Ordering::Release | Ordering::AcqRel"),
        0
    );
    assert_eq!(hits("MyOrdering::Release | MyOrdering::AcqRel"), 0);
}
