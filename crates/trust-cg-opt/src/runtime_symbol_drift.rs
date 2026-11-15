// trust-cg-opt/runtime_symbol_drift.rs - The machine passes' by-name symbols
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Drift test: every symbol a `trust-cg-opt` pass emits or reads the meaning
//! of by name is on the shared [`trust_cg_lower::RuntimeSymbol`] list, whose
//! module-local definitions the compiler refuses. The scan is
//! `trust-cg-lower`'s shared test scanner (`source_scan.rs`, included by
//! path): the crate's module tree from `lib.rs`, lexed, with test items
//! removed by their own bounds.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use trust_cg_lower::RuntimeSymbol;

use crate::source_scan::{crate_files, crate_scans, scan};

/// Per non-test file of this crate (relative to `src/`): its scan.
fn opt_scans() -> BTreeMap<String, crate::source_scan::Scan> {
    let mut scans = crate_scans(&Path::new(env!("CARGO_MANIFEST_DIR")).join("src"));
    scans.remove("runtime_symbol_drift.rs");
    scans
}

/// Every name a pass may not spell as a literal: a listed name, with or
/// without the Mach-O underscore.
fn listed_spellings() -> BTreeSet<String> {
    RuntimeSymbol::ALL
        .into_iter()
        .flat_map(|symbol| [symbol.name().to_string(), format!("_{}", symbol.name())])
        .collect()
}

/// The machine passes' non-test code names no listed symbol as a string
/// literal (with or without the Mach-O underscore), builds no symbol operand
/// from a literal, imports no symbol variant or operand enum by glob or list,
/// recognizes `sin`/`cos` only in the Darwin sin/cos merge, and uses symbol
/// operands (`::Symbol`, `::ExactModuleSymbol`, `.as_symbol`,
/// `.as_exact_module_symbol`, whatever names the enum) only as pinned per
/// file:
///
/// * constructing a symbol operand: PGO block-counter injection
///   (compiler-generated counter symbols), the sin/cos merge
///   (`RuntimeSymbol::SincosStret`) and tail-call formation (the callee's own
///   symbol);
/// * reading a symbol's name: the name-keyed module inliner and tail-call
///   formation (a callee's identity), the sin/cos merge (`sin` and `cos`:
///   Darwin only, skipping `EXACT_MODULE_CALL` calls, and Darwin objects
///   refuse direct calls to module-local functions), SROA
///   (`RuntimeSymbol::Memcpy`) and the vectorizer (`RuntimeSymbol::Calloc`);
/// * name-blind uses, which carry the name without interpreting it: operand
///   hashing (GVN, proof opts, the pass-validation digest and symbolic
///   address atoms), equality canonicalization (CSE, including its own
///   canonical operand's variants), invariant operands (LICM), alias
///   queries (alias hoisting), the x86-64 pass manager's
///   fingerprint, and the x86-64 LICM and SROA operand classifications;
/// * exact module calls (`ExactModuleSymbol`): an exact binding by function
///   identity, carried by the same name-blind uses.
///
/// A new use fails here until it is classified; a name a pass emits or reads
/// the meaning of must be added to `RuntimeSymbol`.
#[test]
fn passes_draw_by_name_symbols_from_the_shared_list() {
    let scans = opt_scans();
    let listed = listed_spellings();
    let mut spelled = Vec::new();
    let mut mentions = BTreeMap::new();
    for (file, scan) in &scans {
        for literal in &scan.literals {
            if listed.contains(literal) {
                spelled.push((file.clone(), literal.clone()));
            }
            if matches!(literal.as_str(), "sin" | "cos") && file != "sincos_merge.rs" {
                spelled.push((file.clone(), literal.clone()));
            }
        }
        assert_eq!(
            scan.literal_operands, 0,
            "{file} builds a symbol operand from a literal"
        );
        assert_eq!(
            scan.aliases, 0,
            "{file} imports an operand enum by alias or glob"
        );
        if scan.mentions != 0 {
            mentions.insert(file.as_str(), scan.mentions);
        }
    }
    assert_eq!(
        spelled,
        Vec::<(String, String)>::new(),
        "names spelled directly"
    );
    assert_eq!(
        mentions,
        BTreeMap::from([
            ("alias_hoist.rs", 2),
            ("cse.rs", 12),
            ("gvn.rs", 2),
            ("inline.rs", 1),
            // Symbol-based memory disjointness was withdrawn. Only LICM's
            // name-blind invariant-operand variants remain; pairing reads no
            // symbol at all. Any future use must be classified here again.
            ("licm.rs", 2),
            // Per-pass translation validation, name-blind: the operand digest
            // hashes a symbol's name and the symbolic semantics keys an
            // address atom by it (one name is one address; two names are
            // never taken as disjoint objects). None interprets or constructs
            // one, and the LICM validator reads no symbol (OD-127).
            ("pass_validation/mod.rs", 2),
            ("pass_validation/semantics.rs", 8),
            ("pgo/inject.rs", 1),
            ("proof_opts.rs", 2),
            ("sincos_merge.rs", 2),
            ("sroa.rs", 1),
            ("tail_call.rs", 3),
            ("vectorize.rs", 1),
            // The shared pure-trap predicate reads a call's symbol to recognize
            // the `[Call abort, Ud2]` block shape; it constructs nothing.
            ("x86_cmov_swap.rs", 4),
            ("x86_licm.rs", 2),
            ("x86_pass_manager.rs", 2),
            ("x86_sroa.rs", 2),
            // `is_pure_trap_block` reads the abort call's symbol to recognize the
            // diverging trap block; it constructs no symbol operand.
            ("x86_trap_block.rs", 1),
            // The fill tier's `memset` libcall route constructs one symbol
            // operand, drawn from `RuntimeSymbol::Memset`, never a literal.
            ("x86_vectorize.rs", 1),
        ]),
        "a pass constructs or reads a symbol operand outside the classified uses"
    );
}

/// The scan itself, on planted sources: each shape a pass could use to spell
/// or read a symbol's name is found after an out-of-line test module, after
/// an inline one, under `#[cfg(not(test))]` and after literals that look like
/// comments or braces; nothing is found inside a test item or a comment.
#[test]
fn the_scan_finds_every_planted_shape() {
    let plants = [
        (
            "as_symbol",
            "fn p(op: &MachOperand) -> bool { op.as_symbol() == Some(\"calloc\") }",
        ),
        (
            "literal operand",
            "fn p() -> MachOperand { MachOperand::Symbol(\"memcpy\".to_string()) }",
        ),
        (
            "match arm",
            "fn p(op: Option<&MachOperand>) -> bool { match op { Some(MachOperand::Symbol(name)) => name == \"strlen\", _ => false } }",
        ),
        (
            "if let",
            "fn p(op: &MachOperand) { if let MachOperand::Symbol(s) = op { drop(s); } }",
        ),
        (
            "let else",
            "fn p(op: &MachOperand) { let MachOperand::Symbol(s) = op else { return }; drop(s); }",
        ),
        (
            "matches guard",
            "fn p(op: &MachOperand) -> bool { matches!(op, MachOperand::Symbol(s) if s == \"x\") }",
        ),
        (
            "spaced path",
            "fn p(op: &MachOperand) -> bool { matches!(op, MachOperand :: Symbol (_)) }",
        ),
        (
            "x86 operand",
            "fn p(op: &X86ISelOperand) -> bool { matches!(op, X86ISelOperand::Symbol(_)) }",
        ),
        (
            "raw identifier variant",
            "fn p(op: &MachOperand) -> bool { if let MachOperand::r#Symbol(s) = op { s == \"strlen\" } else { false } }",
        ),
        (
            "raw identifier accessor",
            "fn p(op: &MachOperand) -> bool { op.r#as_symbol() == Some(\"strlen\") }",
        ),
        (
            "type alias",
            "fn p(op: &MachOperand) -> bool { type Op = MachOperand; matches!(op, Op::Symbol(s) if s == \"strlen\") }",
        ),
        (
            "Self in an impl",
            "impl Ext for MachOperand { fn callee(&self) -> Option<&str> { match self { Self::Symbol(s) => Some(s), _ => None } } }",
        ),
        (
            "qualified path",
            "fn p() -> MachOperand { <MachOperand>::Symbol(String::from(\"strlen\")) }",
        ),
        (
            "exact module symbol",
            "fn p(op: &MachOperand) -> bool { matches!(op, MachOperand::ExactModuleSymbol(s) if s == \"f\") }",
        ),
        (
            "exact module accessor",
            "fn p(op: &MachOperand) -> bool { op.as_exact_module_symbol() == Some(\"f\") }",
        ),
        (
            "macro body",
            "macro_rules! sym { ($n:expr) => { MachOperand::Symbol($n) }; } fn p() -> MachOperand { sym!(String::new()) }",
        ),
    ];
    let detected = |source: &str| {
        let scan = scan(source);
        (scan.mentions, scan.literals.len(), scan.literal_operands)
    };
    for (label, plant) in plants {
        let alone = detected(plant);
        assert!(alone.0 >= 1, "{label}: {alone:?}");
        for (context, prefix, suffix) in [
            (
                "after an out-of-line test module",
                "fn a() {}\n#[cfg(test)]\nmod tests;\n",
                "",
            ),
            (
                "after an inline test module",
                "#[cfg(test)]\nmod tests {\n    fn t() { let _ = \"}\"; }\n}\n",
                "",
            ),
            ("under cfg(not(test))", "#[cfg(not(test))]\n", ""),
            (
                "after comment-like literals",
                "const A: &str = \"// not a comment\"; const B: &str = \"/* nor this\"; \
                 const C: &str = r#\"a \" { quote\"#; const D: char = '\"'; const E: char = '{'; \
                 fn f<'a>(x: &'a str) -> &'a str { x }\n",
                "",
            ),
            ("inside a nested module", "pub(crate) mod inner {\n", "\n}"),
        ] {
            assert_eq!(
                detected(&format!("{prefix}{plant}{suffix}")).0,
                alone.0,
                "{label} {context}"
            );
        }
        for (context, source) in [
            (
                "inside an inline test module",
                format!("#[cfg(test)]\nmod tests {{\n{plant}\n}}\nfn after() {{}}\n"),
            ),
            (
                "on a test item",
                format!("#[cfg(test)]\n{plant}\nfn after() {{}}\n"),
            ),
            ("in a line comment", format!("// {plant}\n")),
            (
                "in a doc comment",
                format!("/// {plant}\nfn documented() {{}}\n"),
            ),
            (
                "in a nested block comment",
                format!("/* /* {plant} */ */\n"),
            ),
        ] {
            assert_eq!(detected(&source), (0, 0, 0), "{label} {context}");
        }
    }
    assert_eq!(detected(plants[1].1).2, 1, "a literal operand is flagged");
    for alias in [
        "use trust_cg_ir::MachOperand::*;",
        "use trust_cg_ir::MachOperand::{Symbol, VReg};",
        "use trust_cg_ir::MachOperand::Symbol;",
        "use trust_cg_ir::X86ISelOperand::{self, ExactModuleSymbol};",
    ] {
        assert!(scan(alias).aliases >= 1, "{alias}");
    }
    for plain in [
        "use trust_cg_ir::MachOperand;",
        "use trust_cg_ir::MachOperand as MO;",
        "use trust_cg_ir::{AArch64Opcode, MachOperand};",
    ] {
        assert_eq!(scan(plain).aliases, 0, "{plain}");
    }
    // The verifier's plants, after `neon_fill.rs`'s out-of-line test module.
    let neon_fill =
        std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("src/neon_fill.rs"))
            .expect("neon_fill.rs");
    let clean = scan(&neon_fill);
    let planted = scan(&format!(
        "{neon_fill}\nfn planted(op: &MachOperand) -> bool {{ op.as_symbol() == Some(\"calloc\") }}\n\
         fn planted_operand() -> MachOperand {{ MachOperand::Symbol(\"memcpy\".to_string()) }}\n\
         fn planted_arm(op: Option<&MachOperand>) -> bool {{ match op {{ Some(MachOperand::Symbol(name)) => name == \"strlen\", _ => false }} }}\n"
    ));
    assert_eq!(planted.mentions, clean.mentions + 3);
    assert_eq!(planted.literal_operands, clean.literal_operands + 1);
    assert!(planted.literals.iter().any(|l| l == "calloc"));
    assert!(planted.literals.iter().any(|l| l == "memcpy"));
    // Test modules are declared, not guessed from file names.
    let mods = scan(
        "#[cfg(test)]\npub(crate) mod tests;\nmod pass;\n#[path = \"x/y.rs\"]\nmod z;\n\
         #[path = \"p.rs\"]\npub mod public;\n\
         #[cfg(test)]\nmod inline_tests {\n    pub mod candidate;\n    fn t() {}\n}\n",
    )
    .modules;
    assert_eq!(
        mods.iter()
            .map(|m| (
                m.name.as_str(),
                m.test,
                m.path.as_deref(),
                m.inline_parents.clone()
            ))
            .collect::<Vec<_>>(),
        [
            ("tests", true, None, vec![]),
            ("pass", false, None, vec![]),
            ("z", false, Some("x/y.rs"), vec![]),
            ("public", false, Some("p.rs"), vec![]),
            ("candidate", true, None, vec!["inline_tests".to_string()]),
        ]
    );
}

/// A file declared both as production code and under `#[cfg(test)]` (a
/// second `#[path]` declaration) is production code, whichever declaration
/// the walk meets last; a file reached only through a test declaration is
/// test-only.
#[test]
fn a_file_declared_both_ways_is_production_code() {
    let root = std::env::temp_dir().join(format!(
        "tcg-source-scan-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos())
    ));
    std::fs::create_dir_all(&root).expect("scratch");
    for (order, lib) in [
        (
            "production first",
            "mod pass;\n#[cfg(test)]\n#[path = \"pass.rs\"]\nmod pass_again;\n#[cfg(test)]\nmod only_tests;\n",
        ),
        (
            "test first",
            "#[cfg(test)]\n#[path = \"pass.rs\"]\nmod pass_again;\nmod pass;\n#[cfg(test)]\nmod only_tests;\n",
        ),
    ] {
        std::fs::write(root.join("lib.rs"), lib).expect("lib.rs");
        std::fs::write(root.join("pass.rs"), "fn pass() {}\n").expect("pass.rs");
        std::fs::write(root.join("only_tests.rs"), "fn t() {}\n").expect("only_tests.rs");
        let files = crate_files(&root);
        assert_eq!(files.get(&root.join("pass.rs")), Some(&false), "{order}");
        assert_eq!(
            files.get(&root.join("only_tests.rs")),
            Some(&true),
            "{order}"
        );
    }
    std::fs::remove_dir_all(&root).ok();
}

/// A production file that splices source in with `include!` fails the scan,
/// because the included text (the verifier's `sym.inc` holding a symbol
/// operand) is never read; `include!` in test code and `include_str!` do not.
#[test]
fn a_source_include_fails_the_scan() {
    let root = std::env::temp_dir().join(format!(
        "tcg-source-scan-include-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_nanos())
    ));
    std::fs::create_dir_all(&root).expect("scratch");
    std::fs::write(root.join("lib.rs"), "mod a;\n").expect("lib.rs");
    std::fs::write(
        root.join("sym.inc"),
        "fn p() -> MachOperand { MachOperand::Symbol(String::new()) }\n",
    )
    .expect("sym.inc");
    let scans_with = |a: &str| {
        std::fs::write(root.join("a.rs"), a).expect("a.rs");
        std::panic::catch_unwind(|| crate_scans(&root).len())
    };
    let refused = [
        "include!(\"sym.inc\");\n",
        "std::include!(\"sym.inc\");\n",
        "fn f() { include ! (\"sym.inc\") }\n",
    ];
    let admitted = [
        "#[cfg(test)]\nmod tests { include!(\"sym.inc\"); }\n",
        "const S: &str = include_str!(\"sym.inc\");\n",
        "// include!(\"sym.inc\");\n",
        "const S: &str = \"include!(sym.inc)\";\n",
    ];
    let outcomes: Vec<(&str, bool)> = refused
        .iter()
        .chain(&admitted)
        .map(|a| (*a, scans_with(a).is_err()))
        .collect();
    std::fs::remove_dir_all(&root).ok();
    for (a, failed) in outcomes {
        assert_eq!(failed, refused.contains(&a), "{a}");
    }
}
