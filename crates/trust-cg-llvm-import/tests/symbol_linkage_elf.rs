#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / symbol_linkage_elf.rs
//
// L02-P13: the link-time facts of LLVM functions and globals imported by
// `import_text` (linkage, visibility, self-keyed COMDAT, section) reach the
// emitted object instead of defaulting to a strong, default-visibility
// symbol.
//
// Object level (every host): through `Compiler::compile` for
// `aarch64-unknown-linux-gnu` at O0-O3 under `static`, `pie` and `pic`, the
// in-tree ELF reader sees every imported definition, declaration and global
// with its binding (`STB_GLOBAL`/`STB_WEAK`/`STB_LOCAL`), visibility, defined
// or undefined state and COMDAT group; `available_externally` is never
// defined. A global of every initializer shape (integer, floating-point,
// struct and pointer arrays, a string, a zero fill, a named struct with
// fields and zero, a null pointer, a scalar) gets the trust-ir linkage and
// visibility, ELF binding, visibility and COMDAT group its stated linkage
// and visibility give, for every admitted linkage and visibility. The
// importer admits a `comdat` clause exactly where the backend
// itself emits a group named like the symbol, for every linkage, and a
// definition written without one is in no group (as llc emits it). For
// `aarch64-apple-darwin`, ODR definitions are `N_WEAK_DEF`, a hidden
// `external` definition is a private extern (`N_SECT | N_EXT | N_PEXT`), and
// every other hidden or protected function, a function section and a weak
// reference are refused by name. A direct call of an
// `extern_weak` function that must go through its address is refused by
// name where that lowering would change it: a stack-passed 128-bit integer
// argument (L06-P15) or a variadic callee.
//
// Admission (every host, through the public `import_text`): every linkage,
// visibility, COMDAT, section and retention fact the importer decides
// reaches trust-ir as LLVM states it, and every fact it cannot carry is
// refused by name (a visibility on a local symbol or two of them, linkages
// LLVM forbids in their position, conflicting headers, the COMDATs the
// backend does not emit, `llvm.metadata`, a function in `@llvm.used`,
// quoted, numbered and `\01` names written otherwise than llc writes them,
// a non-private `.L` name off Mach-O, a hidden, protected or `extern_weak`
// declaration whose signature the importer does not model,
// `thread_local`, `externally_initialized`, `alias` and `ifunc` by keyword,
// and a `dso_local` declaration whose address the module's code takes,
// which llc addresses PC-relative and the backend through the GOT). The
// module triple's object format is read as LLVM's `Triple` reads it.
// These rows mirror the importer's lib unit tests, which the Linux floor
// does not run, so the floor itself fails when one of those decisions
// changes. Object level again: an `@llvm.used` global is alone in its own
// `SHF_GNU_RETAIN` section, as llc places it (`<kind>.<symbol>`, or another
// section of its explicit name), and no unlisted neighbour is retained; a
// hidden, protected or `extern_weak` declaration nothing references is an
// undefined symbol with llc's binding and visibility (an
// `available_externally` global or a default declaration is none); the four
// coverage-mapping section names LLVM makes non-allocated are refused by
// name. The sections named by COMDAT, `@llvm.used` and ordinary members
// are emitted in llc's creation order (an own section where its definition
// is declared, a shared one at its first ordinary member). The x86-64 ELF
// emitter retains each `@llvm.used` global alone too. A global declaration
// listed in `@llvm.used` is written as llc's ELF writer writes it (nothing
// for the listing), and refused by name on Mach-O, where llc writes an
// `N_NO_DEAD_STRIP` undefined symbol, as is a listed function declaration
// in a Mach-O module.
//
// Native (AArch64 Linux GNU only, O0-O3, GNU ld, gold and LLD). Each shape is
// compared with a gcc/g++ twin of the same C-level shape (the Linux host this
// was written on has no clang) and with the same LLVM text compiled by `llc`
// and linked with the same C driver. The llc is `TCG_LLC`, else the first in
// an absolute `PATH` entry, else the one in the sysroot of the compiler that
// builds this test (`$RUSTC`, else `trustc`: `<sysroot>/lib/rustlib/<host>/bin/
// llc`, where a Trust package ships it with its other LLVM tools); it must be
// executable and report that compiler's LLVM major version.
// Without one the llc legs are skipped and named on stderr; `TCG_REQUIRE_LLC`,
// which the Linux floor sets for this target, makes that a failure:
// * a `pic` shared object built from imported hidden, protected, weak-hidden
//   and `linkonce_odr hidden` functions keeps the hidden ones out of
//   `.dynsym` and binds the library's calls to them and to the protected one
//   at link time, so an `LD_PRELOAD` interposer rebinds only the
//   default-visibility call, and an executable cannot link a hidden one;
// * so does one built from hidden, protected, weak and ODR data of eight
//   image shapes (integer, string, zero, floating-point and pointer arrays,
//   named structs with fields and zero, a null pointer) for the library's
//   own reads, and `dlsym` finds only the exported data (the gcc twin writes
//   the ODR forms as C `weak` definitions);
// * `linkonce_odr` and `weak_odr` functions and globals defined in two
//   imported objects (with and without Linux clang's self-keyed COMDATs, and
//   against g++ `inline` twins) link without a duplicate-definition error
//   and share one counter, in both input orders;
// * a `declare hidden` function binds inside the shared object that links
//   its definition (out of `.dynsym`, not interposed) and cannot stay
//   undefined in a shared object, where a default declaration can;
// * an `extern_weak` function reads null when nothing defines it and is
//   called when something does, and an `available_externally` function is a
//   declaration: it links against the definition elsewhere instead of
//   colliding with it, and cannot link without one;
// * a call of a defined `extern_weak` function passes register-pair 128-bit
//   integers and stack-passed floating-point, narrow integer, `i1` and
//   pointer arguments exactly like a direct call, a gcc twin and llc;
// * unreferenced hidden and protected declarations hide and protect the C
//   definitions a `pic` shared object links (an `LD_PRELOAD` interposer
//   rebinds neither library call, `.dynsym` and `dlsym` agree with llc), and
//   GNU ld alone refuses an executable that leaves the hidden ones undefined,
//   as with llc's object (no gcc twin: gcc writes no unreferenced
//   declaration);
// * under `--gc-sections`, static, PIE and shared, the `@llvm.used` globals
//   survive alone (no unlisted neighbour, and no undefined reference one
//   holds, survives) and a `__start_`/`__stop_` walk of a named section sees
//   exactly what llc's image gives (LLD's start-stop-gc drops the unlisted
//   members);
// * `__start_`/`__stop_` walks of named sections mixing COMDAT, used and
//   ordinary members, and the run order of COMDAT and ordinary
//   `.init_array` entries, equal llc's (static, PIE and shared, with and
//   without `--gc-sections`);
// * an x86-64 ELF object linked by LLD under `--gc-sections` (linked, not
//   run) keeps exactly the `@llvm.used` globals llc's object keeps;
// * global declarations listed in `@llvm.used` link and run as llc's
//   object does (static, PIE and shared);
// * functions under a `"target-cpu"` LLVM 22 defines for AArch64
//   (`generic`, `cortex-a72`, `neoverse-v2`, `apple-m1`) pass and return
//   floating-point values as llc's object does (O0-O3), and llc's object
//   under a name it does not define, which the import refuses, takes a
//   `double` from `x0` (L02-P15).
//
// This is execution evidence of these linkers, the glibc loader and that
// llc on this host, not a linker or loader proof.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

mod common;

use std::collections::{BTreeMap, BTreeSet};

use common::{APPLE, LINUX};
use trust_cg_codegen::RelocationModel;
use trust_cg_codegen::compiler::Compiler;
use trust_cg_codegen::elf::reparse::{ElfObjectRecords, read_object_records};
use trust_cg_codegen::macho::linker::MachOParser;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_llvm_import::{import_text, import_text_for_compile, import_text_for_target};

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const MODELS: [RelocationModel; 3] = [
    RelocationModel::Static,
    RelocationModel::Pie,
    RelocationModel::Pic,
];

const STB_LOCAL: u8 = 0;
const STB_GLOBAL: u8 = 1;
const STB_WEAK: u8 = 2;
const STV_DEFAULT: u8 = 0;
const STV_HIDDEN: u8 = 2;
const STV_PROTECTED: u8 = 3;
const SHT_GROUP: u32 = 17;
const GRP_COMDAT: u32 = 1;

/// Import `src` for `triple` and compile it for `triple` at `opt_level` under
/// `model`. The import names the target and no relocation model
/// ([`import_text_for_target`]): the module states the target it is compiled
/// for, as trust-ir requires of a module with an FFI boundary
/// (`TargetInfoRequired`, refused at every ingestion entry since WS7.3), and
/// the `dso_local` rules still refuse what any model would make differ.
fn compile(
    src: &str,
    triple: &str,
    opt_level: OptLevel,
    model: RelocationModel,
) -> Result<Vec<u8>, String> {
    let module = import_text_for_target(src, "symbol_linkage", triple)
        .map_err(|error| format!("import: {error}"))?;
    compile_module(&module, triple, opt_level, model)
}

/// Compile `module` for `triple` at `opt_level` under `model`.
fn compile_module(
    module: &trust_ir::Module,
    triple: &str,
    opt_level: OptLevel,
    model: RelocationModel,
) -> Result<Vec<u8>, String> {
    let spec = TargetSpec::parse(triple).expect("target spec");
    let mut config = common::config(opt_level, &spec);
    config.relocation_model = model;
    Compiler::new_for_target_spec(config, spec)
        .with_codegen_license(common::permit_unlicensed())
        .compile(module)
        .map(|result| result.object_code)
        .map_err(|error| format!("compile: {error}"))
}

/// One named symbol's `(binding, visibility, section name or "UND")`.
type SymbolFacts = (u8, u8, String);

/// The named, non-section symbols of an ELF object, read by the in-tree
/// reader. Mapping symbols (`$x`, `$d`) repeat, so each name keeps every row
/// and [`unique_symbol`] asserts the ones a check reads are unique.
fn elf_symbols(records: &ElfObjectRecords) -> BTreeMap<String, Vec<SymbolFacts>> {
    let mut symbols: BTreeMap<String, Vec<SymbolFacts>> = BTreeMap::new();
    for symbol in records.symbols.iter().filter(|symbol| {
        !symbol.name.is_empty() && symbol.symbol_type != 3 /* STT_SECTION */
    }) {
        let section = if symbol.section_index == 0 {
            "UND".to_string()
        } else {
            records.sections[usize::from(symbol.section_index)]
                .name
                .clone()
        };
        symbols.entry(symbol.name.clone()).or_default().push((
            symbol.binding,
            symbol.visibility,
            section,
        ));
    }
    symbols
}

/// The one row of symbol `name`, if present; two rows fail.
fn unique_symbol<'a>(
    symbols: &'a BTreeMap<String, Vec<SymbolFacts>>,
    name: &str,
) -> Option<&'a SymbolFacts> {
    let rows = symbols.get(name)?;
    assert_eq!(
        rows.len(),
        1,
        "symbol `{name}` appears more than once: {rows:?}"
    );
    rows.first()
}

/// The `GRP_COMDAT` groups of an ELF object: signature symbol -> member
/// section names, read from the raw `SHT_GROUP` sections.
fn elf_comdat_groups(object: &[u8], records: &ElfObjectRecords) -> BTreeMap<String, Vec<String>> {
    let u32_at = |at: usize| u32::from_le_bytes(object[at..at + 4].try_into().unwrap());
    let u64_at = |at: usize| {
        usize::try_from(u64::from_le_bytes(object[at..at + 8].try_into().unwrap())).unwrap()
    };
    let mut groups = BTreeMap::new();
    for (index, section) in records.sections.iter().enumerate() {
        if section.sh_type != SHT_GROUP {
            continue;
        }
        let header = u64_at(0x28) + index * 64;
        let link = u32_at(header + 0x28) as usize;
        let info = u32_at(header + 0x2c) as usize;
        assert_eq!(
            records.sections[link].name, ".symtab",
            "group {index} links the symtab"
        );
        let words: Vec<u32> = common::elf_section_bytes(object, index)
            .as_chunks::<4>()
            .0
            .iter()
            .map(|word| u32::from_le_bytes(*word))
            .collect();
        assert_eq!(
            words.first(),
            Some(&GRP_COMDAT),
            "group {index} is a COMDAT"
        );
        let members = words[1..]
            .iter()
            .map(|member| records.sections[*member as usize].name.clone())
            .collect();
        let signature = records.symbols[info].name.clone();
        assert!(
            groups.insert(signature.clone(), members).is_none(),
            "two groups signed `{signature}`"
        );
    }
    groups
}

fn bind_name(binding: u8) -> &'static str {
    match binding {
        STB_LOCAL => "LOCAL",
        STB_GLOBAL => "GLOBAL",
        STB_WEAK => "WEAK",
        _ => "OTHER",
    }
}

// =============================================================================
// Object level: every host
// =============================================================================

/// Every function and global symbol fact the LLVM text states.
const FACTS_MODULE: &str = r#"
declare extern_weak i64 @d_weak()

$f_odr_hidden = comdat any
$g_odr_hidden = comdat any

@g_default = global i64 1, align 8
@g_hidden = hidden global i64 2, align 8
@g_protected = dso_local protected global i64 3, align 8
@g_weak_protected = weak protected global i64 4, align 8
@g_odr_hidden = linkonce_odr hidden global i64 5, comdat, align 8
@g_wodr = weak_odr global i64 6, align 8
@g_internal = internal global i64 7, align 8
@g_private = private unnamed_addr global i64 8, align 8
@g_import_hidden = external hidden global i64, align 8
@g_import_weak = extern_weak global i64, align 8

define i64 @f_default() {
  ret i64 1
}
define hidden i64 @f_hidden() {
  ret i64 2
}
define protected i64 @f_protected() {
  ret i64 3
}
define weak i64 @f_weak() {
  ret i64 4
}
define weak hidden i64 @f_weak_hidden() {
  ret i64 5
}
define linkonce_odr hidden i64 @f_odr_hidden() comdat {
  ret i64 6
}
define weak_odr protected i64 @f_wodr_protected() {
  ret i64 7
}
define linkonce i64 @f_linkonce() {
  ret i64 8
}
define internal i64 @f_internal() {
  ret i64 9
}
define private i64 @f_private() {
  ret i64 10
}
define available_externally i64 @f_available() {
  ret i64 11
}
define hidden i64 @f_sectioned() section ".text.l02p13" {
  ret i64 12
}

define i64 @use_all() {
  %a = call i64 @f_internal()
  %b = call i64 @f_private()
  %c = call i64 @f_available()
  %d = call i64 @d_hidden()
  %e = call i64 @d_protected()
  %s1 = add i64 %a, %b
  %s2 = add i64 %s1, %c
  %s3 = add i64 %s2, %d
  %s4 = add i64 %s3, %e
  ret i64 %s4
}

define ptr @addr_weak() {
  ret ptr @d_weak
}

define i64 @load_globals() {
  %p = load i64, ptr @g_private, align 8
  %i = load i64, ptr @g_internal, align 8
  %h = load i64, ptr @g_import_hidden, align 8
  %w = load i64, ptr @g_import_weak, align 8
  %s1 = add i64 %p, %i
  %s2 = add i64 %s1, %h
  %s3 = add i64 %s2, %w
  ret i64 %s3
}

declare hidden i64 @d_hidden()
declare protected i64 @d_protected()
"#;

/// `(name, binding, visibility, placement)` of each symbol whose facts the
/// module states; placement is `"UND"`, `"text"`/`"data"` (a shared
/// section), an explicit section name, or `"group"` (alone in a COMDAT group
/// signed by itself). An ODR definition is grouped only with its `comdat`
/// clause: without one, LLVM puts it in no group and llc emits a plain weak
/// symbol (`f_wodr_protected`, `g_wodr`). A symbol listed
/// `must_exist: false` may be folded away at O1-O3 (a local callee inlined),
/// but never with other facts.
const EXPECTED: [(&str, u8, u8, &str, bool); 25] = [
    ("f_default", STB_GLOBAL, STV_DEFAULT, "text", true),
    ("f_sectioned", STB_GLOBAL, STV_HIDDEN, ".text.l02p13", true),
    ("f_hidden", STB_GLOBAL, STV_HIDDEN, "text", true),
    ("f_protected", STB_GLOBAL, STV_PROTECTED, "text", true),
    ("f_weak", STB_WEAK, STV_DEFAULT, "text", true),
    ("f_weak_hidden", STB_WEAK, STV_HIDDEN, "text", true),
    ("f_odr_hidden", STB_WEAK, STV_HIDDEN, "group", true),
    ("f_wodr_protected", STB_WEAK, STV_PROTECTED, "text", true),
    ("f_linkonce", STB_WEAK, STV_DEFAULT, "text", true),
    ("f_internal", STB_LOCAL, STV_DEFAULT, "text", false),
    ("f_private", STB_LOCAL, STV_DEFAULT, "text", false),
    ("f_available", STB_GLOBAL, STV_DEFAULT, "UND", false),
    ("d_hidden", STB_GLOBAL, STV_HIDDEN, "UND", true),
    ("d_protected", STB_GLOBAL, STV_PROTECTED, "UND", true),
    ("d_weak", STB_WEAK, STV_DEFAULT, "UND", true),
    ("g_default", STB_GLOBAL, STV_DEFAULT, "data", true),
    ("g_hidden", STB_GLOBAL, STV_HIDDEN, "data", true),
    ("g_protected", STB_GLOBAL, STV_PROTECTED, "data", true),
    ("g_weak_protected", STB_WEAK, STV_PROTECTED, "data", true),
    ("g_odr_hidden", STB_WEAK, STV_HIDDEN, "group", true),
    ("g_wodr", STB_WEAK, STV_DEFAULT, "data", true),
    ("g_internal", STB_LOCAL, STV_DEFAULT, "data", false),
    ("g_private", STB_LOCAL, STV_DEFAULT, "data", false),
    ("g_import_hidden", STB_GLOBAL, STV_HIDDEN, "UND", true),
    ("g_import_weak", STB_WEAK, STV_DEFAULT, "UND", true),
];

#[test]
fn linux_objects_spell_every_imported_symbol_fact() {
    for opt_level in OPT_LEVELS {
        for model in MODELS {
            let label = format!("{opt_level:?} {model}");
            let object = compile(FACTS_MODULE, LINUX, opt_level, model)
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            common::assert_container(&object, LINUX, &label);
            let records = read_object_records(&object).expect("ELF records");
            let symbols = elf_symbols(&records);
            let groups = elf_comdat_groups(&object, &records);
            for (name, binding, visibility, placement, must_exist) in EXPECTED {
                let Some((got_binding, got_visibility, section)) = unique_symbol(&symbols, name)
                else {
                    assert!(
                        !must_exist || opt_level != OptLevel::O0,
                        "{label}: `{name}` is missing: {symbols:?}"
                    );
                    continue;
                };
                assert_eq!(
                    (bind_name(*got_binding), *got_visibility),
                    (bind_name(binding), visibility),
                    "{label}: `{name}` binding/visibility"
                );
                match placement {
                    "UND" => assert_eq!(section, "UND", "{label}: `{name}` is a reference"),
                    "group" => {
                        assert_ne!(section, "UND", "{label}: `{name}` is defined");
                        assert_eq!(
                            groups.get(name),
                            Some(&vec![section.clone()]),
                            "{label}: `{name}` is alone in the COMDAT group it signs: {groups:?}"
                        );
                    }
                    _ => {
                        assert_ne!(section, "UND", "{label}: `{name}` is defined");
                        if placement.starts_with('.') {
                            assert_eq!(section, placement, "{label}: `{name}` keeps its section");
                        }
                        assert!(
                            !groups.contains_key(name)
                                && !groups.values().flatten().any(|member| member == section),
                            "{label}: `{name}` ({section}) is in no COMDAT group: {groups:?}"
                        );
                    }
                }
            }
            // O0 keeps every call, so the local callees and the
            // `available_externally` reference are all present there.
            if opt_level == OptLevel::O0 {
                for name in ["f_internal", "f_private", "f_available"] {
                    assert!(symbols.contains_key(name), "{label}: `{name}` at O0");
                }
            }
        }
    }
}

/// Every initializer shape a global definition can have in the importer, as
/// `(tag, type and initializer)`: those it reads into a flat data image
/// (`Parser::push_image_global`: an integer, floating-point, struct or
/// pointer array, a `c"..."` string, a zero fill, a named struct with fields
/// or zero, and a null pointer) and a scalar, which it carries as a typed
/// constant. The pointer array points at `@image_anchor`.
const DATA_SHAPES: [(&str, &str); 10] = [
    ("ints", "[4 x i32] [i32 1, i32 2, i32 3, i32 4]"),
    ("str", "[6 x i8] c\"hello\\00\""),
    ("zero", "[4 x i64] zeroinitializer"),
    ("floats", "[2 x double] [double 1.5, double 2.5]"),
    (
        "structs",
        "[2 x %struct.S] [%struct.S { i32 1, i64 2 }, %struct.S { i32 3, i64 4 }]",
    ),
    ("struct", "%struct.S { i32 9, i64 10 }"),
    ("szero", "%struct.S zeroinitializer"),
    ("ptrs", "[2 x ptr] [ptr @image_anchor, ptr null]"),
    ("pnull", "ptr null"),
    ("scalar", "i64 5"),
];

/// Every linkage a global definition is admitted with, as `(tag, LLVM
/// keyword, comdat clause, trust-ir linkage, ELF binding, alone in the COMDAT
/// group it signs)`. A link-once or ODR definition without a `comdat` clause
/// is the backend's ungrouped `Weak` global, as llc emits a plain weak
/// symbol for it.
const DATA_LINKAGES: [(&str, &str, bool, trust_ir::Linkage, u8, bool); 10] = [
    (
        "ext",
        "",
        false,
        trust_ir::Linkage::External,
        STB_GLOBAL,
        false,
    ),
    (
        "weak",
        "weak",
        false,
        trust_ir::Linkage::Weak,
        STB_WEAK,
        false,
    ),
    (
        "loc",
        "linkonce",
        true,
        trust_ir::Linkage::LinkOnce,
        STB_WEAK,
        true,
    ),
    (
        "lo",
        "linkonce",
        false,
        trust_ir::Linkage::Weak,
        STB_WEAK,
        false,
    ),
    (
        "lodrc",
        "linkonce_odr",
        true,
        trust_ir::Linkage::LinkOnceOdr,
        STB_WEAK,
        true,
    ),
    (
        "lodr",
        "linkonce_odr",
        false,
        trust_ir::Linkage::Weak,
        STB_WEAK,
        false,
    ),
    (
        "wodrc",
        "weak_odr",
        true,
        trust_ir::Linkage::WeakOdr,
        STB_WEAK,
        true,
    ),
    (
        "wodr",
        "weak_odr",
        false,
        trust_ir::Linkage::Weak,
        STB_WEAK,
        false,
    ),
    (
        "int",
        "internal",
        false,
        trust_ir::Linkage::Internal,
        STB_LOCAL,
        false,
    ),
    (
        "priv",
        "private",
        false,
        trust_ir::Linkage::Private,
        STB_LOCAL,
        false,
    ),
];

/// The visibilities, as `(tag, LLVM keyword, trust-ir visibility, ELF
/// visibility)`; a local definition takes only the default one (any other is
/// refused by name).
const DATA_VISIBILITIES: [(&str, &str, trust_ir::Visibility, u8); 3] = [
    ("d", "", trust_ir::Visibility::Default, STV_DEFAULT),
    ("h", "hidden", trust_ir::Visibility::Hidden, STV_HIDDEN),
    (
        "p",
        "protected",
        trust_ir::Visibility::Protected,
        STV_PROTECTED,
    ),
];

/// One global definition of [`data_facts_module`] and the facts it states.
struct DataFact {
    name: String,
    linkage: trust_ir::Linkage,
    visibility: trust_ir::Visibility,
    binding: u8,
    elf_visibility: u8,
    grouped: bool,
    local: bool,
}

/// One module defining every [`DATA_SHAPES`] shape under every
/// [`DATA_LINKAGES`] linkage and every [`DATA_VISIBILITIES`] visibility its
/// linkage admits, as a writable `global` and as a `constant`, with the
/// facts each definition states. A function returns the address of each
/// local definition, which nothing else references.
fn data_facts_module() -> (String, Vec<DataFact>) {
    let mut comdats = String::new();
    let mut globals = String::new();
    let mut readers = String::new();
    let mut facts = Vec::new();
    for (shape, initializer) in DATA_SHAPES {
        for (linkage_tag, keyword, comdat, linkage, binding, grouped) in DATA_LINKAGES {
            let local = binding == STB_LOCAL;
            for (visibility_tag, visibility_keyword, visibility, elf_visibility) in
                DATA_VISIBILITIES
            {
                if local && visibility != trust_ir::Visibility::Default {
                    continue;
                }
                for storage in ["global", "constant"] {
                    let name = format!("{shape}_{linkage_tag}_{visibility_tag}_{storage}");
                    if comdat {
                        comdats.push_str(&format!("${name} = comdat any\n"));
                    }
                    let prefix: String = [keyword, visibility_keyword]
                        .iter()
                        .filter(|word| !word.is_empty())
                        .map(|word| format!("{word} "))
                        .collect();
                    let clause = if comdat { ", comdat" } else { "" };
                    globals.push_str(&format!(
                        "@{name} = {prefix}{storage} {initializer}{clause}, align 8\n"
                    ));
                    if local {
                        readers.push_str(&format!(
                            "define ptr @addr_{name}() {{\n  ret ptr @{name}\n}}\n"
                        ));
                    }
                    facts.push(DataFact {
                        name,
                        linkage,
                        visibility,
                        binding,
                        elf_visibility,
                        grouped,
                        local,
                    });
                }
            }
        }
    }
    let src = format!(
        "%struct.S = type {{ i32, i64 }}\n{comdats}\
         @image_anchor = global i64 0, align 8\n{globals}{readers}"
    );
    (src, facts)
}

/// The linkage and visibility of every global definition shape reach
/// trust-ir and the Linux object as LLVM states them, under every admitted
/// linkage and visibility. `linux_objects_spell_every_imported_symbol_fact`
/// states only scalar globals, and the importer pushes every array, string,
/// zero-fill, struct and pointer global at a site of its own
/// (`Parser::push_image_global`); before this row no floor test read the
/// visibility that site writes (the third closure audit's mutant S13, which
/// writes `Default` there, passed every importer floor target). Every
/// definition is present at every level, each local one held by the function
/// that returns its address; a grouped one's group holds its section and,
/// for a relocated initializer, that section's `.rela` section.
#[test]
fn linux_objects_spell_the_symbol_facts_of_every_global_shape() {
    let (src, facts) = data_facts_module();
    let module = import_text(&src, "data_facts").expect("the data facts module imports");
    for fact in &facts {
        assert_eq!(
            trust_ir_facts(&module, &fact.name),
            (fact.linkage, fact.visibility, None, false),
            "`{}` in trust-ir",
            fact.name
        );
    }
    for opt_level in OPT_LEVELS {
        for model in MODELS {
            let label = format!("{opt_level:?} {model}");
            let object = compile(&src, LINUX, opt_level, model)
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            common::assert_container(&object, LINUX, &label);
            let records = read_object_records(&object).expect("ELF records");
            let symbols = elf_symbols(&records);
            let groups = elf_comdat_groups(&object, &records);
            for fact in &facts {
                let name = fact.name.as_str();
                let Some((binding, visibility, section)) = unique_symbol(&symbols, name) else {
                    panic!("{label}: `{name}` is missing (local {})", fact.local);
                };
                assert_eq!(
                    (bind_name(*binding), *visibility),
                    (bind_name(fact.binding), fact.elf_visibility),
                    "{label}: `{name}` binding/visibility"
                );
                assert_ne!(section, "UND", "{label}: `{name}` is defined");
                if fact.grouped {
                    // A relocated initializer's relocation section is in the
                    // group too, as llc places it.
                    let relocations = format!(".rela{section}");
                    let members: Option<Vec<&String>> = groups.get(name).map(|members| {
                        members
                            .iter()
                            .filter(|member| **member != relocations)
                            .collect()
                    });
                    assert_eq!(
                        members,
                        Some(vec![section]),
                        "{label}: `{name}` is alone in the COMDAT group it signs: {groups:?}"
                    );
                } else {
                    assert!(
                        !groups.contains_key(name)
                            && !groups.values().flatten().any(|member| member == section),
                        "{label}: `{name}` ({section}) is in no COMDAT group: {groups:?}"
                    );
                }
            }
        }
    }
}

/// LLVM calls an `extern_weak` function directly (clang guards the call with
/// a null test of the same address); trust-ir admits only a `CallIndirect`
/// through the declaration's `SymbolAddr`. The imported call is that one, it
/// compiles, and the object holds the weak reference and no direct branch
/// relocation (`R_AARCH64_CALL26` / `JUMP26`) against it at O0.
#[test]
fn direct_calls_of_extern_weak_functions_go_through_their_address() {
    let src = "declare extern_weak i64 @w()\n\
               define i64 @c() {\n  %r = call i64 @w()\n  ret i64 %r\n}\n";
    let module = import_text(src, "t").expect("imports");
    let caller = module
        .functions
        .iter()
        .find(|function| function.name == "c")
        .expect("caller");
    let insts: Vec<&trust_ir::inst::Inst> = caller.blocks[0]
        .body
        .iter()
        .map(|node| &node.inst)
        .collect();
    assert!(
        insts
            .iter()
            .any(|inst| matches!(inst, trust_ir::inst::Inst::CallIndirect { .. }))
            && !insts
                .iter()
                .any(|inst| matches!(inst, trust_ir::inst::Inst::Call { .. })),
        "{insts:?}"
    );
    let object = compile(src, LINUX, OptLevel::O0, RelocationModel::Static)
        .expect("the address form compiles");
    let records = read_object_records(&object).expect("ELF records");
    let symbols = elf_symbols(&records);
    assert_eq!(
        unique_symbol(&symbols, "w").map(|(bind, _, ndx)| (*bind, ndx.as_str())),
        Some((STB_WEAK, "UND"))
    );
    let w = common::elf_symbol_index(&records, "w");
    let branch_relocations: Vec<u32> = records
        .relocations
        .iter()
        .filter(|relocation| relocation.record.symbol_index as usize == w)
        .map(|relocation| relocation.record.reloc_type)
        .filter(|kind| {
            [
                trust_cg_codegen::elf::constants::R_AARCH64_CALL26,
                trust_cg_codegen::elf::constants::R_AARCH64_JUMP26,
            ]
            .contains(kind)
        })
        .collect();
    assert!(branch_relocations.is_empty(), "{branch_relocations:?}");
}

/// Argument `index` (from zero) of type `ty` as LLVM instructions computing it
/// from `%x`, and its call operand. The C twins spell the same value with
/// `linux_native::weak_call_c_argument`.
fn weak_call_llvm_argument(ty: &str, index: usize) -> (String, String) {
    let k = index + 1;
    let insts = match ty {
        "i128" => format!(
            "  %a{index}h = zext i64 %x to i128\n  %a{index}s = shl i128 %a{index}h, 64\n  \
             %a{index} = or i128 %a{index}s, {}\n",
            3 * k + 1
        ),
        "i8" | "i16" | "i32" => format!(
            "  %a{index}t = add i64 %x, {}\n  %a{index} = trunc i64 %a{index}t to {ty}\n",
            5 * k
        ),
        "i1" => format!("  %a{index} = icmp sgt i64 %x, {}\n", 5 * k),
        "ptr" => format!(
            "  %a{index} = getelementptr i64, ptr @gvals, i64 {}\n",
            k % 16
        ),
        "i64" => format!("  %a{index} = add i64 %x, {}\n", 11 * k),
        "double" | "float" => {
            format!("  %a{index}i = add i64 %x, {k}\n  %a{index} = sitofp i64 %a{index}i to {ty}\n")
        }
        other => panic!("no argument spelling for `{other}`"),
    };
    (insts, format!("{ty} %a{index}"))
}

/// A module whose `call_weak(x)` makes clang's null-guarded direct call of
/// the `extern_weak` function `@wf` with signature `params` (arguments
/// computed from `x`; a pointer addresses an element of the external
/// `gvals`), and whose `call_strong(x)` makes the same call of the ordinary
/// declaration `@sf`.
fn weak_call_module(params: &[&str]) -> String {
    let (insts, operands): (Vec<String>, Vec<String>) = params
        .iter()
        .enumerate()
        .map(|(index, ty)| weak_call_llvm_argument(ty, index))
        .unzip();
    let (insts, operands, signature) = (insts.concat(), operands.join(", "), params.join(", "));
    let gvals = if params.contains(&"ptr") {
        "@gvals = external global i64\n"
    } else {
        ""
    };
    format!(
        "{gvals}declare extern_weak i64 @wf({signature})\ndeclare i64 @sf({signature})\n\n\
         define i64 @call_weak(i64 %x) {{\nentry:\n  %nz = icmp ne ptr @wf, null\n  \
         br i1 %nz, label %yes, label %no\nyes:\n{insts}  %r = call i64 @wf({operands})\n  \
         ret i64 %r\nno:\n  ret i64 -1\n}}\n\n\
         define i64 @call_strong(i64 %x) {{\nentry:\n{insts}  %r = call i64 @sf({operands})\n  \
         ret i64 %r\n}}\n"
    )
}

/// The call of a defined `extern_weak` function is a `CallIndirect` (the one
/// call trust-ir admits for a weak declaration), which on this base stores
/// only the low half of a stack-passed 128-bit integer argument (L06-P15;
/// the direct call of `@sf` stores both). So such a call, and a call of a
/// variadic weak function (no indirect variadic call is lowered), is refused
/// by name instead of compiled. Before the refusal each of the first four
/// refused signatures below, linked with a C definition of `wf` and `sf`,
/// returned a different value through `@wf` than through `@sf` at O0-O3
/// (the high half of the stack argument was never stored). The rows of
/// seven pointer, `i1`, `i16` or `i32` arguments before a 128-bit integer
/// did the same when the refusal's bound counted that type as taking no
/// general-purpose register. A 128-bit integer in a register pair, and
/// stack-passed floating-point, narrow integer, `i1` and pointer arguments,
/// compile (`linux_native` runs them against gcc twins).
#[test]
fn weak_calls_the_indirect_lowering_would_change_are_refused_by_name() {
    let seven_then_i128 = |ty: &'static str| ([vec![ty; 7], vec!["i128"]].concat(), 8);
    let mut refused: Vec<(Vec<&str>, usize)> = vec![
        seven_then_i128("i64"),
        (vec!["i128"; 5], 5),
        (vec!["i64", "i128", "i64", "i128", "i64", "i128"], 6),
        ([vec!["i64"; 7], vec!["i128", "i64"]].concat(), 8),
        // Seven general-purpose arguments of six types between
        // floating-point ones, which take none.
        (
            vec![
                "i32", "double", "i1", "float", "ptr", "double", "i16", "float", "i8", "double",
                "i64", "ptr", "i128",
            ],
            13,
        ),
        // One `i1`/`i32`/pointer argument moves a later pair to an even
        // register, past x7.
        (
            vec![
                "i128", "float", "i1", "double", "i128", "float", "i32", "i128",
            ],
            8,
        ),
        (
            vec![
                "ptr", "i128", "float", "i128", "double", "i128", "float", "i128",
            ],
            8,
        ),
    ];
    refused.extend(["ptr", "i1", "i16", "i32"].map(seven_then_i128));
    for (params, argument) in &refused {
        let src = weak_call_module(params);
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let error = compile(&src, LINUX, opt_level, RelocationModel::Pie)
                .expect_err("a stack-passed i128 weak call is refused");
            assert!(
                error.starts_with("import: ")
                    && error.contains(&format!(
                        "`extern_weak` function `@wf` whose 128-bit integer argument {argument} \
                         may be passed on the stack"
                    ))
                    && error.contains("L06-P15"),
                "{params:?} {opt_level:?}: {error}"
            );
        }
    }
    let variadic = "declare extern_weak i64 @wv(i64, ...)\n\
                    define i64 @c(i64 %x) {\n  \
                    %r = call i64 (i64, ...) @wv(i64 3, i64 %x, double 2.5, i64 20)\n  \
                    ret i64 %r\n}\n";
    let error = compile(variadic, LINUX, OptLevel::O0, RelocationModel::Pie)
        .expect_err("a variadic weak call is refused");
    assert!(
        error.contains("direct call of the variadic `extern_weak` function `@wv`"),
        "{error}"
    );
    for params in WEAK_CALL_ADMITTED_SIGNATURES {
        let src = weak_call_module(params);
        for opt_level in OPT_LEVELS {
            compile(&src, LINUX, opt_level, RelocationModel::Pie)
                .unwrap_or_else(|error| panic!("{params:?} {opt_level:?}: {error}"));
        }
    }
}

/// `extern_weak` call signatures the importer admits, each passing a class
/// of argument the indirect call must place like a direct one: 128-bit
/// integers in register pairs (the last in x6/x7, also after one argument
/// of each other general-purpose type), floating-point arguments past v7
/// before a register-pair i128, and narrow integers, `i1`, pointers and
/// floats on the stack.
const WEAK_CALL_ADMITTED_SIGNATURES: [&[&str]; 8] = [
    &["i64", "i64", "i64", "i64", "i64", "i64", "i128"],
    &["ptr", "i1", "i16", "i32", "i8", "i64", "i128"],
    &["i128", "i128", "i128", "i128"],
    &[
        "double", "double", "double", "double", "double", "double", "double", "double", "double",
        "i64", "i64", "i64", "i64", "i64", "i64", "i128",
    ],
    &[
        "i64", "i64", "i64", "i64", "i64", "i64", "i64", "i64", "i8", "i16", "i32", "i8", "i16",
    ],
    &[
        "float", "float", "float", "float", "float", "float", "float", "float", "float", "float",
        "float",
    ],
    &[
        "i64", "i64", "i64", "i64", "i64", "i64", "i64", "i64", "ptr", "i1", "i32",
    ],
    &[
        "float", "float", "float", "float", "float", "float", "float", "float", "float", "i1",
        "i1", "i1", "i1", "i1", "i1", "i1", "i1", "i1",
    ],
];

/// For every trust-ir linkage LLVM spells on a definition, the importer
/// admits a self-keyed `comdat` exactly when the backend places a
/// definition of that linkage alone in a COMDAT group it signs, so the
/// importer's admission and the backend's grouping cannot drift apart. And
/// a definition written without the clause, which LLVM puts in no group
/// (llc emits a plain symbol), is never grouped.
#[test]
fn comdat_admission_matches_the_backend_grouping_for_every_linkage() {
    use trust_ir::Linkage;
    for (keyword, spelled) in [
        ("", Linkage::External),
        ("internal", Linkage::Internal),
        ("private", Linkage::Private),
        ("weak", Linkage::Weak),
        ("weak_odr", Linkage::WeakOdr),
        ("linkonce", Linkage::LinkOnce),
        ("linkonce_odr", Linkage::LinkOnceOdr),
        ("available_externally", Linkage::AvailableExternally),
    ] {
        let function = |comdat: &str| {
            format!(
                "$s = comdat any\n\
                 define {keyword} i64 @s() {comdat} {{\n  ret i64 1\n}}\n\
                 define i64 @keep() {{\n  %r = call i64 @s()\n  ret i64 %r\n}}\n\
                 define ptr @addr() {{\n  ret ptr @s\n}}\n"
            )
        };
        let global = |comdat: &str| {
            format!(
                "$s = comdat any\n\
                 @s = {keyword} global i64 1{comdat}, align 8\n\
                 define i64 @keep() {{\n  %r = load i64, ptr @s, align 8\n  ret i64 %r\n}}\n"
            )
        };
        for (kind, with_comdat, without) in [
            ("function", function("comdat"), function("")),
            ("global", global(", comdat"), global("")),
        ] {
            let label = format!(
                "{kind} with linkage `{}`",
                if keyword.is_empty() {
                    "(none)"
                } else {
                    keyword
                }
            );
            let object = compile(&without, LINUX, OptLevel::O0, RelocationModel::Static)
                .unwrap_or_else(|error| panic!("{label} without COMDAT: {error}"));
            let records = read_object_records(&object).expect("ELF records");
            assert!(
                !elf_comdat_groups(&object, &records).contains_key("s"),
                "{label}: no `comdat` clause, so no group (as llc emits it)"
            );
            // The backend's own grouping of the spelled linkage: the
            // clause-less module with `@s` restated at that linkage.
            let mut module = import_text(&without, "t").expect("imports without COMDAT");
            for function in module.functions.iter_mut().filter(|f| f.name == "s") {
                function.linkage = spelled;
            }
            for global in module.globals.iter_mut().filter(|g| g.name == "s") {
                global.linkage = spelled;
            }
            let object = compile_module(&module, LINUX, OptLevel::O0, RelocationModel::Static)
                .unwrap_or_else(|error| panic!("{label} restated: {error}"));
            let records = read_object_records(&object).expect("ELF records");
            let grouped = elf_comdat_groups(&object, &records).contains_key("s");
            match import_text(&with_comdat, "t") {
                Ok(_) => {
                    assert!(
                        grouped,
                        "{label}: COMDAT admitted, but the backend groups nothing"
                    );
                    let object =
                        compile(&with_comdat, LINUX, OptLevel::O0, RelocationModel::Static)
                            .unwrap_or_else(|error| panic!("{label} with COMDAT: {error}"));
                    let records = read_object_records(&object).expect("ELF records");
                    assert!(
                        elf_comdat_groups(&object, &records).contains_key("s"),
                        "{label}: the admitted COMDAT is emitted"
                    );
                }
                Err(trust_cg_llvm_import::Error::Unsupported(reason)) => {
                    assert!(
                        !grouped,
                        "{label}: the backend groups it, but the COMDAT was refused: {reason}"
                    );
                    assert!(reason.contains("`$s`"), "{label}: {reason}");
                }
                Err(other) => panic!("{label}: {other:?}"),
            }
        }
    }
}

/// Mach-O: `N_WEAK_DEF` for the ODR functions (the Mach-O meaning of a
/// self-keyed COMDAT), and a private extern (`N_SECT | N_EXT | N_PEXT`, not
/// weak) for a hidden `external` definition, the one function visibility fact
/// the AArch64 Mach-O object path spells. Every other hidden or protected
/// function (a definition of another linkage, a declaration), a function
/// section and a weak reference are refused by name.
#[test]
fn apple_objects_mark_odr_definitions_weak_and_refuse_the_rest_by_name() {
    use trust_cg_codegen::macho::constants::{N_EXT, N_PEXT, N_SECT};

    let src = "define linkonce_odr i64 @odr() {\n  ret i64 1\n}\n\
               define weak_odr i64 @wodr() {\n  ret i64 2\n}\n\
               define i64 @strong() {\n  %a = call i64 @odr()\n  %b = call i64 @wodr()\n  \
               %s = add i64 %a, %b\n  ret i64 %s\n}\n";
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let object = compile(src, APPLE, opt_level, RelocationModel::Static)
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        common::assert_container(&object, APPLE, "odr");
        let parsed = MachOParser::parse(&object).expect("Mach-O");
        let symbol = |name: &str| {
            parsed
                .symbols
                .iter()
                .find(|symbol| symbol.name.as_str() == name)
                .unwrap_or_else(|| panic!("`{name}` in the Mach-O symbols"))
        };
        for name in ["_odr", "_wodr"] {
            assert!(
                symbol(name).is_defined()
                    && symbol(name).is_external()
                    && symbol(name).is_weak_def(),
                "{opt_level:?}: `{name}` is an external weak definition"
            );
        }
        assert!(
            !symbol("_strong").is_weak_def(),
            "{opt_level:?}: `_strong` stays strong"
        );
    }
    for opt_level in OPT_LEVELS {
        let object = compile(
            "define hidden i64 @h() {\n  ret i64 1\n}\n",
            APPLE,
            opt_level,
            RelocationModel::Static,
        )
        .unwrap_or_else(|error| panic!("{opt_level:?}: hidden external definition: {error}"));
        common::assert_container(&object, APPLE, "h");
        let parsed = MachOParser::parse(&object).expect("Mach-O");
        let hidden: Vec<_> = parsed
            .symbols
            .iter()
            .filter(|symbol| symbol.name.as_str() == "_h")
            .collect();
        assert!(
            matches!(hidden.as_slice(), [h]
                if h.n_type == N_SECT | N_EXT | N_PEXT && !h.is_weak_def()),
            "{opt_level:?}: `_h` must be one private-extern definition: {hidden:?}"
        );
    }
    for (src, needle) in [
        (
            "define protected i64 @p() {\n  ret i64 1\n}\n",
            "function `p` states trust-ir v45 `visibility` = protected",
        ),
        (
            "define linkonce_odr hidden i64 @lh() {\n  ret i64 1\n}\n",
            "function `lh` states trust-ir v45 `visibility` = hidden",
        ),
        (
            "declare hidden i64 @dh()\ndefine i64 @c() {\n  %r = call i64 @dh()\n  ret i64 %r\n}\n",
            "function `dh` states trust-ir v45 `visibility` = hidden",
        ),
        (
            "define i64 @s() section \"__TEXT,__tcg\" {\n  ret i64 1\n}\n",
            "function `s` states trust-ir v45 `section` = \"__TEXT,__tcg\"",
        ),
        (
            "declare extern_weak i64 @w()\ndefine ptr @a() {\n  ret ptr @w\n}\n",
            "unsupported linkage `external_weak` on symbol `w`",
        ),
    ] {
        let error = compile(src, APPLE, OptLevel::O0, RelocationModel::Static)
            .expect_err("Mach-O refuses what it cannot spell");
        assert!(error.contains(needle), "{src}: {error}");
    }
}

// =============================================================================
// Admission: every symbol fact the importer decides, through `import_text`
// =============================================================================

/// One imported symbol's trust-ir facts: `(linkage, visibility, section,
/// retained)`; `retained` is always false for a function, which the
/// importer refuses in `@llvm.used`.
fn trust_ir_facts(
    module: &trust_ir::Module,
    name: &str,
) -> (
    trust_ir::Linkage,
    trust_ir::Visibility,
    Option<String>,
    bool,
) {
    if let Some(function) = module.functions.iter().find(|f| f.name == name) {
        return (
            function.linkage,
            function.visibility,
            function.section.clone(),
            false,
        );
    }
    let global = module
        .globals
        .iter()
        .find(|g| g.name == name)
        .unwrap_or_else(|| panic!("`{name}` is neither a function nor a global of the module"));
    (
        global.linkage,
        global.visibility,
        global.section.clone(),
        global.retained,
    )
}

/// Every linkage, visibility, COMDAT, section and retention fact the LLVM
/// text states for a function or global, in one module.
const ADMITTED_FACTS_MODULE: &str = r#"
target triple = "aarch64-unknown-linux-gnu"

$f_wodr_c = comdat any
$f_lodr_c = comdat any
$g_lo_c = comdat any
$g_lodr_c = comdat any
$g_wodr_c = comdat any

@g_private = private global i64 1, align 8
@g_internal = internal global i64 2, align 8
@g_weak = weak global i64 3, align 8
@g_lo_c = linkonce global i64 4, comdat, align 8
@g_lodr_c = linkonce_odr global i64 5, comdat, align 8
@g_wodr_c = weak_odr global i64 6, comdat, align 8
@g_lodr = linkonce_odr global i64 7, align 8
@g_ae = available_externally global i64 8, align 8
@g_ext = external global i64, align 8
@g_ew = extern_weak global i64, align 8
@g_hidden = hidden global i64 9, align 8
@g_protected = protected constant i64 10, align 8
@g_sec = global i64 11, section "gsec", align 8
@g_used = internal global i64 12, align 8
@g_cused = internal global i64 13, align 8
@llvm.used = appending global [2 x ptr] [ptr @g_used, ptr @f_ae], section "llvm.metadata"
@llvm.compiler.used = appending global [1 x ptr] [ptr @g_cused], section "llvm.metadata"

define private i64 @f_private() {
  ret i64 1
}
define internal i64 @f_internal() {
  ret i64 2
}
define weak i64 @f_weak() {
  ret i64 3
}
define linkonce i64 @f_linkonce() {
  ret i64 4
}
define weak_odr i64 @f_wodr() {
  ret i64 5
}
define linkonce_odr i64 @f_lodr() {
  ret i64 6
}
define weak_odr i64 @f_wodr_c() comdat {
  ret i64 7
}
define linkonce_odr i64 @f_lodr_c() comdat {
  ret i64 8
}
define available_externally i64 @f_ae() {
  ret i64 9
}
define hidden i64 @f_hidden() {
  ret i64 10
}
define protected i64 @f_protected() {
  ret i64 11
}
define external i64 @f_external() section "fsec" {
  ret i64 12
}
declare extern_weak i64 @d_weak()
declare hidden i64 @d_hidden()
declare protected i64 @d_protected()
declare i64 @d_plain()
"#;

/// The importer carries every fact LLVM states for a symbol onto its
/// trust-ir function or global, with the ODR-without-COMDAT downgrade
/// (`weak_odr`/`linkonce_odr` without a `comdat` clause are the backend's
/// ungrouped `Weak`/`LinkOnce` functions and `Weak` globals), retention for
/// `@llvm.used` alone (an `available_externally` function there is
/// admitted in this module, whose triple names ELF: it is no definition)
/// and the explicit sections. The importer's
/// lib unit tests check the same decisions; this row checks them through
/// the public API in a floor target.
#[test]
fn imported_symbol_facts_reach_trust_ir_as_llvm_states_them() {
    use trust_ir::{Linkage as L, Visibility as V};
    let module = import_text(ADMITTED_FACTS_MODULE, "facts").expect("the facts module imports");
    let none = None::<String>;
    for (name, want) in [
        ("f_private", (L::Private, V::Default, none.clone(), false)),
        ("f_internal", (L::Internal, V::Default, none.clone(), false)),
        ("f_weak", (L::Weak, V::Default, none.clone(), false)),
        ("f_linkonce", (L::LinkOnce, V::Default, none.clone(), false)),
        ("f_wodr", (L::Weak, V::Default, none.clone(), false)),
        ("f_lodr", (L::LinkOnce, V::Default, none.clone(), false)),
        ("f_wodr_c", (L::WeakOdr, V::Default, none.clone(), false)),
        (
            "f_lodr_c",
            (L::LinkOnceOdr, V::Default, none.clone(), false),
        ),
        (
            "f_ae",
            (L::AvailableExternally, V::Default, none.clone(), false),
        ),
        ("f_hidden", (L::External, V::Hidden, none.clone(), false)),
        (
            "f_protected",
            (L::External, V::Protected, none.clone(), false),
        ),
        (
            "f_external",
            (L::External, V::Default, Some("fsec".to_string()), false),
        ),
        ("d_weak", (L::ExternalWeak, V::Default, none.clone(), false)),
        ("d_hidden", (L::External, V::Hidden, none.clone(), false)),
        (
            "d_protected",
            (L::External, V::Protected, none.clone(), false),
        ),
        ("d_plain", (L::External, V::Default, none.clone(), false)),
        ("g_private", (L::Private, V::Default, none.clone(), false)),
        ("g_internal", (L::Internal, V::Default, none.clone(), false)),
        ("g_weak", (L::Weak, V::Default, none.clone(), false)),
        ("g_lo_c", (L::LinkOnce, V::Default, none.clone(), false)),
        (
            "g_lodr_c",
            (L::LinkOnceOdr, V::Default, none.clone(), false),
        ),
        ("g_wodr_c", (L::WeakOdr, V::Default, none.clone(), false)),
        ("g_lodr", (L::Weak, V::Default, none.clone(), false)),
        (
            "g_ae",
            (L::AvailableExternally, V::Default, none.clone(), false),
        ),
        ("g_ext", (L::External, V::Default, none.clone(), false)),
        ("g_ew", (L::ExternalWeak, V::Default, none.clone(), false)),
        ("g_hidden", (L::External, V::Hidden, none.clone(), false)),
        (
            "g_protected",
            (L::External, V::Protected, none.clone(), false),
        ),
        (
            "g_sec",
            (L::External, V::Default, Some("gsec".to_string()), false),
        ),
        ("g_used", (L::Internal, V::Default, none.clone(), true)),
        ("g_cused", (L::Internal, V::Default, none.clone(), false)),
    ] {
        assert_eq!(trust_ir_facts(&module, name), want, "`{name}`");
    }
    assert!(
        !module.globals.iter().any(|g| g.name.starts_with("llvm.")),
        "the used arrays are metadata, not globals"
    );
}

/// Each symbol fact neither trust-ir nor this backend can carry is refused
/// by name: a visibility on a local symbol or two of them, a linkage LLVM
/// forbids in its position, conflicting headers, every COMDAT the backend
/// does not emit itself, `llvm.metadata` as a global's section, a function
/// in `@llvm.used`, a symbol name the importer would write where llc writes
/// another (a quoted or numbered external name, a `\01` label off Mach-O, a
/// Mach-O label and a plain name that are one symbol, a symbol that is not
/// private named with LLVM's ELF private prefix `.L` when the target is not
/// Mach-O), `thread_local`, `externally_initialized`, an `alias` or `ifunc`,
/// by its keyword, and a hidden, protected or `extern_weak` declaration
/// whose signature the importer does not model (skipping it, as it skips
/// such a declaration that states no fact, would let a call declare the
/// function `external` and default). The same declaration stating no fact,
/// and a private `.L` global, still import.
#[test]
fn imported_symbol_facts_without_a_spelling_are_refused_by_name() {
    const APPLE_TRIPLE: &str = "target triple = \"arm64-apple-macosx14.0.0\"\n";
    const LINUX_TRIPLE: &str = "target triple = \"aarch64-unknown-linux-gnu\"\n";
    const DOT_L: &str = "this importer carries a `.L` name only for a private symbol";
    const SKIPPED_FACTS: &str = "skipping it would let a call default them";
    let cases: [(String, &str); 36] = [
        (
            "declare hidden protected i32 @f()\n".into(),
            "two visibilities",
        ),
        (
            "@g = hidden protected global i32 1\n".into(),
            "two visibilities",
        ),
        (
            "define internal hidden i32 @f() {\n  ret i32 7\n}\n".into(),
            "visibility `hidden` on a local (`internal`)",
        ),
        (
            "@g = private protected global i32 1\n".into(),
            "visibility `protected` on a local (`private`)",
        ),
        (
            "define extern_weak i32 @f() {\n  ret i32 0\n}\n".into(),
            "`extern_weak` on a definition",
        ),
        (
            "declare internal i32 @f()\n".into(),
            "linkage `internal` on a declaration",
        ),
        (
            "declare hidden i32 @f()\ndefine i32 @f() {\n  ret i32 1\n}\n".into(),
            "twice with different symbol facts",
        ),
        (
            "@g = external global i32 1\n".into(),
            "linkage `external` with an initializer",
        ),
        (
            "@g = extern_weak global i32 1\n".into(),
            "linkage `extern_weak` with an initializer",
        ),
        (
            "$g = comdat any\n@g = available_externally global i32 1, comdat\n".into(),
            "COMDAT `$g` on a declaration",
        ),
        (
            "$x = comdat any\n@x = linkonce_odr global i32 0, comdat\n\
             @_ZGVx = linkonce_odr global i64 0, comdat($x)\n"
                .into(),
            "keyed on another symbol",
        ),
        (
            "$f = comdat largest\ndefine linkonce_odr i32 @f() comdat {\n  ret i32 0\n}\n".into(),
            "selection kind `largest`",
        ),
        (
            "$f = comdat any\ndefine weak i32 @f() comdat {\n  ret i32 0\n}\n".into(),
            "does not emit in a COMDAT group",
        ),
        (
            "$f = comdat any\ndefine linkonce i32 @f() comdat {\n  ret i32 0\n}\n".into(),
            "does not emit in a COMDAT group",
        ),
        (
            "$f = comdat any\ndeclare i32 @f() comdat\n".into(),
            "on a declaration",
        ),
        (
            "define linkonce_odr i32 @f() comdat {\n  ret i32 0\n}\n".into(),
            "COMDAT `$f` is not declared",
        ),
        (
            "@g = global i32 1, section \"llvm.metadata\"\n".into(),
            "section \"llvm.metadata\"",
        ),
        (
            "@llvm.used = appending global [1 x ptr] [ptr @reg], section \"llvm.metadata\"\n\
             define internal i32 @reg() {\n  ret i32 1\n}\n"
                .into(),
            "function `@reg` is listed in `@llvm.used`",
        ),
        (
            format!("{APPLE_TRIPLE}declare void @\"\\01_dup\"()\ndeclare void @dup()\n"),
            "appears both as a `\\01` asm-label",
        ),
        (
            "@\"a b\" = global i64 1\n".into(),
            "is carried only for an internal or private definition",
        ),
        (
            "define weak i64 @\"a b\"() {\n  ret i64 1\n}\n".into(),
            "is carried only for an internal or private definition",
        ),
        (
            format!("{LINUX_TRIPLE}define i64 @\"\\01foo\"() {{\n  ret i64 1\n}}\n"),
            "for a target whose object format is not Mach-O",
        ),
        (
            format!("{APPLE_TRIPLE}define i64 @\"\\01_a b\"() {{\n  ret i64 7\n}}\n"),
            "the `\\01` asm label of the Mach-O symbol `_a b`",
        ),
        (
            "define i64 @0() {\n  ret i64 1\n}\n".into(),
            "a numbered symbol is carried only for an internal or private definition",
        ),
        (
            "@0 = global i64 42\n".into(),
            "a numbered symbol is carried only for an internal or private definition",
        ),
        (
            "@t = thread_local global i32 0\n".into(),
            "`thread_local` (thread-local globals are not imported",
        ),
        (
            "@g = externally_initialized global i32 0\n".into(),
            "`externally_initialized`",
        ),
        (
            "@g = global i64 1\n@a = alias i64, ptr @g\n".into(),
            "global `@a` is an `alias`",
        ),
        (
            "@g = global i64 1\n@a = weak hidden alias i64, ptr @g\n".into(),
            "global `@a` is an `alias`",
        ),
        (
            "define ptr @r() {\n  ret ptr null\n}\n@i = ifunc i64 (), ptr @r\n".into(),
            "global `@i` is an `ifunc`",
        ),
        ("define i64 @.Lbar() {\n  ret i64 3\n}\n".into(), DOT_L),
        (
            format!("{LINUX_TRIPLE}@.Lg = weak hidden global i64 1\n"),
            DOT_L,
        ),
        (
            format!(
                "{LINUX_TRIPLE}declare i64 @.Lext()\ndefine i64 @f() {{\n  \
                 %r = call i64 @.Lext()\n  ret i64 %r\n}}\n"
            ),
            DOT_L,
        ),
        (
            "declare hidden <3 x i7> @v(<3 x i7>)\n".into(),
            SKIPPED_FACTS,
        ),
        (
            format!("{LINUX_TRIPLE}declare protected <4 x i32> @v(<4 x i32>)\n"),
            SKIPPED_FACTS,
        ),
        (
            "declare extern_weak <3 x i7> @v(<3 x i7>)\n".into(),
            SKIPPED_FACTS,
        ),
    ];
    for (src, needle) in &cases {
        match import_text(src, "refused") {
            Err(trust_cg_llvm_import::Error::Unsupported(reason)) => {
                assert!(reason.contains(needle), "{src}: {reason}");
            }
            other => panic!("{src}: expected a named refusal containing {needle:?}, got {other:?}"),
        }
    }
    // The boundary: a declaration with an unmodelled signature that states
    // no fact is skipped, and a private symbol's `.L` name meets nothing.
    let skipped = import_text("declare <3 x i7> @v(<3 x i7>)\n", "skipped")
        .expect("a declaration stating no fact is skipped");
    assert!(skipped.functions.is_empty(), "{:?}", skipped.functions);
    let private = import_text(
        &format!("{LINUX_TRIPLE}@.Lx = private global i64 5\n"),
        "private",
    )
    .expect("a private `.L` global imports");
    assert_eq!(
        trust_ir_facts(&private, ".Lx").0,
        trust_ir::Linkage::Private,
        "`@.Lx`"
    );
}

/// `@llvm.used` globals of every kind beside unlisted neighbours of the same
/// kind: writable, zero fill, read-only, relocated, internal, two in an
/// explicit dotted section shared with an unlisted one, one in a named
/// `__start_`/`__stop_` section, and a COMDAT one; plus an
/// `@llvm.compiler.used` global.
const RETENTION_MODULE: &str = r#"
$cu = comdat any
$cm = comdat any

@ud = global i64 11, align 8
@md = global i64 12, align 8
@ub = global i64 0, align 8
@mb = global i64 0, align 8
@ur = constant i64 13, align 8
@mr = constant i64 14, align 8
@urel = constant [1 x ptr] [ptr @md], align 8
@mrel = constant [1 x ptr] [ptr @md], align 8
@ui = internal global i64 15, align 8
@mi = internal global i64 16, align 8
@nu1 = global i64 21, section ".data.keep", align 8
@nm1 = global i64 22, section ".data.keep", align 8
@nu2 = global i64 23, section ".data.keep", align 8
@su = internal global i64 4, section "myset", align 8
@sm = global i64 1, section "myset", align 8
@cu = linkonce_odr global i64 31, comdat, align 8
@cm = linkonce_odr global i64 32, comdat, align 8
@cc = internal global i64 33, align 8
@llvm.used = appending global [9 x ptr] [ptr @ud, ptr @ub, ptr @ur, ptr @urel, ptr @ui, ptr @nu1, ptr @nu2, ptr @su, ptr @cu], section "llvm.metadata"
@llvm.compiler.used = appending global [1 x ptr] [ptr @cc], section "llvm.metadata"

define i32 @anchor() {
  ret i32 0
}
"#;

/// `SHF_GNU_RETAIN`.
const SHF_GNU_RETAIN: u64 = 0x20_0000;

/// A global in `@llvm.used` is retained ALONE, as llc places it: in a
/// section of its own (`<kind>.<symbol>` without an explicit name, another
/// section of its explicit name with one), flagged `SHF_GNU_RETAIN`, so the
/// flag keeps exactly that global through `--gc-sections`. No unlisted
/// neighbour, and no `@llvm.compiler.used` global, is in a retained section.
/// Before, the importer's retention set `SHF_GNU_RETAIN` on the whole shared
/// section a used global was packed into (`.data`, `.bss`, `.rodata`, a
/// named one), and every neighbour survived `--gc-sections` with it.
#[test]
fn used_globals_are_retained_alone_in_their_own_sections() {
    for opt_level in OPT_LEVELS {
        for model in MODELS {
            let label = format!("{opt_level:?} {model}");
            let object = compile(RETENTION_MODULE, LINUX, opt_level, model)
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            let records = read_object_records(&object).expect("ELF records");
            let defining = |name: &str| {
                let symbol = records
                    .symbols
                    .iter()
                    .find(|symbol| symbol.name == name && symbol.section_index != 0)
                    .unwrap_or_else(|| panic!("{label}: `{name}` is defined"));
                usize::from(symbol.section_index)
            };
            let data_symbols_in = |section: usize| -> Vec<String> {
                records
                    .symbols
                    .iter()
                    .filter(|symbol| {
                        usize::from(symbol.section_index) == section
                            && symbol.symbol_type == 1 /* STT_OBJECT */
                    })
                    .map(|symbol| symbol.name.clone())
                    .collect()
            };
            for (name, section) in [
                ("ud", ".data.ud"),
                ("ub", ".bss.ub"),
                ("ur", ".rodata.ur"),
                ("urel", ".data.rel.ro.urel"),
                ("ui", ".data.ui"),
                ("nu1", ".data.keep"),
                ("nu2", ".data.keep"),
                ("su", "myset"),
                ("cu", ".data.cu"),
            ] {
                let index = defining(name);
                let header = &records.sections[index];
                assert_eq!(header.name, section, "{label}: `{name}`'s own section");
                assert_ne!(
                    header.sh_flags & SHF_GNU_RETAIN,
                    0,
                    "{label}: `{name}`'s section is retained: {header:?}"
                );
                assert_eq!(
                    data_symbols_in(index),
                    vec![name.to_string()],
                    "{label}: `{name}` is alone in its retained section"
                );
            }
            // The unlisted neighbours (the optimizer may drop an unused
            // internal one) and the compiler-used global are never retained.
            for name in ["md", "mb", "mr", "mrel", "mi", "nm1", "sm", "cm", "cc"] {
                let Some(symbol) = records
                    .symbols
                    .iter()
                    .find(|symbol| symbol.name == name && symbol.section_index != 0)
                else {
                    assert!(
                        matches!(name, "mi" | "cc") && opt_level != OptLevel::O0,
                        "{label}: `{name}` is missing"
                    );
                    continue;
                };
                let header = &records.sections[usize::from(symbol.section_index)];
                assert_eq!(
                    header.sh_flags & SHF_GNU_RETAIN,
                    0,
                    "{label}: `{name}` shares no retained section: {header:?}"
                );
            }
            // Two used globals and one unlisted one name `.data.keep`: three
            // sections of that name, as llc's unique sections; one used and
            // one unlisted name `myset`: two.
            for (name, count) in [(".data.keep", 3), ("myset", 2)] {
                assert_eq!(
                    records
                        .sections
                        .iter()
                        .filter(|section| section.name == name)
                        .count(),
                    count,
                    "{label}: sections named `{name}`"
                );
            }
            // Sections are in llc's creation order, which decides the order
            // the linker concatenates same-named inputs in: `nu1`'s own
            // `.data.keep`, then the shared one `nm1` opens, then `nu2`'s;
            // `su`'s own `myset` before the shared one of `sm`.
            for (first, second) in [("nu1", "nm1"), ("nm1", "nu2"), ("su", "sm")] {
                if let (Some(a), Some(b)) = (
                    records.symbols.iter().find(|s| s.name == first),
                    records.symbols.iter().find(|s| s.name == second),
                ) {
                    assert!(
                        a.section_index < b.section_index,
                        "{label}: `{first}`'s section precedes `{second}`'s"
                    );
                }
            }
            // The used COMDAT global is retained inside its own group.
            let groups = elf_comdat_groups(&object, &records);
            assert_eq!(
                groups.get("cu"),
                Some(&vec![".data.cu".to_string()]),
                "{label}: {groups:?}"
            );
            assert!(
                records.sections.iter().any(|s| s.sh_type == SHT_GROUP),
                "{label}"
            );
        }
    }
}

/// Declarations nothing references, with every fact llc 22 writes for one:
/// hidden and protected function and data declarations, `extern_weak` ones
/// of each visibility, an `available_externally` hidden function, and a
/// hidden intrinsic declaration. llc writes no symbol for a default
/// declaration or an `available_externally` global (a hidden or protected
/// one is refused by name: see
/// `available_externally_globals_with_a_visibility_are_refused_by_name`).
const UNREFERENCED_DECLARATIONS_MODULE: &str = r#"
declare hidden i64 @dh()
declare protected i64 @dp()
declare i64 @dd()
declare extern_weak i64 @dw()
declare extern_weak hidden i64 @dwh()
declare extern_weak protected i64 @dwp()
@gh = external hidden global i64
@gp = external protected global i64
@gd = external global i64
@gw = extern_weak global i64
@gwh = extern_weak hidden global i64
@gwp = extern_weak protected global i64
@gae = available_externally global i64 5
define available_externally hidden i64 @faeh() {
  ret i64 1
}
define available_externally i64 @fae() {
  ret i64 1
}
declare hidden void @llvm.donothing()

define i32 @anchor() {
  ret i32 0
}
"#;

/// Every declaration llc 22 writes even when nothing references it (its
/// `AsmPrinter` states a declaration's `extern_weak` linkage and non-default
/// visibility on the symbol) is an undefined symbol of the imported object
/// with llc's binding and visibility, at every level and model; the ones
/// llc leaves out stay out. Before, the ELF emitters wrote an undefined
/// symbol only for a name something referenced, so a hidden declaration no
/// longer hid the definition another object supplied (an `LD_PRELOAD`
/// interposer rebound the library's own call, the native row below).
#[test]
fn unreferenced_declarations_are_written_with_llc_s_facts() {
    let undefined = [
        ("dh", STB_GLOBAL, STV_HIDDEN),
        ("dp", STB_GLOBAL, STV_PROTECTED),
        ("dw", STB_WEAK, STV_DEFAULT),
        ("dwh", STB_WEAK, STV_HIDDEN),
        ("dwp", STB_WEAK, STV_PROTECTED),
        ("gh", STB_GLOBAL, STV_HIDDEN),
        ("gp", STB_GLOBAL, STV_PROTECTED),
        ("gw", STB_WEAK, STV_DEFAULT),
        ("gwh", STB_WEAK, STV_HIDDEN),
        ("gwp", STB_WEAK, STV_PROTECTED),
        ("faeh", STB_GLOBAL, STV_HIDDEN),
        ("llvm.donothing", STB_GLOBAL, STV_HIDDEN),
    ];
    for opt_level in OPT_LEVELS {
        for model in MODELS {
            let label = format!("{opt_level:?} {model}");
            let object = compile(UNREFERENCED_DECLARATIONS_MODULE, LINUX, opt_level, model)
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            let records = read_object_records(&object).expect("ELF records");
            let symbols = elf_symbols(&records);
            for (name, binding, visibility) in undefined {
                assert_eq!(
                    unique_symbol(&symbols, name),
                    Some(&(binding, visibility, "UND".to_string())),
                    "{label}: `{name}`"
                );
            }
            for name in ["dd", "gd", "gae", "fae"] {
                assert!(
                    !symbols.contains_key(name),
                    "{label}: llc writes no `{name}`: {:?}",
                    symbols.get(name)
                );
            }
        }
    }
}

/// An `available_externally` global with hidden or protected visibility is
/// refused by name, listed in `@llvm.used` or not and referenced or not.
/// llc 22 writes no visibility for an `available_externally` global (its
/// `AsmPrinter` skips the global before stating one), so a reference to it
/// is a `STV_DEFAULT` undefined symbol, and nothing is written for an
/// unreferenced one. The import wrote the stated visibility on the
/// undefined symbol: an executable linked against a library defining the
/// symbol failed under every linker where llc's object linked, and a shared
/// object linking the definition hid it where llc's (gold) exported it. A
/// default one and an `available_externally` function of every visibility
/// keep llc's facts (`U`, and a hidden or protected `U` for the functions,
/// which llc's `AsmPrinter` states for every declaration).
#[test]
fn available_externally_globals_with_a_visibility_are_refused_by_name() {
    for visibility in ["hidden", "protected"] {
        for listed in [false, true] {
            for referenced in [false, true] {
                let mut src =
                    format!("@g = available_externally {visibility} global i64 5, align 8\n");
                if listed {
                    src.push_str(
                        "@llvm.used = appending global [1 x ptr] [ptr @g], section \
                         \"llvm.metadata\"\n",
                    );
                }
                src.push_str(if referenced {
                    "define i64 @get() {\n  %v = load i64, ptr @g, align 8\n  ret i64 %v\n}\n"
                } else {
                    "define i64 @get() {\n  ret i64 0\n}\n"
                });
                let label = format!("{visibility}, listed {listed}, referenced {referenced}");
                match import_text(&src, "available_externally") {
                    Err(trust_cg_llvm_import::Error::Unsupported(reason)) => assert!(
                        reason.contains("global `@g`")
                            && reason.contains(&format!(
                                "`available_externally` global with `{visibility}` visibility"
                            )),
                        "{label}: {reason}"
                    ),
                    other => panic!("{label}: expected a named refusal, got {other:?}"),
                }
            }
        }
    }
    let admitted = "@gae = available_externally global i64 5, align 8\n\
                    @gaed = available_externally default global i64 6, align 8\n\
                    define available_externally hidden i64 @faeh() {\n  ret i64 1\n}\n\
                    define available_externally protected i64 @faep() {\n  ret i64 2\n}\n\
                    define i64 @get() {\n\
                    \x20 %a = load i64, ptr @gae, align 8\n\
                    \x20 %b = load i64, ptr @gaed, align 8\n\
                    \x20 %c = call i64 @faeh()\n\
                    \x20 %s = add i64 %a, %b\n\
                    \x20 %t = add i64 %s, %c\n\
                    \x20 ret i64 %t\n\
                    }\n";
    // The backend's own trust-ir contract for such a global, which the
    // importer no longer reaches (another producer may state it): a hidden
    // `AvailableExternally` import is a hidden undefined symbol when
    // something references it, and, as llc writes no symbol for an
    // unreferenced `available_externally` global, none when nothing does.
    let mut hidden_in_trust_ir = import_text(
        "@gaer = available_externally global i64 5, align 8\n\
         @gaeu = available_externally global i64 6, align 8\n\
         define i64 @get() {\n  %v = load i64, ptr @gaer, align 8\n  ret i64 %v\n}\n",
        "available_externally",
    )
    .expect("default available_externally globals import");
    for global in &mut hidden_in_trust_ir.globals {
        global.visibility = trust_ir::Visibility::Hidden;
    }
    for opt_level in OPT_LEVELS {
        for model in MODELS {
            let label = format!("{opt_level:?} {model}");
            let object = compile(admitted, LINUX, opt_level, model)
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            let records = read_object_records(&object).expect("ELF records");
            let symbols = elf_symbols(&records);
            for (name, visibility) in [
                ("gae", STV_DEFAULT),
                ("gaed", STV_DEFAULT),
                ("faeh", STV_HIDDEN),
                ("faep", STV_PROTECTED),
            ] {
                assert_eq!(
                    unique_symbol(&symbols, name),
                    Some(&(STB_GLOBAL, visibility, "UND".to_string())),
                    "{label}: `{name}`"
                );
            }
            let object = compile_module(&hidden_in_trust_ir, LINUX, opt_level, model)
                .unwrap_or_else(|error| panic!("{label} trust-ir: {error}"));
            let records = read_object_records(&object).expect("ELF records");
            let symbols = elf_symbols(&records);
            assert_eq!(
                unique_symbol(&symbols, "gaer"),
                Some(&(STB_GLOBAL, STV_HIDDEN, "UND".to_string())),
                "{label} trust-ir: `gaer`"
            );
            assert!(
                !symbols.contains_key("gaeu"),
                "{label} trust-ir: no `gaeu`: {:?}",
                symbols.get("gaeu")
            );
        }
    }
}

/// How an AArch64 ELF object's relocations name symbol `name`: `GOT` (the
/// `ADR_GOT_PAGE`/`LD64_GOT_LO12_NC` pair), `PC` (a PC-relative page and
/// its absolute low twelve bits), `CALL` (`CALL26`/`JUMP26`) or `ABS64`.
fn relocation_forms(records: &ElfObjectRecords, name: &str) -> BTreeSet<&'static str> {
    records
        .relocations
        .iter()
        .filter(|relocation| {
            records
                .symbols
                .get(relocation.record.symbol_index as usize)
                .is_some_and(|symbol| symbol.name == name)
        })
        .map(|relocation| match relocation.record.reloc_type {
            257 => "ABS64",
            275 | 277 | 278 | 284 | 285 | 286 | 299 => "PC",
            282 | 283 => "CALL",
            311 | 312 => "GOT",
            _ => "OTHER",
        })
        .collect()
}

/// `dso_local` lets llc 22 assume a symbol is defined in the linked image,
/// and it then addresses a default-visibility one PC-relative under every
/// relocation model, where it otherwise uses the GOT; the importer drops
/// the keyword (trust-ir has no such fact). For a declaration for the
/// linker (a data or function declaration, an `available_externally`
/// global or function) the backend's GOT form differs from llc's under
/// every model. Measured (L02-P13, third verifier round and its repair,
/// O0-O3): shared objects linking the import's object under GNU ld, gold
/// and LLD, with an `LD_PRELOAD` interposer taking its read, where llc's
/// linked under gold alone and kept the definition's, and GNU ld `-pie`
/// refusing llc's object only. So a module whose code takes such a
/// declaration's address is refused by name. Forms that stay admitted and
/// equal llc 22.1.2's (`llvm-readobj -r`): a direct call (`CALL26`), a
/// pointer in an initializer (`ABS64`), a declaration nothing addresses (no
/// symbol), a `dso_preemptable` one (LLVM's default: the GOT in both) and
/// an `extern_weak` one (the GOT in both: an address that may be null). A
/// hidden or protected declaration, which LLVM makes dso-local without the
/// keyword, stays admitted with the backend's GOT form, as before, where
/// llc's is PC-relative (the backend's rule for an IFUNC definition). A
/// `dso_local` definition is addressed PC-relative under `static` and
/// `pie`, as llc does; under `pic` the backend keeps the GOT where llc binds
/// the module's references locally.
///
/// The rules read the relocation model a caller compiles under
/// (`import_text_for_compile`, LD-31). Every refused spelling is admitted
/// for an AArch64 ELF target under `static` (its objects go into non-PIE
/// executables, where llc's PC-relative reference and the import's GOT load
/// are one address unless the defining library binds its own references
/// or the static link gives a library's function no canonical address:
/// `linux_native::imported_static_dso_local_declarations_run_like_llc`),
/// and refused under `pie` and `pic`, for an x86-64 or Mach-O target, for
/// no known target, and with no model known (above). Under a known `pic` a
/// referenced `dso_local` definition is refused too; with no model known it
/// stays admitted, and its `pic` form is the GOT (below). A declaration an
/// `available_externally` body addresses is refused where the backend may
/// splice the body and the definition it copies may be in a shared library
/// (a default body under `static` and `pie`, a hidden or protected one
/// under `pic`, every body with no model known; for x86-64 and Mach-O every
/// body the backend may splice). A stub's 16-bit global index is read
/// whole (a declaration after 300 globals).
#[test]
fn dso_local_declarations_whose_address_code_takes_are_refused_by_name() {
    let data_declarations = [
        (
            "global declaration",
            "@s = external dso_local global i64, align 8\n",
        ),
        (
            "global declaration",
            "@s = external dso_local default local_unnamed_addr global i64, align 8\n",
        ),
        (
            "`available_externally` global",
            "@s = available_externally dso_local global i64 7, align 8\n",
        ),
    ];
    let data_uses = [
        "define i64 @u() {\n  %v = load i64, ptr @s, align 8\n  ret i64 %v\n}\n",
        "define void @u() {\n  store i64 1, ptr @s, align 8\n  ret void\n}\n",
        "define ptr @u() {\n  ret ptr @s\n}\n",
        "define ptr @u() {\n  ret ptr getelementptr inbounds (i8, ptr @s, i64 4)\n}\n",
    ];
    let function_declarations = [
        ("function declaration", "declare dso_local i64 @s()\n"),
        (
            "function declaration",
            "declare dso_local default i64 @s()\n",
        ),
        (
            "`available_externally` function",
            "define available_externally dso_local i64 @s() {\n  ret i64 1\n}\n",
        ),
    ];
    let function_uses = [
        "define ptr @u() {\n  ret ptr @s\n}\n",
        "define void @u(ptr %p) {\n  store ptr @s, ptr %p, align 8\n  ret void\n}\n",
        "declare void @take(ptr)\ndefine void @u() {\n  call void @take(ptr @s)\n  ret void\n}\n",
    ];
    let refused =
        data_declarations
            .iter()
            .flat_map(|declaration| data_uses.iter().map(move |usage| (declaration, usage)))
            .chain(function_declarations.iter().flat_map(|declaration| {
                function_uses.iter().map(move |usage| (declaration, usage))
            }));
    let set = |items: &[&'static str]| items.iter().copied().collect::<BTreeSet<_>>();
    for ((what, declaration), usage) in refused {
        let src = format!("{declaration}{usage}");
        let refusal = format!("{what} `@s` is `dso_local` and the module's code takes its address");
        match import_text(&src, "dso_local") {
            Err(trust_cg_llvm_import::Error::Unsupported(reason)) => assert!(
                reason.contains(&refusal) && reason.contains("with no relocation model known"),
                "{src}: {reason}"
            ),
            other => panic!("{src}: expected a named refusal, got {other:?}"),
        }
        for (target, model) in [
            (LINUX, RelocationModel::Pie),
            (LINUX, RelocationModel::Pic),
            (X86_LINUX, RelocationModel::Static),
            (APPLE, RelocationModel::Static),
        ] {
            match import_text_for_compile(&src, "dso_local", target, model) {
                Err(trust_cg_llvm_import::Error::Unsupported(reason)) => assert!(
                    reason.contains(&refusal)
                        && reason
                            .contains(&format!("compiled under the `{model}` relocation model")),
                    "{target} {model}: {src}: {reason}"
                ),
                other => panic!("{target} {model}: {src}: expected a named refusal, got {other:?}"),
            }
        }
        // Admitted for AArch64 ELF under `static`, with the backend's GOT
        // form where llc's is PC-relative.
        let module = import_text_for_compile(&src, "dso_local", LINUX, RelocationModel::Static)
            .unwrap_or_else(|error| panic!("static: {src}: {error}"));
        for opt_level in OPT_LEVELS {
            let object = compile_module(&module, LINUX, opt_level, RelocationModel::Static)
                .unwrap_or_else(|error| panic!("{opt_level:?}: {src}: {error}"));
            let records = read_object_records(&object).expect("ELF records");
            assert_eq!(
                relocation_forms(&records, "s"),
                set(&["GOT"]),
                "{opt_level:?}: {src}"
            );
        }
        // The other spelling of the AArch64 architecture is read alike; a
        // big-endian or ILP32 one is no AArch64 ELF target here.
        import_text_for_compile(
            &src,
            "dso_local",
            "arm64-unknown-linux-gnu",
            RelocationModel::Static,
        )
        .unwrap_or_else(|error| panic!("arm64 static: {src}: {error}"));
        for target in [
            "aarch64_be-unknown-linux-gnu",
            "aarch64_32-unknown-linux-gnu",
        ] {
            assert!(
                matches!(
                    import_text_for_compile(&src, "dso_local", target, RelocationModel::Static),
                    Err(trust_cg_llvm_import::Error::Unsupported(reason)) if reason.contains(&refusal)
                ),
                "{target}: {src}"
            );
        }
    }
    // Under a known `pic` a `dso_local` definition the module references
    // in any way is refused; under `static` and `pie` it is admitted.
    for (src, what) in [
        (
            "@d = dso_local global i64 1, align 8\n\
             define i64 @u() {\n  %v = load i64, ptr @d, align 8\n  ret i64 %v\n}\n",
            "global definition",
        ),
        (
            "@d = weak dso_local global i64 1, align 8\n\
             define i64 @u() {\n  %v = load i64, ptr @d, align 8\n  ret i64 %v\n}\n",
            "global definition",
        ),
        (
            "define dso_local i64 @d() {\n  ret i64 3\n}\n\
             define i64 @u() {\n  %v = call i64 @d()\n  ret i64 %v\n}\n",
            "function definition",
        ),
        (
            "define dso_local i64 @d() {\n  ret i64 3\n}\n\
             define ptr @u() {\n  ret ptr @d\n}\n",
            "function definition",
        ),
        (
            "define dso_local i64 @d() {\n  ret i64 3\n}\n\
             @t = global [1 x ptr] [ptr @d], align 8\n",
            "function definition",
        ),
    ] {
        match import_text_for_compile(src, "dso_local", LINUX, RelocationModel::Pic) {
            Err(trust_cg_llvm_import::Error::Unsupported(reason)) => assert!(
                reason.contains(&format!(
                    "{what} `@d` is `dso_local` and the module references it, compiled under \
                     the `pic` relocation model"
                )),
                "{src}: {reason}"
            ),
            other => panic!("pic: {src}: expected a named refusal, got {other:?}"),
        }
        for model in [RelocationModel::Static, RelocationModel::Pie] {
            import_text_for_compile(src, "dso_local", LINUX, model)
                .unwrap_or_else(|error| panic!("{model}: {src}: {error}"));
        }
    }
    // A reference from an `available_externally` body the backend splices
    // under `pic` (a hidden one) counts for the definitions rule; a default
    // body, withheld under `pic`, does not.
    let spliced_call = |visibility: &str| {
        format!(
            "define dso_local i64 @d() {{\n  ret i64 3\n}}\n\
             define available_externally {visibility}i64 @u() {{\n  %v = call i64 @d()\n\
             \x20 ret i64 %v\n}}\n\
             define i64 @w() {{\n  %r = call i64 @u()\n  ret i64 %r\n}}\n"
        )
    };
    match import_text_for_compile(
        &spliced_call("hidden "),
        "dso_local",
        LINUX,
        RelocationModel::Pic,
    ) {
        Err(trust_cg_llvm_import::Error::Unsupported(reason)) => assert!(
            reason.contains(
                "function definition `@d` is `dso_local` and the module references it, compiled \
                 under the `pic` relocation model"
            ),
            "{reason}"
        ),
        other => panic!("a spliced hidden body under pic: expected a named refusal, got {other:?}"),
    }
    import_text_for_compile(&spliced_call(""), "dso_local", LINUX, RelocationModel::Pic)
        .expect("a default body, withheld under pic");
    // Local `dso_local` definitions (`internal`, `private`) bind inside the
    // object in both: admitted under `pic`, referenced every way.
    import_text_for_compile(
        "@d = internal dso_local global i64 1, align 8\n\
         @e = private dso_local global i64 2, align 8\n\
         define internal dso_local i64 @f() {\n  ret i64 3\n}\n\
         define private dso_local i64 @g() {\n  ret i64 4\n}\n\
         @t = global [2 x ptr] [ptr @f, ptr @d], align 8\n\
         define i64 @u() {\n  %a = load i64, ptr @d, align 8\n  %b = load i64, ptr @e, align 8\n\
         \x20 %c = call i64 @f()\n  %h = call i64 @g()\n  %s = add i64 %a, %b\n\
         \x20 %t = add i64 %s, %c\n  %v = add i64 %t, %h\n  ret i64 %v\n}\n\
         define ptr @w() {\n  ret ptr @f\n}\n",
        "dso_local",
        LINUX,
        RelocationModel::Pic,
    )
    .expect("local dso_local definitions under pic");
    // The fourth verifier round's `available_externally` module: `@u`'s
    // body reads `@s`; llc's object only calls `@u`. The backend splices the
    // body into `@w` at O1-O3 wherever it does not withhold it (every body
    // under `static` and `pie`, a hidden or protected one under `pic`), and
    // the spliced code reads `s` through the GOT, where the definition `@u`
    // copies, compiled by llc from the same text, addresses `s` PC-relative:
    // in a shared library linked by gold (GNU ld and LLD refuse it there)
    // that binds `s` inside the library, and an `LD_PRELOAD` interposer took
    // the splice's read (1005) and not the definition's (12) at O1-O3, for a
    // default `@u` under `static` and `pie` (its definition may be in a
    // library) and a hidden or protected one under `pic` (its definition is
    // in the library being linked; the sixth and seventh rounds). So the
    // declaration is refused by name there and with no model known. A
    // hidden or protected `@u` under `static` and `pie` is defined in the
    // executable (llc's program does not link otherwise), where both
    // programs read one `s`: admitted for AArch64 ELF, with objects
    // byte-identical to the twin's without `dso_local`, and refused for
    // x86-64 and Mach-O (not measured). A default `@u` under `pic` is never
    // spliced (no relocation names `s`) and stays admitted; the twin without
    // `dso_local` is admitted everywhere, and its body is spliced under
    // `static` and `pie` (the GOT form at O1-O3).
    let inline_only = |visibility: &str, dso_local: &str| {
        format!(
            "@s = external {dso_local}global i64, align 8\n\
             define available_externally {visibility}i64 @u() {{\n\
             \x20 %v = load i64, ptr @s, align 8\n  ret i64 %v\n}}\n\
             define i64 @w() {{\n  %r = call i64 @u()\n  ret i64 %r\n}}\n"
        )
    };
    let withheld = import_text_for_compile(
        &inline_only("", "dso_local "),
        "ae",
        LINUX,
        RelocationModel::Pic,
    )
    .expect("a default available_externally body under pic");
    for opt_level in OPT_LEVELS {
        let object = compile_module(&withheld, LINUX, opt_level, RelocationModel::Pic)
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        let records = read_object_records(&object).expect("ELF records");
        assert_eq!(relocation_forms(&records, "s"), set(&[]), "{opt_level:?}");
    }
    let spliced_refusal = "global declaration `@s` is `dso_local` and the \
                           `available_externally` body of `@u` takes its address";
    for visibility in ["", "hidden ", "protected "] {
        let src = inline_only(visibility, "dso_local ");
        match import_text(&src, "ae") {
            Err(trust_cg_llvm_import::Error::Unsupported(reason)) => assert!(
                reason.contains(spliced_refusal)
                    && reason.contains("with no relocation model known"),
                "{visibility}no model: {reason}"
            ),
            other => panic!("{visibility}no model: expected a named refusal, got {other:?}"),
        }
        for target in [LINUX, X86_LINUX, APPLE] {
            for model in MODELS {
                let label = format!("{visibility}{target} {model}");
                let result = import_text_for_compile(&src, "ae", target, model);
                let admitted = if visibility.is_empty() {
                    model == RelocationModel::Pic
                } else {
                    target == LINUX && model != RelocationModel::Pic
                };
                if admitted {
                    let module = result.unwrap_or_else(|error| panic!("{label}: {error}"));
                    if target != LINUX {
                        continue;
                    }
                    let twin =
                        import_text_for_compile(&inline_only(visibility, ""), "ae", LINUX, model)
                            .unwrap_or_else(|error| panic!("{label} without dso_local: {error}"));
                    for opt_level in OPT_LEVELS {
                        let object = compile_module(&module, LINUX, opt_level, model)
                            .unwrap_or_else(|error| panic!("{label} {opt_level:?}: {error}"));
                        assert_eq!(
                            object,
                            compile_module(&twin, LINUX, opt_level, model)
                                .unwrap_or_else(|error| panic!("{label} {opt_level:?}: {error}")),
                            "{label} {opt_level:?}: the object of the twin without dso_local"
                        );
                    }
                    continue;
                }
                match result {
                    Err(trust_cg_llvm_import::Error::Unsupported(reason)) => assert!(
                        reason.contains(spliced_refusal)
                            && reason.contains(&format!(
                                "compiled under the `{model}` relocation model"
                            )),
                        "{label}: {reason}"
                    ),
                    other => panic!("{label}: expected a named refusal, got {other:?}"),
                }
            }
        }
        for model in [RelocationModel::Static, RelocationModel::Pie] {
            let label = format!("{visibility}{model} without dso_local");
            let twin = import_text_for_compile(&inline_only(visibility, ""), "ae", LINUX, model)
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            for opt_level in OPT_LEVELS {
                let object = compile_module(&twin, LINUX, opt_level, model)
                    .unwrap_or_else(|error| panic!("{label} {opt_level:?}: {error}"));
                let spliced = opt_level != OptLevel::O0;
                assert_eq!(
                    relocation_forms(&read_object_records(&object).expect("records"), "s"),
                    if spliced { set(&["GOT"]) } else { set(&[]) },
                    "{label} {opt_level:?}: the body is spliced at O1-O3"
                );
            }
        }
    }
    // A stub's global index is read from all 16 bits of its field: a
    // `dso_local` declaration after 300 definitions, addressed, is refused
    // by its own name under `pie` (the fifth verifier round's mutant, which
    // read 8 bits, took it for global 44, a definition, and admitted it).
    let many: String = (0..300)
        .map(|index| format!("@d{index} = global i64 {index}, align 8\n"))
        .chain(std::iter::once(
            "@late = external dso_local global i64, align 8\n\
             define i64 @u() {\n  %v = load i64, ptr @late, align 8\n  ret i64 %v\n}\n"
                .to_string(),
        ))
        .collect();
    match import_text_for_compile(&many, "many", LINUX, RelocationModel::Pie) {
        Err(trust_cg_llvm_import::Error::Unsupported(reason)) => assert!(
            reason.contains(
                "global declaration `@late` is `dso_local` and the module's code takes its \
                 address, compiled under the `pie` relocation model"
            ),
            "{reason}"
        ),
        other => panic!("300 globals: expected a named refusal, got {other:?}"),
    }
    // `static` admits the declaration only for a known AArch64 ELF target:
    // with no compile triple and none in the module it is refused, and the
    // module's own AArch64 Linux triple is read in place of an empty one.
    let declaration = "@s = external dso_local global i64, align 8\n\
                       define i64 @u() {\n  %v = load i64, ptr @s, align 8\n  ret i64 %v\n}\n";
    match import_text_for_compile(declaration, "untargeted", "", RelocationModel::Static) {
        Err(trust_cg_llvm_import::Error::Unsupported(reason)) => assert!(
            reason.contains(
                "global declaration `@s` is `dso_local` and the module's code takes its \
                 address, compiled under the `static` relocation model"
            ),
            "{reason}"
        ),
        other => panic!("no target: expected a named refusal, got {other:?}"),
    }
    import_text_for_compile(
        &format!("target triple = \"{LINUX}\"\n{declaration}"),
        "module-triple",
        "",
        RelocationModel::Static,
    )
    .expect("the module's AArch64 Linux triple under static");
    let admitted = "@sd = external dso_local global i64, align 8\n\
                    @sa = available_externally dso_local global i64 7, align 8\n\
                    @su = external dso_local global i64, align 8\n\
                    @sw = extern_weak dso_local global i64, align 8\n\
                    @sh = external dso_local hidden global i64, align 8\n\
                    @sp = external dso_local protected global i64, align 8\n\
                    @sq = external dso_preemptable global i64, align 8\n\
                    @d = dso_local global i64 12, align 8\n\
                    @dw = weak dso_local global i64 3, align 8\n\
                    @table = global [2 x ptr] [ptr @sd, ptr @fd], align 8\n\
                    declare dso_local i64 @fd()\n\
                    declare dso_local i64 @fu()\n\
                    declare extern_weak dso_local i64 @fw()\n\
                    declare dso_local hidden i64 @fh()\n\
                    define available_externally dso_local i64 @fa() {\n  ret i64 4\n}\n\
                    define dso_local i64 @df() {\n  ret i64 5\n}\n\
                    define i64 @calls() {\n\
                    \x20 %a = call i64 @fd()\n\
                    \x20 %b = call i64 @fa()\n\
                    \x20 %s = add i64 %a, %b\n\
                    \x20 ret i64 %s\n\
                    }\n\
                    define i64 @reads() {\n\
                    \x20 %w = load volatile i64, ptr @sw, align 8\n\
                    \x20 %h = load volatile i64, ptr @sh, align 8\n\
                    \x20 %p = load volatile i64, ptr @sp, align 8\n\
                    \x20 %q = load volatile i64, ptr @sq, align 8\n\
                    \x20 %d = load volatile i64, ptr @d, align 8\n\
                    \x20 %v = load volatile i64, ptr @dw, align 8\n\
                    \x20 %s1 = add i64 %w, %h\n\
                    \x20 %s2 = add i64 %s1, %p\n\
                    \x20 %s3 = add i64 %s2, %d\n\
                    \x20 %s4 = add i64 %s3, %v\n\
                    \x20 %s5 = add i64 %s4, %q\n\
                    \x20 ret i64 %s5\n\
                    }\n\
                    define ptr @weak_address() {\n  ret ptr @fw\n}\n\
                    define ptr @hidden_address() {\n  ret ptr @fh\n}\n\
                    define ptr @definition_address() {\n  ret ptr @df\n}\n";
    let untargeted =
        import_text(admitted, "dso_local").expect("the admitted dso_local forms import");
    // The objects below compile the module imported for their target, with no
    // model known: it declares functions (FFI boundaries), so it must state
    // its target (`TargetInfoRequired`). Naming the target changes nothing
    // else the importer reads here.
    let module = import_text_for_target(admitted, "dso_local", LINUX)
        .expect("the admitted dso_local forms import for the compile target");
    assert_eq!(
        (&module.globals, &module.functions),
        (&untargeted.globals, &untargeted.functions)
    );
    // Under a known `pic` its referenced `dso_local` definitions are refused
    // (`@d`, `@dw` and `@df` are read or addressed; `@d` is named first);
    // under `static` and `pie` they are admitted, as with no model known.
    match import_text_for_compile(admitted, "dso_local", LINUX, RelocationModel::Pic) {
        Err(trust_cg_llvm_import::Error::Unsupported(reason)) => assert!(
            reason.contains(
                "global definition `@d` is `dso_local` and the module references it, compiled \
                 under the `pic` relocation model"
            ),
            "{reason}"
        ),
        other => panic!("pic: expected a named refusal, got {other:?}"),
    }
    for model in [RelocationModel::Static, RelocationModel::Pie] {
        let known = import_text_for_compile(admitted, "dso_local", LINUX, model)
            .unwrap_or_else(|error| panic!("{model}: {error}"));
        assert_eq!(known.globals, module.globals, "{model}");
    }
    for opt_level in OPT_LEVELS {
        for model in MODELS {
            let label = format!("{opt_level:?} {model}");
            let object = compile_module(&module, LINUX, opt_level, model)
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            let records = read_object_records(&object).expect("ELF records");
            let forms = |name: &str| relocation_forms(&records, name);
            assert_eq!(forms("fd"), set(&["ABS64", "CALL"]), "{label}: `fd`");
            assert_eq!(forms("sd"), set(&["ABS64"]), "{label}: `sd`");
            assert!(
                [set(&["CALL"]), set(&[])].contains(&forms("fa")),
                "{label}: `fa` is called or inlined: {:?}",
                forms("fa")
            );
            for name in ["sw", "sh", "sp", "sq", "fw", "fh"] {
                assert_eq!(forms(name), set(&["GOT"]), "{label}: `{name}`");
            }
            let definition = if model == RelocationModel::Pic {
                set(&["GOT"])
            } else {
                set(&["PC"])
            };
            for name in ["d", "dw", "df"] {
                assert_eq!(forms(name), definition, "{label}: `{name}`");
            }
            let symbols = elf_symbols(&records);
            for name in ["sa", "su", "fu"] {
                assert!(
                    !symbols.contains_key(name),
                    "{label}: nothing addresses `{name}`, and llc writes no symbol for it"
                );
            }
        }
    }
}

/// An `unnamed_addr` constant in an explicit section is refused by name
/// exactly where LLVM 22 gives it a mergeable section kind
/// (`getKindForGlobal`): no relocation, and a null-terminated array of
/// `i8`, `i16` or `i32` or 4, 8, 16 or 32 bytes. llc writes that member's
/// section `SHF_MERGE` with an entry size, apart from the section's members
/// of other kinds (one section per flags and entry size), and linkers fold
/// equal entries, so a `__start_`/`__stop_` walk of the importer's one
/// unmergeable section read other members, in another order, than llc's
/// (two equal entries and a third: 3 walked against llc's 2 under GNU ld,
/// gold and LLD). The rest are admitted as before: a shape LLVM does not
/// merge, `local_unnamed_addr`, no `unnamed_addr`, a mutable global, and a
/// zero constant in a `.bss` name, whose kind LLVM takes from the name.
#[test]
fn mergeable_unnamed_addr_constants_in_named_sections_are_refused_by_name() {
    const MERGEABLE: [&str; 17] = [
        "i32 7",
        "i64 7",
        "i128 7",
        "float 1.0",
        "double 1.0",
        "ptr null",
        "[3 x i8] c\"ab\\00\"",
        "[4 x i8] c\"abcd\"",
        "[1 x i8] zeroinitializer",
        "[8 x i8] zeroinitializer",
        "[3 x i16] [i16 1, i16 2, i16 0]",
        "[4 x i16] [i16 1, i16 2, i16 3, i16 4]",
        "[3 x i32] [i32 1, i32 2, i32 0]",
        "[2 x i64] [i64 1, i64 2]",
        "[4 x i64] [i64 1, i64 2, i64 3, i64 4]",
        "[4 x double] [double 1.0, double 2.0, double 3.0, double 4.0]",
        "[2 x ptr] [ptr null, ptr null]",
    ];
    const UNMERGEABLE: [&str; 9] = [
        "i8 7",
        "i16 7",
        "[5 x i8] c\"abcde\"",
        "[6 x i8] c\"ab\\00cde\"",
        "[2 x i8] zeroinitializer",
        "[3 x i16] [i16 1, i16 2, i16 3]",
        "[3 x i32] [i32 1, i32 2, i32 3]",
        "[3 x i64] [i64 1, i64 2, i64 3]",
        "[2 x ptr] [ptr @other, ptr null]",
    ];
    let module = |prefix: &str, init: &str, section: &str| {
        format!(
            "@other = global i64 1\n\
             @g = {prefix} {init}, section \"{section}\", align 8\n\
             define ptr @anchor() {{\n  ret ptr @g\n}}\n"
        )
    };
    for section in ["tcgm", ".rodata.tcg", ".data.tcg"] {
        for prefix in ["internal unnamed_addr constant", "unnamed_addr constant"] {
            for init in MERGEABLE {
                let label = format!("{prefix} {init} in {section}");
                match import_text(&module(prefix, init, section), "mergeable") {
                    Err(trust_cg_llvm_import::Error::Unsupported(reason)) => assert!(
                        reason
                            .contains(&format!("`unnamed_addr` constant in section \"{section}\""))
                            && reason.contains("SHF_MERGE"),
                        "{label}: {reason}"
                    ),
                    other => panic!("{label}: expected a named refusal, got {other:?}"),
                }
            }
            for init in UNMERGEABLE {
                // A relocated constant in a `.rodata` name is the backend's
                // own refusal (`[TCG-SECTION-READONLY]`).
                if section == ".rodata.tcg" && init.contains('@') {
                    continue;
                }
                let label = format!("{prefix} {init} in {section}");
                compile(
                    &module(prefix, init, section),
                    LINUX,
                    OptLevel::O0,
                    RelocationModel::Pie,
                )
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            }
        }
        for prefix in [
            "internal local_unnamed_addr constant",
            "internal constant",
            "internal unnamed_addr global",
        ] {
            for init in MERGEABLE {
                let label = format!("{prefix} {init} in {section}");
                if section == ".rodata.tcg" && prefix.ends_with("global") {
                    continue;
                }
                compile(
                    &module(prefix, init, section),
                    LINUX,
                    OptLevel::O0,
                    RelocationModel::Pie,
                )
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            }
        }
    }
    for init in [
        "[1 x i8] zeroinitializer",
        "[8 x i8] zeroinitializer",
        "ptr null",
        "[2 x ptr] [ptr null, ptr null]",
    ] {
        let label = format!("{init} in .bss.tcg");
        compile(
            &module("internal unnamed_addr constant", init, ".bss.tcg"),
            LINUX,
            OptLevel::O0,
            RelocationModel::Pie,
        )
        .unwrap_or_else(|error| panic!("{label}: {error}"));
    }
    // Every name LLVM 22 gives a kind of its own (`getELFKindForNamedSection`:
    // metadata, zero fill, thread data), exactly and by prefix, keeps a
    // mergeable constant out of the refusal: llc 22.1.2 writes none of these
    // sections `SHF_MERGE` (measured: `NOBITS WA` for the zero-fill names,
    // `PROGBITS WAT` for `.tdata`, unallocated for the metadata ones). A name
    // that only resembles one is not LLVM's, and llc writes the constant
    // `SHF_MERGE`: refused by name. The third verifier round's mutants that
    // dropped `.sbss`/`.sbss.` or the exact `.bss` from the list passed
    // every test.
    for section in [
        ".bss",
        ".sbss",
        ".tdata",
        ".tbss",
        ".llvmbc",
        ".llvmcmd",
        "__llvm_covmap",
        "__llvm_covfun",
        "__llvm_covdata",
        "__llvm_covnames",
        ".bss.tcg",
        ".gnu.linkonce.b.tcg",
        ".llvm.linkonce.b.tcg",
        ".sbss.tcg",
        ".gnu.linkonce.sb.tcg",
        ".llvm.linkonce.sb.tcg",
        ".tdata.tcg",
        ".gnu.linkonce.td.tcg",
        ".llvm.linkonce.td.tcg",
        ".tbss.tcg",
        ".gnu.linkonce.tb.tcg",
        ".llvm.linkonce.tb.tcg",
    ] {
        let text = module(
            "internal unnamed_addr constant",
            "[1 x i8] zeroinitializer",
            section,
        );
        import_text(&text, "named_kind")
            .unwrap_or_else(|error| panic!("a constant in {section}: {error}"));
    }
    for section in [
        ".bssx",
        ".sbssx",
        ".tdatax",
        ".tbssx",
        ".llvmbcx",
        ".llvmcmdx",
        "__llvm_covmapx",
        ".bsss",
        ".gnu.linkonce.bx",
        ".llvm.linkonce.tbx",
        "x.bss",
    ] {
        let text = module(
            "internal unnamed_addr constant",
            "[1 x i8] zeroinitializer",
            section,
        );
        match import_text(&text, "near_name") {
            Err(trust_cg_llvm_import::Error::Unsupported(reason)) => assert!(
                reason.contains(&format!("`unnamed_addr` constant in section \"{section}\""))
                    && reason.contains("SHF_MERGE"),
                "{section}: {reason}"
            ),
            other => panic!("{section}: expected a named refusal, got {other:?}"),
        }
    }
    // The audit's walk: two equal entries and a third in one named section.
    let walk = "@c1 = internal unnamed_addr constant i64 5, section \"tcgm\", align 8\n\
                @c2 = internal unnamed_addr constant i64 5, section \"tcgm\", align 8\n\
                @c3 = internal unnamed_addr constant i64 9, section \"tcgm\", align 8\n\
                define i64 @touch() {\n\
                \x20 %x = load i64, ptr @c1, align 8\n\
                \x20 ret i64 %x\n\
                }\n";
    match import_text(walk, "walk") {
        Err(trust_cg_llvm_import::Error::Unsupported(reason)) => assert!(
            reason.contains("global `@c1`") && reason.contains("\"tcgm\""),
            "{reason}"
        ),
        other => panic!("expected a named refusal, got {other:?}"),
    }
}

/// The four coverage-mapping section names LLVM 22 makes non-allocated
/// metadata by name are refused by name for a global of every kind and for
/// a function, where the backend used to load them (llc leaves them
/// unloaded, so a program reading one through its symbol read garbage or
/// faulted with llc and ran with the import). A coverage name LLVM does not
/// classify keeps its placement.
#[test]
fn coverage_mapping_section_names_are_refused_by_name() {
    for name in [
        "__llvm_covmap",
        "__llvm_covfun",
        "__llvm_covdata",
        "__llvm_covnames",
    ] {
        let anchor = "define i32 @anchor() {\n  ret i32 0\n}\n";
        for src in [
            format!("@m = constant [4 x i8] c\"abcd\", section \"{name}\", align 1\n{anchor}"),
            format!("@m = global i64 5, section \"{name}\", align 8\n{anchor}"),
            format!("@m = global i64 0, section \"{name}\", align 8\n{anchor}"),
            format!("define i32 @f() section \"{name}\" {{\n  ret i32 1\n}}\n"),
        ] {
            for opt_level in [OptLevel::O0, OptLevel::O2] {
                let error = compile(&src, LINUX, opt_level, RelocationModel::Pie)
                    .expect_err("a coverage-mapping section is refused");
                assert!(
                    error.contains("[TCG-SECTION-RESERVED]")
                        && error.contains("SectionKind::Metadata")
                        && error.contains(name),
                    "{opt_level:?} {src}: {error}"
                );
            }
        }
    }
    let object = compile(
        "@m = constant [4 x i8] c\"abcd\", section \"__llvm_covinit\", align 1\n\
         define i32 @anchor() {\n  ret i32 0\n}\n",
        LINUX,
        OptLevel::O0,
        RelocationModel::Pie,
    )
    .expect("an unclassified coverage name keeps its placement");
    let records = read_object_records(&object).expect("ELF records");
    let section = records
        .sections
        .iter()
        .find(|section| section.name == "__llvm_covinit")
        .expect("__llvm_covinit");
    assert_eq!(section.sh_flags, 2 /* SHF_ALLOC */);
}

/// Named sections whose members are COMDAT, `@llvm.used` and ordinary
/// definitions interleaved, and a constructor table of COMDAT and ordinary
/// entries. llc 22 emits the globals in module order and creates each
/// section at the first global it holds: a COMDAT or used definition's own
/// section where it is declared, a shared one at its first ordinary member.
/// The linker concatenates same-named input sections in that order, so it
/// decides a `__start_`/`__stop_` walk and the constructors' run order.
const ORDER_MODULE: &str = r#"
$k1 = comdat any
$k2 = comdat any
$k3 = comdat any
$km = comdat any
$kr = comdat any
$ca = comdat any
$cd = comdat any

@state = global i64 0, align 8
@k1 = linkonce_odr global i64 4, section "tcga", comdat, align 8
@p = global i64 1, section "tcga", align 8
@k2 = weak_odr global i64 6, section "tcgb", comdat, align 8
@q = global i64 2, section "tcgb", align 8
@k3 = linkonce_odr global i64 5, section "tcga", comdat, align 8
@r = internal global i64 3, section "tcgb", align 8
@u = internal global i64 3, section "tcgmix", align 8
@km = linkonce_odr global i64 7, section "tcgmix", comdat, align 8
@m = global i64 1, section "tcgmix", align 8
@kr = linkonce_odr global i64 8, section "tcgmix", comdat, align 8
@ca = linkonce_odr constant [1 x ptr] [ptr @ctor_a], section ".init_array", comdat, align 8
@cb = internal constant [1 x ptr] [ptr @ctor_b], section ".init_array", align 8
@cd = linkonce_odr constant [1 x ptr] [ptr @ctor_d], section ".init_array", comdat, align 8
@cc = internal constant [1 x ptr] [ptr @ctor_c], section ".init_array", align 8
@llvm.used = appending global [2 x ptr] [ptr @u, ptr @kr], section "llvm.metadata"

define internal void @ctor_a() {
  %v = load i64, ptr @state, align 8
  %m = mul i64 %v, 10
  %s = add i64 %m, 1
  store i64 %s, ptr @state, align 8
  ret void
}

define internal void @ctor_b() {
  %v = load i64, ptr @state, align 8
  %m = mul i64 %v, 10
  %s = add i64 %m, 2
  store i64 %s, ptr @state, align 8
  ret void
}

define internal void @ctor_c() {
  %v = load i64, ptr @state, align 8
  %m = mul i64 %v, 10
  %s = add i64 %m, 3
  store i64 %s, ptr @state, align 8
  ret void
}

define internal void @ctor_d() {
  %v = load i64, ptr @state, align 8
  %m = mul i64 %v, 10
  %s = add i64 %m, 4
  store i64 %s, ptr @state, align 8
  ret void
}

define i64 @read_state() {
  %v = load i64, ptr @state, align 8
  ret i64 %v
}

define i64 @touch() {
  %a = load i64, ptr @k1, align 8
  %b = load i64, ptr @p, align 8
  %c = load i64, ptr @k2, align 8
  %d = load i64, ptr @q, align 8
  %e = load i64, ptr @k3, align 8
  %f = load i64, ptr @r, align 8
  %g = load i64, ptr @km, align 8
  %h = load i64, ptr @m, align 8
  %i = load i64, ptr @kr, align 8
  %s1 = add i64 %a, %b
  %s2 = add i64 %s1, %c
  %s3 = add i64 %s2, %d
  %s4 = add i64 %s3, %e
  %s5 = add i64 %s4, %f
  %s6 = add i64 %s5, %g
  %s7 = add i64 %s6, %h
  %s8 = add i64 %s7, %i
  ret i64 %s8
}
"#;

/// `SHF_GROUP`.
const SHF_GROUP: u64 = 0x200;

/// One input section of a named section, in section-header order:
/// `(in a group, SHF_GNU_RETAIN, the data symbols it defines by offset)`.
type PlacedSection = (bool, bool, Vec<String>);

/// The sections named `name` in section-header order (the order the linker
/// concatenates them in), each with its group and retention flags and the
/// data symbols it defines, by offset.
fn placed_sections(records: &ElfObjectRecords, name: &str) -> Vec<PlacedSection> {
    records
        .sections
        .iter()
        .enumerate()
        .filter(|(_, section)| section.name == name)
        .map(|(index, section)| {
            let mut members: Vec<(u64, String)> = records
                .symbols
                .iter()
                .filter(|symbol| {
                    usize::from(symbol.section_index) == index
                        && symbol.symbol_type == 1 /* STT_OBJECT */
                })
                .map(|symbol| (symbol.value, symbol.name.clone()))
                .collect();
            members.sort();
            (
                section.sh_flags & SHF_GROUP != 0,
                section.sh_flags & SHF_GNU_RETAIN != 0,
                members.into_iter().map(|(_, name)| name).collect(),
            )
        })
        .collect()
}

/// [`ORDER_MODULE`]'s named sections as llc 22.1.2 creates them.
fn expected_placed_order() -> Vec<(&'static str, Vec<PlacedSection>)> {
    let section = |grouped: bool, retained: bool, members: &[&str]| -> PlacedSection {
        (
            grouped,
            retained,
            members.iter().map(|member| member.to_string()).collect(),
        )
    };
    vec![
        (
            "tcga",
            vec![
                section(true, false, &["k1"]),
                section(false, false, &["p"]),
                section(true, false, &["k3"]),
            ],
        ),
        (
            "tcgb",
            vec![
                section(true, false, &["k2"]),
                section(false, false, &["q", "r"]),
            ],
        ),
        (
            "tcgmix",
            vec![
                section(false, true, &["u"]),
                section(true, false, &["km"]),
                section(false, false, &["m"]),
                section(true, true, &["kr"]),
            ],
        ),
        (
            ".init_array",
            vec![
                section(true, false, &["ca"]),
                section(false, false, &["cb", "cc"]),
                section(true, false, &["cd"]),
            ],
        ),
    ]
}

/// The named sections of explicit-section, COMDAT and `@llvm.used`
/// definitions are emitted in llc's creation order, at every level and
/// model: a COMDAT or used definition's own section where it is declared,
/// a shared one where its first ordinary member is. Before, every COMDAT
/// section came after all the others, so a COMDAT member declared first was
/// walked last and its constructor ran after the ordinary ones (the native
/// row below runs both against llc).
#[test]
fn placed_sections_are_emitted_in_llc_s_creation_order() {
    for opt_level in OPT_LEVELS {
        for model in MODELS {
            let label = format!("{opt_level:?} {model}");
            let object = compile(ORDER_MODULE, LINUX, opt_level, model)
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            let records = read_object_records(&object).expect("ELF records");
            for (name, expected) in expected_placed_order() {
                assert_eq!(
                    placed_sections(&records, name),
                    expected,
                    "{label}: the sections named `{name}`"
                );
            }
        }
    }
}

/// `@llvm.used` globals of every x86-64 ELF kind beside unlisted ones of
/// the same kind; the unlisted internal one holds a pointer to a function
/// no object defines. The used relocated constant points at a used global,
/// so it keeps no unlisted section alive.
const X86_RETENTION_MODULE: &str = r#"
@ud = global i64 11, align 8
@ud2 = global i64 17, align 8
@md = hidden global i64 12, align 8
@ur = constant i64 13, align 8
@mr = hidden constant i64 14, align 8
@urel = constant [1 x ptr] [ptr @ur], align 8
@mrel = hidden constant [1 x ptr] [ptr @mr], align 8
@ui = internal global i64 15, align 8
@mi = internal global [1 x ptr] [ptr @tcg_missing], align 8
@llvm.used = appending global [5 x ptr] [ptr @ud, ptr @ud2, ptr @ur, ptr @urel, ptr @ui], section "llvm.metadata"

declare void @tcg_missing()

define i64 @anchor() {
  ret i64 0
}
"#;

const X86_LINUX: &str = "x86_64-unknown-linux-gnu";

/// The x86-64 ELF emitter retains each `@llvm.used` global alone, as the
/// AArch64 ones do: its own `<kind>.<symbol>` section (`.data.ud`,
/// `.rodata.ur`, `.data.rel.ro.urel`; this emitter has no `.bss`) flagged
/// `SHF_GNU_RETAIN`, and no shared section is retained (the native row
/// below links it with LLD `--gc-sections` against llc). x86-64 implements
/// only the `static` model. The lib unit test of the emitter checks the
/// same rule; this row keeps it on the floor.
#[test]
fn x86_64_used_globals_are_retained_alone_in_their_own_sections() {
    for opt_level in OPT_LEVELS {
        let label = format!("{opt_level:?}");
        let object = compile(
            X86_RETENTION_MODULE,
            X86_LINUX,
            opt_level,
            RelocationModel::Static,
        )
        .unwrap_or_else(|error| panic!("{label}: {error}"));
        let records = read_object_records(&object).expect("ELF records");
        assert_eq!(records.machine, 62 /* EM_X86_64 */, "{label}");
        let section_of = |name: &str| {
            records
                .symbols
                .iter()
                .find(|symbol| symbol.name == name && symbol.section_index != 0)
                .map(|symbol| usize::from(symbol.section_index))
        };
        for (name, section) in [
            ("ud", ".data.ud"),
            ("ud2", ".data.ud2"),
            ("ur", ".rodata.ur"),
            ("urel", ".data.rel.ro.urel"),
            ("ui", ".data.ui"),
        ] {
            let index = section_of(name).unwrap_or_else(|| panic!("{label}: `{name}` is defined"));
            let header = &records.sections[index];
            assert_eq!(header.name, section, "{label}: `{name}`'s own section");
            assert_ne!(
                header.sh_flags & SHF_GNU_RETAIN,
                0,
                "{label}: `{name}`'s section is retained"
            );
            let members: Vec<&str> = records
                .symbols
                .iter()
                .filter(|symbol| usize::from(symbol.section_index) == index)
                .filter(|symbol| symbol.symbol_type == 1 /* STT_OBJECT */)
                .map(|symbol| symbol.name.as_str())
                .collect();
            assert_eq!(members, [name], "{label}: `{name}` is alone");
        }
        for (name, section) in [
            ("md", ".data"),
            ("mr", ".rodata"),
            ("mrel", ".data.rel.ro"),
            ("mi", ".data"),
        ] {
            let Some(index) = section_of(name) else {
                assert!(
                    name == "mi" && opt_level != OptLevel::O0,
                    "{label}: `{name}` is missing"
                );
                continue;
            };
            let header = &records.sections[index];
            assert_eq!(header.name, section, "{label}: `{name}`'s shared section");
            assert_eq!(
                header.sh_flags & SHF_GNU_RETAIN,
                0,
                "{label}: `{name}`'s shared section is not retained"
            );
        }
        assert!(
            records
                .sections
                .iter()
                .filter(|section| section.sh_flags & SHF_GNU_RETAIN != 0)
                .all(|section| section.name.matches('.').count() >= 2),
            "{label}: only own `<kind>.<symbol>` sections are retained: {:?}",
            records.sections
        );
    }
}

/// Global declarations listed in `@llvm.used`: referenced and unreferenced
/// `external` and `available_externally` ones, a hidden one and an
/// `extern_weak` one.
const USED_DECLARATIONS_MODULE: &str = r#"
@gd = external global i64
@gu = external global i64
@gae = available_externally global i64 5
@gaeu = available_externally global i64 6
@gh = external hidden global i64
@gw = extern_weak global i64
@llvm.used = appending global [6 x ptr] [ptr @gd, ptr @gu, ptr @gae, ptr @gaeu, ptr @gh, ptr @gw], section "llvm.metadata"

define i64 @get() {
  %a = load i64, ptr @gd, align 8
  %b = load i64, ptr @gae, align 8
  %c = load i64, ptr @gh, align 8
  %s = add i64 %a, %b
  %t = add i64 %s, %c
  ret i64 %t
}
"#;

/// [`USED_DECLARATIONS_MODULE`] without the hidden and weak declarations,
/// which the x86-64 and Mach-O emitters refuse for their own reasons.
const USED_PLAIN_DECLARATIONS_MODULE: &str = r#"
@gd = external global i64
@gu = external global i64
@gae = available_externally global i64 5
@gaeu = available_externally global i64 6
@llvm.used = appending global [4 x ptr] [ptr @gd, ptr @gu, ptr @gae, ptr @gaeu], section "llvm.metadata"

define i64 @get() {
  %a = load i64, ptr @gd, align 8
  %b = load i64, ptr @gae, align 8
  %s = add i64 %a, %b
  ret i64 %s
}
"#;

/// A declaration listed in `@llvm.used` is marked retained by the importer,
/// as LLVM lists it, and each object path decides it as llc 22.1.2 writes
/// it. llc's ELF writer writes nothing for the listing (measured: `U gd`,
/// `U gae`, hidden `U gh`, weak `U gw`; no `gu`, no `gaeu`), so the AArch64
/// ELF objects at every level and model and the x86-64 ELF ones carry
/// exactly those rows. llc's Mach-O writer gives every listed declaration an
/// `N_NO_DEAD_STRIP` undefined symbol, referenced or not, which no Mach-O
/// emitter here writes: the AArch64 and x86-64 Mach-O compiles are refused
/// by name, and so is a listed function declaration in a module whose triple
/// names a Mach-O target. Before, every one of these modules was refused
/// ("a cross-object import marked retained") where llc compiles it.
#[test]
fn used_declarations_are_written_as_llc_writes_them() {
    let module = import_text(USED_DECLARATIONS_MODULE, "used_decls").expect("import");
    for name in ["gd", "gu", "gae", "gaeu", "gh", "gw"] {
        assert!(
            module.globals.iter().any(|g| g.name == name && g.retained),
            "`{name}` is marked retained, as LLVM lists it"
        );
    }
    for opt_level in OPT_LEVELS {
        for model in MODELS {
            let label = format!("{opt_level:?} {model}");
            let object = compile_module(&module, LINUX, opt_level, model)
                .unwrap_or_else(|error| panic!("{label}: {error}"));
            let records = read_object_records(&object).expect("ELF records");
            let symbols = elf_symbols(&records);
            for (name, binding, visibility) in [
                ("gd", STB_GLOBAL, STV_DEFAULT),
                ("gae", STB_GLOBAL, STV_DEFAULT),
                ("gh", STB_GLOBAL, STV_HIDDEN),
                ("gw", STB_WEAK, STV_DEFAULT),
            ] {
                assert_eq!(
                    unique_symbol(&symbols, name),
                    Some(&(binding, visibility, "UND".to_string())),
                    "{label}: `{name}`"
                );
            }
            for name in ["gu", "gaeu"] {
                assert!(
                    !symbols.contains_key(name),
                    "{label}: llc writes no `{name}`"
                );
            }
            assert!(
                records
                    .sections
                    .iter()
                    .all(|section| section.sh_flags & SHF_GNU_RETAIN == 0),
                "{label}: a declaration retains no section"
            );
        }
        let label = format!("{opt_level:?} x86-64");
        let object = compile(
            USED_PLAIN_DECLARATIONS_MODULE,
            X86_LINUX,
            opt_level,
            RelocationModel::Static,
        )
        .unwrap_or_else(|error| panic!("{label}: {error}"));
        let records = read_object_records(&object).expect("ELF records");
        let symbols = elf_symbols(&records);
        for name in ["gd", "gae"] {
            assert_eq!(
                unique_symbol(&symbols, name),
                Some(&(STB_GLOBAL, STV_DEFAULT, "UND".to_string())),
                "{label}: `{name}`"
            );
        }
        for name in ["gu", "gaeu"] {
            assert!(
                !symbols.contains_key(name),
                "{label}: llc writes no `{name}`"
            );
        }
        // Each refusal names the form llc's writer for that format gives the
        // listing (measured with llc 22.1.2): Mach-O an `N_NO_DEAD_STRIP`
        // undefined symbol, COFF a `/INCLUDE:` directive in `.drectve`.
        for (triple, needle, llc_form) in [
            (APPLE, "is an import marked retained", "N_NO_DEAD_STRIP"),
            (
                "x86_64-apple-darwin",
                "the import is marked retained",
                "N_NO_DEAD_STRIP",
            ),
            (
                "x86_64-pc-windows-msvc",
                "the import is marked retained",
                "/INCLUDE:gd",
            ),
        ] {
            let error = compile(
                USED_PLAIN_DECLARATIONS_MODULE,
                triple,
                opt_level,
                RelocationModel::Static,
            )
            .expect_err("a non-ELF object path refuses a listed declaration");
            assert!(
                error.contains(needle) && error.contains(llc_form),
                "{opt_level:?} {triple}: {error}"
            );
        }
    }
    // A listed function declaration is admitted only in a module whose own
    // triple names ELF: llc's ELF writer writes nothing for it (no symbol for
    // an unreferenced default one), and the importer does not know the
    // object format a module is compiled for. Mach-O, COFF, Wasm and a
    // module without a triple are refused by name (before the verifier's
    // second round only a Mach-O triple was, and a module without one
    // compiled for Mach-O dropped the listing that llc writes as an
    // `N_NO_DEAD_STRIP` undefined symbol).
    for (function, body) in [
        ("fd", "declare i64 @fd()\n"),
        (
            "fae",
            "define available_externally i64 @fae() {\n  ret i64 1\n}\n",
        ),
    ] {
        let listed = format!(
            "@llvm.used = appending global [1 x ptr] [ptr @{function}], section \
             \"llvm.metadata\"\n{body}define i64 @anchor() {{\n  ret i64 0\n}}\n"
        );
        // The module triple is read as LLVM's `Triple` reads it (split at
        // most three times, the format an environment ending names before
        // the architecture's and OS's default, no normalization): llc
        // 22.1.2 writes an ELF object, and nothing for the listing, for each
        // triple of the first list, and a Mach-O object with an
        // `N_NO_DEAD_STRIP` `_fd` for the `-macho` ones (measured). The
        // third verifier round's mutants dropping the `macho` ending, the
        // Wasm architecture or the `elf` ending passed every floor target.
        for (module_triple, target) in [
            (LINUX, LINUX),
            (X86_LINUX, X86_LINUX),
            ("aarch64-linux-gnu", LINUX),
            ("aarch64-unknown-linux-gnu-elf", LINUX),
            ("aarch64-unknown-none-elf", LINUX),
            ("arm64-apple-macosx14.0.0-elf", LINUX),
            ("x86_64-pc-windows-msvc-elf", X86_LINUX),
        ] {
            let text = format!("target triple = \"{module_triple}\"\n{listed}");
            let object = compile(&text, target, OptLevel::O0, RelocationModel::Static)
                .unwrap_or_else(|error| panic!("{function} {module_triple} on {target}: {error}"));
            let records = read_object_records(&object).expect("ELF records");
            assert!(
                !elf_symbols(&records).contains_key(function),
                "{module_triple} on {target}: llc's ELF writer writes no `{function}`"
            );
        }
        for (module_triple, needle) in [
            (
                Some("arm64-apple-macosx14.0.0"),
                "is listed in `@llvm.used` in a Mach-O module",
            ),
            (
                Some("x86_64-apple-darwin"),
                "is listed in `@llvm.used` in a Mach-O module",
            ),
            (
                Some("aarch64-unknown-linux-macho"),
                "is listed in `@llvm.used` in a Mach-O module",
            ),
            (
                Some("aarch64-unknown-linux-gnu-macho"),
                "is listed in `@llvm.used` in a Mach-O module",
            ),
            // Every other Darwin OS name LLVM reads, and Windows spelled
            // `win32`: llc 22.1.2 wrote a Mach-O object with an
            // `N_NO_DEAD_STRIP` `_fd` for each Apple triple and a COFF one
            // with `/INCLUDE:fd` for each `win32` one (the fourth verifier
            // round's mutants dropping these names from `src/triple.rs`
            // passed every test, and admitted the listing for them).
            (
                Some("arm64-apple-ios17.0.0"),
                "is listed in `@llvm.used` in a Mach-O module",
            ),
            (
                Some("arm64-apple-tvos17.0"),
                "is listed in `@llvm.used` in a Mach-O module",
            ),
            (
                Some("x86_64-apple-tvos17.0"),
                "is listed in `@llvm.used` in a Mach-O module",
            ),
            (
                Some("arm64-apple-watchos10.0"),
                "is listed in `@llvm.used` in a Mach-O module",
            ),
            (
                Some("arm64_32-apple-watchos10.0"),
                "is listed in `@llvm.used` in a Mach-O module",
            ),
            (
                Some("aarch64_32-apple-watchos10.0"),
                "is listed in `@llvm.used` in a Mach-O module",
            ),
            (
                Some("arm64-apple-bridgeos8.0"),
                "is listed in `@llvm.used` in a Mach-O module",
            ),
            (
                Some("arm64-apple-driverkit23.0"),
                "is listed in `@llvm.used` in a Mach-O module",
            ),
            (
                Some("arm64-apple-xros1.0"),
                "is listed in `@llvm.used` in a Mach-O module",
            ),
            (
                Some("arm64-apple-visionos1.0"),
                "is listed in `@llvm.used` in a Mach-O module",
            ),
            (
                Some("x86_64-pc-win32"),
                "names no ELF target (the compile target's object format is COFF)",
            ),
            (
                Some("aarch64-pc-win32"),
                "names no ELF target (the compile target's object format is COFF)",
            ),
            (
                Some("wasm32-unknown-linux"),
                "in a module whose `target triple` names no ELF target",
            ),
            (
                Some(""),
                "in a module whose `target triple` names no ELF target",
            ),
            (
                Some("x86_64-pc-windows-msvc"),
                "in a module whose `target triple` names no ELF target",
            ),
            (
                Some("wasm32-unknown-unknown"),
                "in a module whose `target triple` names no ELF target",
            ),
            (
                Some("x86_64-unknown-linux-coff"),
                "in a module whose `target triple` names no ELF target",
            ),
            (
                None,
                "in a module whose `target triple` names no ELF target",
            ),
        ] {
            let text = match module_triple {
                Some(triple) => format!("target triple = \"{triple}\"\n{listed}"),
                None => listed.clone(),
            };
            match import_text(&text, "listed") {
                Err(trust_cg_llvm_import::Error::Unsupported(reason)) => assert!(
                    reason.contains(&format!("function declaration `@{function}`"))
                        && reason.contains(needle),
                    "{module_triple:?}: {reason}"
                ),
                other => {
                    panic!("{function} {module_triple:?}: expected a named refusal, got {other:?}")
                }
            }
        }
    }
    // The same reading decides the `\01` asm label: read as the Mach-O C
    // name (`@"\01_lab"` is `lab`) only where the triple names the Mach-O
    // format, and refused by name everywhere else, an Apple OS with an
    // `-elf` ending included (llc 22.1.2 writes an ELF object for it).
    let label = "define i64 @\"\\01_lab\"() {\n  ret i64 1\n}\n";
    for (triple, mach_o) in [
        ("arm64-apple-macosx14.0.0", true),
        ("aarch64-unknown-linux-macho", true),
        ("aarch64-unknown-linux-gnu-macho", true),
        ("arm64-apple-macosx14.0.0-elf", false),
        ("aarch64-linux-gnu", false),
        ("wasm32-unknown-linux", false),
    ] {
        let text = format!("target triple = \"{triple}\"\n{label}");
        match (import_text(&text, "label"), mach_o) {
            (Ok(module), true) => assert!(
                module.functions.iter().any(|f| f.name == "lab"),
                "{triple}: the label is the Mach-O C name"
            ),
            (Err(trust_cg_llvm_import::Error::Unsupported(reason)), false) => assert!(
                reason.contains("for a target whose object format is not Mach-O"),
                "{triple}: {reason}"
            ),
            (other, _) => panic!("{triple}: {other:?}"),
        }
    }
}

// =============================================================================
// Integer literals read at their type's width
// =============================================================================

/// Integer literals LLVM reads at their type's width (`APSInt::extOrTrunc`):
/// `i64 18076885954311749632` is the `i64` with bits `0xFADE000000000000`,
/// which lies in the lowering adapter's global-address stub interval
/// `[0xFADE << 48, 0xFADF << 48)` with `@g` as the global at index 0;
/// `i32 4294967295`, `i16 65535` and `i8 255` are -1; an array GEP index
/// `i32 4294967295` is one element back, a struct GEP's outer index one
/// struct back and a constant-expression GEP's index one byte back. The
/// sixth round's shapes (the fifth verifier round's findings): an `i1` GEP
/// index, constant (`1`, `true`) or computed, is sign-extended (one element,
/// struct or byte back); `2^61 - 1` elements of 8 bytes wrap to 8 bytes back;
/// unsigned switch cases, a scalar global's initializer and an `i1` field of
/// an aggregate initializer are read at their width; `i1` literals other than
/// 0 and 1 are their low bit; literals outside their type's two ranges are
/// their low bits; an `alloca` count is zero-extended. The seventh round's
/// (the sixth verifier round's): `i1 false` as a GEP index is no offset; an
/// `alloca` count `i1 true` is one element and `i8 -56` 200; an integer
/// array initializer's literals are their low bits (`i8 300` is 44, `i16
/// 65537` 1); folded GEP offsets past `2^64` wrap as llc folds them (8, 8,
/// 24 and 8 bytes forward; two terms summing below `-2^63`; a constant
/// expression's outer index of `2^60` structs of 16 bytes and its second
/// field, 8 bytes). `main` in the AArch64 Linux driver
/// (`linux_native::INTEGER_LITERALS_DRIVER`) prints what each function
/// computes.
const INTEGER_LITERALS_MODULE: &str = "@g = global i64 42, align 8\n\
declare i64 @h(i64)\n\
define i64 @f_ret() {\n  ret i64 18076885954311749632\n}\n\
define void @f_store(ptr %p) {\n  store i64 18076885954311749632, ptr %p, align 8\n  ret void\n}\n\
define i64 @f_phi(i32 %c) {\n\
entry:\n  %t = icmp ne i32 %c, 0\n  br i1 %t, label %a, label %b\n\
a:\n  br label %b\n\
b:\n  %v = phi i64 [ 18076885954311749632, %a ], [ 3, %entry ]\n  ret i64 %v\n}\n\
define i32 @f_cmp(i64 %x) {\n  %e = icmp eq i64 %x, 18076885954311749632\n\
\x20 %r = zext i1 %e to i32\n  ret i32 %r\n}\n\
define i64 @f_arg() {\n  %r = call i64 @h(i64 18076885954311749632)\n  ret i64 %r\n}\n\
define i64 @f_add(i64 %x) {\n  %r = add i64 %x, 18076885954311749632\n  ret i64 %r\n}\n\
define i32 @r32() {\n  ret i32 4294967295\n}\n\
define i16 @r16() {\n  ret i16 65535\n}\n\
define i8 @r8() {\n  ret i8 255\n}\n\
define ptr @gep_back(ptr %p) {\n\
\x20 %q = getelementptr [4 x i64], ptr %p, i64 0, i32 4294967295\n  ret ptr %q\n}\n\
%S = type { i64, i64 }\n\
@bytes = global [4 x i8] c\"abcd\", align 1\n\
define ptr @gep_struct(ptr %p) {\n\
\x20 %q = getelementptr %S, ptr %p, i32 4294967295, i32 1\n  ret ptr %q\n}\n\
define ptr @gep_const() {\n  ret ptr getelementptr (i8, ptr @bytes, i32 4294967295)\n}\n\
define ptr @bytes_addr() {\n  ret ptr @bytes\n}\n\
%B = type { i1, i8 }\n\
@c64 = constant i64 18076885954311749632, align 8\n\
@c8 = constant i8 255, align 1\n\
@c1 = constant i1 2, align 1\n\
@c1m = constant i1 -1, align 1\n\
@agg = global %B { i1 -1, i8 5 }, align 1\n\
define ptr @i1_gep_arr(ptr %p) {\n\
\x20 %q = getelementptr [4 x i64], ptr %p, i64 0, i1 1\n  ret ptr %q\n}\n\
define ptr @i1_gep_struct(ptr %p) {\n  %q = getelementptr %S, ptr %p, i1 1, i32 1\n  ret ptr %q\n}\n\
define ptr @i1_gep_const() {\n  ret ptr getelementptr (i8, ptr @bytes, i1 1)\n}\n\
define ptr @i1_gep_const_true() {\n  ret ptr getelementptr (i8, ptr @bytes, i1 true)\n}\n\
define ptr @i1_gep_true(ptr %p) {\n  %q = getelementptr i8, ptr %p, i1 true\n  ret ptr %q\n}\n\
define ptr @i1_gep_dyn(ptr %p, i64 %x) {\n  %c = icmp ne i64 %x, 0\n\
\x20 %q = getelementptr [4 x i64], ptr %p, i64 0, i1 %c\n  ret ptr %q\n}\n\
define ptr @i1_gep_struct_dyn(ptr %p, i64 %x) {\n  %c = icmp ne i64 %x, 0\n\
\x20 %q = getelementptr %S, ptr %p, i1 %c, i32 1\n  ret ptr %q\n}\n\
define ptr @gep_wrap(ptr %p) {\n\
\x20 %q = getelementptr [4 x i64], ptr %p, i64 0, i64 2305843009213693951\n  ret ptr %q\n}\n\
define i64 @sw64(i64 %x) {\nentry:\n  switch i64 %x, label %d [\n    i64 18076885954311749632, label %a\n  ]\n\
a:\n  ret i64 1\nd:\n  ret i64 0\n}\n\
define i32 @sw32(i32 %x) {\nentry:\n  switch i32 %x, label %d [\n    i32 4294967295, label %a\n  ]\n\
a:\n  ret i32 1\nd:\n  ret i32 0\n}\n\
define i32 @sw8(i8 %x) {\nentry:\n  switch i8 %x, label %d [\n    i8 255, label %a\n  ]\n\
a:\n  ret i32 1\nd:\n  ret i32 0\n}\n\
define i32 @sw1(i64 %x) {\nentry:\n  %c = icmp ne i64 %x, 0\n\
\x20 switch i1 %c, label %d [\n    i1 true, label %a\n  ]\na:\n  ret i32 1\nd:\n  ret i32 0\n}\n\
define i32 @sw1_lit(i64 %x) {\nentry:\n  %c = icmp ne i64 %x, 0\n\
\x20 switch i1 %c, label %d [\n    i1 3, label %a\n  ]\na:\n  ret i32 1\nd:\n  ret i32 0\n}\n\
define i64 @load_c64() {\n  %v = load i64, ptr @c64, align 8\n  ret i64 %v\n}\n\
define i32 @load_c8() {\n  %v = load i8, ptr @c8, align 1\n  %r = zext i8 %v to i32\n  ret i32 %r\n}\n\
define i32 @load_c1() {\n  %v = load i1, ptr @c1, align 1\n  %r = zext i1 %v to i32\n  ret i32 %r\n}\n\
define i32 @load_c1m() {\n  %v = load i1, ptr @c1m, align 1\n  %r = zext i1 %v to i32\n  ret i32 %r\n}\n\
define i32 @agg_byte0() {\n  %v = load i8, ptr @agg, align 1\n  %r = zext i8 %v to i32\n  ret i32 %r\n}\n\
define i32 @agg_bool() {\n  %v = load i1, ptr @agg, align 1\n  %r = select i1 %v, i32 7, i32 9\n\
\x20 ret i32 %r\n}\n\
define i32 @zext_i1_2() {\n  %r = zext i1 2 to i32\n  ret i32 %r\n}\n\
define i32 @zext_i1_3() {\n  %r = zext i1 3 to i32\n  ret i32 %r\n}\n\
define i32 @zext_i1_m1() {\n  %r = zext i1 -1 to i32\n  ret i32 %r\n}\n\
define i32 @sext_i1_1() {\n  %r = sext i1 1 to i32\n  ret i32 %r\n}\n\
define i64 @sext_i1_dyn(i64 %x) {\n  %c = icmp ne i64 %x, 0\n  %r = sext i1 %c to i64\n  ret i64 %r\n}\n\
define i32 @br_i1_2() {\nentry:\n  br i1 2, label %t, label %f\nt:\n  ret i32 1\nf:\n  ret i32 0\n}\n\
define i32 @sel_i1_3(i32 %a, i32 %b) {\n  %s = select i1 3, i32 %a, i32 %b\n  ret i32 %s\n}\n\
define i32 @r8_300() {\n  %v = add i8 300, 0\n  %r = sext i8 %v to i32\n  ret i32 %r\n}\n\
define i32 @r8_m129() {\n  %v = add i8 -129, 0\n  %r = sext i8 %v to i32\n  ret i32 %r\n}\n\
define i64 @r32_wide() {\n  %v = add i32 4294967296, 7\n  %r = sext i32 %v to i64\n  ret i64 %r\n}\n\
define i64 @r64_wide() {\n  ret i64 18446744073709551621\n}\n\
declare i64 @sum_bytes(ptr, i64)\n\
declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)\n\
define i64 @alloca_i8(i8 %n) {\nentry:\n  %p = alloca i8, i8 %n, align 1\n  %c = zext i8 %n to i64\n\
\x20 call void @llvm.memset.p0.i64(ptr %p, i8 1, i64 %c, i1 false)\n\
\x20 %s = call i64 @sum_bytes(ptr %p, i64 %c)\n  ret i64 %s\n}\n\
define ptr @alloca_i8_300() {\n  %p = alloca i8, i8 300, align 1\n  ret ptr %p\n}\n\
define i64 @alloca_i8_lit() {\nentry:\n  %p = alloca i8, i8 200, align 1\n\
\x20 call void @llvm.memset.p0.i64(ptr %p, i8 1, i64 200, i1 false)\n\
\x20 %s = call i64 @sum_bytes(ptr %p, i64 200)\n  ret i64 %s\n}\n\
define ptr @i1_gep_false(ptr %p) {\n\
\x20 %q = getelementptr [4 x i64], ptr %p, i64 0, i1 false\n  ret ptr %q\n}\n\
define ptr @i1_gep_struct_false(ptr %p) {\n\
\x20 %q = getelementptr %S, ptr %p, i1 false, i32 1\n  ret ptr %q\n}\n\
define ptr @i1_gep_const_false() {\n  ret ptr getelementptr (i8, ptr @bytes, i1 false)\n}\n\
define i64 @alloca_i1_true() {\nentry:\n  %p = alloca i64, i1 true, align 8\n\
\x20 store volatile i64 77, ptr %p, align 8\n  %v = load volatile i64, ptr %p, align 8\n\
\x20 ret i64 %v\n}\n\
define i64 @alloca_i8_neg() {\nentry:\n  %p = alloca i8, i8 -56, align 1\n\
\x20 call void @llvm.memset.p0.i64(ptr %p, i8 1, i64 200, i1 false)\n\
\x20 %s = call i64 @sum_bytes(ptr %p, i64 200)\n  ret i64 %s\n}\n\
define i64 @alloca_arr_neg() {\nentry:\n  %p = alloca [4 x i8], i8 -56, align 1\n\
\x20 call void @llvm.memset.p0.i64(ptr %p, i8 1, i64 800, i1 false)\n\
\x20 %s = call i64 @sum_bytes(ptr %p, i64 800)\n  ret i64 %s\n}\n\
define ptr @bytes_outer(i64 %i) {\n\
\x20 %q = getelementptr [4 x i8], ptr @bytes, i64 18446744073709551616, i64 %i\n  ret ptr %q\n}\n\
@a8 = global [2 x i8] [i8 300, i8 1], align 1\n\
@a16 = global [3 x i16] [i16 -1, i16 65535, i16 65537], align 2\n\
@q4 = global [4 x i64] [i64 10, i64 11, i64 12, i64 13], align 8\n\
define ptr @gep_wrap_up(ptr %p) {\n\
\x20 %q = getelementptr [4 x i64], ptr %p, i64 0, i64 2305843009213693953\n  ret ptr %q\n}\n\
define ptr @gep_wrap_neg(ptr %p) {\n\
\x20 %q = getelementptr [4 x i64], ptr %p, i64 0, i64 -2305843009213693951\n  ret ptr %q\n}\n\
define ptr @gep_wrap_struct(ptr %p) {\n\
\x20 %q = getelementptr %S, ptr %p, i64 1152921504606846977, i32 1\n  ret ptr %q\n}\n\
define ptr @gep_wrap_const() {\n\
\x20 ret ptr getelementptr ([4 x i64], ptr @q4, i64 0, i64 2305843009213693953)\n}\n\
define ptr @gep_wrap_sum(ptr %p) {\n\
\x20 %q = getelementptr [4 x [2 x i64]], ptr %p, i64 -144115188075855872, i64 -1\n  ret ptr %q\n}\n\
@sg = global %S { i64 21, i64 22 }, align 8\n\
define ptr @gep_const_field() {\n\
\x20 ret ptr getelementptr (%S, ptr @sg, i64 1152921504606846976, i32 1)\n}\n";

/// An integer literal is read as LLVM reads it for its type and spelled in
/// the importer's signed carrier's range, so no `i64` literal lands in the
/// stub interval the lowering adapter decodes as a global's address. The
/// fourth verifier round of L02-P13 compiled `ret i64 18076885954311749632`
/// to `@g`'s address (at e8ae736f6; at 395954590 trust-ir's codegen
/// admission refused the unsigned spelling as a `const type mismatch`, and
/// a `ptr` literal of the same value, which LLVM's parser rejects, still
/// compiled to `@g`'s address). Every function of
/// [`INTEGER_LITERALS_MODULE`] compiles with no relocation naming `g`, the
/// constants are spelled signed, and an array GEP index `i32 4294967295`
/// folds to 8 bytes back (it folded to 34,359,738,360 bytes forward), as do
/// an `i1` index of 1 (it folded 8 bytes forward) and `2^61 - 1` elements of
/// 8 bytes. A literal outside its type's two ranges is its low bits (`i8
/// 300` is 44), as llc reads it, in an operand, an `alloca` count and an
/// integer array initializer; `i1 false` is no GEP offset, and a folded
/// offset past `2^64` wraps; an integer literal for a pointer is refused by
/// name.
#[test]
fn integer_literals_are_read_at_their_type_width() {
    // Imported for the target it is compiled for: the module declares `@h`,
    // an FFI boundary, so it must state its target (`TargetInfoRequired`).
    let module = import_text_for_target(INTEGER_LITERALS_MODULE, "literals", LINUX)
        .expect("the literal forms import");
    let constants: BTreeSet<(String, i128)> = module
        .functions
        .iter()
        .flat_map(|function| {
            function
                .blocks
                .iter()
                .flat_map(|block| &block.body)
                .filter_map(move |node| match &node.inst {
                    trust_ir::inst::Inst::Const {
                        ty,
                        value: trust_ir::Constant::Int(value),
                    } => Some((format!("{}:{ty:?}", function.name), *value)),
                    _ => None,
                })
        })
        .collect();
    for expected in [
        ("f_ret:I64", -369_858_119_397_801_984),
        ("f_store:I64", -369_858_119_397_801_984),
        ("f_phi:I64", -369_858_119_397_801_984),
        ("f_cmp:I64", -369_858_119_397_801_984),
        ("f_arg:I64", -369_858_119_397_801_984),
        ("f_add:I64", -369_858_119_397_801_984),
        ("r32:I32", -1),
        ("r16:I16", -1),
        ("r8:I8", -1),
        ("gep_back:I64", -8),
        ("gep_struct:I64", -8),
        ("gep_const:I64", -1),
        ("i1_gep_arr:I64", -8),
        ("i1_gep_struct:I64", -8),
        ("i1_gep_const:I64", -1),
        ("i1_gep_const_true:I64", -1),
        ("gep_wrap:I64", -8),
        ("r8_300:I8", 44),
        ("r8_m129:I8", 127),
        ("r32_wide:I32", 0),
        ("r64_wide:I64", 5),
        ("i1_gep_struct_false:I64", 8),
        ("gep_wrap_up:I64", 8),
        ("gep_wrap_neg:I64", 8),
        ("gep_wrap_struct:I64", 24),
        ("gep_wrap_const:I64", 8),
        ("gep_wrap_sum:I64", -(1 << 63)),
        ("gep_wrap_sum:I64", -16),
        ("gep_const_field:I64", 8),
    ] {
        assert!(
            constants.contains(&(expected.0.to_string(), expected.1)),
            "{expected:?} in {constants:?}"
        );
    }
    // `i1 false` is no GEP offset (read as `true`, the seventh verifier
    // round's mutant went one element, struct or byte back).
    for unexpected in [
        ("i1_gep_false:I64", -8),
        ("i1_gep_struct_false:I64", -8),
        ("i1_gep_const_false:I64", -1),
    ] {
        assert!(
            !constants.contains(&(unexpected.0.to_string(), unexpected.1)),
            "{unexpected:?} in {constants:?}"
        );
    }
    // An integer array initializer's literals are their low bits.
    let in_range = import_text(
        "@a8 = global [2 x i8] [i8 44, i8 1], align 1\n\
         @a16 = global [3 x i16] [i16 -1, i16 -1, i16 1], align 2\n",
        "in-range",
    )
    .expect("in-range array initializers");
    for (index, name) in ["a8", "a16"].into_iter().enumerate() {
        let global = module
            .globals
            .iter()
            .find(|global| global.name == name)
            .unwrap_or_else(|| panic!("@{name}"));
        assert_eq!(
            global.initializer, in_range.globals[index].initializer,
            "@{name}: its literals' low bits"
        );
    }
    // An `alloca` count is zero-extended to `i64`: the literal `i8 200`
    // folds to the `i64` 200 (not the `i8` -56), and a computed one is a
    // `zext`.
    let function = |name: &str| {
        module
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap_or_else(|| panic!("@{name}"))
    };
    let producer = |function: &trust_ir::Function, value: trust_ir::ValueId| {
        function
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .find(|node| node.results.contains(&value))
            .map(|node| node.inst.clone())
    };
    for (name, expected) in [
        ("alloca_i8_lit", "Const I64 200"),
        ("alloca_i8_300", "Const I64 44"),
        ("alloca_i8", "ZExt I8 -> I64"),
        ("alloca_i1_true", "Const I64 1"),
        ("alloca_i8_neg", "Const I64 200"),
        ("alloca_arr_neg", "Const I64 800"),
    ] {
        let f = function(name);
        let count = f
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .find_map(|node| match &node.inst {
                trust_ir::inst::Inst::Alloca {
                    count: Some(count), ..
                } => Some(*count),
                _ => None,
            })
            .unwrap_or_else(|| panic!("@{name}: a counted alloca"));
        let read = match producer(f, count) {
            Some(trust_ir::inst::Inst::Const {
                ty: trust_ir::Ty::I64,
                value: trust_ir::Constant::Int(value),
            }) => format!("Const I64 {value}"),
            Some(trust_ir::inst::Inst::Cast {
                op: trust_ir::inst::CastOp::ZExt,
                src_ty: trust_ir::Ty::I8,
                dst_ty: trust_ir::Ty::I64,
                ..
            }) => "ZExt I8 -> I64".to_string(),
            other => panic!("@{name}: count {other:?}"),
        };
        assert_eq!(read, expected, "@{name}");
    }
    // The switch cases are spelled signed, an `i1` one as its low bit.
    let cases: BTreeSet<(String, i128)> = module
        .functions
        .iter()
        .flat_map(|function| {
            function
                .blocks
                .iter()
                .flat_map(|block| &block.body)
                .filter_map(move |node| match &node.inst {
                    trust_ir::inst::Inst::Switch { cases, .. } => Some(
                        cases
                            .iter()
                            .filter_map(|case| match case.value {
                                trust_ir::Constant::Int(value) => {
                                    Some((function.name.clone(), value))
                                }
                                _ => None,
                            })
                            .collect::<Vec<_>>(),
                    ),
                    _ => None,
                })
                .flatten()
        })
        .collect();
    assert_eq!(
        cases,
        [
            ("sw1", 1),
            ("sw1_lit", 1),
            ("sw32", -1),
            ("sw64", -369_858_119_397_801_984),
            ("sw8", -1),
        ]
        .into_iter()
        .map(|(name, value)| (name.to_string(), value))
        .collect::<BTreeSet<_>>()
    );
    for opt_level in OPT_LEVELS {
        let object = compile_module(&module, LINUX, opt_level, RelocationModel::Static)
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"));
        let records = read_object_records(&object).expect("ELF records");
        assert_eq!(
            relocation_forms(&records, "g"),
            BTreeSet::new(),
            "{opt_level:?}: no code addresses `@g`"
        );
    }
    // A folded GEP offset of 0xFADE000000000000 bytes (2259610744288968704
    // elements of 8) keeps its 64 bits, spelled signed: no code addresses
    // `@g` either.
    let far = "@g = global i64 42, align 8\ndefine ptr @f(ptr %p) {\n  %q = getelementptr \
               [4 x i64], ptr %p, i64 0, i64 2259610744288968704\n  ret ptr %q\n}\n";
    let module = import_text(far, "far").expect("a far GEP offset");
    let object = compile_module(&module, LINUX, OptLevel::O0, RelocationModel::Static)
        .expect("a far GEP offset compiles");
    assert_eq!(
        relocation_forms(&read_object_records(&object).expect("records"), "g"),
        BTreeSet::new(),
        "a far GEP offset is no address of `@g`"
    );
    // A constant-expression GEP's offset is summed modulo 2^64 as well:
    // -2^57 elements of 64 bytes and -1 of 16 are -2^63 - 16, which wraps to
    // 2^63 - 16 (summed without the reduction it is no `i64`).
    let sum = import_text(
        "@q = global [4 x i64] zeroinitializer, align 8\ndefine ptr @f() {\n  ret ptr \
         getelementptr ([4 x [2 x i64]], ptr @q, i64 -144115188075855872, i64 -1)\n}\n",
        "sum",
    )
    .expect("a constant-expression GEP offset summed past -2^63");
    assert!(
        sum.functions[0]
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .any(|node| matches!(
                &node.inst,
                trust_ir::inst::Inst::Const {
                    ty: trust_ir::Ty::I64,
                    value: trust_ir::Constant::Int(value),
                } if *value == (1 << 63) - 16
            )),
        "{:?}",
        sum.functions[0]
    );
    for (src, needle) in [
        (
            "@g = global i64 42\ndefine ptr @f() {\n  ret ptr 18076885954311749632\n}\n",
            "integer literal `18076885954311749632` for a pointer",
        ),
        (
            "@g = global i64 42\ndefine ptr @f(i1 %c) {\nentry:\n  br i1 %c, label %a, label %b\n\
             a:\n  br label %b\nb:\n  %p = phi ptr [ 18076885954311749632, %entry ], [ null, %a ]\n\
             \x20 ret ptr %p\n}\n",
            "integer literal `18076885954311749632` for a pointer",
        ),
        // An `alloca` no stack object can be: an `i128` count of 2^64
        // elements or more, and an aggregate of 2^64 bytes or more.
        (
            "define ptr @f() {\n  %p = alloca i8, i128 18446744073709551616, align 1\n\
             \x20 ret ptr %p\n}\n",
            "alloca count `i128 18446744073709551616`: 2^64 or more elements",
        ),
        (
            "define ptr @f() {\n  %p = alloca [8 x i8], i64 -1, align 1\n  ret ptr %p\n}\n",
            "array alloca of 18446744073709551615 elements of 8 bytes: its byte size reaches 2^64",
        ),
    ] {
        match import_text(src, "literal") {
            Err(trust_cg_llvm_import::Error::Unsupported(reason)) => {
                assert!(reason.contains(needle), "{src}: {reason}")
            }
            other => panic!("{src}: expected a named refusal, got {other:?}"),
        }
    }
}

// =============================================================================
// Native: AArch64 Linux GNU only
// =============================================================================

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod linux_native {
    use super::*;
    use std::collections::BTreeSet;
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::process::Command;

    fn run(command: &mut Command) -> (bool, String, String) {
        let output = command
            .env("LC_ALL", "C")
            .output()
            .unwrap_or_else(|error| panic!("{command:?}: {error}"));
        (
            output.status.success(),
            String::from_utf8_lossy(&output.stdout).into_owned(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        )
    }

    fn ok(command: &mut Command, directory: &Path) -> String {
        let (success, stdout, stderr) = run(command);
        assert!(
            success,
            "{command:?} failed; files in {directory:?}\nstdout={stdout}\nstderr={stderr}"
        );
        stdout
    }

    fn write(directory: &Path, name: &str, bytes: impl AsRef<[u8]>) -> PathBuf {
        let path = directory.join(name);
        fs::write(&path, bytes).expect("write scratch file");
        path
    }

    /// The `cc` linker selections: GNU ld always, gold and LLD when present.
    /// `TCG_REQUIRE_GOLD` and `TCG_REQUIRE_LLD` turn a missing one into a
    /// failure.
    fn linkers() -> Vec<(&'static str, Vec<String>)> {
        let on_path = |tool: &str| {
            std::env::var_os("PATH").and_then(|paths| {
                std::env::split_paths(&paths).find(|dir| dir.join(tool).is_file())
            })
        };
        let mut linkers = vec![("bfd", vec!["-fuse-ld=bfd".to_string()])];
        if on_path("ld.gold").is_some() || Path::new("/usr/bin/ld.gold").is_file() {
            linkers.push(("gold", vec!["-fuse-ld=gold".to_string()]));
        } else {
            assert!(
                std::env::var_os("TCG_REQUIRE_GOLD").is_none(),
                "TCG_REQUIRE_GOLD is set but no ld.gold was found"
            );
            eprintln!("SKIP: no ld.gold (PATH, /usr/bin); the gold legs did not run");
        }
        match std::env::var_os("TCG_LLD_DIR")
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|home| Path::new(&home).join(".local/bin")))
            .filter(|dir| dir.join("ld.lld").is_file())
            .or_else(|| on_path("ld.lld"))
        {
            Some(dir) => linkers.push((
                "lld",
                vec!["-fuse-ld=lld".to_string(), format!("-B{}/", dir.display())],
            )),
            None => {
                assert!(
                    std::env::var_os("TCG_REQUIRE_LLD").is_none(),
                    "TCG_REQUIRE_LLD is set but no ld.lld was found"
                );
                eprintln!(
                    "SKIP: no ld.lld (TCG_LLD_DIR, ~/.local/bin, PATH); the LLD legs did not run"
                );
            }
        }
        linkers
    }

    fn cc(flags: &[String]) -> Command {
        let mut command = Command::new("cc");
        command.args(flags);
        command
    }

    /// Compile C or C++ `source` (by extension) to an object with `flags`.
    fn host_object(directory: &Path, source: &Path, flags: &[&str]) -> PathBuf {
        let object = source.with_extension("o");
        let compiler = if source.extension().is_some_and(|ext| ext == "cc") {
            "g++"
        } else {
            "gcc"
        };
        ok(
            Command::new(compiler)
                .args(flags)
                .arg("-c")
                .arg(source)
                .arg("-o")
                .arg(&object),
            directory,
        );
        object
    }

    /// Import and compile `src` for Linux and write it as `name`.
    fn imported_object(
        directory: &Path,
        name: &str,
        src: &str,
        opt_level: OptLevel,
        model: RelocationModel,
    ) -> PathBuf {
        let object = compile(src, LINUX, opt_level, model)
            .unwrap_or_else(|error| panic!("{name} {opt_level:?} {model}: {error}"));
        write(directory, name, object)
    }

    /// Where a compiler's sysroot keeps `llc`: a Trust package ships it
    /// there, beside its other LLVM tools.
    const LLC_IN_SYSROOT: &str = "lib/rustlib/aarch64-unknown-linux-gnu/bin/llc";

    /// The `llc` of the LLVM twin legs, found in this order: `TCG_LLC`, the
    /// first `llc` in an absolute `PATH` entry (a relative entry would resolve
    /// against this test's working directory, not the floor's, so it is not
    /// searched), then `<sysroot>/`[`LLC_IN_SYSROOT`] of the compiler that
    /// builds this test (`$RUSTC`, else `trustc`). Every candidate must be an
    /// executable file, and the one found must report the same LLVM major
    /// version as that compiler (`-vV`'s `LLVM version:`). The compiler is
    /// probed without the `TCG_*` and `TRUST_CG_*` variables, which a Trust
    /// compiler refuses as untracked controls. The floor's preflight
    /// (`resolve_llc` in `scripts/check_linux_aarch64.py`) applies the same
    /// rule. The llc used, its route and both versions are printed. Without a
    /// usable one the legs are skipped and named on stderr; `TCG_REQUIRE_LLC`
    /// (which the Linux floor sets for this target) makes that a failure
    /// whose message names the remedy for the compiler found: the package's
    /// `lib/rustlib/<host>/bin` for a Trust one; for any other, building this
    /// test with a Trust package's `trustc` or setting `TCG_LLC`.
    fn llc() -> Option<PathBuf> {
        let compiler = std::env::var_os("RUSTC").unwrap_or_else(|| "trustc".into());
        let facts = compiler_facts(&compiler);
        let explicit = std::env::var_os("TCG_LLC").map(PathBuf::from);
        let on_path = std::env::var_os("PATH").and_then(|paths| {
            std::env::split_paths(&paths)
                .filter(|dir| dir.is_absolute())
                .map(|dir| dir.join("llc"))
                .find(|path| is_executable_file(path))
        });
        let candidate = match (explicit, on_path) {
            (Some(path), _) => Some((path, "TCG_LLC".to_string())),
            (None, Some(path)) => Some((path, "PATH".to_string())),
            (None, None) => facts
                .as_ref()
                .map(|facts| facts.sysroot.join(LLC_IN_SYSROOT))
                .filter(|path| is_executable_file(path))
                .map(|path| (path, format!("the sysroot of {compiler:?}"))),
        };
        let remedy = match &facts {
            Some(facts) if facts.trust => format!(
                "the Trust package {:?} ships its LLVM tools at {LLC_IN_SYSROOT}; use a Trust \
                 package that carries them, or set TCG_LLC",
                facts.sysroot
            ),
            Some(_) => format!(
                "{compiler:?} is not a Trust compiler; build this test with a Trust package's \
                 trustc (RUSTC), whose sysroot ships llc at {LLC_IN_SYSROOT}, or set TCG_LLC to \
                 an llc of {compiler:?}'s LLVM major version"
            ),
            None => format!("{compiler:?} -vV or --print sysroot failed; set TCG_LLC"),
        };
        let problem = match (&candidate, &facts) {
            (None, _) => "no llc was found".to_string(),
            (Some((path, route)), _) if !is_executable_file(path) => {
                format!("{route} names {path:?}, which is not an executable file")
            }
            (Some(_), None) => format!("{compiler:?} reports no LLVM version to match"),
            (Some((path, route)), Some(facts)) => {
                let version = llc_version(path);
                match (llvm_major(&version), facts.llvm_major) {
                    (Some(found), Some(wanted)) if found == wanted => {
                        eprintln!(
                            "llc twin legs: {path:?} from {route} ({version}; compiler \
                             {compiler:?}: {}, LLVM {wanted})",
                            facts.release
                        );
                        return candidate.map(|(path, _)| path);
                    }
                    (found, wanted) => format!(
                        "{path:?} from {route} reports {version:?} (LLVM major {found:?}), but \
                         {compiler:?} is LLVM major {wanted:?}"
                    ),
                }
            }
        };
        assert!(
            std::env::var_os("TCG_REQUIRE_LLC").is_none(),
            "TCG_REQUIRE_LLC is set but no usable llc was found (TCG_LLC, PATH, the sysroot of \
             {compiler:?}): {problem}; {remedy}"
        );
        eprintln!(
            "SKIP: no usable llc (TCG_LLC, PATH, the sysroot of {compiler:?}); the llc twin legs \
             did not run: {problem}; {remedy}"
        );
        None
    }

    /// An existing regular file with an execute bit, the rule the floor's
    /// preflight applies too.
    fn is_executable_file(path: &Path) -> bool {
        use std::os::unix::fs::PermissionsExt;
        fs::metadata(path)
            .is_ok_and(|meta| meta.is_file() && meta.permissions().mode() & 0o111 != 0)
    }

    /// The `LLVM version ...` line of `llc --version`, or a placeholder.
    fn llc_version(path: &Path) -> String {
        let (_, version, _) = run(Command::new(path).arg("--version"));
        version
            .lines()
            .find(|line| line.contains("LLVM version"))
            .map_or("no LLVM version line".to_string(), |line| {
                line.trim().to_string()
            })
    }

    /// The major version in an `LLVM version 22.1.6...` (llc) or
    /// `LLVM version: 22.1.6` (`rustc -vV`) line.
    fn llvm_major(text: &str) -> Option<u32> {
        let rest = text.split("LLVM version").nth(1)?;
        let digits: String = rest
            .trim_start_matches([':', ' '])
            .chars()
            .take_while(char::is_ascii_digit)
            .collect();
        digits.parse().ok()
    }

    /// What the llc lookup needs from the compiler that builds this test.
    struct CompilerFacts {
        sysroot: PathBuf,
        /// Its `-vV` names the `trustc` driver.
        trust: bool,
        /// Its `-vV` `release:` line.
        release: String,
        llvm_major: Option<u32>,
    }

    /// Probe `compiler` (`--print sysroot`, `-vV`) without the `TCG_*` and
    /// `TRUST_CG_*` variables.
    fn compiler_facts(compiler: &std::ffi::OsStr) -> Option<CompilerFacts> {
        let probe = |args: &[&str]| {
            let mut command = Command::new(compiler);
            command.args(args);
            for (name, _) in std::env::vars_os() {
                if name
                    .to_str()
                    .is_some_and(|name| name.starts_with("TCG_") || name.starts_with("TRUST_CG_"))
                {
                    command.env_remove(&name);
                }
            }
            let output = command
                .output()
                .ok()
                .filter(|output| output.status.success())?;
            String::from_utf8(output.stdout).ok()
        };
        let sysroot = PathBuf::from(probe(&["--print", "sysroot"])?.trim());
        let verbose = probe(&["-vV"])?;
        Some(CompilerFacts {
            sysroot,
            trust: verbose.lines().any(|line| line.trim() == "binary: trustc"),
            release: verbose
                .lines()
                .find_map(|line| line.strip_prefix("release: "))
                .unwrap_or("no release line")
                .to_string(),
            llvm_major: verbose
                .lines()
                .find(|line| line.starts_with("LLVM version"))
                .and_then(llvm_major),
        })
    }

    /// Compile the same LLVM text `src` with `llc` for AArch64 Linux at
    /// `opt_level` and write it as `name`. `pie` and `pic` both use llc's
    /// `pic` model (llc has no PIE model; pic code is correct in a PIE).
    fn llc_object(
        llc: &Path,
        directory: &Path,
        name: &str,
        src: &str,
        opt_level: OptLevel,
        model: RelocationModel,
    ) -> PathBuf {
        let source = write(directory, &format!("{name}.ll"), src);
        let object = directory.join(format!("{name}.o"));
        let level = match opt_level {
            OptLevel::O0 => "-O0",
            OptLevel::O1 => "-O1",
            OptLevel::O2 => "-O2",
            OptLevel::O3 => "-O3",
        };
        let relocation = match model {
            RelocationModel::Static => "-relocation-model=static",
            RelocationModel::Pie | RelocationModel::Pic => "-relocation-model=pic",
        };
        ok(
            Command::new(llc)
                .args([
                    "-mtriple=aarch64-unknown-linux-gnu",
                    "-filetype=obj",
                    level,
                    relocation,
                ])
                .arg(&source)
                .arg("-o")
                .arg(&object),
            directory,
        );
        object
    }

    /// `.dynsym` of a linked image: name -> `(bind, vis, ndx)`.
    fn dynsym(path: &Path, directory: &Path) -> BTreeMap<String, (String, String, String)> {
        let text = ok(
            Command::new("readelf")
                .args(["--wide", "--dyn-syms"])
                .arg(path),
            directory,
        );
        text.lines()
            .filter_map(|line| {
                let columns: Vec<&str> = line.split_whitespace().collect();
                (columns.len() >= 8 && columns[0].ends_with(':')).then(|| {
                    (
                        columns[7].split('@').next().unwrap_or("").to_string(),
                        (
                            columns[4].to_string(),
                            columns[5].to_string(),
                            columns[6].to_string(),
                        ),
                    )
                })
            })
            .collect()
    }

    fn relocs(path: &Path, directory: &Path) -> String {
        ok(
            Command::new("readelf")
                .args(["--wide", "--relocs"])
                .arg(path),
            directory,
        )
    }

    // -------------------------------------------------------------------------
    // Hidden and protected functions in a `pic` shared object
    // -------------------------------------------------------------------------

    /// The imported library: Linux clang's spelling (a self-keyed COMDAT on
    /// the `linkonce_odr` function) with `comdat`, Darwin clang's without.
    fn library(comdat: bool) -> String {
        let (declaration, clause) = if comdat {
            ("$lp_odr_hidden = comdat any\n", " comdat")
        } else {
            ("", "")
        };
        format!(
            "{declaration}\
             define i64 @lp_default() {{\n  ret i64 11\n}}\n\
             define protected i64 @lp_protected() {{\n  ret i64 22\n}}\n\
             define hidden i64 @lp_hidden() {{\n  ret i64 33\n}}\n\
             define linkonce_odr hidden i64 @lp_odr_hidden(){clause} {{\n  ret i64 44\n}}\n\
             define weak hidden i64 @lp_weak_hidden() {{\n  ret i64 55\n}}\n\
             define i64 @call_lp_default() {{\n  %r = call i64 @lp_default()\n  ret i64 %r\n}}\n\
             define i64 @call_lp_protected() {{\n  %r = call i64 @lp_protected()\n  ret i64 %r\n}}\n\
             define i64 @call_lp_hidden() {{\n  %r = call i64 @lp_hidden()\n  ret i64 %r\n}}\n\
             define i64 @call_lp_odr_hidden() {{\n  %r = call i64 @lp_odr_hidden()\n  \
             ret i64 %r\n}}\n\
             define i64 @call_lp_weak_hidden() {{\n  %r = call i64 @lp_weak_hidden()\n  \
             ret i64 %r\n}}\n"
        )
    }

    /// The g++ twin of [`library`]: the same five functions and callers.
    const LIBRARY_TWIN: &str = r#"
extern "C" {
long lp_default(void) { return 11; }
__attribute__((visibility("protected"))) long lp_protected(void) { return 22; }
__attribute__((visibility("hidden"))) long lp_hidden(void) { return 33; }
__attribute__((visibility("hidden"), noinline)) inline long lp_odr_hidden(void) { return 44; }
__attribute__((weak, visibility("hidden"))) long lp_weak_hidden(void) { return 55; }
long call_lp_default(void) { return lp_default(); }
long call_lp_protected(void) { return lp_protected(); }
long call_lp_hidden(void) { return lp_hidden(); }
long call_lp_odr_hidden(void) { return lp_odr_hidden(); }
long call_lp_weak_hidden(void) { return lp_weak_hidden(); }
}
"#;

    const LIBRARY_DRIVER: &str = "#include <stdio.h>\n\
        long call_lp_default(void), call_lp_protected(void), call_lp_hidden(void),\n\
          call_lp_odr_hidden(void), call_lp_weak_hidden(void);\n\
        int main(void) {\n\
          printf(\"default=%ld protected=%ld hidden=%ld odr_hidden=%ld weak_hidden=%ld\\n\",\n\
            call_lp_default(), call_lp_protected(), call_lp_hidden(),\n\
            call_lp_odr_hidden(), call_lp_weak_hidden());\n\
          return 0;\n\
        }\n";

    const LIBRARY_INTERPOSER: &str = "long lp_default(void) { return 111; }\n\
        long lp_protected(void) { return 222; }\n\
        long lp_hidden(void) { return 333; }\n\
        long lp_odr_hidden(void) { return 444; }\n\
        long lp_weak_hidden(void) { return 555; }\n";

    const LIBRARY_OUTSIDER: &str = "long lp_hidden(void);\n\
        int main(void) { return lp_hidden() != 33; }\n";

    /// What one linked library shows: its exported `lp_*` symbols, whether
    /// its relocations name any hidden or protected `lp_*` symbol, the plain
    /// and `LD_PRELOAD` runs, and whether an outsider linked `lp_hidden`.
    #[derive(Debug, PartialEq, Eq)]
    struct LibraryObservation {
        exported: BTreeMap<String, (String, String)>,
        bound_names_in_relocs: Vec<String>,
        plain: String,
        preloaded: String,
        outsider_linked: bool,
    }

    fn observe_library(
        leg: &Path,
        flags: &[String],
        library_object: &Path,
        support: &[PathBuf],
    ) -> LibraryObservation {
        let library = leg.join("liblp.so");
        ok(
            cc(flags)
                .args(["-shared", "-Wl,-z,defs,-z,now"])
                .arg(library_object)
                .args(support)
                .arg("-o")
                .arg(&library),
            leg,
        );
        let exported = dynsym(&library, leg)
            .into_iter()
            .filter(|(name, _)| name.starts_with("lp_"))
            .map(|(name, (bind, vis, _))| (name, (bind, vis)))
            .collect();
        let relocations = relocs(&library, leg);
        let bound_names_in_relocs = [
            "lp_protected",
            "lp_hidden",
            "lp_odr_hidden",
            "lp_weak_hidden",
        ]
        .into_iter()
        .filter(|name| {
            relocations
                .split_whitespace()
                .any(|word| word.split('@').next() == Some(name))
        })
        .map(str::to_string)
        .collect();
        let interposer = leg.join("libinterpose.so");
        ok(
            cc(flags)
                .args(["-shared", "-fPIC", "-x", "c"])
                .arg(write(leg, "interposer.c", LIBRARY_INTERPOSER))
                .arg("-o")
                .arg(&interposer),
            leg,
        );
        let driver = leg.join("driver");
        let rpath = format!("-Wl,-rpath,{}", leg.display());
        ok(
            cc(flags)
                .args(["-fPIE", "-pie"])
                .arg(write(leg, "driver.c", LIBRARY_DRIVER))
                .arg(format!("-L{}", leg.display()))
                .arg("-llp")
                .arg(&rpath)
                .arg("-o")
                .arg(&driver),
            leg,
        );
        let plain = ok(&mut Command::new(&driver), leg).trim().to_string();
        let preloaded = ok(Command::new(&driver).env("LD_PRELOAD", &interposer), leg)
            .trim()
            .to_string();
        let (outsider_linked, _, _) = run(cc(flags)
            .arg(write(leg, "outsider.c", LIBRARY_OUTSIDER))
            .arg(format!("-L{}", leg.display()))
            .arg("-llp")
            .arg(&rpath)
            .arg("-o")
            .arg(leg.join("outsider")));
        LibraryObservation {
            exported,
            bound_names_in_relocs,
            plain,
            preloaded,
            outsider_linked,
        }
    }

    /// Hidden, weak-hidden and `linkonce_odr hidden` functions imported from
    /// LLVM text stay out of a `pic` shared object's `.dynsym`, the
    /// protected one is exported `PROTECTED`, and the library's own calls to
    /// all four are bound at link time: an `LD_PRELOAD` interposer rebinds
    /// only the default-visibility call, and an executable cannot link
    /// `lp_hidden`. The g++ twin of the same shape, and the same LLVM text
    /// compiled by `llc`, show exactly the same.
    #[test]
    fn imported_hidden_and_protected_functions_resist_interposition() {
        let linkers = linkers();
        let llc = llc();
        let directory = common::unique_temp_dir("l02p13-interposition");
        let twin_source = write(&directory, "twin.cc", LIBRARY_TWIN);
        let twin_object = host_object(&directory, &twin_source, &["-O2", "-fPIC"]);
        for (opt_level, comdat) in OPT_LEVELS
            .into_iter()
            .flat_map(|opt_level| [(opt_level, false), (opt_level, true)])
        {
            let tag = format!("{opt_level:?}-{}", if comdat { "comdat" } else { "plain" });
            let object = imported_object(
                &directory,
                &format!("library-{tag}.o"),
                &library(comdat),
                opt_level,
                RelocationModel::Pic,
            );
            let llc_library = llc.as_deref().map(|llc| {
                llc_object(
                    llc,
                    &directory,
                    &format!("library-{tag}-llc"),
                    &library(comdat),
                    opt_level,
                    RelocationModel::Pic,
                )
            });
            for (linker, flags) in &linkers {
                let label = format!("{tag} {linker}");
                let leg = directory.join(format!("{tag}-{linker}"));
                let twin_leg = leg.join("twin");
                fs::create_dir_all(&twin_leg).expect("scratch");
                let imported = observe_library(&leg, flags, &object, &[]);
                let expected = LibraryObservation {
                    exported: [
                        ("lp_default", ("GLOBAL", "DEFAULT")),
                        ("lp_protected", ("GLOBAL", "PROTECTED")),
                    ]
                    .into_iter()
                    .map(|(name, (bind, vis))| {
                        (name.to_string(), (bind.to_string(), vis.to_string()))
                    })
                    .collect(),
                    bound_names_in_relocs: Vec::new(),
                    plain: "default=11 protected=22 hidden=33 odr_hidden=44 weak_hidden=55"
                        .to_string(),
                    preloaded: "default=111 protected=22 hidden=33 odr_hidden=44 weak_hidden=55"
                        .to_string(),
                    outsider_linked: false,
                };
                assert_eq!(imported, expected, "{label}: imported library");
                let twin = observe_library(&twin_leg, flags, &twin_object, &[]);
                assert_eq!(imported, twin, "{label}: imported library vs its g++ twin");
                if let Some(llc_library) = &llc_library {
                    let llc_leg = leg.join("llc");
                    fs::create_dir_all(&llc_leg).expect("scratch");
                    let from_llc = observe_library(&llc_leg, flags, llc_library, &[]);
                    assert_eq!(imported, from_llc, "{label}: imported library vs llc");
                }
            }
        }
        eprintln!("L02-P13 interposition passed: {directory:?}");
    }

    // -------------------------------------------------------------------------
    // Hidden and protected data of every shape in a `pic` shared object
    // -------------------------------------------------------------------------

    /// One data shape of the library: its LLVM type and initializer, the
    /// LLVM reader body from `@N` to the `i64` `%v` it returns, the C twin's
    /// definition and reader expression, the interposer's C definition, the
    /// value the library reads from its own definition, and the value it
    /// reads from the interposer's.
    struct NativeDataShape {
        tag: &'static str,
        llvm: &'static str,
        reader: &'static str,
        twin: &'static str,
        twin_read: &'static str,
        interposer: &'static str,
        value: i64,
        interposed: i64,
    }

    /// The image shapes of `Parser::push_image_global`: an integer, a byte
    /// string, a zero, a floating-point and a pointer array (the last
    /// pointing at the hidden `lib_anchor`, 77; the interposer's at
    /// `ip_anchor`, 707), a named struct with fields and zero, and a null
    /// pointer. `N` stands for the global's name.
    const NATIVE_DATA_SHAPES: [NativeDataShape; 8] = [
        NativeDataShape {
            tag: "ints",
            llvm: "[4 x i32] [i32 1, i32 2, i32 3, i32 4]",
            reader: "  %p = getelementptr [4 x i32], ptr @N, i64 0, i64 2\n  \
                     %l = load i32, ptr %p, align 4\n  %v = sext i32 %l to i64\n",
            twin: "int N[4] = {1, 2, 3, 4};",
            twin_read: "N[2]",
            interposer: "int N[4] = {101, 102, 103, 104};",
            value: 3,
            interposed: 103,
        },
        NativeDataShape {
            tag: "str",
            llvm: "[6 x i8] c\"hello\\00\"",
            reader: "  %l = load i8, ptr @N, align 1\n  %v = zext i8 %l to i64\n",
            twin: "char N[6] = \"hello\";",
            twin_read: "(unsigned char)N[0]",
            interposer: "char N[6] = \"HELLO\";",
            value: 104,
            interposed: 72,
        },
        NativeDataShape {
            tag: "zero",
            llvm: "[4 x i64] zeroinitializer",
            reader: "  %p = getelementptr [4 x i64], ptr @N, i64 0, i64 1\n  \
                     %v = load i64, ptr %p, align 8\n",
            twin: "long N[4] = {0};",
            twin_read: "N[1]",
            interposer: "long N[4] = {7, 7, 7, 7};",
            value: 0,
            interposed: 7,
        },
        NativeDataShape {
            tag: "floats",
            llvm: "[2 x double] [double 1.5, double 2.5]",
            reader: "  %p = getelementptr [2 x double], ptr @N, i64 0, i64 1\n  \
                     %l = load double, ptr %p, align 8\n  %v = fptosi double %l to i64\n",
            twin: "double N[2] = {1.5, 2.5};",
            twin_read: "(long)N[1]",
            interposer: "double N[2] = {11.5, 12.5};",
            value: 2,
            interposed: 12,
        },
        NativeDataShape {
            tag: "struct",
            llvm: "%struct.S { i32 9, i64 10 }",
            reader: "  %p = getelementptr %struct.S, ptr @N, i64 0, i32 1\n  \
                     %v = load i64, ptr %p, align 8\n",
            twin: "struct S N = {9, 10};",
            twin_read: "N.b",
            interposer: "struct S N = {1, 2};",
            value: 10,
            interposed: 2,
        },
        NativeDataShape {
            tag: "szero",
            llvm: "%struct.S zeroinitializer",
            reader: "  %p = getelementptr %struct.S, ptr @N, i64 0, i32 1\n  \
                     %v = load i64, ptr %p, align 8\n",
            twin: "struct S N = {0, 0};",
            twin_read: "N.b",
            interposer: "struct S N = {5, 6};",
            value: 0,
            interposed: 6,
        },
        NativeDataShape {
            tag: "ptrs",
            llvm: "[2 x ptr] [ptr @lib_anchor, ptr null]",
            reader: "  %q = load ptr, ptr @N, align 8\n  %v = load i64, ptr %q, align 8\n",
            twin: "long *N[2] = {&lib_anchor, 0};",
            twin_read: "*N[0]",
            interposer: "long *N[2] = {&ip_anchor, 0};",
            value: 77,
            interposed: 707,
        },
        NativeDataShape {
            tag: "pnull",
            llvm: "ptr null",
            reader: "  %q = load ptr, ptr @N, align 8\n  %c = icmp eq ptr %q, null\n  \
                     %v = zext i1 %c to i64\n",
            twin: "long *N = 0;",
            twin_read: "N == 0",
            interposer: "long *N = &ip_anchor;",
            value: 1,
            interposed: 0,
        },
    ];

    /// One linkage and visibility of the library's data: its LLVM prefix,
    /// whether it carries Linux clang's self-keyed `comdat`, the C twin's
    /// attributes (an ODR form is a C `weak` definition: g++ 13 writes a
    /// C++17 inline variable `STB_GNU_UNIQUE`, where llc writes these
    /// `STB_WEAK`), the `.dynsym`
    /// binding and visibility of an exported one, and whether an
    /// `LD_PRELOAD` interposer rebinds the library's own reads.
    struct NativeDataForm {
        tag: &'static str,
        prefix: &'static str,
        comdat: bool,
        twin: &'static str,
        exported: Option<(&'static str, &'static str)>,
        interposed: bool,
    }

    const NATIVE_DATA_FORMS: [NativeDataForm; 8] = [
        NativeDataForm {
            tag: "def",
            prefix: "",
            comdat: false,
            twin: "",
            exported: Some(("GLOBAL", "DEFAULT")),
            interposed: true,
        },
        NativeDataForm {
            tag: "hid",
            prefix: "hidden ",
            comdat: false,
            twin: "__attribute__((visibility(\"hidden\"))) ",
            exported: None,
            interposed: false,
        },
        NativeDataForm {
            tag: "prot",
            prefix: "protected ",
            comdat: false,
            twin: "__attribute__((visibility(\"protected\"))) ",
            exported: Some(("GLOBAL", "PROTECTED")),
            interposed: false,
        },
        NativeDataForm {
            tag: "wdef",
            prefix: "weak ",
            comdat: false,
            twin: "__attribute__((weak)) ",
            exported: Some(("WEAK", "DEFAULT")),
            interposed: true,
        },
        NativeDataForm {
            tag: "whid",
            prefix: "weak hidden ",
            comdat: false,
            twin: "__attribute__((weak, visibility(\"hidden\"))) ",
            exported: None,
            interposed: false,
        },
        NativeDataForm {
            tag: "wprot",
            prefix: "weak protected ",
            comdat: false,
            twin: "__attribute__((weak, visibility(\"protected\"))) ",
            exported: Some(("WEAK", "PROTECTED")),
            interposed: false,
        },
        NativeDataForm {
            tag: "lodrhid",
            prefix: "linkonce_odr hidden ",
            comdat: true,
            twin: "__attribute__((weak, visibility(\"hidden\"))) ",
            exported: None,
            interposed: false,
        },
        NativeDataForm {
            tag: "wodrprot",
            prefix: "weak_odr protected ",
            comdat: true,
            twin: "__attribute__((weak, visibility(\"protected\"))) ",
            exported: Some(("WEAK", "PROTECTED")),
            interposed: false,
        },
    ];

    /// Every global of the data library: `(name, shape, form)`.
    fn native_data() -> Vec<(String, &'static NativeDataShape, &'static NativeDataForm)> {
        NATIVE_DATA_SHAPES
            .iter()
            .flat_map(|shape| {
                NATIVE_DATA_FORMS
                    .iter()
                    .map(move |form| (format!("d_{}_{}", shape.tag, form.tag), shape, form))
            })
            .collect()
    }

    /// The imported data library: every shape in every form, and a reader
    /// `read_<name>` of each.
    fn data_library() -> String {
        let data = native_data();
        let mut src = String::new();
        for (name, _, form) in &data {
            if form.comdat {
                src.push_str(&format!("${name} = comdat any\n"));
            }
        }
        src.push_str("%struct.S = type { i32, i64 }\n");
        src.push_str("@lib_anchor = hidden global i64 77, align 8\n");
        for (name, shape, form) in &data {
            let clause = if form.comdat { ", comdat" } else { "" };
            src.push_str(&format!(
                "@{name} = {}global {}{clause}, align 8\n",
                form.prefix, shape.llvm
            ));
        }
        for (name, shape, _) in &data {
            src.push_str(&format!(
                "define i64 @read_{name}() {{\n{}  ret i64 %v\n}}\n",
                shape.reader.replace("@N", &format!("@{name}"))
            ));
        }
        src
    }

    /// The gcc twin of [`data_library`].
    fn data_twin() -> String {
        let mut src = String::from(
            "struct S { int a; long b; };\n\
             __attribute__((visibility(\"hidden\"))) long lib_anchor = 77;\n",
        );
        for (name, shape, form) in native_data() {
            src.push_str(&format!(
                "{}{}\nlong read_{name}(void) {{ return {}; }}\n",
                form.twin,
                shape.twin.replacen('N', &name, 1),
                shape.twin_read.replace('N', &name)
            ));
        }
        src
    }

    /// Defines every name of [`data_library`] with other contents.
    fn data_interposer() -> String {
        let mut src = String::from("struct S { int a; long b; };\nlong ip_anchor = 707;\n");
        for (name, shape, _) in native_data() {
            src.push_str(&shape.interposer.replacen('N', &name, 1));
            src.push('\n');
        }
        src
    }

    /// Prints what every reader returns, then the names `dlsym` finds.
    fn data_driver() -> String {
        let data = native_data();
        let mut src = String::from("#include <dlfcn.h>\n#include <stdio.h>\n");
        for (name, _, _) in &data {
            src.push_str(&format!("long read_{name}(void);\n"));
        }
        src.push_str("int main(void) {\n");
        for (name, _, _) in &data {
            src.push_str(&format!("  printf(\"{name}=%ld \", read_{name}());\n"));
        }
        src.push_str("  printf(\"\\n\");\n");
        for (name, _, _) in &data {
            src.push_str(&format!(
                "  if (dlsym(RTLD_DEFAULT, \"{name}\")) printf(\"{name} \");\n"
            ));
        }
        src.push_str("  printf(\"\\n\");\n  return 0;\n}\n");
        src
    }

    /// What one linked data library shows: its exported `d_*` symbols and
    /// the driver's plain and `LD_PRELOAD` runs (the values read, then the
    /// names `dlsym` finds).
    #[derive(Debug, PartialEq, Eq)]
    struct DataObservation {
        exported: BTreeMap<String, (String, String)>,
        plain: String,
        preloaded: String,
    }

    /// The observation the LLVM text states: hidden data stays out of
    /// `.dynsym` and `dlsym`, protected data is exported `PROTECTED`, and only
    /// the default-visibility reads are rebound by the interposer (which
    /// defines every name, so `dlsym` finds each under it).
    fn expected_data_observation() -> DataObservation {
        let data = native_data();
        let values = |preloaded: bool| {
            data.iter()
                .map(|(name, shape, form)| {
                    let value = if preloaded && form.interposed {
                        shape.interposed
                    } else {
                        shape.value
                    };
                    format!("{name}={value}")
                })
                .collect::<Vec<_>>()
                .join(" ")
        };
        let names = |all: bool| {
            data.iter()
                .filter(|(_, _, form)| all || form.exported.is_some())
                .map(|(name, _, _)| name.as_str())
                .collect::<Vec<_>>()
                .join(" ")
        };
        DataObservation {
            exported: data
                .iter()
                .filter_map(|(name, _, form)| {
                    form.exported
                        .map(|(bind, vis)| (name.clone(), (bind.to_string(), vis.to_string())))
                })
                .collect(),
            plain: format!("{}\n{}", values(false), names(false)),
            preloaded: format!("{}\n{}", values(true), names(true)),
        }
    }

    fn observe_data_library(
        leg: &Path,
        flags: &[String],
        library_object: &Path,
    ) -> DataObservation {
        let library = leg.join("libdata.so");
        ok(
            cc(flags)
                .args(["-shared", "-Wl,-z,defs,-z,now"])
                .arg(library_object)
                .arg("-o")
                .arg(&library),
            leg,
        );
        let exported = dynsym(&library, leg)
            .into_iter()
            .filter(|(name, _)| name.starts_with("d_"))
            .map(|(name, (bind, vis, _))| (name, (bind, vis)))
            .collect();
        let interposer = leg.join("libinterpose.so");
        ok(
            cc(flags)
                .args(["-shared", "-fPIC", "-x", "c"])
                .arg(write(leg, "interposer.c", data_interposer()))
                .arg("-o")
                .arg(&interposer),
            leg,
        );
        let driver = leg.join("driver");
        ok(
            cc(flags)
                .args(["-fPIE", "-pie"])
                .arg(write(leg, "driver.c", data_driver()))
                .arg(format!("-L{}", leg.display()))
                .arg("-ldata")
                .arg("-ldl")
                .arg(format!("-Wl,-rpath,{}", leg.display()))
                .arg("-o")
                .arg(&driver),
            leg,
        );
        let lines = |stdout: String| stdout.lines().map(str::trim).collect::<Vec<_>>().join("\n");
        DataObservation {
            exported,
            plain: lines(ok(&mut Command::new(&driver), leg)),
            preloaded: lines(ok(
                Command::new(&driver).env("LD_PRELOAD", &interposer),
                leg,
            )),
        }
    }

    /// Hidden, protected, weak and ODR globals of every image shape (integer,
    /// string, zero, floating-point and pointer arrays, named structs with
    /// fields and zero, a null pointer) imported from LLVM text keep their
    /// visibility in a `pic` shared object: the hidden ones stay out of
    /// `.dynsym` and `dlsym`, the protected ones are exported `PROTECTED`,
    /// and the library's own reads of both are bound at link time, so an
    /// `LD_PRELOAD` interposer defining every name rebinds only the
    /// default-visibility reads. The gcc twin of the same shapes (at -O2) and
    /// the same LLVM text compiled by `llc` show exactly the same, at O0-O3
    /// through GNU ld, gold and LLD. The third closure audit's mutant S13
    /// (every image global written with default visibility) exports the
    /// hidden and protected data and lets the interposer rebind its reads.
    #[test]
    fn imported_hidden_and_protected_data_resist_interposition() {
        let linkers = linkers();
        let llc = llc();
        let directory = common::unique_temp_dir("l02p13-data-interposition");
        let src = data_library();
        let twin_object = host_object(
            &directory,
            &write(&directory, "data-twin.c", data_twin()),
            &["-O2", "-fPIC"],
        );
        let expected = expected_data_observation();
        for opt_level in OPT_LEVELS {
            let tag = format!("{opt_level:?}");
            let object = imported_object(
                &directory,
                &format!("data-{tag}.o"),
                &src,
                opt_level,
                RelocationModel::Pic,
            );
            let llc_library = llc.as_deref().map(|llc| {
                llc_object(
                    llc,
                    &directory,
                    &format!("data-{tag}-llc"),
                    &src,
                    opt_level,
                    RelocationModel::Pic,
                )
            });
            for (linker, flags) in &linkers {
                let label = format!("{tag} {linker}");
                let leg = directory.join(format!("data-{tag}-{linker}"));
                let twin_leg = leg.join("twin");
                fs::create_dir_all(&twin_leg).expect("scratch");
                let imported = observe_data_library(&leg, flags, &object);
                assert_eq!(imported, expected, "{label}: imported data library");
                let twin = observe_data_library(&twin_leg, flags, &twin_object);
                assert_eq!(
                    imported, twin,
                    "{label}: imported data library vs its gcc twin"
                );
                if let Some(llc_library) = &llc_library {
                    let llc_leg = leg.join("llc");
                    fs::create_dir_all(&llc_leg).expect("scratch");
                    let from_llc = observe_data_library(&llc_leg, flags, llc_library);
                    assert_eq!(imported, from_llc, "{label}: imported data library vs llc");
                }
            }
        }
        eprintln!("L02-P13 data interposition passed: {directory:?}");
    }

    // -------------------------------------------------------------------------
    // One-definition-rule definitions in two objects
    // -------------------------------------------------------------------------

    /// One side of the ODR pair, `side` naming its entry point. With
    /// `comdat`, the Linux clang shape (self-keyed `any` COMDATs); without,
    /// the Darwin clang shape.
    fn odr_side(side: &str, comdat: bool) -> String {
        let (decl, clause, global_clause) = if comdat {
            (
                "$odr_fn = comdat any\n$odr_bump = comdat any\n$odr_counter = comdat any\n\
                 $wodr_fn = comdat any\n$wodr_value = comdat any\n",
                " comdat",
                ", comdat",
            )
        } else {
            ("", "", "")
        };
        format!(
            "{decl}\
             @odr_counter = linkonce_odr dso_local global i64 0{global_clause}, align 8\n\
             @wodr_value = weak_odr dso_local global i64 7{global_clause}, align 8\n\
             define linkonce_odr dso_local i64 @odr_fn(){clause} {{\n  ret i64 42\n}}\n\
             define linkonce_odr dso_local i64 @odr_bump(){clause} {{\n\
               %v = load i64, ptr @odr_counter, align 8\n\
               %n = add i64 %v, 1\n\
               store i64 %n, ptr @odr_counter, align 8\n\
               ret i64 %n\n}}\n\
             define weak_odr dso_local i64 @wodr_fn(){clause} {{\n\
               %v = load i64, ptr @wodr_value, align 8\n  ret i64 %v\n}}\n\
             define dso_local i64 @{side}_entry() {{\n\
               %f = call i64 @odr_fn()\n\
               %m = mul i64 %f, 1000\n\
               %b = call i64 @odr_bump()\n\
               %r = add i64 %m, %b\n\
               ret i64 %r\n}}\n"
        )
    }

    /// The g++ twin of one ODR side: `inline` functions and variables, which
    /// g++ places in COMDAT groups named like the symbol.
    fn odr_twin(side: &str) -> String {
        format!(
            "extern \"C\" {{\n\
             inline long odr_counter = 0;\n\
             __attribute__((noinline)) inline long odr_fn(void) {{ return 42; }}\n\
             __attribute__((noinline)) inline long odr_bump(void) {{ return ++odr_counter; }}\n\
             long {side}_entry(void) {{ return odr_fn() * 1000 + odr_bump(); }}\n\
             }}\n"
        )
    }

    const ODR_MAIN: &str = "#include <stdio.h>\n\
        extern long odr_counter;\n\
        long a_entry(void), b_entry(void);\n\
        int main(void) {\n\
          long a = a_entry();\n\
          long b = b_entry();\n\
          printf(\"a=%ld b=%ld counter=%ld\\n\", a, b, odr_counter);\n\
          return 0;\n\
        }\n";

    const WODR_MAIN: &str = "#include <stdio.h>\n\
        long wodr_fn(void);\n\
        int main(void) { printf(\"wodr=%ld\\n\", wodr_fn()); return 0; }\n";

    /// `linkonce_odr` and `weak_odr` functions and globals defined in two
    /// imported objects (Linux clang's self-keyed COMDAT spelling and the
    /// Darwin spelling without one) link without a duplicate-definition
    /// error and share ONE `odr_counter`, in both input orders, and also
    /// against a g++ twin whose `inline` entities are g++ COMDAT groups.
    #[test]
    fn imported_one_definition_rule_symbols_coalesce_across_objects() {
        let linkers = linkers();
        let llc = llc();
        let directory = common::unique_temp_dir("l02p13-odr");
        let main = write(&directory, "main.c", ODR_MAIN);
        let wodr_main = write(&directory, "wodr_main.c", WODR_MAIN);
        let twin_a = host_object(
            &directory,
            &write(&directory, "twin_a.cc", odr_twin("a")),
            &["-std=c++17", "-O2"],
        );
        let twin_b = host_object(
            &directory,
            &write(&directory, "twin_b.cc", odr_twin("b")),
            &["-std=c++17", "-O2"],
        );
        for opt_level in OPT_LEVELS {
            for comdat in [false, true] {
                let tag = format!("{opt_level:?}-{}", if comdat { "comdat" } else { "plain" });
                let a = imported_object(
                    &directory,
                    &format!("a-{tag}.o"),
                    &odr_side("a", comdat),
                    opt_level,
                    RelocationModel::Pie,
                );
                let b = imported_object(
                    &directory,
                    &format!("b-{tag}.o"),
                    &odr_side("b", comdat),
                    opt_level,
                    RelocationModel::Pie,
                );
                // The same LLVM text through llc, alone and mixed with the
                // imported objects in both orders.
                let llc_sides = llc.as_deref().map(|llc| {
                    let side = |name: &str| {
                        llc_object(
                            llc,
                            &directory,
                            &format!("{name}-{tag}-llc"),
                            &odr_side(name, comdat),
                            opt_level,
                            RelocationModel::Pie,
                        )
                    };
                    (side("a"), side("b"))
                });
                for (linker, flags) in &linkers {
                    let mut orders = vec![
                        ("a-b", [&a, &b]),
                        ("b-a", [&b, &a]),
                        ("a-twin_b", [&a, &twin_b]),
                        ("twin_a-b", [&twin_a, &b]),
                    ];
                    if let Some((llc_a, llc_b)) = &llc_sides {
                        orders.extend([
                            ("llc_a-llc_b", [llc_a, llc_b]),
                            ("a-llc_b", [&a, llc_b]),
                            ("llc_a-b", [llc_a, &b]),
                        ]);
                    }
                    for (order, objects) in orders {
                        let label = format!("{tag} {linker} {order}");
                        let binary = directory.join(format!("odr-{tag}-{linker}-{order}"));
                        ok(
                            cc(flags).arg(&main).args(objects).arg("-o").arg(&binary),
                            &directory,
                        );
                        assert_eq!(
                            ok(&mut Command::new(&binary), &directory).trim(),
                            "a=42001 b=42002 counter=2",
                            "{label}"
                        );
                    }
                    let binary = directory.join(format!("wodr-{tag}-{linker}"));
                    ok(
                        cc(flags)
                            .arg(&wodr_main)
                            .args([&a, &b])
                            .arg("-o")
                            .arg(&binary),
                        &directory,
                    );
                    assert_eq!(
                        ok(&mut Command::new(&binary), &directory).trim(),
                        "wodr=7",
                        "{tag} {linker} weak_odr"
                    );
                    if let Some((llc_a, llc_b)) = &llc_sides {
                        let binary = directory.join(format!("wodr-{tag}-{linker}-llc"));
                        ok(
                            cc(flags)
                                .arg(&wodr_main)
                                .args([llc_a, llc_b])
                                .arg("-o")
                                .arg(&binary),
                            &directory,
                        );
                        assert_eq!(
                            ok(&mut Command::new(&binary), &directory).trim(),
                            "wodr=7",
                            "{tag} {linker} weak_odr llc"
                        );
                    }
                }
            }
        }
        eprintln!("L02-P13 ODR coalescing passed: {directory:?}");
    }

    // -------------------------------------------------------------------------
    // Hidden declarations bind inside the image
    // -------------------------------------------------------------------------

    const HIDDEN_DECLARATIONS: &str = r#"
declare hidden i64 @dh_provider()
declare i64 @dd_provider()

define i64 @call_dh() {
  %r = call i64 @dh_provider()
  ret i64 %r
}
define i64 @call_dd() {
  %r = call i64 @dd_provider()
  ret i64 %r
}
define ptr @addr_dh() {
  ret ptr @dh_provider
}
"#;

    const HIDDEN_DECLARATIONS_TWIN: &str = "\
        __attribute__((visibility(\"hidden\"))) long dh_provider(void);\n\
        long dd_provider(void);\n\
        long call_dh(void) { return dh_provider(); }\n\
        long call_dd(void) { return dd_provider(); }\n\
        void *addr_dh(void) { return (void *)dh_provider; }\n";

    /// Default-visibility C definitions of both providers.
    const PROVIDERS: &str = "long dh_provider(void) { return 7; }\n\
        long dd_provider(void) { return 8; }\n";

    const DECLARATION_DRIVER: &str = "#include <stdio.h>\n\
        long call_dh(void), call_dd(void);\n\
        void *addr_dh(void);\n\
        int main(void) {\n\
          long (*dh)(void) = (long (*)(void))addr_dh();\n\
          printf(\"dh=%ld dd=%ld addr_dh=%ld\\n\", call_dh(), call_dd(), dh());\n\
          return 0;\n\
        }\n";

    const DECLARATION_INTERPOSER: &str = "long dh_provider(void) { return 77; }\n\
        long dd_provider(void) { return 88; }\n";

    #[derive(Debug, PartialEq, Eq)]
    struct DeclarationObservation {
        exported_providers: BTreeSet<String>,
        plain: String,
        preloaded: String,
        links_without_provider: bool,
    }

    fn observe_declarations(
        leg: &Path,
        flags: &[String],
        object: &Path,
        providers: &Path,
    ) -> DeclarationObservation {
        let library = leg.join("libdecl.so");
        ok(
            cc(flags)
                .args(["-shared", "-Wl,-z,defs"])
                .arg(object)
                .arg(providers)
                .arg("-o")
                .arg(&library),
            leg,
        );
        let exported_providers = dynsym(&library, leg)
            .into_keys()
            .filter(|name| name.ends_with("_provider"))
            .collect();
        let interposer = leg.join("libinterpose.so");
        ok(
            cc(flags)
                .args(["-shared", "-fPIC", "-x", "c"])
                .arg(write(leg, "interposer.c", DECLARATION_INTERPOSER))
                .arg("-o")
                .arg(&interposer),
            leg,
        );
        let driver = leg.join("driver");
        ok(
            cc(flags)
                .arg(write(leg, "driver.c", DECLARATION_DRIVER))
                .arg(format!("-L{}", leg.display()))
                .arg("-ldecl")
                .arg(format!("-Wl,-rpath,{}", leg.display()))
                .arg("-o")
                .arg(&driver),
            leg,
        );
        let plain = ok(&mut Command::new(&driver), leg).trim().to_string();
        let preloaded = ok(Command::new(&driver).env("LD_PRELOAD", &interposer), leg)
            .trim()
            .to_string();
        // Without `-z defs` a shared object may leave a DEFAULT reference
        // undefined for the loader, but never a hidden one.
        let (links_without_provider, _, stderr) = run(cc(flags)
            .arg("-shared")
            .arg(object)
            .arg("-o")
            .arg(leg.join("libnoprovider.so")));
        assert!(
            links_without_provider || stderr.contains("dh_provider"),
            "{leg:?}: the refusal names the hidden reference: {stderr}"
        );
        DeclarationObservation {
            exported_providers,
            plain,
            preloaded,
            links_without_provider,
        }
    }

    /// A `declare hidden` function binds inside the `pic` shared object that
    /// links its (default-visibility C) definition: the merged symbol takes
    /// the reference's hidden visibility, so it is absent from `.dynsym` and
    /// an `LD_PRELOAD` interposer rebinds only the default declaration; and
    /// a shared object cannot leave the hidden reference undefined. A
    /// default-visibility-only twin module links without its provider.
    #[test]
    fn imported_hidden_declarations_bind_inside_the_image() {
        let linkers = linkers();
        let llc = llc();
        let directory = common::unique_temp_dir("l02p13-declarations");
        let providers = host_object(
            &directory,
            &write(&directory, "providers.c", PROVIDERS),
            &["-O2", "-fPIC"],
        );
        let twin = host_object(
            &directory,
            &write(&directory, "twin.c", HIDDEN_DECLARATIONS_TWIN),
            &["-O2", "-fPIC"],
        );
        let default_only = "define i64 @call_dd() {\n  %r = call i64 @dd_provider()\n  \
                            ret i64 %r\n}\ndeclare i64 @dd_provider()\n";
        for opt_level in OPT_LEVELS {
            let object = imported_object(
                &directory,
                &format!("declarations-{opt_level:?}.o"),
                HIDDEN_DECLARATIONS,
                opt_level,
                RelocationModel::Pic,
            );
            let default_object = imported_object(
                &directory,
                &format!("default-only-{opt_level:?}.o"),
                default_only,
                opt_level,
                RelocationModel::Pic,
            );
            let llc_declarations = llc.as_deref().map(|llc| {
                llc_object(
                    llc,
                    &directory,
                    &format!("declarations-{opt_level:?}-llc"),
                    HIDDEN_DECLARATIONS,
                    opt_level,
                    RelocationModel::Pic,
                )
            });
            for (linker, flags) in &linkers {
                let label = format!("{opt_level:?} {linker}");
                let leg = directory.join(format!("{opt_level:?}-{linker}"));
                let twin_leg = leg.join("twin");
                fs::create_dir_all(&twin_leg).expect("scratch");
                let imported = observe_declarations(&leg, flags, &object, &providers);
                assert_eq!(
                    imported,
                    DeclarationObservation {
                        exported_providers: BTreeSet::from(["dd_provider".to_string()]),
                        plain: "dh=7 dd=8 addr_dh=7".to_string(),
                        preloaded: "dh=7 dd=88 addr_dh=7".to_string(),
                        links_without_provider: false,
                    },
                    "{label}: imported hidden declaration"
                );
                assert_eq!(
                    imported,
                    observe_declarations(&twin_leg, flags, &twin, &providers),
                    "{label}: imported vs gcc twin"
                );
                if let Some(llc_declarations) = &llc_declarations {
                    let llc_leg = leg.join("llc");
                    fs::create_dir_all(&llc_leg).expect("scratch");
                    assert_eq!(
                        imported,
                        observe_declarations(&llc_leg, flags, llc_declarations, &providers),
                        "{label}: imported vs llc"
                    );
                }
                let (default_links, _, stderr) = run(cc(flags)
                    .arg("-shared")
                    .arg(&default_object)
                    .arg("-o")
                    .arg(leg.join("libdefault.so")));
                assert!(
                    default_links,
                    "{label}: a default declaration may stay undefined in a shared object: \
                     {stderr}"
                );
            }
        }
        eprintln!("L02-P13 hidden declarations passed: {directory:?}");
    }

    // -------------------------------------------------------------------------
    // Unreferenced hidden, protected and weak declarations
    // -------------------------------------------------------------------------

    /// Declarations nothing in the module references: hidden and protected
    /// functions and data the library's C object defines, and a weak
    /// function nothing defines.
    const UNREFERENCED_LIBRARY: &str = r#"
declare hidden i64 @tcg_helper()
@tcg_hdata = external hidden global i64
declare protected i64 @tcg_phelper()
declare extern_weak i64 @tcg_wnone()

define i64 @api(i64 %x) {
  %r = add i64 %x, 1
  ret i64 %r
}
"#;

    const UNREFERENCED_PROVIDERS: &str = "long tcg_hdata = 5;\n\
        long tcg_helper(void) { return 7; }\n\
        long tcg_phelper(void) { return 9; }\n\
        long call_helpers(void) { return tcg_helper() * 100 + tcg_phelper() * 10 + tcg_hdata; }\n";

    const UNREFERENCED_DRIVER: &str = "#define _GNU_SOURCE\n#include <dlfcn.h>\n\
        #include <stdio.h>\n\
        long api(long);\nlong call_helpers(void);\n\
        static const char *seen(const char *name) {\n\
          return dlsym(RTLD_DEFAULT, name) ? \"found\" : \"absent\";\n\
        }\n\
        int main(void) {\n\
          printf(\"api=%ld helpers=%ld helper=%s hdata=%s phelper=%s\\n\", api(1),\n\
                 call_helpers(), seen(\"tcg_helper\"), seen(\"tcg_hdata\"), seen(\"tcg_phelper\"));\n\
          return 0;\n\
        }\n";

    const UNREFERENCED_INTERPOSER: &str = "long tcg_helper(void) { return 1000; }\n\
        long tcg_phelper(void) { return 2000; }\n";

    /// What one library built from an imported or llc object shows: its
    /// `tcg_` dynamic symbols, the driver's line plain and under an
    /// `LD_PRELOAD` interposer, and whether an executable links the object
    /// without the providers.
    #[derive(Debug, PartialEq, Eq)]
    struct UnreferencedObservation {
        dynamic: BTreeMap<String, (String, String, String)>,
        plain: String,
        preloaded: String,
        links_without_providers: bool,
    }

    fn observe_unreferenced(
        leg: &Path,
        flags: &[String],
        object: &Path,
        providers: &Path,
        driver_source: &Path,
        interposer: &Path,
    ) -> UnreferencedObservation {
        fs::create_dir_all(leg).expect("scratch");
        let library = leg.join("libunref.so");
        ok(
            cc(flags)
                .arg("-shared")
                .arg(object)
                .arg(providers)
                .arg("-o")
                .arg(&library),
            leg,
        );
        let dynamic = dynsym(&library, leg)
            .into_iter()
            .filter(|(name, _)| name.starts_with("tcg_"))
            .collect();
        let driver = leg.join("driver");
        ok(
            cc(flags)
                .arg(driver_source)
                .arg(&library)
                .arg(format!("-Wl,-rpath,{}", leg.display()))
                .arg("-ldl")
                .arg("-o")
                .arg(&driver),
            leg,
        );
        let plain = ok(&mut Command::new(&driver), leg).trim().to_string();
        let preloaded = ok(Command::new(&driver).env("LD_PRELOAD", interposer), leg)
            .trim()
            .to_string();
        let (links_without_providers, _, _) = run(cc(flags)
            .arg(write(
                leg,
                "main.c",
                "long api(long);\nint main(void) { return (int)api(-1); }\n",
            ))
            .arg(object)
            .arg("-o")
            .arg(leg.join("no-providers")));
        UnreferencedObservation {
            dynamic,
            plain,
            preloaded,
            links_without_providers,
        }
    }

    /// llc writes a hidden, protected or `extern_weak` declaration as an
    /// undefined symbol with that fact even when nothing references it, so a
    /// hidden one takes the C definition in the same `pic` shared object out
    /// of `.dynsym` and binds the library's own call to it, and a protected
    /// one keeps the definition exported but binds the library's call: an
    /// `LD_PRELOAD` interposer rebinds neither (`helpers=795`). GNU ld refuses
    /// an executable that leaves the hidden symbols undefined; gold and LLD
    /// link it. The imported object, now written the same way, equals llc's
    /// at O0-O3 through GNU ld, gold and LLD; before, the importer wrote no
    /// symbol for these declarations, the library exported the hidden
    /// definitions and the interposer rebound its calls (`helpers=120005`).
    #[test]
    fn imported_unreferenced_declarations_bind_like_llc() {
        let linkers = linkers();
        let llc = llc();
        let directory = common::unique_temp_dir("l02p13-unreferenced");
        let providers = host_object(
            &directory,
            &write(&directory, "providers.c", UNREFERENCED_PROVIDERS),
            &["-O2", "-fPIC"],
        );
        let driver = write(&directory, "driver.c", UNREFERENCED_DRIVER);
        let interposer_source = write(&directory, "interposer.c", UNREFERENCED_INTERPOSER);
        for opt_level in OPT_LEVELS {
            let object = imported_object(
                &directory,
                &format!("unreferenced-{opt_level:?}.o"),
                UNREFERENCED_LIBRARY,
                opt_level,
                RelocationModel::Pic,
            );
            let llc_object = llc.as_deref().map(|llc| {
                llc_object(
                    llc,
                    &directory,
                    &format!("unreferenced-{opt_level:?}-llc"),
                    UNREFERENCED_LIBRARY,
                    opt_level,
                    RelocationModel::Pic,
                )
            });
            for (linker, flags) in &linkers {
                let label = format!("{opt_level:?} {linker}");
                let leg = directory.join(format!("{opt_level:?}-{linker}"));
                fs::create_dir_all(&leg).expect("scratch");
                let interposer = leg.join("libinterpose.so");
                ok(
                    cc(flags)
                        .args(["-shared", "-fPIC"])
                        .arg(&interposer_source)
                        .arg("-o")
                        .arg(&interposer),
                    &leg,
                );
                let imported = observe_unreferenced(
                    &leg.join("imported"),
                    flags,
                    &object,
                    &providers,
                    &driver,
                    &interposer,
                );
                assert_eq!(
                    (imported.plain.as_str(), imported.preloaded.as_str()),
                    (
                        "api=2 helpers=795 helper=absent hdata=absent phelper=found",
                        "api=2 helpers=795 helper=found hdata=absent phelper=found",
                    ),
                    "{label}: the hidden and protected declarations bind the library's calls"
                );
                assert!(
                    !imported.dynamic.contains_key("tcg_helper")
                        && !imported.dynamic.contains_key("tcg_hdata")
                        && imported
                            .dynamic
                            .get("tcg_phelper")
                            .is_some_and(|(_, visibility, _)| visibility == "PROTECTED"),
                    "{label}: .dynsym {:?}",
                    imported.dynamic
                );
                assert_eq!(
                    imported.links_without_providers,
                    *linker != "bfd",
                    "{label}: GNU ld alone refuses the undefined hidden symbols"
                );
                if let Some(llc_object) = &llc_object {
                    assert_eq!(
                        imported,
                        observe_unreferenced(
                            &leg.join("llc"),
                            flags,
                            llc_object,
                            &providers,
                            &driver,
                            &interposer,
                        ),
                        "{label}: imported vs llc"
                    );
                }
            }
        }
        eprintln!("L02-P13 unreferenced declarations passed: {directory:?}");
    }

    // -------------------------------------------------------------------------
    // @llvm.used retention under --gc-sections
    // -------------------------------------------------------------------------

    /// `@llvm.used` globals of every implicit kind, in an explicit dotted
    /// section and in a `__start_`/`__stop_` section, and a COMDAT one, each
    /// beside unlisted neighbours; one internal neighbour's slot names a
    /// function no object defines. The unlisted neighbours are hidden or
    /// internal, so a shared object does not export them and keeps none of
    /// them as a `--gc-sections` root (llc packs each kind's neighbours into
    /// one shared section, which an exported one would keep).
    const GC_RETENTION_MODULE: &str = r#"
$cu = comdat any

@ud = global i64 11, align 8
@md = hidden global i64 12, align 8
@ub = global i64 0, align 8
@mb = hidden global i64 0, align 8
@ur = constant i64 13, align 8
@mr = hidden constant i64 14, align 8
@ui = internal global i64 15, align 8
@mi = internal global [1 x ptr] [ptr @tcg_missing], align 8
@nu = global i64 21, section ".data.keep", align 8
@nm = hidden global i64 22, section ".data.keep", align 8
@su = internal global i64 4, section "tcgset", align 8
@sm1 = hidden global i64 1, section "tcgset", align 8
@sm2 = hidden global i64 2, section "tcgset", align 8
@cu = linkonce_odr global i64 31, comdat, align 8
@llvm.used = appending global [7 x ptr] [ptr @ud, ptr @ub, ptr @ur, ptr @ui, ptr @nu, ptr @su, ptr @cu], section "llvm.metadata"

declare void @tcg_missing()

define i64 @anchor() {
  ret i64 0
}
"#;

    /// Walks `tcgset` through the linker's `__start_`/`__stop_` symbols
    /// (weak: an empty walk when no `tcgset` section survives) and returns
    /// its members' values as decimal digits in walk order, so the order
    /// the linker concatenated the input sections in is read back too.
    const GC_SET_WALKER: &str = "\
        extern long __start_tcgset[] __attribute__((weak, visibility(\"hidden\")));\n\
        extern long __stop_tcgset[] __attribute__((weak, visibility(\"hidden\")));\n\
        long tcgset_walk(long *count) {\n\
          long seq = 0, n = 0;\n\
          for (long *p = __start_tcgset; p < __stop_tcgset; p++) { seq = seq * 10 + *p; n++; }\n\
          *count = n;\n\
          return seq;\n\
        }\n";

    const GC_DRIVER: &str = "#include <stdio.h>\n\
        long anchor(void);\nlong tcgset_walk(long *count);\n\
        int main(void) {\n\
          long n = 0, seq = tcgset_walk(&n);\n\
          printf(\"n=%ld seq=%ld anchor=%ld\\n\", n, seq, anchor());\n\
          return 0;\n\
        }\n";

    /// The globals of [`GC_RETENTION_MODULE`] whose presence in a linked
    /// image is read back.
    const GC_GLOBALS: [&str; 13] = [
        "ud", "md", "ub", "mb", "ur", "mr", "ui", "mi", "nu", "nm", "su", "sm1", "cu",
    ];

    /// Link `object` with the set walker under `--gc-sections` as `mode`
    /// (`static`: `-no-pie`; `pie`; `shared`: a library the driver links),
    /// run the driver, and return its line and the [`GC_GLOBALS`] the image
    /// keeps.
    fn observe_gc(
        leg: &Path,
        flags: &[String],
        mode: &str,
        object: &Path,
        walker: &Path,
        driver: &Path,
    ) -> (String, Vec<&'static str>) {
        fs::create_dir_all(leg).expect("scratch");
        let binary = leg.join("driver");
        let image = if mode == "shared" {
            let library = leg.join("libgc.so");
            ok(
                cc(flags)
                    .args(["-shared", "-Wl,--gc-sections"])
                    .arg(object)
                    .arg(walker)
                    .arg("-o")
                    .arg(&library),
                leg,
            );
            ok(
                cc(flags)
                    .arg(driver)
                    .arg(&library)
                    .arg(format!("-Wl,-rpath,{}", leg.display()))
                    .arg("-o")
                    .arg(&binary),
                leg,
            );
            library
        } else {
            ok(
                cc(flags)
                    .arg(if mode == "static" { "-no-pie" } else { "-pie" })
                    .arg("-Wl,--gc-sections")
                    .arg(driver)
                    .arg(object)
                    .arg(walker)
                    .arg("-o")
                    .arg(&binary),
                leg,
            );
            binary.clone()
        };
        let line = ok(&mut Command::new(&binary), leg).trim().to_string();
        let names: BTreeSet<String> = ok(Command::new("nm").arg(&image), leg)
            .lines()
            .filter_map(|line| line.split_whitespace().last().map(str::to_string))
            .collect();
        let kept = GC_GLOBALS
            .into_iter()
            .filter(|name| names.contains(*name))
            .collect();
        (line, kept)
    }

    /// Under `--gc-sections` a used global survives ALONE, as with llc: the
    /// unlisted neighbours of every kind go, the internal neighbour whose
    /// slot names an undefined function goes with that reference, so every
    /// image links and runs, and LLD's `__start_`/
    /// `__stop_` walk (start-stop-gc) sees the used set member alone
    /// (`n=1 seq=4`) where GNU ld and gold keep the set whole. The imported
    /// image equals llc's at O0-O3, static, PIE and shared, through all
    /// three linkers, the walk order included (GNU ld and gold walk the used
    /// member first, as llc creates its own section before the shared one).
    /// Before, `SHF_GNU_RETAIN` on the whole shared section kept every
    /// neighbour: the executables failed to link (`undefined reference to
    /// tcg_missing`), LLD walked `n=3`, and the unlisted globals survived.
    #[test]
    fn imported_used_globals_alone_survive_gc_sections_like_llc() {
        let linkers = linkers();
        let llc = llc();
        let directory = common::unique_temp_dir("l02p13-gc-retention");
        let walker = host_object(
            &directory,
            &write(&directory, "walker.c", GC_SET_WALKER),
            &["-O2", "-fPIC"],
        );
        let driver = write(&directory, "driver.c", GC_DRIVER);
        let used = ["ud", "ub", "ur", "ui", "nu", "su", "cu"];
        for opt_level in OPT_LEVELS {
            for (mode, model) in [
                ("static", RelocationModel::Static),
                ("pie", RelocationModel::Pie),
                ("shared", RelocationModel::Pic),
            ] {
                let object = imported_object(
                    &directory,
                    &format!("gc-{opt_level:?}-{mode}.o"),
                    GC_RETENTION_MODULE,
                    opt_level,
                    model,
                );
                let llc_object = llc.as_deref().map(|llc| {
                    llc_object(
                        llc,
                        &directory,
                        &format!("gc-{opt_level:?}-{mode}-llc"),
                        GC_RETENTION_MODULE,
                        opt_level,
                        model,
                    )
                });
                for (linker, flags) in &linkers {
                    let label = format!("{opt_level:?} {mode} {linker}");
                    let leg = directory.join(format!("{opt_level:?}-{mode}-{linker}"));
                    let (line, kept) = observe_gc(
                        &leg.join("imported"),
                        flags,
                        mode,
                        &object,
                        &walker,
                        &driver,
                    );
                    // llc creates `su`'s own `tcgset` section first and the
                    // shared one for `sm1` and `sm2` after it.
                    let walked = if *linker == "lld" {
                        "n=1 seq=4"
                    } else {
                        "n=3 seq=412"
                    };
                    assert_eq!(line, format!("{walked} anchor=0"), "{label}");
                    for name in used {
                        assert!(
                            kept.contains(&name),
                            "{label}: `{name}` is retained: {kept:?}"
                        );
                    }
                    for name in ["md", "mb", "mr", "mi", "nm"] {
                        assert!(
                            !kept.contains(&name),
                            "{label}: unlisted `{name}` is collected: {kept:?}"
                        );
                    }
                    if let Some(llc_object) = &llc_object {
                        assert_eq!(
                            (line, kept),
                            observe_gc(&leg.join("llc"), flags, mode, llc_object, &walker, &driver),
                            "{label}: imported vs llc"
                        );
                    }
                }
            }
        }
        eprintln!("L02-P13 used-global retention passed: {directory:?}");
    }

    // -------------------------------------------------------------------------
    // Section creation order: walks and constructor tables
    // -------------------------------------------------------------------------

    /// Walks `tcga`, `tcgb` and `tcgmix` of [`super::ORDER_MODULE`] through
    /// the linker's `__start_`/`__stop_` symbols, returning each set's
    /// members as decimal digits in walk order.
    const ORDER_WALKER: &str = "\
        #define WALK(set) \\\n\
          extern long __start_##set[] __attribute__((weak, visibility(\"hidden\"))); \\\n\
          extern long __stop_##set[] __attribute__((weak, visibility(\"hidden\"))); \\\n\
          long walk_##set(void) { \\\n\
            long seq = 0; \\\n\
            for (long *p = __start_##set; p < __stop_##set; p++) seq = seq * 10 + *p; \\\n\
            return seq; \\\n\
          }\n\
        WALK(tcga)\nWALK(tcgb)\nWALK(tcgmix)\n";

    const ORDER_DRIVER: &str = "#include <stdio.h>\n\
        long read_state(void);\nlong touch(void);\n\
        long walk_tcga(void);\nlong walk_tcgb(void);\nlong walk_tcgmix(void);\n\
        int main(void) {\n\
          printf(\"ctors=%ld tcga=%ld tcgb=%ld tcgmix=%ld touch=%ld\\n\", read_state(),\n\
                 walk_tcga(), walk_tcgb(), walk_tcgmix(), touch());\n\
          return 0;\n\
        }\n";

    /// Link `object` with the walker as `mode` (`static`: `-no-pie`; `pie`;
    /// `shared`: a library the driver links), with `--gc-sections` when
    /// `gc`, and return the driver's line.
    fn observe_order(
        leg: &Path,
        flags: &[String],
        mode: &str,
        gc: bool,
        object: &Path,
        walker: &Path,
        driver: &Path,
    ) -> String {
        fs::create_dir_all(leg).expect("scratch");
        let gc_flag: &[&str] = if gc { &["-Wl,--gc-sections"] } else { &[] };
        let binary = leg.join("driver");
        if mode == "shared" {
            let library = leg.join("liborder.so");
            ok(
                cc(flags)
                    .arg("-shared")
                    .args(gc_flag)
                    .arg(object)
                    .arg(walker)
                    .arg("-o")
                    .arg(&library),
                leg,
            );
            ok(
                cc(flags)
                    .arg(driver)
                    .arg(&library)
                    .arg(format!("-Wl,-rpath,{}", leg.display()))
                    .arg("-o")
                    .arg(&binary),
                leg,
            );
        } else {
            ok(
                cc(flags)
                    .arg(if mode == "static" { "-no-pie" } else { "-pie" })
                    .args(gc_flag)
                    .arg(driver)
                    .arg(object)
                    .arg(walker)
                    .arg("-o")
                    .arg(&binary),
                leg,
            );
        }
        ok(&mut Command::new(&binary), leg).trim().to_string()
    }

    /// The linker concatenates same-named input sections in object order, so
    /// llc's section creation order decides a `__start_`/`__stop_` walk and
    /// the run order of `.init_array` entries. The imported object walks
    /// `tcga` as 4, 1, 5 (COMDAT, ordinary, COMDAT), `tcgb` as 6, 2, 3
    /// (COMDAT, then the shared ordinary pair), `tcgmix` as 3, 7, 1, 8 (used,
    /// COMDAT, ordinary, used COMDAT) and runs the constructors a, b, c, d
    /// (COMDAT, the ordinary pair, COMDAT), exactly as llc's object does, at
    /// O0-O3, static, PIE and shared, with and without `--gc-sections`,
    /// through GNU ld, gold and LLD, and both objects' sections of each name
    /// carry the same members in the same order. Before, every COMDAT
    /// section followed the others: the walks read 145, 236 and 3178 and the
    /// constructors ran b, c, a, d.
    #[test]
    fn imported_placed_section_order_runs_like_llc() {
        let linkers = linkers();
        let llc = llc();
        let directory = common::unique_temp_dir("l02p13-section-order");
        let walker = host_object(
            &directory,
            &write(&directory, "walker.c", ORDER_WALKER),
            &["-O2", "-fPIC"],
        );
        let driver = write(&directory, "driver.c", ORDER_DRIVER);
        let expected = "ctors=1234 tcga=415 tcgb=623 tcgmix=3718 touch=37";
        for opt_level in OPT_LEVELS {
            for (mode, model) in [
                ("static", RelocationModel::Static),
                ("pie", RelocationModel::Pie),
                ("shared", RelocationModel::Pic),
            ] {
                let object = imported_object(
                    &directory,
                    &format!("order-{opt_level:?}-{mode}.o"),
                    ORDER_MODULE,
                    opt_level,
                    model,
                );
                let llc_object = llc.as_deref().map(|llc| {
                    llc_object(
                        llc,
                        &directory,
                        &format!("order-{opt_level:?}-{mode}-llc"),
                        ORDER_MODULE,
                        opt_level,
                        model,
                    )
                });
                if let Some(llc_object) = &llc_object {
                    let imported =
                        read_object_records(&fs::read(&object).expect("read")).expect("records");
                    let twin = read_object_records(&fs::read(llc_object).expect("read"))
                        .expect("llc records");
                    for (name, _) in expected_placed_order() {
                        assert_eq!(
                            placed_sections(&imported, name),
                            placed_sections(&twin, name),
                            "{opt_level:?} {mode}: the sections named `{name}`, imported vs llc"
                        );
                    }
                }
                for (linker, flags) in &linkers {
                    for gc in [false, true] {
                        let label = format!("{opt_level:?} {mode} {linker} gc={gc}");
                        let leg = directory.join(format!("{opt_level:?}-{mode}-{linker}-{gc}"));
                        let line = observe_order(
                            &leg.join("imported"),
                            flags,
                            mode,
                            gc,
                            &object,
                            &walker,
                            &driver,
                        );
                        assert_eq!(line, expected, "{label}");
                        if let Some(llc_object) = &llc_object {
                            assert_eq!(
                                line,
                                observe_order(
                                    &leg.join("llc"),
                                    flags,
                                    mode,
                                    gc,
                                    llc_object,
                                    &walker,
                                    &driver
                                ),
                                "{label}: imported vs llc"
                            );
                        }
                    }
                }
            }
        }
        eprintln!("L02-P13 section creation order passed: {directory:?}");
    }

    // -------------------------------------------------------------------------
    // x86-64 ELF retention under LLD --gc-sections
    // -------------------------------------------------------------------------

    /// The `ld.lld` the LLD legs use ([`linkers`]' lookup).
    fn lld() -> Option<PathBuf> {
        let found = std::env::var_os("TCG_LLD_DIR")
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|home| Path::new(&home).join(".local/bin")))
            .map(|dir| dir.join("ld.lld"))
            .filter(|path| path.is_file())
            .or_else(|| {
                std::env::var_os("PATH").and_then(|paths| {
                    std::env::split_paths(&paths)
                        .map(|dir| dir.join("ld.lld"))
                        .find(|path| path.is_file())
                })
            });
        if found.is_none() {
            assert!(
                std::env::var_os("TCG_REQUIRE_LLD").is_none(),
                "TCG_REQUIRE_LLD is set but no ld.lld was found"
            );
            eprintln!("SKIP: no ld.lld; the x86-64 LLD legs did not run");
        }
        found
    }

    /// Link the x86-64 ELF `object` by itself with LLD under
    /// `--gc-sections` (entry `anchor`, no C runtime) and return the
    /// [`super::X86_RETENTION_MODULE`] globals the image keeps. The image
    /// is not run: this AArch64 host only links and reads it.
    fn x86_gc_kept(lld: &Path, leg: &Path, object: &Path) -> Vec<&'static str> {
        fs::create_dir_all(leg).expect("scratch");
        let image = leg.join("image");
        ok(
            Command::new(lld)
                .args([
                    "-m",
                    "elf_x86_64",
                    "--gc-sections",
                    "-e",
                    "anchor",
                    "-static",
                ])
                .arg(object)
                .arg("-o")
                .arg(&image),
            leg,
        );
        let names: BTreeSet<String> = ok(Command::new("nm").arg(&image), leg)
            .lines()
            .filter_map(|line| line.split_whitespace().last().map(str::to_string))
            .collect();
        [
            "ud", "ud2", "md", "ur", "mr", "urel", "mrel", "ui", "mi", "anchor",
        ]
        .into_iter()
        .filter(|name| names.contains(*name))
        .collect()
    }

    /// The x86-64 ELF emitter's per-global retention, linked: with LLD
    /// `--gc-sections` the `@llvm.used` globals survive and every unlisted
    /// one is collected, with the slot naming an undefined function, so the
    /// image links, exactly as llc's x86-64 object at O0-O3 (static, the
    /// only x86-64 model here). A section that retained an unlisted
    /// neighbour would keep it, and its undefined reference would fail the
    /// link.
    #[test]
    fn imported_x86_64_used_globals_survive_lld_gc_sections_like_llc() {
        let Some(lld) = lld() else {
            return;
        };
        let llc = llc();
        let directory = common::unique_temp_dir("l02p13-x86-gc");
        for opt_level in OPT_LEVELS {
            let label = format!("{opt_level:?}");
            let object = write(
                &directory,
                &format!("x86-{opt_level:?}.o"),
                compile(
                    X86_RETENTION_MODULE,
                    X86_LINUX,
                    opt_level,
                    RelocationModel::Static,
                )
                .unwrap_or_else(|error| panic!("{label}: {error}")),
            );
            let leg = directory.join(format!("{opt_level:?}"));
            let kept = x86_gc_kept(&lld, &leg.join("imported"), &object);
            assert_eq!(
                kept,
                ["ud", "ud2", "ur", "urel", "ui", "anchor"],
                "{label}: kept"
            );
            if let Some(llc) = &llc {
                let source = write(
                    &directory,
                    &format!("x86-{opt_level:?}-llc.ll"),
                    X86_RETENTION_MODULE,
                );
                let llc_object = directory.join(format!("x86-{opt_level:?}-llc.o"));
                ok(
                    Command::new(llc)
                        .args([
                            "-mtriple=x86_64-unknown-linux-gnu",
                            "-filetype=obj",
                            "-relocation-model=static",
                            match opt_level {
                                OptLevel::O0 => "-O0",
                                OptLevel::O1 => "-O1",
                                OptLevel::O2 => "-O2",
                                OptLevel::O3 => "-O3",
                            },
                        ])
                        .arg(&source)
                        .arg("-o")
                        .arg(&llc_object),
                    &directory,
                );
                assert_eq!(
                    kept,
                    x86_gc_kept(&lld, &leg.join("llc"), &llc_object),
                    "{label}: imported vs llc"
                );
            }
        }
        eprintln!("L02-P13 x86-64 retention passed: {directory:?}");
    }

    // -------------------------------------------------------------------------
    // Declarations listed in @llvm.used
    // -------------------------------------------------------------------------

    const USED_DECLARATIONS_PROVIDER: &str = "long gd = 30;\nlong gae = 5;\nlong gh = 100;\n";

    const USED_DECLARATIONS_DRIVER: &str = "#include <stdio.h>\n\
        long get(void);\n\
        int main(void) {\n\
          printf(\"get=%ld\\n\", get());\n\
          return 0;\n\
        }\n";

    /// Link `object` with the provider as `mode` and return the driver's
    /// line.
    fn observe_used_declarations(
        leg: &Path,
        flags: &[String],
        mode: &str,
        object: &Path,
        provider: &Path,
        driver: &Path,
    ) -> String {
        fs::create_dir_all(leg).expect("scratch");
        let binary = leg.join("driver");
        if mode == "shared" {
            let library = leg.join("libused.so");
            ok(
                cc(flags)
                    .arg("-shared")
                    .arg(object)
                    .arg(provider)
                    .arg("-o")
                    .arg(&library),
                leg,
            );
            ok(
                cc(flags)
                    .arg(driver)
                    .arg(&library)
                    .arg(format!("-Wl,-rpath,{}", leg.display()))
                    .arg("-o")
                    .arg(&binary),
                leg,
            );
        } else {
            ok(
                cc(flags)
                    .arg(if mode == "static" { "-no-pie" } else { "-pie" })
                    .arg(driver)
                    .arg(object)
                    .arg(provider)
                    .arg("-o")
                    .arg(&binary),
                leg,
            );
        }
        ok(&mut Command::new(&binary), leg).trim().to_string()
    }

    /// Global declarations listed in `@llvm.used` compile and link as llc's
    /// object does: the referenced ones (default, `available_externally`
    /// and hidden) bind to the C provider, the unreferenced ones (which no
    /// object defines) are not in either object's symbol table, and the
    /// `extern_weak` one is a weak undefined symbol in both, so every image
    /// links and returns 135 at O0-O3, static, PIE and shared, through GNU
    /// ld, gold and LLD. Before, the import was refused.
    #[test]
    fn imported_used_declarations_link_like_llc() {
        let linkers = linkers();
        let llc = llc();
        let directory = common::unique_temp_dir("l02p13-used-declarations");
        let provider = host_object(
            &directory,
            &write(&directory, "provider.c", USED_DECLARATIONS_PROVIDER),
            &["-O2", "-fPIC"],
        );
        let driver = write(&directory, "driver.c", USED_DECLARATIONS_DRIVER);
        for opt_level in OPT_LEVELS {
            for (mode, model) in [
                ("static", RelocationModel::Static),
                ("pie", RelocationModel::Pie),
                ("shared", RelocationModel::Pic),
            ] {
                let object = imported_object(
                    &directory,
                    &format!("used-{opt_level:?}-{mode}.o"),
                    USED_DECLARATIONS_MODULE,
                    opt_level,
                    model,
                );
                let llc_object = llc.as_deref().map(|llc| {
                    llc_object(
                        llc,
                        &directory,
                        &format!("used-{opt_level:?}-{mode}-llc"),
                        USED_DECLARATIONS_MODULE,
                        opt_level,
                        model,
                    )
                });
                if let Some(llc_object) = &llc_object {
                    // Every named undefined symbol: `(name, binding,
                    // visibility)`.
                    let undefined = |path: &Path| -> BTreeSet<(String, u8, u8)> {
                        read_object_records(&fs::read(path).expect("read"))
                            .expect("records")
                            .symbols
                            .iter()
                            .filter(|symbol| !symbol.name.is_empty() && symbol.section_index == 0)
                            .map(|symbol| (symbol.name.clone(), symbol.binding, symbol.visibility))
                            .collect()
                    };
                    assert_eq!(
                        undefined(&object),
                        undefined(llc_object),
                        "{opt_level:?} {mode}: undefined symbols, imported vs llc"
                    );
                }
                for (linker, flags) in &linkers {
                    let label = format!("{opt_level:?} {mode} {linker}");
                    let leg = directory.join(format!("{opt_level:?}-{mode}-{linker}"));
                    let line = observe_used_declarations(
                        &leg.join("imported"),
                        flags,
                        mode,
                        &object,
                        &provider,
                        &driver,
                    );
                    assert_eq!(line, "get=135", "{label}");
                    if let Some(llc_object) = &llc_object {
                        assert_eq!(
                            line,
                            observe_used_declarations(
                                &leg.join("llc"),
                                flags,
                                mode,
                                llc_object,
                                &provider,
                                &driver
                            ),
                            "{label}: imported vs llc"
                        );
                    }
                }
            }
        }
        eprintln!("L02-P13 used declarations passed: {directory:?}");
    }

    // -------------------------------------------------------------------------
    // extern_weak and available_externally are declarations
    // -------------------------------------------------------------------------

    const DECLARATION_FORMS: &str = r#"
declare extern_weak i64 @maybe()

define available_externally i64 @ae_answer() {
  ret i64 42
}

define i64 @probe_maybe() {
entry:
  %slot = alloca ptr, align 8
  store ptr @maybe, ptr %slot, align 8
  %fp = load ptr, ptr %slot, align 8
  %present = icmp ne ptr %fp, null
  br i1 %present, label %yes, label %no
yes:
  %r = call i64 %fp()
  ret i64 %r
no:
  ret i64 -1
}

define i64 @probe_direct() {
entry:
  %present = icmp ne ptr @maybe, null
  br i1 %present, label %yes, label %no
yes:
  %r = call i64 @maybe()
  ret i64 %r
no:
  ret i64 -1
}

define i64 @use_ae() {
  %r = call i64 @ae_answer()
  ret i64 %r
}
"#;

    /// The gcc twin: a weak declaration and a C99 inline definition (which,
    /// like `available_externally`, is not an external definition).
    const DECLARATION_FORMS_TWIN: &str = "\
        extern long maybe(void) __attribute__((weak));\n\
        inline long ae_answer(void) { return 42; }\n\
        long probe_maybe(void) {\n\
          long (*volatile fp)(void) = maybe;\n\
          return fp ? fp() : -1;\n\
        }\n\
        long probe_direct(void) { return maybe ? maybe() : -1; }\n\
        long use_ae(void) { return ae_answer(); }\n";

    const FORMS_MAIN: &str = "#include <stdio.h>\n\
        long probe_maybe(void), probe_direct(void), use_ae(void);\n\
        int main(void) {\n\
          printf(\"maybe=%ld direct=%ld ae=%ld\\n\", probe_maybe(), probe_direct(), use_ae());\n\
          return 0;\n\
        }\n";

    /// An `extern_weak` function reads null when nothing defines it and is
    /// called when something does, through a stored pointer and through
    /// clang's null-guarded direct call (imported as a call through its
    /// address). The declaration comes first: the importer still refuses a
    /// function address used before its declaring line. An
    /// `available_externally` function is never defined here, so it links
    /// against the external definition instead of colliding with it, and (at
    /// O0, where the call stays) it cannot link without one. The gcc twin
    /// agrees on every run.
    #[test]
    fn imported_extern_weak_and_available_externally_are_declarations() {
        let linkers = linkers();
        let llc = llc();
        let directory = common::unique_temp_dir("l02p13-forms");
        let main = write(&directory, "main.c", FORMS_MAIN);
        let ae_provider = host_object(
            &directory,
            &write(
                &directory,
                "ae_provider.c",
                "long ae_answer(void) { return 42; }\n",
            ),
            &["-O2"],
        );
        let maybe_provider = host_object(
            &directory,
            &write(
                &directory,
                "maybe_provider.c",
                "long maybe(void) { return 5; }\n",
            ),
            &["-O2"],
        );
        let twin = host_object(
            &directory,
            &write(&directory, "twin.c", DECLARATION_FORMS_TWIN),
            &["-std=gnu11", "-O0"],
        );
        for opt_level in OPT_LEVELS {
            let object = imported_object(
                &directory,
                &format!("forms-{opt_level:?}.o"),
                DECLARATION_FORMS,
                opt_level,
                RelocationModel::Pie,
            );
            let records =
                read_object_records(&fs::read(&object).expect("object")).expect("ELF records");
            let symbols = elf_symbols(&records);
            assert_eq!(
                unique_symbol(&symbols, "maybe").map(|(bind, _, ndx)| (*bind, ndx.as_str())),
                Some((STB_WEAK, "UND")),
                "{opt_level:?}: `maybe` is a weak reference"
            );
            assert!(
                unique_symbol(&symbols, "ae_answer").is_none_or(|(_, _, ndx)| ndx == "UND"),
                "{opt_level:?}: `ae_answer` is never defined: {:?}",
                symbols.get("ae_answer")
            );
            let llc_forms = llc.as_deref().map(|llc| {
                llc_object(
                    llc,
                    &directory,
                    &format!("forms-{opt_level:?}-llc"),
                    DECLARATION_FORMS,
                    opt_level,
                    RelocationModel::Pie,
                )
            });
            for (linker, flags) in &linkers {
                let mut arms = vec![("imported", &object), ("twin", &twin)];
                arms.extend(llc_forms.iter().map(|llc_forms| ("llc", llc_forms)));
                for (arm, subject) in arms {
                    let label = format!("{opt_level:?} {linker} {arm}");
                    let run_with = |extra: &[&PathBuf], name: &str| {
                        let binary = directory.join(format!("{name}-{opt_level:?}-{linker}-{arm}"));
                        ok(
                            cc(flags)
                                .arg(&main)
                                .arg(subject)
                                .args(extra)
                                .arg("-o")
                                .arg(&binary),
                            &directory,
                        );
                        ok(&mut Command::new(&binary), &directory)
                            .trim()
                            .to_string()
                    };
                    assert_eq!(
                        run_with(&[&ae_provider], "without-maybe"),
                        "maybe=-1 direct=-1 ae=42",
                        "{label}: a missing weak definition reads null"
                    );
                    assert_eq!(
                        run_with(&[&ae_provider, &maybe_provider], "with-maybe"),
                        "maybe=5 direct=5 ae=42",
                        "{label}: a linked weak definition is called"
                    );
                    if opt_level == OptLevel::O0 {
                        let (linked, _, stderr) = run(cc(flags)
                            .arg(&main)
                            .arg(subject)
                            .arg("-o")
                            .arg(directory.join(format!("no-ae-{linker}-{arm}"))));
                        assert!(
                            !linked && stderr.contains("ae_answer"),
                            "{label}: an `available_externally` body is no definition: {stderr}"
                        );
                    }
                }
            }
        }
        eprintln!("L02-P13 declaration forms passed: {directory:?}");
    }

    // -------------------------------------------------------------------------
    // Calls of a defined extern_weak function pass arguments like direct calls
    // -------------------------------------------------------------------------

    /// The C type of an argument spelling of [`weak_call_module`].
    fn weak_call_c_type(ty: &str) -> &'static str {
        match ty {
            "i1" => "_Bool",
            "ptr" => "long *",
            "i8" => "signed char",
            "i16" => "short",
            "i32" => "int",
            "i64" => "long",
            "i128" => "__int128",
            "double" => "double",
            "float" => "float",
            other => panic!("no C type for `{other}`"),
        }
    }

    /// Argument `index` of [`weak_call_llvm_argument`] computed from `x` in C.
    fn weak_call_c_argument(ty: &str, index: usize) -> String {
        let k = index + 1;
        match ty {
            "i128" => format!("((((__int128)(unsigned long)x) << 64) | {})", 3 * k + 1),
            "i8" | "i16" | "i32" => format!("({})(x + {})", weak_call_c_type(ty), 5 * k),
            "i1" => format!("(x > {})", 5 * k),
            "ptr" => format!("&gvals[{}]", k % 16),
            "i64" => format!("(x + {})", 11 * k),
            _ => format!("({})(x + {k})", weak_call_c_type(ty)),
        }
    }

    /// The C parameter list of `params` and a checksum of every parameter
    /// that reads both halves of a 128-bit integer.
    fn weak_call_c_signature(params: &[&str]) -> (String, String) {
        let list = params
            .iter()
            .enumerate()
            .map(|(index, ty)| format!("{} p{index}", weak_call_c_type(ty)))
            .collect::<Vec<_>>()
            .join(", ");
        let checksum = params
            .iter()
            .enumerate()
            .map(|(index, ty)| {
                let k = index + 1;
                match *ty {
                    "i128" => format!(
                        "(long)(p{index} >> 64) * {} + (long)(p{index} & 0xffffffff) * {}",
                        7 * k,
                        13 * k
                    ),
                    "double" | "float" => format!("(long)(p{index} * 3.0) * {k}"),
                    "ptr" => format!("*p{index} * {k}"),
                    _ => format!("(long)p{index} * {}", 17 * k),
                }
            })
            .collect::<Vec<_>>()
            .join(" + ");
        (list, checksum)
    }

    /// Defines the `gvals` that pointer arguments address.
    const WEAK_CALL_MAIN: &str = "#include <stdio.h>\n\
        long gvals[16] = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59};\n\
        long call_weak(long), call_strong(long);\n\
        int main(void) {\n\
          printf(\"weak=%ld strong=%ld\\n\", call_weak(42), call_strong(42));\n\
          return 0;\n\
        }\n";

    /// A null-guarded direct call of a defined `extern_weak` function, which
    /// the importer respells as a call through its address, passes every
    /// admitted signature's arguments exactly like the direct call of an
    /// ordinary declaration with the same signature and like the gcc `-O0`
    /// twin (`if (wf) wf(...)`): register-pair 128-bit integers (also after
    /// a pointer, `i1`, `i16`, `i32`, `i8` and `i64`), stack-passed
    /// floating-point, narrow integer, `i1` and pointer arguments. The C
    /// definitions read both halves of every 128-bit integer and the value
    /// behind every pointer. Without a definition of `wf`
    /// the guard reads null in both. (The stack-passed 128-bit shapes are
    /// refused at import; see
    /// `weak_calls_the_indirect_lowering_would_change_are_refused_by_name`.)
    #[test]
    fn imported_weak_calls_pass_arguments_like_direct_calls() {
        let linkers = linkers();
        let llc = llc();
        let directory = common::unique_temp_dir("l02p13-weak-calls");
        let main = write(&directory, "main.c", WEAK_CALL_MAIN);
        for (row, params) in WEAK_CALL_ADMITTED_SIGNATURES.iter().enumerate() {
            let (list, checksum) = weak_call_c_signature(params);
            let arguments = params
                .iter()
                .enumerate()
                .map(|(index, ty)| weak_call_c_argument(ty, index))
                .collect::<Vec<_>>()
                .join(", ");
            let wf = host_object(
                &directory,
                &write(
                    &directory,
                    &format!("wf{row}.c"),
                    format!("long wf({list}) {{ return {checksum}; }}\n"),
                ),
                &["-O2"],
            );
            let sf = host_object(
                &directory,
                &write(
                    &directory,
                    &format!("sf{row}.c"),
                    format!("long sf({list}) {{ return {checksum}; }}\n"),
                ),
                &["-O2"],
            );
            let twin = host_object(
                &directory,
                &write(
                    &directory,
                    &format!("twin{row}.c"),
                    format!(
                        "extern long gvals[16];\n\
                         extern long wf({list}) __attribute__((weak));\n\
                         extern long sf({list});\n\
                         long call_weak(long x) {{ if (wf) return wf({arguments}); return -1; }}\n\
                         long call_strong(long x) {{ return sf({arguments}); }}\n"
                    ),
                ),
                &["-O0"],
            );
            let src = weak_call_module(params);
            let objects: Vec<(String, PathBuf)> = OPT_LEVELS
                .iter()
                .map(|opt_level| {
                    (
                        format!("{opt_level:?}"),
                        imported_object(
                            &directory,
                            &format!("weak{row}-{opt_level:?}.o"),
                            &src,
                            *opt_level,
                            RelocationModel::Pie,
                        ),
                    )
                })
                .collect();
            let llc_objects: Vec<(String, PathBuf)> = llc
                .as_deref()
                .map(|llc| {
                    OPT_LEVELS
                        .iter()
                        .map(|opt_level| {
                            (
                                format!("llc-{opt_level:?}"),
                                llc_object(
                                    llc,
                                    &directory,
                                    &format!("weak{row}-{opt_level:?}-llc"),
                                    &src,
                                    *opt_level,
                                    RelocationModel::Pie,
                                ),
                            )
                        })
                        .collect()
                })
                .unwrap_or_default();
            for (linker, flags) in &linkers {
                let run_with = |subject: &PathBuf, extra: &[&PathBuf], name: &str| {
                    let binary = directory.join(format!("{name}-{row}-{linker}"));
                    ok(
                        cc(flags)
                            .arg(&main)
                            .arg(subject)
                            .args(extra)
                            .arg("-o")
                            .arg(&binary),
                        &directory,
                    );
                    ok(&mut Command::new(&binary), &directory)
                        .trim()
                        .to_string()
                };
                let expected = run_with(&twin, &[&wf, &sf], "twin");
                let value = expected
                    .strip_prefix("weak=")
                    .and_then(|rest| rest.split_once(" strong="))
                    .filter(|(weak, strong)| weak == strong)
                    .map(|(weak, _)| weak.to_string())
                    .unwrap_or_else(|| panic!("{params:?} {linker}: twin printed {expected}"));
                assert_eq!(
                    run_with(&twin, &[&sf], "twin-null"),
                    format!("weak=-1 strong={value}"),
                    "{params:?} {linker}: the twin's guard reads null"
                );
                for (level, object) in objects.iter().chain(&llc_objects) {
                    let label = format!("{params:?} {level} {linker}");
                    assert_eq!(
                        run_with(object, &[&wf, &sf], &format!("imported-{level}")),
                        expected,
                        "{label}: the call through the weak address passes what the direct \
                         call, the gcc twin and llc pass"
                    );
                    assert_eq!(
                        run_with(object, &[&sf], &format!("imported-null-{level}")),
                        format!("weak=-1 strong={value}"),
                        "{label}: a missing weak definition reads null"
                    );
                }
            }
        }
        eprintln!("L02-P13 weak calls passed: {directory:?}");
    }

    // -------------------------------------------------------------------------
    // Integer literals read at their type's width
    // -------------------------------------------------------------------------

    /// The C driver of [`INTEGER_LITERALS_MODULE`] and the line llc 22.1.2's
    /// objects print at O0-O3 ([`INTEGER_LITERALS_LINE`]).
    const INTEGER_LITERALS_DRIVER: &str = "#include <stdio.h>\n#include <stdint.h>\n\
    uint64_t h(uint64_t x) { return x; }\n\
    extern uint64_t f_ret(void);\nextern void f_store(uint64_t *);\nextern uint64_t f_phi(int);\n\
    extern int f_cmp(uint64_t);\nextern uint64_t f_arg(void);\nextern uint64_t f_add(uint64_t);\n\
    extern int32_t r32(void);\nextern int16_t r16(void);\nextern int8_t r8(void);\n\
    extern long *gep_back(long *);\nextern long *gep_struct(long *);\n\
    extern char *gep_const(void);\nextern char *bytes_addr(void);\nlong arr[4] = {1, 2, 3, 4};\n\
    extern long *i1_gep_arr(long *);\nextern long *i1_gep_struct(long *);\n\
    extern char *i1_gep_const(void);\nextern char *i1_gep_const_true(void);\n\
    extern char *i1_gep_true(char *);\n\
    extern long *i1_gep_dyn(long *, long);\nextern long *i1_gep_struct_dyn(long *, long);\n\
    extern long *gep_wrap(long *);\nextern long sw64(uint64_t);\nextern int sw32(uint32_t);\n\
    extern int sw8(uint8_t);\nextern int sw1(long);\nextern int sw1_lit(long);\n\
    extern uint64_t load_c64(void);\nextern int load_c8(void), load_c1(void), load_c1m(void);\n\
    extern int agg_byte0(void), agg_bool(void);\n\
    extern int zext_i1_2(void), zext_i1_3(void), zext_i1_m1(void), sext_i1_1(void);\n\
    extern long sext_i1_dyn(long);\nextern int br_i1_2(void);\nextern int sel_i1_3(int, int);\n\
    extern int r8_300(void), r8_m129(void);\nextern long r32_wide(void);\n\
    extern uint64_t r64_wide(void);\nextern long alloca_i8(uint8_t);\nextern long alloca_i8_lit(void);\n\
    extern long *i1_gep_false(long *);\nextern long *i1_gep_struct_false(long *);\n\
    extern char *i1_gep_const_false(void);\nextern long alloca_i1_true(void), alloca_i8_neg(void);\n\
    extern long alloca_arr_neg(void);\nextern char *bytes_outer(long);\n\
    extern unsigned char a8[2];\nextern unsigned short a16[3];\n\
    extern long *gep_wrap_up(long *), *gep_wrap_neg(long *), *gep_wrap_struct(long *);\n\
    extern long *gep_wrap_const(void);\nextern char *gep_wrap_sum(char *);\n\
    extern long *gep_const_field(void);\n\
    long sum_bytes(const unsigned char *p, long n) {\n  long s = 0;\n\
      for (long i = 0; i < n; i++) s += p[i];\n  return s;\n}\n\
    int main(void) {\n  uint64_t s = 0;\n  char buf[4] = {'w', 'x', 'y', 'z'};\n  f_store(&s);\n\
      printf(\"ret=%lx store=%lx phi1=%lx phi0=%lx cmp=%d/%d arg=%lx add=%lx r32=%d r16=%d r8=%d \"\n\
             \"gep=%ld gep_struct=%ld gep_const=%d\", (unsigned long)f_ret(), (unsigned long)s,\n\
             (unsigned long)f_phi(1), (unsigned long)f_phi(0), f_cmp(0xFADE000000000000ull), f_cmp(5),\n\
             (unsigned long)f_arg(), (unsigned long)f_add(1), r32(), r16(), r8(),\n\
             *gep_back(&arr[2]), *gep_struct(&arr[2]), gep_const() == bytes_addr() - 1);\n\
      printf(\" i1_gep=%ld i1_struct=%ld i1_const=%d/%d i1_true=%d i1_dyn=%ld/%ld i1_sdyn=%ld/%ld \"\n\
             \"wrap=%ld\", *i1_gep_arr(&arr[2]), *i1_gep_struct(&arr[2]),\n\
             i1_gep_const() == bytes_addr() - 1, i1_gep_const_true() == bytes_addr() - 1,\n\
             i1_gep_true(&buf[2]) == &buf[1],\n\
             *i1_gep_dyn(&arr[2], 1), *i1_gep_dyn(&arr[2], 0), *i1_gep_struct_dyn(&arr[2], 1),\n\
             *i1_gep_struct_dyn(&arr[2], 0), *gep_wrap(&arr[2]));\n\
      printf(\" sw64=%ld/%ld sw32=%d/%d sw8=%d/%d sw1=%d/%d sw1_lit=%d/%d\",\n\
             sw64(0xFADE000000000000ull), sw64(5), sw32(0xFFFFFFFFu), sw32(5), sw8(255), sw8(5),\n\
             sw1(1), sw1(0), sw1_lit(1), sw1_lit(0));\n\
      printf(\" c64=%lx c8=%d c1=%d/%d agg0=%d aggb=%d\", (unsigned long)load_c64(), load_c8(),\n\
             load_c1(), load_c1m(), agg_byte0(), agg_bool());\n\
      printf(\" z2=%d z3=%d zm1=%d s1=%d sdyn=%ld/%ld br2=%d sel3=%d\", zext_i1_2(), zext_i1_3(),\n\
             zext_i1_m1(), sext_i1_1(), sext_i1_dyn(1), sext_i1_dyn(0), br_i1_2(), sel_i1_3(10, 20));\n\
      printf(\" r8_300=%d r8_m129=%d r32_wide=%ld r64_wide=%lx alloca=%ld alloca_lit=%ld\",\n\
             r8_300(), r8_m129(), r32_wide(), (unsigned long)r64_wide(), alloca_i8(200),\n\
             alloca_i8_lit());\n\
      printf(\" i1_false=%ld/%ld/%d alloca_i1=%ld alloca_neg=%ld/%ld a8=%d/%d a16=%d/%d/%d \"\n\
             \"wrap_up=%ld wrap_neg=%ld wrap_struct=%ld wrap_const=%ld wrap_sum=%lx outer=%c \"\n\
             \"const_field=%ld\\n\",\n\
             *i1_gep_false(&arr[2]), *i1_gep_struct_false(&arr[2]),\n\
             i1_gep_const_false() == bytes_addr(), alloca_i1_true(), alloca_i8_neg(),\n\
             alloca_arr_neg(), a8[0], a8[1], a16[0], a16[1], a16[2], *gep_wrap_up(&arr[1]),\n\
             *gep_wrap_neg(&arr[1]), *gep_wrap_struct(&arr[0]), *gep_wrap_const(),\n\
             (unsigned long)((uintptr_t)gep_wrap_sum((char *)arr) - (uintptr_t)arr),\n\
             *bytes_outer(1), *gep_const_field());\n\
      return 0;\n}\n";

    const INTEGER_LITERALS_LINE: &str = "ret=fade000000000000 store=fade000000000000 \
        phi1=fade000000000000 phi0=3 cmp=1/0 arg=fade000000000000 add=fade000000000001 r32=-1 r16=-1 \
        r8=-1 gep=2 gep_struct=2 gep_const=1 i1_gep=2 i1_struct=2 i1_const=1/1 i1_true=1 i1_dyn=2/3 \
        i1_sdyn=2/4 wrap=2 sw64=1/0 sw32=1/0 sw8=1/0 sw1=1/0 sw1_lit=1/0 c64=fade000000000000 c8=255 \
        c1=0/1 agg0=1 aggb=7 z2=0 z3=1 zm1=1 s1=-1 sdyn=-1/0 br2=0 sel3=10 r8_300=44 r8_m129=127 \
        r32_wide=7 r64_wide=5 alloca=200 alloca_lit=200 i1_false=3/4/1 alloca_i1=77 \
        alloca_neg=200/800 a8=44/1 a16=65535/65535/1 wrap_up=3 wrap_neg=3 wrap_struct=4 wrap_const=11 \
        wrap_sum=7ffffffffffffff0 outer=b const_field=22";

    /// [`INTEGER_LITERALS_MODULE`] runs as llc's object does: every
    /// function's literal is the value LLVM reads (`0xfade000000000000`,
    /// -1, one element back), not `@g`'s address, at O0-O3, linked
    /// `-no-pie` with GNU ld, gold and LLD.
    #[test]
    fn imported_integer_literals_run_like_llc() {
        let linkers = linkers();
        let llc = llc();
        let directory = common::unique_temp_dir("l02p13-integer-literals");
        let driver = host_object(
            &directory,
            &write(&directory, "driver.c", INTEGER_LITERALS_DRIVER),
            &["-O0", "-fno-pic"],
        );
        for opt_level in OPT_LEVELS {
            let object = imported_object(
                &directory,
                &format!("literals-{opt_level:?}.o"),
                INTEGER_LITERALS_MODULE,
                opt_level,
                RelocationModel::Static,
            );
            let twin = llc.as_deref().map(|llc| {
                llc_object(
                    llc,
                    &directory,
                    &format!("literals-{opt_level:?}-llc"),
                    INTEGER_LITERALS_MODULE,
                    opt_level,
                    RelocationModel::Static,
                )
            });
            for (linker, flags) in &linkers {
                for (who, subject) in std::iter::once(("imported", &object))
                    .chain(twin.iter().map(|twin| ("llc", twin)))
                {
                    let binary = directory.join(format!("{who}-{opt_level:?}-{linker}"));
                    ok(
                        cc(flags)
                            .arg("-no-pie")
                            .arg(&driver)
                            .arg(subject)
                            .arg("-o")
                            .arg(&binary),
                        &directory,
                    );
                    assert_eq!(
                        ok(&mut Command::new(&binary), &directory).trim(),
                        INTEGER_LITERALS_LINE,
                        "{who} {opt_level:?} {linker}"
                    );
                }
            }
        }
        eprintln!("L02-P13 integer literals passed: {directory:?}");
    }

    // -------------------------------------------------------------------------
    // `dso_local` declarations under the `static` relocation model
    // -------------------------------------------------------------------------

    /// `dso_local` declarations of a data and a function symbol, every
    /// address form the importer refuses with no model known.
    const STATIC_DSO_LOCAL_MODULE: &str = "@s = external dso_local global i64, align 8\n\
        declare dso_local i64 @f()\n\
        define i64 @read_s() {\n  %v = load i64, ptr @s, align 8\n  ret i64 %v\n}\n\
        define void @write_s(i64 %x) {\n  store i64 %x, ptr @s, align 8\n  ret void\n}\n\
        define ptr @addr_s() {\n  ret ptr @s\n}\n\
        define ptr @addr_s4() {\n  ret ptr getelementptr inbounds (i8, ptr @s, i64 4)\n}\n\
        define ptr @addr_f() {\n  ret ptr @f\n}\n\
        define i64 @call_f() {\n  %r = call i64 @f()\n  ret i64 %r\n}\n";

    /// rustc's `-C relocation-model=static` output for a `no_std` crate
    /// whose `read_ext` reads `extern { static ext_data: i64; }` (trustc
    /// `--emit=llvm-ir -C opt-level=2`, the fourth verifier round's
    /// module), its functions and declarations as written.
    const RUSTC_STATIC_MODULE: &str = "target triple = \"aarch64-unknown-linux-gnu\"\n\
        @ext_data = external dso_local local_unnamed_addr global i64\n\
        define dso_local noundef i64 @read_ext() unnamed_addr #1 {\n\
        start:\n  %_1 = load i64, ptr @ext_data, align 8, !noundef !3\n\
        \x20 %_0 = add i64 %_1, 1\n  ret i64 %_0\n}\n\
        attributes #1 = { mustprogress nofree norecurse nosync nounwind willreturn memory(read, \
        argmem: none, inaccessiblemem: none, target_mem0: none, target_mem1: none) uwtable \
        \"frame-pointer\"=\"non-leaf\" \"probe-stack\"=\"inline-asm\" \"target-cpu\"=\"generic\" \
        \"target-features\"=\"+v8a,+outline-atomics\" }\n\
        !llvm.module.flags = !{!0, !1}\n\
        !0 = !{i32 7, !\"uwtable\", i32 2}\n\
        !1 = !{i32 7, !\"frame-pointer\", i32 1}\n\
        !3 = !{}\n";

    /// The definitions, `V` (empty unless defined, as for the protected
    /// library) the symbols' visibility.
    const STATIC_DSO_LOCAL_DEFINITIONS: &str = "#ifndef V\n#define V\n#endif\n\
        V long s = 12;\nV long ext_data = 41;\n\
        V long f(void) { return 7; }\n\
        long *lib_addr_s(void) { return &s; }\n\
        long (*lib_addr_f(void))(void) { return f; }\n\
        long lib_get_s(void) { return s; }\n";

    const STATIC_DSO_LOCAL_INTERPOSER: &str =
        "long s = 1005;\nlong ext_data = 1004;\nlong f(void) { return 1005; }\n";

    /// Calls the modules and the definitions' accessors. Built three ways
    /// ([`STATIC_DSO_LOCAL_DRIVERS`]): `-fno-pic` naming none of `s`, `f`
    /// and `ext_data`, so every reference to them in the executable is the
    /// module's; and, with `NAMES`, taking `&s` and `f` itself, `-fno-pic`
    /// (non-PIC references, as other `static`-model code makes) and `-fPIE`
    /// (through the GOT).
    const STATIC_DSO_LOCAL_DRIVER: &str = "#include <stdio.h>\n\
        extern long *lib_addr_s(void);\nextern long (*lib_addr_f(void))(void);\n\
        extern long lib_get_s(void);\nextern long read_s(void);\nextern void write_s(long);\n\
        extern long *addr_s(void);\nextern char *addr_s4(void);\n\
        extern long (*addr_f(void))(void);\nextern long call_f(void);\n\
        extern long read_ext(void);\n\
        #ifdef NAMES\nextern long s;\nextern long f(void);\n#endif\n\
        int main(void) {\n  long r = read_s();\n  write_s(77);\n  long g = lib_get_s();\n\
          printf(\"read=%ld lib_after_write=%ld addr_eq=%d addr4_eq=%d faddr_eq=%d \
        call_addr=%ld call=%ld ext=%ld\", r, g, addr_s() == lib_addr_s(),\n\
            addr_s4() == (char *)lib_addr_s() + 4, addr_f() == lib_addr_f(), addr_f()(), call_f(),\n\
            read_ext());\n\
        #ifdef NAMES\n\
          printf(\" c_s_eq=%d c_f_eq=%d c_read=%ld\", addr_s() == &s, addr_f() == f, s);\n\
        #endif\n\
          printf(\"\\n\");\n  return 0;\n}\n";

    /// The driver builds: its name, its flags, and whether it names `s` and
    /// `f` non-PIC.
    const STATIC_DSO_LOCAL_DRIVERS: [(&str, &[&str], bool); 3] = [
        ("no-names", &["-O0", "-fno-pic"], false),
        ("names-no-pic", &["-O0", "-fno-pic", "-DNAMES"], true),
        ("names-pie", &["-O0", "-fPIE", "-DNAMES"], false),
    ];

    /// What a run of [`STATIC_DSO_LOCAL_DRIVER`] prints, from where each
    /// reference binds, or `None` where the executable does not link. With
    /// the definitions in a shared library a symbol has two addresses: the
    /// one the static link gives the executable's non-PIC references (a copy
    /// relocation for `s`, a canonical PLT entry for `f`, made when the
    /// executable has one: llc's PC-relative object or the `names-no-pic`
    /// driver), and the one the dynamic linker binds GOT slots to. GNU ld and
    /// LLD export the executable's (its copy, its PLT entry), so the two are
    /// one, but a library linked `-Bsymbolic` keeps its own references to its
    /// own definitions (`-Bsymbolic-functions`: to its functions), and gold
    /// exports no canonical PLT entry for `f`. llc's object takes the
    /// executable's address and the import's the GOT's, so the two objects
    /// print alike except in those links; in each of them llc's program
    /// already gives the symbol two addresses (the sixth round of L02-P13,
    /// LD-31). No linker makes a copy relocation or canonical PLT entry for
    /// a protected definition, so an executable with a non-PIC reference to
    /// one does not link (llc's object, or the `names-no-pic` driver), where
    /// the import's GOT references link and name the library's (the seventh
    /// round).
    fn static_dso_local_line(
        llc: bool,
        linker: &str,
        names: Option<bool>,
        config: &str,
    ) -> Option<String> {
        let library = config.starts_with("no-pie-library");
        let interposed = config == "no-pie-library-interposed";
        let symbolic = config == "no-pie-library-bsymbolic";
        let symbolic_functions = config == "no-pie-library-bsymbolic-functions";
        let protected = config == "no-pie-library-protected";
        let gold = linker == "gold";
        // An executable reference the static link resolves non-PIC.
        let executable_reference = llc || names == Some(true);
        if protected && executable_reference {
            return None;
        }
        // `s`: a copy in the executable, unseen by a `-Bsymbolic` library.
        let data_split = symbolic && executable_reference;
        // `f`: where each address points (`true`: the executable's PLT
        // entry; `false`: the definition).
        let plt = library && executable_reference;
        let got_binds_plt = plt && !gold;
        let module_f = if llc { plt } else { got_binds_plt };
        let library_f = !symbolic && !symbolic_functions && got_binds_plt;
        let driver_f = match names {
            Some(true) => plt,
            _ => got_binds_plt,
        };
        let flag = |equal: bool| u8::from(equal);
        let mut line = format!(
            "read={} lib_after_write={} addr_eq={} addr4_eq={} faddr_eq={} call_addr={} call={} \
             ext={}",
            if interposed { 1005 } else { 12 },
            if data_split { 12 } else { 77 },
            flag(!data_split),
            flag(!data_split),
            flag(module_f == library_f),
            if interposed { 1005 } else { 7 },
            if interposed { 1005 } else { 7 },
            if interposed { 1005 } else { 42 },
        );
        if names.is_some() {
            line.push_str(&format!(
                " c_s_eq=1 c_f_eq={} c_read=77",
                flag(module_f == driver_f)
            ));
        }
        Some(line)
    }

    /// The `static` relocation model admits an addressed `dso_local`
    /// declaration for AArch64 ELF (LD-31): a `static` object goes into a
    /// non-PIE executable. Linked `-no-pie` and `-static` with the
    /// definitions in the executable, and `-no-pie` with them in a shared
    /// library (plain, under an `LD_PRELOAD` interposer, linked `-Bsymbolic`
    /// or `-Bsymbolic-functions`, and with protected definitions), with each
    /// driver of [`STATIC_DSO_LOCAL_DRIVERS`], at O0-O3 under GNU ld, gold
    /// and LLD, llc's object and the import's print [`static_dso_local_line`]
    /// or do not link where it says so: alike in every link but those where
    /// the defining library binds its own references (`-Bsymbolic`, unless a
    /// `-fno-pic` driver names the data symbol itself, giving the import's
    /// program the copy too; `-Bsymbolic-functions`, for `f`), gold with the
    /// function in a library, and the protected definitions, which fail
    /// llc's object to link and not the import's. Where both link, llc's
    /// object takes the executable's address and the import's the
    /// library's: the import's program has one copy of `s` where llc's has
    /// two, and its address of `f` is the library's and `-fPIE` code's where
    /// llc's is `-fno-pic` code's.
    #[test]
    fn imported_static_dso_local_declarations_run_like_llc() {
        let linkers = linkers();
        let llc = llc();
        let directory = common::unique_temp_dir("l02p13-static-dso-local");
        let drivers: Vec<(&str, PathBuf, Option<bool>)> = STATIC_DSO_LOCAL_DRIVERS
            .iter()
            .map(|(name, flags, non_pic)| {
                let source = write(
                    &directory,
                    &format!("driver-{name}.c"),
                    STATIC_DSO_LOCAL_DRIVER,
                );
                let names = flags.contains(&"-DNAMES").then_some(*non_pic);
                (*name, host_object(&directory, &source, flags), names)
            })
            .collect();
        let definitions_c = write(&directory, "defs.c", STATIC_DSO_LOCAL_DEFINITIONS);
        let definitions = host_object(&directory, &definitions_c, &["-O0", "-fno-pic"]);
        let library = directory.join("libdefs.so");
        ok(
            Command::new("gcc")
                .args(["-shared", "-fPIC", "-O0"])
                .arg(&definitions_c)
                .arg("-o")
                .arg(&library),
            &directory,
        );
        let symbolic_library = directory.join("libsymbolic.so");
        ok(
            Command::new("gcc")
                .args(["-shared", "-fPIC", "-O0", "-Wl,-Bsymbolic"])
                .arg(&definitions_c)
                .arg("-o")
                .arg(&symbolic_library),
            &directory,
        );
        let symbolic_functions_library = directory.join("libsymbolicfunctions.so");
        ok(
            Command::new("gcc")
                .args(["-shared", "-fPIC", "-O0", "-Wl,-Bsymbolic-functions"])
                .arg(&definitions_c)
                .arg("-o")
                .arg(&symbolic_functions_library),
            &directory,
        );
        let protected_library = directory.join("libprotected.so");
        ok(
            Command::new("gcc")
                .args([
                    "-shared",
                    "-fPIC",
                    "-O0",
                    "-DV=__attribute__((visibility(\"protected\")))",
                ])
                .arg(&definitions_c)
                .arg("-o")
                .arg(&protected_library),
            &directory,
        );
        let interposer = directory.join("libint.so");
        ok(
            Command::new("gcc")
                .args(["-shared", "-fPIC", "-O0"])
                .arg(write(&directory, "int.c", STATIC_DSO_LOCAL_INTERPOSER))
                .arg("-o")
                .arg(&interposer),
            &directory,
        );
        let objects =
            |opt_level: OptLevel, name: &str, src: &str| -> Vec<(&'static str, PathBuf)> {
                let module = import_text_for_compile(src, name, LINUX, RelocationModel::Static)
                    .unwrap_or_else(|error| panic!("{name}: {error}"));
                let object = compile_module(&module, LINUX, opt_level, RelocationModel::Static)
                    .unwrap_or_else(|error| panic!("{name} {opt_level:?}: {error}"));
                let mut objects = vec![(
                    "imported",
                    write(&directory, &format!("{name}-{opt_level:?}.o"), object),
                )];
                if let Some(llc) = llc.as_deref() {
                    objects.push((
                        "llc",
                        llc_object(
                            llc,
                            &directory,
                            &format!("{name}-{opt_level:?}-llc"),
                            src,
                            opt_level,
                            RelocationModel::Static,
                        ),
                    ));
                }
                objects
            };
        let mut differing = 0;
        for opt_level in OPT_LEVELS {
            let module = objects(opt_level, "static-dso-local", STATIC_DSO_LOCAL_MODULE);
            let rustc = objects(opt_level, "rustc-static", RUSTC_STATIC_MODULE);
            for (linker, flags) in &linkers {
                for (driver_name, driver, names) in &drivers {
                    for config in [
                        "no-pie-exe",
                        "static-exe",
                        "no-pie-library",
                        "no-pie-library-interposed",
                        "no-pie-library-bsymbolic",
                        "no-pie-library-bsymbolic-functions",
                        "no-pie-library-protected",
                    ] {
                        for ((who, object), (_, rustc_object)) in module.iter().zip(&rustc) {
                            let label =
                                format!("{who} {opt_level:?} {linker} {driver_name} {config}");
                            let binary = directory.join(format!(
                                "{who}-{opt_level:?}-{linker}-{driver_name}-{config}"
                            ));
                            let mut link = cc(flags);
                            link.arg(if config == "static-exe" {
                                "-static"
                            } else {
                                "-no-pie"
                            })
                            .arg(driver)
                            .arg(object)
                            .arg(rustc_object);
                            if config.ends_with("-exe") {
                                link.arg(&definitions);
                            } else {
                                link.arg(match config {
                                    "no-pie-library-bsymbolic" => &symbolic_library,
                                    "no-pie-library-bsymbolic-functions" => {
                                        &symbolic_functions_library
                                    }
                                    "no-pie-library-protected" => &protected_library,
                                    _ => &library,
                                })
                                .arg(format!("-Wl,-rpath,{}", directory.display()));
                            }
                            let expected =
                                static_dso_local_line(*who == "llc", linker, *names, config);
                            let (linked, _, stderr) = run(link.arg("-o").arg(&binary));
                            let line = if linked {
                                let mut run = Command::new(&binary);
                                if config == "no-pie-library-interposed" {
                                    run.env("LD_PRELOAD", &interposer);
                                }
                                Some(ok(&mut run, &directory).trim().to_string())
                            } else {
                                None
                            };
                            assert_eq!(line, expected, "{label}: {stderr}");
                            if *who == "llc"
                                && line != static_dso_local_line(false, linker, *names, config)
                            {
                                differing += 1;
                            }
                        }
                    }
                }
            }
        }
        // The links where llc's object and the import's print differently
        // or only one links: per opt level, the `-Bsymbolic` library with
        // the `no-names` and `names-pie` drivers under each linker and with
        // `names-no-pic` under gold (7), gold's plain and interposed library
        // with each driver (6), the `-Bsymbolic-functions` library with the
        // `no-names` and `names-pie` drivers under each linker and with
        // `names-no-pic` under gold (7), and the protected definitions with
        // the `no-names` and `names-pie` drivers under each linker (6: llc's
        // object does not link; with `names-no-pic` neither does).
        if llc.is_some() && linkers.len() == 3 {
            assert_eq!(differing, 4 * 26, "differing links");
        }
        eprintln!("L02-P13 static dso_local declarations passed: {directory:?}");
    }

    // -------------------------------------------------------------------------
    // Functions under a named processor (`"target-cpu"`, L02-P15)
    // -------------------------------------------------------------------------

    /// Functions passing and returning `double` and `float` values, built
    /// for the processor `cpu`, so the calling convention llc builds them
    /// with shows in what a gcc-built (hard-float) caller prints. This row
    /// lives here for this file's llc lookup, which the Linux floor
    /// requires (`TCG_REQUIRE_LLC`).
    fn processor_module(cpu: &str) -> String {
        format!(
            "target triple = \"aarch64-unknown-linux-gnu\"\n\
             define double @cpu_mix(double %a, i64 %k, float %b) #0 {{\n\
             \x20 %c = fpext float %b to double\n  %s = fadd double %a, %c\n\
             \x20 %n = sitofp i64 %k to double\n  %r = fmul double %s, %n\n  ret double %r\n}}\n\
             define i64 @cpu_bits(double %a) #0 {{\n  %r = bitcast double %a to i64\n  \
             ret i64 %r\n}}\n\
             define float @cpu_half(float %x) #0 {{\n  %r = fmul float %x, 5.000000e-01\n  \
             ret float %r\n}}\n\
             define double @cpu_twice(double %x) #0 {{\n\
             \x20 %r = call double @cpu_mix(double %x, i64 2, float 5.000000e-01)\n  \
             ret double %r\n}}\n\
             attributes #0 = {{ noinline nounwind \"target-cpu\"=\"{cpu}\" }}\n"
        )
    }

    const PROCESSOR_DRIVER: &str = "#include <stdio.h>\n\
        extern double cpu_mix(double, long, float);\nextern long cpu_bits(double);\n\
        extern float cpu_half(float);\nextern double cpu_twice(double);\n\
        int main(void) {\n  printf(\"mix=%.17g bits=%lx half=%.9g twice=%.17g\\n\", \
        cpu_mix(1.25, 3, 0.5f),\n         cpu_bits(2.5), (double)cpu_half(3.0f), \
        cpu_twice(1.5));\n  return 0;\n}\n";

    const PROCESSOR_LINE: &str = "mix=5.25 bits=4004000000000000 half=1.5 twice=4";

    /// `cpu_bits` alone under `cpu`: a soft-float build of the other
    /// functions calls floating-point library functions (`__adddf3`,
    /// `__extendsfdf2`, ...) that libgcc does not provide on AArch64, so it
    /// does not link.
    fn processor_bits_module(cpu: &str) -> String {
        format!(
            "target triple = \"aarch64-unknown-linux-gnu\"\n\
             define i64 @cpu_bits(double %a) #0 {{\n  %r = bitcast double %a to i64\n  \
             ret i64 %r\n}}\n\
             attributes #0 = {{ noinline nounwind \"target-cpu\"=\"{cpu}\" }}\n"
        )
    }

    /// Calls only `cpu_bits` ([`processor_bits_module`]).
    const PROCESSOR_BITS_DRIVER: &str = "#include <stdio.h>\n\
        extern long cpu_bits(double);\n\
        int main(void) {\n  printf(\"bits=%lx\\n\", cpu_bits(2.5));\n  return 0;\n}\n";

    /// Functions under four processor names LLVM 22 defines for AArch64, as
    /// LLVM spells them (`apple-m1` an alias), run as llc's object does: at
    /// O0-O3, linked `-no-pie` with GNU ld, gold and LLD, the hard-float
    /// AAPCS the gcc-built caller uses. The control: the import refuses a
    /// name LLVM 22 does not define, and llc's object of `cpu_bits` under
    /// it takes the `double` from `x0` (soft-float), so the caller prints
    /// another value than under `generic` (llc's object of the whole module
    /// under it does not link: [`processor_bits_module`]).
    #[test]
    fn imported_named_processors_run_like_llc() {
        let linkers = linkers();
        let llc = llc();
        let directory = common::unique_temp_dir("l02p15-target-cpu");
        let driver = host_object(
            &directory,
            &write(&directory, "cpu_driver.c", PROCESSOR_DRIVER),
            &["-O0", "-fno-pic"],
        );
        for cpu in ["generic", "cortex-a72", "neoverse-v2", "apple-m1"] {
            let src = processor_module(cpu);
            for opt_level in OPT_LEVELS {
                let object = imported_object(
                    &directory,
                    &format!("cpu-{cpu}-{opt_level:?}.o"),
                    &src,
                    opt_level,
                    RelocationModel::Static,
                );
                let twin = llc.as_deref().map(|llc| {
                    llc_object(
                        llc,
                        &directory,
                        &format!("cpu-{cpu}-{opt_level:?}-llc"),
                        &src,
                        opt_level,
                        RelocationModel::Static,
                    )
                });
                for (linker, flags) in &linkers {
                    for (who, subject) in std::iter::once(("imported", &object))
                        .chain(twin.iter().map(|twin| ("llc", twin)))
                    {
                        let binary =
                            directory.join(format!("cpu-{cpu}-{who}-{opt_level:?}-{linker}"));
                        ok(
                            cc(flags)
                                .arg("-no-pie")
                                .arg(&driver)
                                .arg(subject)
                                .arg("-o")
                                .arg(&binary),
                            &directory,
                        );
                        assert_eq!(
                            ok(&mut Command::new(&binary), &directory).trim(),
                            PROCESSOR_LINE,
                            "{cpu} {who} {opt_level:?} {linker}"
                        );
                    }
                }
            }
        }
        for module in [
            processor_module("nosuchcpu"),
            processor_bits_module("nosuchcpu"),
        ] {
            let refusal = import_text_for_target(&module, "cpu", LINUX)
                .expect_err("an undefined processor name is refused")
                .to_string();
            assert!(
                refusal.contains("processor \"nosuchcpu\" is not one LLVM 22 defines"),
                "{refusal}"
            );
        }
        if let Some(llc) = llc.as_deref() {
            let bits_driver = host_object(
                &directory,
                &write(&directory, "cpu_bits_driver.c", PROCESSOR_BITS_DRIVER),
                &["-O0", "-fno-pic"],
            );
            for opt_level in OPT_LEVELS {
                for cpu in ["generic", "nosuchcpu"] {
                    let object = llc_object(
                        llc,
                        &directory,
                        &format!("cpu-bits-{cpu}-{opt_level:?}-llc"),
                        &processor_bits_module(cpu),
                        opt_level,
                        RelocationModel::Static,
                    );
                    let binary = directory.join(format!("cpu-bits-{cpu}-{opt_level:?}"));
                    ok(
                        cc(&linkers[0].1)
                            .arg("-no-pie")
                            .arg(&bits_driver)
                            .arg(&object)
                            .arg("-o")
                            .arg(&binary),
                        &directory,
                    );
                    let line = ok(&mut Command::new(&binary), &directory);
                    assert_eq!(
                        line.trim() == "bits=4004000000000000",
                        cpu == "generic",
                        "{cpu} {opt_level:?}: {line}"
                    );
                }
            }
        }
        eprintln!("L02-P15 named processors passed: {directory:?}");
    }
}
