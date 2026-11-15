// trust-cg-codegen/tests/module_local_binding_other_targets.rs
//
// L02-P1 (2026-10-24 closure audit): function bindings on the object paths
// `Compiler::compile` takes off AArch64 (x86-64 ELF, Mach-O and COFF; RISC-V
// ELF). Those writers used to bind every non-weak definition global, so an
// `Internal`/`Private` definition named only by a `SymbolAddr`, or by
// nothing, captured another object's undefined reference or replaced its
// weak definition at link time (ld.lld reproducers of the audit); RISC-V and
// COFF also wrote weak and link-once definitions strong.
//
// What these tests pin, through `Compiler::compile` and the independent
// object readers:
//
// * an unreferenced module-local definition is local in every object
//   (`STB_LOCAL`, a non-external Mach-O symbol, `IMAGE_SYM_CLASS_STATIC`);
// * a `SymbolAddr` naming a module-local function, in a body or a global
//   initializer, is refused by name on x86-64 Mach-O and COFF and RISC-V
//   (the identity census, `AotStaticFunctionIdentityBindingUnsupported`),
//   while AArch64 ELF and, since ruling OD-X86-ELF-LOCAL-BINDING-20261027,
//   x86-64 ELF, which bind every reference locally, compile it;
// * RISC-V writes weak and link-once definitions `STB_WEAK` and relocates the
//   module's own calls to them; COFF refuses them by name;
// * with ld.lld (the GNU flavour, cross-target): another object's call no
//   longer binds to a module-local body (x86-64 ELF, RISC-V, and x86-64 COFF
//   through LLD's MinGW driver), another object's weak definition is kept,
//   and a RISC-V weak definition gives way to a strong one for the module's
//   own call. Link-level evidence only: this host executes none of these
//   targets. Without an LLD the link legs print `SKIP`, and with
//   `TCG_REQUIRE_LLD` set they fail;
// * x86-64 Mach-O (the round-2 verifier's reproducers): a reference spelled
//   `_x` is relocated against `__x`, never against the definition of `x`
//   (`_x`), a name that coincides with one of the emitter's LSDA labels is
//   refused by name, and with ld64.lld the calls reach the definition their
//   name spells.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#[allow(dead_code)]
#[path = "common/skip.rs"]
mod skip;

use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::coff::{
    CoffRelocation, CoffWriter, IMAGE_SYM_CLASS_EXTERNAL, IMAGE_SYM_CLASS_STATIC,
    IMAGE_SYM_DTYPE_FUNCTION,
};
use trust_cg_codegen::pipeline::{OptLevel, parse_trust_ir_text};
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{CompileError, Compiler, CompilerConfig};
use trust_ir::Module;

const X86_ELF: &str = "x86_64-unknown-linux-gnu";
const X86_MACHO: &str = "x86_64-apple-darwin";
const X86_COFF: &str = "x86_64-pc-windows-msvc";
const RISCV: &str = "riscv64-unknown-linux-gnu";
const AARCH64_ELF: &str = "aarch64-unknown-linux-gnu";
/// The object paths off AArch64. x86-64 Mach-O and COFF and RISC-V bind no
/// reference to a module-local function locally, and so refuse every such
/// reference; x86-64 ELF does since ruling OD-X86-ELF-LOCAL-BINDING-20261027.
/// Each binds an unreferenced module-local definition local.
const OTHER_TARGETS: [&str; 4] = [X86_ELF, X86_MACHO, X86_COFF, RISCV];

/// An unreferenced `internal` (or `private`) `sk_local` returning 13 beside
/// an External `sk_api` (the audit's `unref.tmpl`).
const UNREF: &str = r#"module "unref"
target "TRIPLE" 8 little
functy.0 = () -> (u64)
LOCAL fn @sk_local(functy.0) {
bb0:
    %0 = const u64 13
    ret %0
}
fn @sk_api(functy.0) {
bb0:
    %0 = const u64 2
    ret %0
}
"#;

/// Another module declaring `sk_local` and calling it (`caller.tmpl`).
const CALLER: &str = r#"module "caller"
target "TRIPLE" 8 little
functy.0 = () -> (u64)
external fn @sk_local(functy.0) {
}
fn @sk_caller(functy.0) {
bb0:
    %0 = call @func.0()
    ret %0
}
"#;

/// Another module with its own weak `sk_local` returning 7, called by
/// `sk_call` (the audit's LLVM `weak_other_x86.ll`, as trust-ir).
const WEAK_OTHER: &str = r#"module "weak_other"
target "TRIPLE" 8 little
functy.0 = () -> (u64)
weak fn @sk_local(functy.0) {
bb0:
    %0 = const u64 7
    ret %0
}
fn @sk_call(functy.0) {
bb0:
    %0 = call @func.0()
    ret %0
}
"#;

/// `sk_local`'s address in a body: `sk_local_addr` returns it.
const SYMADDR_BODY: &str = r#"module "symaddr_body"
target "TRIPLE" 8 little
functy.0 = () -> (u64)
functy.1 = () -> (ptr)
internal fn @sk_local(functy.0) {
bb0:
    %0 = const u64 13
    ret %0
}
fn @sk_local_addr(functy.1) {
bb0:
    %0 = const ptr symaddr<sk_local>
    ret %0
}
"#;

/// `sk_local`'s address in a global initializer only (`internal_in_table`).
const SYMADDR_TABLE: &str = r#"module "symaddr_table"
target "TRIPLE" 8 little
functy.0 = () -> (u64)
global external visibility(default) @sk_table ptr = symaddr<sk_local>
internal fn @sk_local(functy.0) {
bb0:
    %0 = const u64 13
    ret %0
}
fn @sk_api(functy.0) {
bb0:
    %0 = const u64 2
    ret %0
}
"#;

/// A `LINKAGE` `sk_weakdef` returning 13 and an External `sk_api` calling it
/// (`weakcall.tmpl`).
const WEAKCALL: &str = r#"module "weakcall"
target "TRIPLE" 8 little
functy.0 = () -> (u64)
LINKAGE fn @sk_weakdef(functy.0) {
bb0:
    %0 = const u64 13
    ret %0
}
fn @sk_api(functy.0) {
bb0:
    %0 = call @func.0()
    ret %0
}
"#;

/// A strong `sk_weakdef` returning 7.
const STRONG: &str = r#"module "strong"
target "TRIPLE" 8 little
functy.0 = () -> (u64)
fn @sk_weakdef(functy.0) {
bb0:
    %0 = const u64 7
    ret %0
}
"#;

const WEAK_LINKAGES: [&str; 4] = ["weak", "linkonce", "weak_odr", "linkonce_odr"];

fn module(template: &str, triple: &str, replacements: &[(&str, &str)]) -> Module {
    let mut text = template.replace("TRIPLE", triple);
    for (from, to) in replacements {
        text = text.replace(from, to);
    }
    parse_trust_ir_text(&text).unwrap_or_else(|error| panic!("{text}\n{error:?}"))
}

fn compiler(triple: &str, opt_level: OptLevel) -> Compiler {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            parallel: false,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).unwrap(),
    )
    .with_codegen_license(
        trust_cg_lower::CodegenLicensePolicy::default()
            .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
    )
}

#[allow(clippy::result_large_err)] // Test helper returns the compiler's own error type unchanged.
fn compile(module: &Module, triple: &str, opt_level: OptLevel) -> Result<Vec<u8>, CompileError> {
    trust_cg_codegen::env_lock::with_env_edits(|env| {
        env.remove("TCG_AY_REGALLOC");
        compiler(triple, opt_level)
            .compile(module)
            .map(|result| result.object_code)
    })
}

fn compiled(module: &Module, triple: &str, opt_level: OptLevel) -> Vec<u8> {
    compile(module, triple, opt_level)
        .unwrap_or_else(|error| panic!("{triple} {opt_level:?}: {error:?}"))
}

/// How `object` (for `triple`) binds the function definition `name`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Bound {
    Local,
    Global,
    Weak,
}

/// The bindings of every symbol spelling `name` in `object` (Mach-O names
/// carry their leading `_`), each a function defined in a section.
fn bindings(object: &[u8], triple: &str, name: &str) -> Vec<Bound> {
    if triple.contains("apple") {
        let records = trust_cg_codegen::macho::reparse::read_object_records(object).unwrap();
        records
            .symbols
            .iter()
            .filter(|symbol| !symbol.is_stab() && symbol.name == format!("_{name}"))
            .map(|symbol| {
                assert!(symbol.is_section_definition(), "{name}: {symbol:?}");
                if !symbol.is_external() {
                    Bound::Local
                } else if symbol.n_desc & 0x0080 != 0 {
                    Bound::Weak
                } else {
                    Bound::Global
                }
            })
            .collect()
    } else if triple.contains("windows") {
        trust_cg_codegen::coff::reparse::read_symbols(object)
            .unwrap()
            .into_iter()
            .filter(|symbol| symbol.name == name)
            .map(|symbol| {
                assert!(
                    symbol.section_number > 0 && symbol.typ == IMAGE_SYM_DTYPE_FUNCTION,
                    "{name}: {symbol:?}"
                );
                match symbol.storage_class {
                    IMAGE_SYM_CLASS_STATIC => Bound::Local,
                    IMAGE_SYM_CLASS_EXTERNAL => Bound::Global,
                    other => panic!("{name}: storage class {other}"),
                }
            })
            .collect()
    } else {
        let records = trust_cg_codegen::elf::reparse::read_object_records(object).unwrap();
        records
            .symbols
            .iter()
            .filter(|symbol| symbol.name == name)
            .map(|symbol| {
                assert!(
                    symbol.defining_section().is_some() && symbol.symbol_type == 2,
                    "{name}: {symbol:?}"
                );
                match symbol.binding {
                    0 => Bound::Local,
                    1 => Bound::Global,
                    2 => Bound::Weak,
                    other => panic!("{name}: binding {other}"),
                }
            })
            .collect()
    }
}

/// An unreferenced `internal` or `private` definition is one local function
/// symbol in every object these paths write, at O0 and O2; the External one
/// beside it stays global. AArch64 ELF, which already bound them locally, is
/// the control.
#[test]
fn unreferenced_module_local_definitions_are_bound_locally() {
    for triple in OTHER_TARGETS.into_iter().chain([AARCH64_ELF]) {
        for local in ["internal", "private"] {
            for opt_level in [OptLevel::O0, OptLevel::O2] {
                let object = compiled(
                    &module(UNREF, triple, &[("LOCAL", local)]),
                    triple,
                    opt_level,
                );
                assert_eq!(
                    bindings(&object, triple, "sk_local"),
                    [Bound::Local],
                    "{triple} {local} {opt_level:?}"
                );
                assert_eq!(
                    bindings(&object, triple, "sk_api"),
                    [Bound::Global],
                    "{triple} {local} {opt_level:?}"
                );
            }
        }
    }
}

/// The x86-64 ELF writer assigns symbol indices by arithmetic (locals
/// first): a module-local function, module-local data, a global function, a
/// data definition and an undefined callee in one object still name the
/// right symbols in every relocation.
#[test]
fn x86_64_elf_local_functions_keep_every_relocation_on_its_symbol() {
    const MIXED: &str = r#"module "mixed"
target "x86_64-unknown-linux-gnu" 8 little
functy.0 = () -> (u64)
global internal mut @sk_private_word u64 = 5
global external mut visibility(default) @sk_word u64 = 6
internal fn @sk_local(functy.0) {
bb0:
    %0 = const u64 13
    ret %0
}
external fn @sk_extern(functy.0) {
}
fn @sk_api(functy.0) {
bb0:
    %0 = global_addr @global.0
    %1 = load u64, ptr %0
    %2 = global_addr @global.1
    %3 = load u64, ptr %2
    %4 = call @func.1()
    %5 = add u64 %1, %3
    %6 = add u64 %5, %4
    ret %6
}
"#;
    let parsed = parse_trust_ir_text(MIXED).unwrap();
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let object = compiled(&parsed, X86_ELF, opt_level);
        assert_eq!(bindings(&object, X86_ELF, "sk_local"), [Bound::Local]);
        assert_eq!(bindings(&object, X86_ELF, "sk_api"), [Bound::Global]);
        let records = trust_cg_codegen::elf::reparse::read_object_records(&object).unwrap();
        let named: std::collections::BTreeSet<&str> = records
            .relocations
            .iter()
            .filter_map(|relocation| {
                records
                    .symbols
                    .get(relocation.record.symbol_index as usize)
                    .map(|symbol| symbol.name.as_str())
            })
            .filter(|name| name.starts_with("sk_"))
            .collect();
        assert_eq!(
            named,
            std::collections::BTreeSet::from(["sk_extern", "sk_private_word", "sk_word"]),
            "{opt_level:?}"
        );
        let locals_end = records
            .symbols
            .iter()
            .position(|symbol| symbol.binding != 0)
            .unwrap_or(records.symbols.len());
        assert!(
            records.symbols[locals_end..]
                .iter()
                .all(|symbol| symbol.binding != 0),
            "every local precedes every global: {:?}",
            records.symbols
        );
    }
}

/// A `SymbolAddr` naming a module-local function, in a body or only in a
/// global initializer, is an address the object resolves through that
/// definition's symbol: refused by name before lowering on every path that
/// binds no reference locally (x86-64 Mach-O and COFF, RISC-V), and
/// attributed by the preflight census to the body that makes it or, for the
/// initializer, to the function it names. AArch64 ELF compiles both, and so
/// does x86-64 ELF since ruling OD-X86-ELF-LOCAL-BINDING-20261027 (which
/// admits references there and reads them back): there every relocation
/// naming `sk_local` names its one local symbol. (Until that ruling this row
/// refused both on x86-64 ELF too.)
#[test]
fn symbol_addresses_of_module_local_functions_are_refused_off_aarch64() {
    for (template, attributed) in [(SYMADDR_BODY, "sk_local_addr"), (SYMADDR_TABLE, "sk_local")] {
        for triple in [X86_MACHO, X86_COFF, RISCV] {
            let source = module(template, triple, &[]);
            match compile(&source, triple, OptLevel::O2) {
                Err(CompileError::AotStaticFunctionIdentityBindingUnsupported {
                    target,
                    candidate_count,
                }) => {
                    assert_eq!(candidate_count, 1, "{triple}");
                    assert!(
                        target.starts_with(triple.split('-').next().unwrap()),
                        "{target}"
                    );
                }
                other => panic!("{triple}: expected the identity refusal, got {other:?}"),
            }
            let rows = compiler(triple, OptLevel::O2).preflight(&source);
            let refused: Vec<&str> = rows
                .iter()
                .filter(|(_, error)| {
                    matches!(
                        error,
                        CompileError::AotStaticFunctionIdentityBindingUnsupported { .. }
                    )
                })
                .map(|(id, _)| source.functions[id.index() as usize].name.as_str())
                .collect();
            assert_eq!(refused, [attributed], "{triple}: {rows:?}");
        }
        for triple in [AARCH64_ELF, X86_ELF] {
            let object = compiled(&module(template, triple, &[]), triple, OptLevel::O2);
            assert_eq!(
                bindings(&object, triple, "sk_local"),
                [Bound::Local],
                "{triple}"
            );
            let records = trust_cg_codegen::elf::reparse::read_object_records(&object).unwrap();
            let naming: Vec<u8> = records
                .relocations
                .iter()
                .map(|relocation| &records.symbols[relocation.record.symbol_index as usize])
                .filter(|symbol| symbol.name == "sk_local")
                .map(|symbol| symbol.binding)
                .collect();
            if triple == X86_ELF {
                // The string address is relocated against the local symbol
                // (AArch64 may fold it to a section-relative form).
                assert!(!naming.is_empty(), "{triple}: no relocation names sk_local");
            }
            assert!(
                naming.iter().all(|binding| *binding == 0),
                "{triple}: every relocation naming sk_local names its local symbol: {naming:?}"
            );
        }
    }
}

/// RISC-V writes every weak and link-once definition `STB_WEAK`, and the
/// module's own call to it is an `R_RISCV_CALL` relocation against that
/// symbol, never a call patched to its own body. COFF writes neither form
/// and refuses each by name (`UnsupportedLinkage`). x86-64 ELF and Mach-O
/// keep writing them weak.
#[test]
fn weak_and_link_once_definitions_are_weak_or_refused_by_name() {
    for linkage in WEAK_LINKAGES {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let object = compiled(
                &module(WEAKCALL, RISCV, &[("LINKAGE", linkage)]),
                RISCV,
                opt_level,
            );
            assert_eq!(
                bindings(&object, RISCV, "sk_weakdef"),
                [Bound::Weak],
                "{linkage} {opt_level:?}"
            );
            let records = trust_cg_codegen::elf::reparse::read_object_records(&object).unwrap();
            let calls: Vec<&str> = records
                .relocations
                .iter()
                .filter(
                    |relocation| relocation.record.reloc_type == 18, /* R_RISCV_CALL */
                )
                .map(|relocation| {
                    records.symbols[relocation.record.symbol_index as usize]
                        .name
                        .as_str()
                })
                .collect();
            // `Weak`/`LinkOnce` bodies are never inlined (another object may
            // replace them); the ODR forms promise equivalent definitions and
            // may be inlined from O1, but a call that stays is relocated.
            if opt_level == OptLevel::O0 || !linkage.ends_with("_odr") {
                assert_eq!(calls, ["sk_weakdef"], "{linkage} {opt_level:?}");
            } else {
                assert!(
                    calls.iter().all(|callee| *callee == "sk_weakdef"),
                    "{linkage} {opt_level:?}: {calls:?}"
                );
            }
            for triple in [X86_ELF, X86_MACHO] {
                let object = compiled(
                    &module(WEAKCALL, triple, &[("LINKAGE", linkage)]),
                    triple,
                    opt_level,
                );
                assert_eq!(
                    bindings(&object, triple, "sk_weakdef"),
                    [Bound::Weak],
                    "{triple} {linkage}"
                );
            }
        }
        match compile(
            &module(WEAKCALL, X86_COFF, &[("LINKAGE", linkage)]),
            X86_COFF,
            OptLevel::O2,
        ) {
            Err(CompileError::Adapter(trust_cg_lower::AdapterError::UnsupportedLinkage {
                symbol,
                ..
            })) => assert_eq!(symbol, "sk_weakdef", "{linkage}"),
            other => panic!("COFF {linkage}: expected UnsupportedLinkage, got {other:?}"),
        }
    }
}

// ---------------------------------------------------------------------------
// Link-level controls with ld.lld (GNU flavour, cross-target, nothing runs)
// ---------------------------------------------------------------------------

/// The first `ld.lld` in `TCG_LLD_DIR`, `~/.local/bin` and `PATH`; with none,
/// `test` prints `SKIP` and gets `None`, unless `TCG_REQUIRE_LLD` is set.
fn lld_for(test: &str) -> Option<PathBuf> {
    let found = std::env::var_os("TCG_LLD_DIR")
        .map(PathBuf::from)
        .into_iter()
        .chain(std::env::var_os("HOME").map(|home| Path::new(&home).join(".local/bin")))
        .chain(
            std::env::var_os("PATH")
                .map(|paths| std::env::split_paths(&paths).collect::<Vec<_>>())
                .unwrap_or_default(),
        )
        .map(|dir| dir.join("ld.lld"))
        .find(|path| path.is_file());
    if found.is_none() {
        assert!(
            std::env::var_os("TCG_REQUIRE_LLD").is_none(),
            "{test}: TCG_REQUIRE_LLD is set but no ld.lld (TCG_LLD_DIR, ~/.local/bin, PATH)"
        );
        skip::skip_test(test, "no ld.lld (TCG_LLD_DIR, ~/.local/bin, PATH)");
    }
    found
}

fn write(dir: &Path, name: &str, bytes: &[u8]) -> PathBuf {
    let path = dir.join(name);
    std::fs::write(&path, bytes).unwrap();
    path
}

/// Run ld.lld with `args`; its exit status and standard error.
fn lld(lld: &Path, args: &[&std::ffi::OsStr]) -> (bool, String) {
    let output = Command::new(lld).args(args).output().unwrap();
    (
        output.status.success(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// A linked ELF64 little-endian image read back: its sections (name,
/// address, file offset, size) and its `.symtab` (name, value, binding).
struct LinkedElf {
    bytes: Vec<u8>,
    sections: Vec<(String, u64, u64, u64)>,
    symbols: Vec<(String, u64, u8)>,
}

impl LinkedElf {
    fn read(path: &Path) -> Self {
        let bytes = std::fs::read(path).unwrap();
        let u16_at = |at: usize| u16::from_le_bytes(bytes[at..at + 2].try_into().unwrap());
        let u32_at = |at: usize| u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap());
        let u64_at = |at: usize| u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap());
        assert_eq!(&bytes[..6], &[0x7f, b'E', b'L', b'F', 2, 1]);
        let (shoff, shentsize, shnum, shstrndx) = (
            u64_at(40) as usize,
            u16_at(58) as usize,
            u16_at(60) as usize,
            u16_at(62) as usize,
        );
        let header = |index: usize| shoff + index * shentsize;
        let string = |table: usize, offset: usize| {
            let start = u64_at(header(table) + 24) as usize + offset;
            let end = start + bytes[start..].iter().position(|&b| b == 0).unwrap();
            String::from_utf8(bytes[start..end].to_vec()).unwrap()
        };
        let mut sections = Vec::new();
        let mut symbols = Vec::new();
        for index in 0..shnum {
            let at = header(index);
            sections.push((
                string(shstrndx, u32_at(at) as usize),
                u64_at(at + 16),
                u64_at(at + 24),
                u64_at(at + 32),
            ));
            if u32_at(at + 4) == 2 {
                // SHT_SYMTAB
                let (offset, size, link) = (
                    u64_at(at + 24) as usize,
                    u64_at(at + 32) as usize,
                    u32_at(at + 40),
                );
                for entry in (offset..offset + size).step_by(24) {
                    symbols.push((
                        string(link as usize, u32_at(entry) as usize),
                        u64_at(entry + 8),
                        bytes[entry + 4] >> 4,
                    ));
                }
            }
        }
        Self {
            bytes,
            sections,
            symbols,
        }
    }

    /// Every `(value, binding)` of the symbols named `name`.
    fn symbol(&self, name: &str) -> Vec<(u64, u8)> {
        self.symbols
            .iter()
            .filter(|(symbol, ..)| symbol == name)
            .map(|(_, value, binding)| (*value, *binding))
            .collect()
    }

    /// The `length` bytes at virtual address `address` in `.text`.
    fn text(&self, address: u64, length: usize) -> &[u8] {
        let (_, start, offset, size) = self
            .sections
            .iter()
            .find(|(name, ..)| name == ".text")
            .unwrap();
        assert!(address >= *start && address + length as u64 <= start + size);
        let at = (offset + (address - start)) as usize;
        &self.bytes[at..at + length]
    }
}

/// The offset, from the start of `function`, of the one relocation of
/// `reloc_type` in `object` naming `symbol`.
fn relocation_offset(object: &[u8], function: &str, reloc_type: u32, symbol: &str) -> u64 {
    let records = trust_cg_codegen::elf::reparse::read_object_records(object).unwrap();
    let start = records
        .symbols
        .iter()
        .find(|candidate| candidate.name == function)
        .unwrap()
        .value;
    let offsets: Vec<u64> = records
        .relocations
        .iter()
        .filter(|relocation| {
            relocation.record.reloc_type == reloc_type
                && records.symbols[relocation.record.symbol_index as usize].name == symbol
        })
        .map(|relocation| relocation.record.r_offset - start)
        .collect();
    assert_eq!(offsets.len(), 1, "{function} -> {symbol}: {offsets:?}");
    offsets[0]
}

/// Another object's declaration of `sk_local` does not bind to the
/// module-local definition: ld.lld refuses the static link with an
/// undefined symbol for x86-64 ELF and RISC-V (`-static -e sk_caller`) and
/// for x86-64 COFF through LLD's MinGW driver (`-m i386pep`). Before the
/// repair each linked, and `sk_caller` called the module-local body. A
/// control with `sk_local` External links on each target, so the refusal is
/// the binding's.
#[test]
fn another_objects_declaration_does_not_bind_to_a_module_local_definition() {
    let Some(lld_path) =
        lld_for("another_objects_declaration_does_not_bind_to_a_module_local_definition")
    else {
        return;
    };
    let dir = tempfile::tempdir().unwrap();
    let dir = dir.path();
    for (triple, emulation) in [(X86_ELF, "elf_x86_64"), (RISCV, "elf64lriscv")] {
        let caller = write(
            dir,
            &format!("caller-{triple}.o"),
            &compiled(&module(CALLER, triple, &[]), triple, OptLevel::O2),
        );
        for (local, links) in [("internal", false), ("private", false), ("external", true)] {
            let unref = write(
                dir,
                &format!("unref-{local}-{triple}.o"),
                &compiled(
                    &module(UNREF, triple, &[("LOCAL", local)]),
                    triple,
                    OptLevel::O2,
                ),
            );
            let output = dir.join(format!("cap-{local}-{triple}"));
            let (linked, stderr) = lld(
                &lld_path,
                &[
                    "-m".as_ref(),
                    emulation.as_ref(),
                    "-static".as_ref(),
                    "-e".as_ref(),
                    "sk_caller".as_ref(),
                    unref.as_os_str(),
                    caller.as_os_str(),
                    "-o".as_ref(),
                    output.as_os_str(),
                ],
            );
            assert_eq!(linked, links, "{triple} {local}: {stderr}");
            if !links {
                assert!(
                    stderr.contains("undefined symbol: sk_local"),
                    "{triple} {local}: {stderr}"
                );
            }
        }
    }

    // x86-64 COFF: the caller is written by hand (the trust-cg COFF emitter
    // refuses a call to a callee its module does not define): `sub rsp, 40;
    // call sk_local; add rsp, 40; ret`, with one IMAGE_REL_AMD64_REL32.
    let mut writer = CoffWriter::new_x86_64();
    let text = writer.add_text_section_with_align(
        &[
            0x48, 0x83, 0xec, 0x28, 0xe8, 0, 0, 0, 0, 0x48, 0x83, 0xc4, 0x28, 0xc3,
        ],
        4,
    );
    writer.add_function_symbol("sk_caller", text, 0);
    let callee = writer.add_symbol(
        "sk_local",
        0,
        0,
        IMAGE_SYM_DTYPE_FUNCTION,
        IMAGE_SYM_CLASS_EXTERNAL,
    );
    writer.add_relocation(
        usize::from(text - 1),
        CoffRelocation::amd64_rel32(5, callee),
    );
    let caller = write(dir, "caller_coff.obj", &writer.write().unwrap());
    for (local, links) in [("internal", false), ("private", false), ("external", true)] {
        let unref = write(
            dir,
            &format!("unref-{local}-coff.obj"),
            &compiled(
                &module(UNREF, X86_COFF, &[("LOCAL", local)]),
                X86_COFF,
                OptLevel::O2,
            ),
        );
        let output = dir.join(format!("cap-{local}.exe"));
        let (linked, stderr) = lld(
            &lld_path,
            &[
                "-m".as_ref(),
                "i386pep".as_ref(),
                "--entry=sk_caller".as_ref(),
                "--subsystem=console".as_ref(),
                unref.as_os_str(),
                caller.as_os_str(),
                "-o".as_ref(),
                output.as_os_str(),
            ],
        );
        assert_eq!(linked, links, "COFF {local}: {stderr}");
        if !links {
            assert!(
                stderr.contains("undefined symbol: sk_local"),
                "COFF {local}: {stderr}"
            );
        }
    }
}

/// x86-64 ELF: an object with its own weak `sk_local` (7) and a caller
/// `sk_call` links beside the trust-cg object whose `internal` `sk_local`
/// (13) is unreferenced (the audit's data-word form is now refused before
/// emission), in either input order: the image keeps the weak definition as
/// its one non-local `sk_local`, the module-local body stays a separate local
/// symbol, and `sk_call`'s call reaches the weak body. Before the repair the
/// module-local body replaced the weak one (`callq` -> `movl $0xd`).
#[test]
fn another_objects_weak_definition_is_kept_beside_a_module_local_one() {
    let Some(lld_path) =
        lld_for("another_objects_weak_definition_is_kept_beside_a_module_local_one")
    else {
        return;
    };
    let dir = tempfile::tempdir().unwrap();
    let dir = dir.path();
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let weak_object = compiled(&module(WEAK_OTHER, X86_ELF, &[]), X86_ELF, opt_level);
        let call_offset = relocation_offset(
            &weak_object,
            "sk_call",
            4, /* R_X86_64_PLT32 */
            "sk_local",
        );
        let weak = write(dir, &format!("weak-{opt_level:?}.o"), &weak_object);
        let unref = write(
            dir,
            &format!("unref-{opt_level:?}.o"),
            &compiled(
                &module(UNREF, X86_ELF, &[("LOCAL", "internal")]),
                X86_ELF,
                opt_level,
            ),
        );
        // Both input orders: the linker must keep the weak definition either way.
        for (first, second) in [(&unref, &weak), (&weak, &unref)] {
            let output = dir.join(format!("weakcap-{opt_level:?}"));
            let (linked, stderr) = lld(
                &lld_path,
                &[
                    "-m".as_ref(),
                    "elf_x86_64".as_ref(),
                    "-static".as_ref(),
                    "-e".as_ref(),
                    "sk_call".as_ref(),
                    first.as_os_str(),
                    second.as_os_str(),
                    "-o".as_ref(),
                    output.as_os_str(),
                ],
            );
            assert!(linked, "{opt_level:?}: {stderr}");
            let image = LinkedElf::read(&output);
            let sk_local = image.symbol("sk_local");
            let global: Vec<u64> = sk_local
                .iter()
                .filter(|(_, binding)| *binding != 0)
                .map(|(value, _)| *value)
                .collect();
            let local: Vec<u64> = sk_local
                .iter()
                .filter(|(_, binding)| *binding == 0)
                .map(|(value, _)| *value)
                .collect();
            assert_eq!(global.len(), 1, "{opt_level:?}: {sk_local:?}");
            assert_eq!(local.len(), 1, "{opt_level:?}: {sk_local:?}");
            assert!(
                sk_local.iter().any(|(_, binding)| *binding == 2),
                "the kept definition is the weak one: {sk_local:?}"
            );
            let [(sk_call, _)] = image.symbol("sk_call")[..] else {
                panic!("one sk_call: {:?}", image.symbol("sk_call"));
            };
            let field = sk_call + call_offset;
            let rel32 = i32::from_le_bytes(image.text(field, 4).try_into().unwrap());
            let target = (field as i64 + 4 + i64::from(rel32)) as u64;
            assert_eq!(
                target, global[0],
                "{opt_level:?}: sk_call reaches the weak sk_local"
            );
            assert_ne!(
                target, local[0],
                "{opt_level:?}: never the module-local body"
            );
        }
    }
}

/// RISC-V: the trust-cg object's weak (or link-once) `sk_weakdef` gives way
/// to another object's strong definition, and the module's own `sk_api`
/// calls the strong one: its `R_RISCV_CALL` is resolved by the linker to the
/// definition the link keeps. Before the repair both definitions were
/// global (`duplicate symbol: sk_weakdef`), and the module's call was patched
/// to its own body.
#[test]
fn riscv_weak_definition_gives_way_to_a_strong_one_for_its_own_call() {
    let Some(lld_path) =
        lld_for("riscv_weak_definition_gives_way_to_a_strong_one_for_its_own_call")
    else {
        return;
    };
    let dir = tempfile::tempdir().unwrap();
    let dir = dir.path();
    let strong = write(
        dir,
        "strong.o",
        &compiled(&module(STRONG, RISCV, &[]), RISCV, OptLevel::O2),
    );
    for linkage in ["weak", "linkonce"] {
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let object = compiled(
                &module(WEAKCALL, RISCV, &[("LINKAGE", linkage)]),
                RISCV,
                opt_level,
            );
            let call_offset =
                relocation_offset(&object, "sk_api", 18 /* R_RISCV_CALL */, "sk_weakdef");
            let weak = write(dir, &format!("weak-{linkage}-{opt_level:?}.o"), &object);
            let output = dir.join(format!("rvweak-{linkage}-{opt_level:?}"));
            let (linked, stderr) = lld(
                &lld_path,
                &[
                    "-m".as_ref(),
                    "elf64lriscv".as_ref(),
                    "-static".as_ref(),
                    "-e".as_ref(),
                    "sk_api".as_ref(),
                    weak.as_os_str(),
                    strong.as_os_str(),
                    "-o".as_ref(),
                    output.as_os_str(),
                ],
            );
            assert!(linked, "{linkage} {opt_level:?}: {stderr}");
            let image = LinkedElf::read(&output);
            let [(strong_address, 1)] = image.symbol("sk_weakdef")[..] else {
                panic!("one strong sk_weakdef: {:?}", image.symbol("sk_weakdef"));
            };
            let [(sk_api, _)] = image.symbol("sk_api")[..] else {
                panic!("one sk_api");
            };
            let pc = sk_api + call_offset;
            let words = image.text(pc, 8);
            let auipc = u32::from_le_bytes(words[..4].try_into().unwrap());
            let jalr = u32::from_le_bytes(words[4..].try_into().unwrap());
            assert_eq!(auipc & 0x7f, 0x17, "AUIPC");
            assert_eq!(jalr & 0x7f, 0x67, "JALR");
            let high = i64::from((auipc & 0xffff_f000) as i32);
            let low = i64::from((jalr as i32) >> 20);
            let target = (pc as i64 + high + low) as u64;
            assert_eq!(
                target, strong_address,
                "{linkage} {opt_level:?}: sk_api calls the strong definition"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// x86-64 Mach-O: a reference binds to the symbol its own name spells
// ---------------------------------------------------------------------------
//
// The L02-P1 round-2 verifier (2026-10-24): the x86-64 Mach-O module emitter
// keyed every definition under both its trust-ir name `x` and its nlist name
// `_x`, and looked every reference up under both, so a reference spelled
// `_x` (nlist `__x`) bound to the definition of `x`. Every other object path
// and llc spell the undefined `__x`. The emitter now keys symbols by nlist
// name only.

/// An `internal` `mc_local` (13), a declaration of `_mc_local` and
/// `mc_call` calling the declaration (the verifier's `mcall.tmpl`).
const MC_CALL: &str = r#"module "mcall"
target "x86_64-apple-darwin" 8 little
functy.0 = () -> (u64)
internal fn @mc_local(functy.0) {
bb0:
    %0 = const u64 13
    ret %0
}
external fn @_mc_local(functy.0) {
}
fn @mc_call(functy.0) {
bb0:
    %0 = call @func.1()
    ret %0
}
"#;

/// `symaddr<_cb_local>` in a body beside a `private` `cb_local`.
const MC_BODY_ADDR: &str = r#"module "mbody"
target "x86_64-apple-darwin" 8 little
functy.0 = () -> (u64)
functy.1 = () -> (ptr)
private fn @cb_local(functy.0) {
bb0:
    %0 = const u64 13
    ret %0
}
fn @cb_addr(functy.1) {
bb0:
    %0 = const ptr symaddr<_cb_local>
    ret %0
}
"#;

/// `symaddr<_cb_local>` in a global initializer beside an `internal`
/// `cb_local`.
const MC_DATA_ADDR: &str = r#"module "mdata"
target "x86_64-apple-darwin" 8 little
functy.0 = () -> (u64)
global external visibility(default) @cb_table ptr = symaddr<_cb_local>
internal fn @cb_local(functy.0) {
bb0:
    %0 = const u64 13
    ret %0
}
fn @cb_api(functy.0) {
bb0:
    %0 = const u64 2
    ret %0
}
"#;

/// An imported `_dc_word` beside internal data `dc_word`, addressed by
/// `dc_addr` (the verifier's `mdatacap.tmpl`).
const MC_DATA_IMPORT: &str = r#"module "mdatacap"
target "x86_64-apple-darwin" 8 little
functy.0 = () -> (ptr)
global internal mut align(8) @dc_word u64 = 5
global external mut @_dc_word u64
fn @dc_addr(functy.0) {
bb0:
    %0 = global_addr @global.1
    ret %0
}
"#;

/// An External definition `_md_g` (1), an `internal` `md_g` (2) and `md_call`
/// calling `_md_g` (the verifier's `mdef.tmpl`).
const MC_DEF: &str = r#"module "mdef"
target "x86_64-apple-darwin" 8 little
functy.0 = () -> (u64)
fn @_md_g(functy.0) {
bb0:
    %0 = const u64 1
    ret %0
}
internal fn @md_g(functy.0) {
bb0:
    %0 = const u64 2
    ret %0
}
fn @md_call(functy.0) {
bb0:
    %0 = call @func.0()
    ret %0
}
"#;

/// An `internal` `___udivti3` (13) and `rs_div`, whose `u128` division the
/// backend lowers to a call to the runtime's `__udivti3` (nlist
/// `___udivti3`; the verifier's `rtshadow.tmpl`).
const MC_RUNTIME_SHADOW: &str = r#"module "rtshadow"
target "x86_64-apple-darwin" 8 little
functy.0 = (u128, u128) -> (u128)
internal fn @___udivti3(functy.0) {
bb0(%0: u128, %1: u128):
    %2 = const u128 13
    ret %2
}
fn @rs_div(functy.0) {
bb0(%0: u128, %1: u128):
    %2 = udiv u128 %0, %1
    ret %2
}
"#;

/// An `internal` `_rust_eh_personality` beside `lp_api` (the verifier's
/// `localpers.tmpl`, renamed): under `panic=unwind` the `__eh_frame`
/// personality is `rust_eh_personality` (nlist `_rust_eh_personality`).
const MC_PERSONALITY_SHADOW: &str = r#"module "localpers"
target "x86_64-apple-darwin" 8 little
functy.0 = () -> (u64)
internal fn @_rust_eh_personality(functy.0) {
bb0:
    %0 = const u64 0
    ret %0
}
fn @lp_api(functy.0) {
bb0:
    %0 = const u64 5
    ret %0
}
"#;

#[allow(clippy::result_large_err)] // Test helper returns the compiler's own error type unchanged.
fn compile_unwind(
    module: &Module,
    triple: &str,
    opt_level: OptLevel,
) -> Result<Vec<u8>, CompileError> {
    trust_cg_codegen::env_lock::with_env_edits(|env| {
        env.remove("TCG_AY_REGALLOC");
        Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level,
                parallel: false,
                panic_unwind: true,
                ..CompilerConfig::default()
            },
            TargetSpec::parse(triple).unwrap(),
        )
        .with_codegen_license(
            trust_cg_lower::CodegenLicensePolicy::default()
                .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
        )
        .compile(module)
        .map(|result| result.object_code)
    })
}

/// x86-64 Mach-O relocation kinds (`X86_64_RELOC_*`).
const MACHO_UNSIGNED: u8 = 0;
const MACHO_BRANCH: u8 = 2;
const MACHO_GOT_LOAD: u8 = 3;
const MACHO_GOT: u8 = 4;

/// Every external relocation of the Mach-O `object` whose symbol is named
/// `_<spelling>` for one of `spellings`: its section, `X86_64_RELOC_*` kind,
/// symbol name, and whether that symbol is defined in a section.
fn macho_relocations_naming(object: &[u8], spellings: &[&str]) -> Vec<(String, u8, String, bool)> {
    let records = trust_cg_codegen::macho::reparse::read_object_records(object).unwrap();
    let wanted: Vec<String> = spellings.iter().map(|name| format!("_{name}")).collect();
    let mut found = Vec::new();
    for (section, relocations) in records.sections.iter().zip(&records.section_relocations) {
        for relocation in relocations.iter().filter(|relocation| relocation.r_extern) {
            let symbol = &records.symbols[relocation.r_symbolnum as usize];
            if wanted.contains(&symbol.name) {
                found.push((
                    section.sectname.clone(),
                    relocation.r_type,
                    symbol.name.clone(),
                    symbol.is_section_definition(),
                ));
            }
        }
    }
    found
}

/// Every reproducer of the verifier's `p1_macho_capture.sh`, at O0 and O2:
/// a reference spelled `_x` beside a definition of `x` is relocated against
/// the symbol `__x` (an undefined external, or the External definition of
/// `_x`), never against `_x`, the module-local definition, which stays
/// local. Before the repair every row relocated against `_x`: the call to
/// the declaration `_mc_local` reached the module-local `mc_local`, both
/// `symaddr<_cb_local>` forms addressed the module-local `cb_local`, the
/// import `_dc_word` read internal `dc_word`, `md_call` called the internal
/// `md_g` (returning 2, where `_md_g` returns 1), the backend's `__udivti3`
/// call reached the internal `___udivti3`, and the `__eh_frame`
/// personality was the internal `_rust_eh_personality`.
#[test]
fn x86_64_macho_references_bind_to_the_symbol_their_own_name_spells() {
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        // (module, its module-local function, the module-local name, the
        // reference's trust-ir spelling, the relocation kind)
        for (source, local_function, local, reference, kind) in [
            (MC_CALL, true, "mc_local", "_mc_local", Some(MACHO_BRANCH)),
            (
                MC_BODY_ADDR,
                true,
                "cb_local",
                "_cb_local",
                Some(MACHO_GOT_LOAD),
            ),
            (
                MC_DATA_ADDR,
                true,
                "cb_local",
                "_cb_local",
                Some(MACHO_UNSIGNED),
            ),
            (MC_DATA_IMPORT, false, "dc_word", "_dc_word", None),
            (
                MC_RUNTIME_SHADOW,
                true,
                "___udivti3",
                "__udivti3",
                Some(MACHO_BRANCH),
            ),
        ] {
            let what = format!("{reference} {opt_level:?}");
            let object = compiled(&parse_trust_ir_text(source).unwrap(), X86_MACHO, opt_level);
            if local_function {
                assert_eq!(
                    bindings(&object, X86_MACHO, local),
                    [Bound::Local],
                    "{what}"
                );
            }
            let relocations = macho_relocations_naming(&object, &[local, reference]);
            assert!(!relocations.is_empty(), "{what}: no relocation");
            for (section, r_type, symbol, defined) in &relocations {
                assert_eq!(symbol, &format!("_{reference}"), "{what}: {relocations:?}");
                assert!(!defined, "{what}: an undefined external: {relocations:?}");
                if let Some(kind) = kind {
                    assert_eq!(*r_type, kind, "{what} in {section}: {relocations:?}");
                }
            }
        }

        // The External definition `_md_g` is the one `md_call` calls: at O0
        // the branch names `__md_g`, at O2 the body is inlined; no
        // relocation ever names the internal `md_g`.
        let object = compiled(&parse_trust_ir_text(MC_DEF).unwrap(), X86_MACHO, opt_level);
        assert_eq!(bindings(&object, X86_MACHO, "md_g"), [Bound::Local]);
        assert_eq!(bindings(&object, X86_MACHO, "_md_g"), [Bound::Global]);
        let relocations = macho_relocations_naming(&object, &["md_g", "_md_g"]);
        assert!(
            relocations.iter().all(|(_, r_type, symbol, defined)| {
                *r_type == MACHO_BRANCH && symbol == "__md_g" && *defined
            }),
            "{opt_level:?}: {relocations:?}"
        );
        if opt_level == OptLevel::O0 {
            assert_eq!(relocations.len(), 1, "{relocations:?}");
        }

        // The `__eh_frame` personality is the undefined `_rust_eh_personality`,
        // never the module-local `__rust_eh_personality`.
        let object = compile_unwind(
            &parse_trust_ir_text(MC_PERSONALITY_SHADOW).unwrap(),
            X86_MACHO,
            opt_level,
        )
        .unwrap_or_else(|error| panic!("{opt_level:?}: {error:?}"));
        assert_eq!(
            bindings(&object, X86_MACHO, "_rust_eh_personality"),
            [Bound::Local]
        );
        // (The module-local function's own FDE names its symbol for its
        // address range; the personality is the one `X86_64_RELOC_GOT`.)
        let relocations: Vec<_> =
            macho_relocations_naming(&object, &["rust_eh_personality", "_rust_eh_personality"])
                .into_iter()
                .filter(|(_, r_type, ..)| *r_type == MACHO_GOT)
                .collect();
        assert_eq!(
            relocations,
            [(
                "__eh_frame".to_string(),
                MACHO_GOT,
                "_rust_eh_personality".to_string(),
                false
            )],
            "{opt_level:?}"
        );
    }
}

/// The emitter's own LSDA labels (`_GCC_except_table_<fn>`) share the nlist
/// namespace: under `panic=unwind`, a function whose nlist name is another
/// function's LSDA label, and a call to a declaration of that name, are
/// refused by name (`MachOSymbolNameCollision`) instead of naming the label
/// (before the repair the call relocated against the LSDA: a branch into
/// `__gcc_except_tab`). Without `panic=unwind` no label is written and both
/// compile.
#[test]
fn x86_64_macho_names_that_coincide_with_an_lsda_label_are_refused() {
    const DEFINED: &str = r#"module "lsda_def"
target "x86_64-apple-darwin" 8 little
functy.0 = () -> (u64)
fn @lp_api(functy.0) {
bb0:
    %0 = const u64 5
    ret %0
}
fn @GCC_except_table_lp_api(functy.0) {
bb0:
    %0 = const u64 6
    ret %0
}
"#;
    const CALLED: &str = r#"module "lsda_call"
target "x86_64-apple-darwin" 8 little
functy.0 = () -> (u64)
external fn @GCC_except_table_lp_api(functy.0) {
}
fn @lp_api(functy.0) {
bb0:
    %0 = call @func.0()
    ret %0
}
"#;
    use trust_cg_codegen::pipeline::PipelineError;
    use trust_cg_codegen::x86_64::X86PipelineError;
    for (source, kind, existing) in [
        (DEFINED, "LSDA label", "function"),
        (CALLED, "reference", "LSDA label"),
    ] {
        let module = parse_trust_ir_text(source).unwrap();
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            match compile_unwind(&module, X86_MACHO, opt_level) {
                Err(CompileError::Pipeline(PipelineError::X86(
                    X86PipelineError::MachOSymbolNameCollision {
                        nlist,
                        kind: refused_kind,
                        existing: refused_existing,
                        ..
                    },
                ))) => {
                    assert_eq!(nlist, "_GCC_except_table_lp_api", "{kind}");
                    assert_eq!((refused_kind, refused_existing), (kind, existing));
                }
                other => panic!("{kind} {opt_level:?}: expected the collision, got {other:?}"),
            }
            compiled(&module, X86_MACHO, opt_level);
        }
    }
}

/// The first `ld64.lld` in `TCG_LLD_DIR`, `~/.local/bin` and `PATH`, or
/// beside the first `ld.lld` there once its symbolic links are resolved
/// (rustc's `gcc-ld` directory holds both); with none, `test` prints `SKIP`
/// and gets `None`, unless `TCG_REQUIRE_LLD` is set.
fn ld64_lld_for(test: &str) -> Option<PathBuf> {
    let dirs: Vec<PathBuf> = std::env::var_os("TCG_LLD_DIR")
        .map(PathBuf::from)
        .into_iter()
        .chain(std::env::var_os("HOME").map(|home| Path::new(&home).join(".local/bin")))
        .chain(
            std::env::var_os("PATH")
                .map(|paths| std::env::split_paths(&paths).collect::<Vec<_>>())
                .unwrap_or_default(),
        )
        .collect();
    let found = dirs
        .iter()
        .map(|dir| dir.join("ld64.lld"))
        .find(|path| path.is_file())
        .or_else(|| {
            dirs.iter()
                .map(|dir| dir.join("ld.lld"))
                .filter(|path| path.is_file())
                .filter_map(|path| std::fs::canonicalize(path).ok())
                .filter_map(|path| path.parent().map(|parent| parent.join("ld64.lld")))
                .find(|path| path.is_file())
        });
    if found.is_none() {
        assert!(
            std::env::var_os("TCG_REQUIRE_LLD").is_none(),
            "{test}: TCG_REQUIRE_LLD is set but no ld64.lld (TCG_LLD_DIR, ~/.local/bin, PATH, \
             or beside ld.lld)"
        );
        skip::skip_test(
            test,
            "no ld64.lld (TCG_LLD_DIR, ~/.local/bin, PATH, beside ld.lld)",
        );
    }
    found
}

/// A linked x86-64 Mach-O image read back: its `__TEXT,__text` section
/// (address, file offset, size) and its symbol table (name, value).
struct LinkedMachO {
    bytes: Vec<u8>,
    text: (u64, u64, u64),
    symbols: Vec<(String, u64)>,
}

impl LinkedMachO {
    fn read(path: &Path) -> Self {
        let bytes = std::fs::read(path).unwrap();
        let u32_at = |at: usize| u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap());
        let u64_at = |at: usize| u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap());
        let name_at = |at: usize, len: usize| {
            let raw = &bytes[at..at + len];
            let end = raw.iter().position(|&b| b == 0).unwrap_or(len);
            String::from_utf8(raw[..end].to_vec()).unwrap()
        };
        assert_eq!(u32_at(0), 0xfeed_facf, "MH_MAGIC_64");
        let ncmds = u32_at(16) as usize;
        let mut at = 32;
        let mut text = None;
        let mut symbols = Vec::new();
        for _ in 0..ncmds {
            let (cmd, size) = (u32_at(at), u32_at(at + 4) as usize);
            if cmd == 0x19 {
                // LC_SEGMENT_64: `nsects` 80-byte section headers follow.
                for index in 0..u32_at(at + 64) as usize {
                    let section = at + 72 + index * 80;
                    if name_at(section, 16) == "__text" && name_at(section + 16, 16) == "__TEXT" {
                        text = Some((
                            u64_at(section + 32),
                            u64::from(u32_at(section + 48)),
                            u64_at(section + 40),
                        ));
                    }
                }
            } else if cmd == 0x2 {
                // LC_SYMTAB: 16-byte nlist_64 entries.
                let (symoff, nsyms, stroff) = (
                    u32_at(at + 8) as usize,
                    u32_at(at + 12) as usize,
                    u32_at(at + 16) as usize,
                );
                for index in 0..nsyms {
                    let entry = symoff + index * 16;
                    let start = stroff + u32_at(entry) as usize;
                    let end = start + bytes[start..].iter().position(|&b| b == 0).unwrap();
                    symbols.push((
                        String::from_utf8(bytes[start..end].to_vec()).unwrap(),
                        u64_at(entry + 8),
                    ));
                }
            }
            at += size;
        }
        Self {
            text: text.expect("__TEXT,__text"),
            bytes,
            symbols,
        }
    }

    /// The value of the one symbol named `name`.
    fn symbol(&self, name: &str) -> u64 {
        let values: Vec<u64> = self
            .symbols
            .iter()
            .filter(|(symbol, _)| symbol == name)
            .map(|(_, value)| *value)
            .collect();
        assert_eq!(values.len(), 1, "{name}: {:?}", self.symbols);
        values[0]
    }

    /// The target of the `rel32` call field at address `field`.
    fn call_target(&self, field: u64) -> u64 {
        let (start, offset, size) = self.text;
        assert!(field >= start && field + 4 <= start + size);
        let at = (offset + (field - start)) as usize;
        let rel32 = i32::from_le_bytes(self.bytes[at..at + 4].try_into().unwrap());
        (field as i64 + 4 + i64::from(rel32)) as u64
    }
}

/// The offset, from the start of `function`, of the one `X86_64_RELOC_BRANCH`
/// in the Mach-O `object` naming `symbol`.
fn macho_branch_offset(object: &[u8], function: &str, symbol: &str) -> u64 {
    let records = trust_cg_codegen::macho::reparse::read_object_records(object).unwrap();
    let start = records
        .symbols
        .iter()
        .find(|candidate| candidate.name == function)
        .unwrap()
        .n_value;
    let offsets: Vec<u64> = records.section_relocations[0]
        .iter()
        .filter(|relocation| {
            relocation.r_extern
                && relocation.r_type == MACHO_BRANCH
                && records.symbols[relocation.r_symbolnum as usize].name == symbol
        })
        .map(|relocation| u64::from(relocation.r_address) - start)
        .collect();
    assert_eq!(offsets.len(), 1, "{function} -> {symbol}: {offsets:?}");
    offsets[0]
}

/// Link level, with ld64.lld (`-arch x86_64`, nothing runs): beside another
/// object defining `__mc_local` (77), the call of `_mc_call` reaches
/// `__mc_local`, never the module-local `_mc_local` (13); beside another
/// object's `___udivti3`, `_rs_div`'s runtime call reaches it, never the
/// module-local `____udivti3`. Before the repair both calls reached the
/// module-local body (the verifier's `rust-lld -flavor darwin` links).
#[test]
fn x86_64_macho_calls_reach_the_definition_their_name_spells_at_link_time() {
    let Some(ld64) =
        ld64_lld_for("x86_64_macho_calls_reach_the_definition_their_name_spells_at_link_time")
    else {
        return;
    };
    const MC_PROVIDER: &str = r#"module "prov"
target "x86_64-apple-darwin" 8 little
functy.0 = () -> (u64)
fn @_mc_local(functy.0) {
bb0:
    %0 = const u64 77
    ret %0
}
"#;
    const RT_PROVIDER: &str = r#"module "crt"
target "x86_64-apple-darwin" 8 little
functy.0 = (u128, u128) -> (u128)
fn @__udivti3(functy.0) {
bb0(%0: u128, %1: u128):
    %2 = const u128 77
    ret %2
}
"#;
    let dir = tempfile::tempdir().unwrap();
    let dir = dir.path();
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        for (source, provider, entry, callee, local) in [
            (MC_CALL, MC_PROVIDER, "_mc_call", "__mc_local", "_mc_local"),
            (
                MC_RUNTIME_SHADOW,
                RT_PROVIDER,
                "_rs_div",
                "___udivti3",
                "____udivti3",
            ),
        ] {
            let what = format!("{entry} {opt_level:?}");
            let object = compiled(&parse_trust_ir_text(source).unwrap(), X86_MACHO, opt_level);
            let offset = macho_branch_offset(&object, entry, callee);
            let user = write(dir, &format!("{entry}-{opt_level:?}.o"), &object);
            let provided = write(
                dir,
                &format!("{entry}-provider-{opt_level:?}.o"),
                &compiled(
                    &parse_trust_ir_text(provider).unwrap(),
                    X86_MACHO,
                    OptLevel::O0,
                ),
            );
            let output = dir.join(format!("{entry}-{opt_level:?}.img"));
            let (linked, stderr) = lld(
                &ld64,
                &[
                    "-arch".as_ref(),
                    "x86_64".as_ref(),
                    "-platform_version".as_ref(),
                    "macos".as_ref(),
                    "11.0".as_ref(),
                    "11.0".as_ref(),
                    "-e".as_ref(),
                    entry.as_ref(),
                    user.as_os_str(),
                    provided.as_os_str(),
                    "-o".as_ref(),
                    output.as_os_str(),
                ],
            );
            assert!(linked, "{what}: {stderr}");
            let image = LinkedMachO::read(&output);
            let target = image.call_target(image.symbol(entry) + offset);
            assert_eq!(target, image.symbol(callee), "{what}: reaches {callee}");
            assert_ne!(target, image.symbol(local), "{what}: never {local}");
        }
    }
}
