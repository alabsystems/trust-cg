// trust-cg-codegen/object_sections.rs - explicit output-section placement
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Explicit output-section placement for object globals (trust-ir v41
//! `Global.section`, carried as [`ObjectGlobal::section`]).
//!
//! A section name is an authority claim about where a DEFINITION's bytes must
//! land and which loader semantics they get (writable, read-only after
//! relocation, thread-local, a constructor table the runtime calls). This
//! module decides, per object format, whether a request can be honored and
//! with exactly which section type and flags. Everything it cannot honor is a
//! refusal with a stable, named [`SectionRefusal`] code — never a silent
//! fallback to the default placement.
//!
//! ## ELF (AArch64)
//!
//! | name class | section | requirement |
//! | --- | --- | --- |
//! | `.init_array[.N]`, `.fini_array[.N]`, `.preinit_array` | `SHT_INIT_ARRAY` / `SHT_FINI_ARRAY` / `SHT_PREINIT_ARRAY`, `SHF_ALLOC\|SHF_WRITE`, entsize 8 | every 8-byte slot is a relocated pointer (`R_AARCH64_ABS64`); immutable (`PT_GNU_RELRO` under both linkers); not thread-local |
//! | `.bss[.*]`, `.sbss[.*]`, `.lbss[.*]` | `SHT_NOBITS`, `SHF_ALLOC\|SHF_WRITE` | all-zero image, no relocated pointer; not thread-local; immutable in `.bss.rel.ro[.*]` |
//! | `.tbss[.*]` | `SHT_NOBITS`, `SHF_ALLOC\|SHF_WRITE\|SHF_TLS` | all-zero image, no relocated pointer; thread-local |
//! | `.tdata[.*]` | `SHF_ALLOC\|SHF_WRITE\|SHF_TLS` | thread-local |
//! | `.rodata[.*]`, `.rodata1` | `SHF_ALLOC` | immutable, no relocated pointer |
//! | `.data.rel.ro[.*]` | `SHF_ALLOC\|SHF_WRITE` | immutable |
//! | `.toc` | `SHF_ALLOC`, plus `SHF_WRITE` when relocated | immutable |
//! | `.data[.*]`, `.data1` | `SHF_ALLOC\|SHF_WRITE` | not thread-local |
//! | any name no linker rule below names | `SHF_ALLOC`, plus `SHF_WRITE` when mutable or relocated | not thread-local |
//!
//! A `retained` definition is never packed with another global: like a
//! COMDAT one it gets a section of its own, of the same name and flags plus
//! `SHF_GNU_RETAIN` (LLVM's `@llvm.used` placement, see
//! [`ElfImplicitSection`]). Refused: malformed
//! names (empty, over-long, whitespace/control/`,`/quote characters), names
//! the object writer owns (`.symtab`, `.rela*`, `.group`, `.eh_frame`,
//! `.debug*`, `.note*`, `.got*`, `.plt*`, `.dyn*`, `.gnu.*`, ...), the
//! coverage-mapping names LLVM 22 makes non-allocated metadata by name
//! (`__llvm_covmap`, `__llvm_covfun`, `__llvm_covdata`, `__llvm_covnames`,
//! [`ELF_METADATA_SECTION_NAMES`]), a
//! zero-fill name for a global with a nonzero byte or a relocated pointer
//! slot (`SHT_NOBITS` has no file bytes to hold or patch,
//! [`SectionRefusal::ZeroFillSection`]), the legacy `.ctors`/`.dtors` tables
//! (reverse-order semantics), and every name the default link places where
//! the global's kind cannot live, per the table below.
//! Globals sharing one name share one section, except a retained or COMDAT
//! member, which gets its own section of that name; members sharing one
//! section whose derived type/flags differ are a
//! [`SectionRefusal::FlagConflict`].
//!
//! ### Default linker placement (GNU ld 2.42, LLD 22.1.6)
//!
//! A section name decides the OUTPUT section and segment the linker gives
//! the bytes, so the rule above is derived from where the two linkers the
//! AArch64 Linux link driver supports put each input name when no `-T`
//! script is given. [`ELF_NAME_RULES`] is that table, first match wins; a
//! name no row matches is an orphan under both linkers, placed by its own
//! flags. The GNU column is the default AArch64 script `ld --verbose`
//! prints (`aarch64linux.xdw` for gcc's `-pie -z now -z relro`, the same
//! input patterns in `.xw` (`-no-pie`) and `.xsw` (`-shared`), and without
//! a `PT_GNU_RELRO` segment under `-z norelro`), plus the rules BFD applies
//! by NAME outside the script: it parses every input whose name starts with
//! `.eh_frame_entry` as compact unwind entries, and its special-section
//! table types orphan outputs named `.rela*`, `.relr.dyn` and `.stab*str`.
//! The unit test `elf_name_rules_match_the_gnu_ld_2_42_default_script`
//! re-derives the column from the retained script
//! (`tests/fixtures/gnu-ld-2.42-aarch64linux.xdw`) and the retained by-name
//! list (`tests/fixtures/gnu-ld-2.42-bfd-by-name.txt`). The LLD column is LLD's built-in name folding and `PT_GNU_RELRO` rules,
//! probed empirically. The recorded probe
//! (`reports/perf/2026-09-23-linux-explicit-section-write-faults/README.md`) links
//! each name with trust-cg's section type and flags under both linkers
//! (PIE, `-no-pie`, `-z norelro`, `-shared`), stores through it and records
//! the output section, the segments and the exit status.
//!
//! | input names | GNU ld 2.42 output | LLD 22.1.6 output | data global |
//! | --- | --- | --- | --- |
//! | `.text`, `.text.*` | `.text` (exec) | `.text` (exec) | `[TCG-SECTION-EXEC]` |
//! | `.stub` | `.text` (exec; a store faults) | orphan | `[TCG-SECTION-EXEC]` |
//! | `.init`, `.fini` | `.init`/`.fini` (exec, crti/crtn splice) | same | `[TCG-SECTION-EXEC]` |
//! | `.iplt` | `.plt` (exec; segment turns RWX) | `.iplt` (exec; RWX) | `[TCG-SECTION-EXEC]` |
//! | `.rodata`, `.rodata.*` | `.rodata` (read-only) | `.rodata` (by flags) | immutable, no pointer slot |
//! | `.rodata1` | `.rodata1` (read-only; a writable member turns the text segment RWX) | orphan | immutable, no pointer slot |
//! | `.eh_frame_entry*` (a prefix: `.eh_frame_entryx`, `.eh_frame_entry_x`, ...) | parsed by name as compact unwind entries wherever placed (link error beside the C runtime's DWARF `.eh_frame`) | orphan | `[TCG-SECTION-RESERVED]` |
//! | `.eh_frame.*`, `.sframe[.*]`, `.gcc_except_table.*`, `.gnu_extab*`, `.exception_ranges*` | unwind output, read-only, or `PT_GNU_RELRO` when a member is writable (a store faults) | orphan (`.gcc_except_table` by flags) | `[TCG-SECTION-RESERVED]` |
//! | `.tdata`, `.tdata.*` / `.tbss`, `.tbss.*` | `.tdata` / `.tbss` (`PT_TLS`) | same | thread-local only |
//! | `.tcommon` | `.tbss` (inside `PT_GNU_RELRO`, a store faults; beside a thread-local member it joins the `PT_TLS` template) | orphan | `[TCG-SECTION-TLS]` |
//! | `.preinit_array`, `.init_array[.*]`, `.fini_array[.*]` | same name, `PT_GNU_RELRO` | same | immutable pointer table |
//! | `.ctors[.*]`, `.dtors[.*]` | `.init_array` / `.fini_array`, `PT_GNU_RELRO` | `.ctors` / `.dtors`, `PT_GNU_RELRO` | `[TCG-SECTION-CTORS]` |
//! | `.jcr` | `.jcr`, `PT_GNU_RELRO` | `.jcr`, `PT_GNU_RELRO` | `[TCG-SECTION-RESERVED]` (crtstuff table) |
//! | `.data.rel.ro`, `.data.rel.ro.*` | `.data.rel.ro`, `PT_GNU_RELRO` | same | immutable |
//! | `.igot`, `.igot.plt` | `.got` (`PT_GNU_RELRO` under `-z now`) | orphan | `[TCG-SECTION-RESERVED]` |
//! | `.toc` | orphan | `.toc`, `PT_GNU_RELRO` | immutable |
//! | `.relro_padding` | orphan | synthetic `.relro_padding` (link error) | `[TCG-SECTION-RESERVED]` |
//! | `.bss.rel.ro`, `.bss.rel.ro.*` | `.bss` | `.bss.rel.ro`, `PT_GNU_RELRO` | immutable zero fill |
//! | `.data`, `.data.*` / `.data1` | `.data` / `.data1` | `.data` / orphan | writable data |
//! | `.bss`, `.bss.*` | `.bss` | `.bss` | zero fill |
//! | `COMMON` | `.bss` (the common-symbol pseudo-section) | `.bss` | `[TCG-SECTION-RESERVED]` |
//! | `.sbss*`, `.lbss*`, `.sdata*`, `.ldata*`, `.lrodata*`, `.srodata*` | orphan | `.sbss` ... `.srodata` (by flags) | by flags (`.sbss*`/`.lbss*` zero fill) |
//! | `.rela*` / `.relr.dyn` / `.stab*str` | orphan typed `SHT_RELA` (`-shared`: a store faults) / `SHT_RELR` (`-shared`: unusable library) / `SHT_STRTAB` | orphan | `[TCG-SECTION-RESERVED]` |
//! | `.stab`, `.stabstr`, `.stab.excl[str]`, `.stab.index[str]`, `.line` | non-allocated at address 0 (link error) | orphan | `[TCG-SECTION-RESERVED]` |
//! | `.gnu_debuglink` | `/DISCARD/` (link error) | orphan | `[TCG-SECTION-RESERVED]` |
//! | `.tm_clone_table` | orphan, between crtbegin's `__TMC_LIST__` and crtend's `__TMC_END__` | same | `[TCG-SECTION-RESERVED]` (crtstuff table) |
//!
//! The other names both scripts give meaning to (`.interp`, `.hash`,
//! `.dyn*`, `.got*`, `.plt`, `.rela.*`, `.gnu.*`, `.note*`, `.comment`,
//! `.debug*`, `.eh_frame`, `.eh_frame_hdr`, `.gcc_except_table`, `.ARM.*`)
//! are writer- or linker-owned names refused before the table. A mutable
//! global in a read-only or `PT_GNU_RELRO` output under EITHER linker is
//! `[TCG-SECTION-READONLY]`, so `.bss.rel.ro` and `.toc` are
//! immutable-only although GNU ld leaves them writable. Every refusal
//! applies to both linkers' outputs: a name one linker gives special
//! meaning is refused even where the other would honour it. Names with no
//! row (`.data.rel.rox`, `.bss.rel.rox`, `.tcommon.x`, `.jcrx`,
//! `.eh_framex`, `.eh_frame_entq`, `.rodata1.x`, `.stabx`, `.linex`,
//! `.relro`, `tcg_custom`, ...) are orphans under both linkers and keep the
//! global's own flags. Being one character past a family is not enough on
//! its own: where BFD matches a raw prefix by name (`.eh_frame_entry*`,
//! `.rela*`) or a prefix and suffix (`.stab*str`), every name it matches has
//! a row and is refused, `.eh_frame_entryx` and `.relax` included.
//!
//! GNU ld 2.42's default AArch64 script has no pattern for `.sbss*` or
//! `.lbss*`, so it places them as orphans by their `SHT_NOBITS`
//! `SHF_ALLOC|SHF_WRITE` flags. AArch64 has no counterpart of x86-64's
//! `SHF_X86_64_LARGE`, so `.lbss` carries no large-section flag.
//!
//! Without an explicit name, [`ElfImplicitSection`] is the one placement
//! decision for both the shared implicit sections and the own
//! `<base>.<symbol>` section of a COMDAT (grouped) or retained definition. A
//! symbol whose `<base>.<symbol>` would leave `<base>`'s row of the table (a
//! mutable symbol literally named `rel.ro` or `rel.ro.*` makes
//! `.data.rel.ro...` or `.bss.rel.ro...`) is refused by name
//! ([`ElfImplicitSection::unique_section`]).
//!
//! ## ELF functions (AArch64, trust-ir v45 `Function.section`)
//!
//! Every honoured name is an `SHT_PROGBITS` `SHF_ALLOC|SHF_EXECINSTR`
//! section ([`classify_elf_function_section`]); the text planner packs the
//! functions that share a name and gives a COMDAT function its own grouped
//! section of that name. `.text` itself is the shared default text section.
//! Honoured names are an allowlist: a `.text`-prefixed name (`.text`,
//! `.text.*`, `.textual`) or a name that does not start with `.`. GNU ld
//! 2.42's default AArch64 script folds `.text` and `.text.*` into the `.text`
//! output and matches no other `.text`-prefixed or undotted input name, so
//! the linker places those as orphans by their `SHF_ALLOC|SHF_EXECINSTR`
//! flags; lld folds only `.text` and `.text.*` the same way. Refused: the
//! data-global rule's malformed and reserved names, `.init` and `.fini` (the
//! C runtime splices their contents into one `_init`/`_fini` body), the
//! data-class names the default scripts merge into data storage
//! ([`SectionRefusal::DataSection`]), the unwind and debug families
//! ([`SectionRefusal::ReservedName`]), every other dot-prefixed name,
//! which is the toolchains' own namespace ([`SectionRefusal::ReservedName`]),
//! and `COMMON`, the one undotted name both linkers fold into `.bss`
//! ([`SectionRefusal::DataSection`]). A name a data global in the same
//! object also uses is a [`SectionRefusal::FlagConflict`].
//!
//! ## Mach-O (AArch64)
//!
//! A name must be a `segment,section[,type[,attributes]]` pair with 1..=16
//! byte components. Segments `__DATA`, `__DATA_CONST` and `__TEXT` are
//! honored (`__TEXT` only for immutable relocation-free data, `__DATA_CONST`
//! only for immutable data); `__DATA,__mod_init_func` / `__DATA_CONST,__mod_init_func`
//! become an `S_MOD_INIT_FUNC_POINTERS` constructor table under the same slot
//! rule as `.init_array`. The type may be `regular` (or `mod_init_funcs` for a
//! constructor table) and the attribute `no_dead_strip`. Section names the
//! linker gives special meaning (`__text`, `__cstring`, `__thread_*`,
//! `__mod_term_func`, `__eh_frame`, ...) are refused.

use std::fmt;

use crate::pipeline::ObjectGlobal;

/// Pointer width of every supported object target.
const POINTER_SIZE: usize = 8;

/// Longest explicit section name accepted on ELF (bytes).
const MAX_ELF_SECTION_NAME: usize = 1024;

/// Mach-O `segname` / `sectname` field width.
const MACHO_NAME_FIELD: usize = 16;

/// Why an explicit section request cannot be honored. Each variant is a stable
/// diagnostic code (`[TCG-SECTION-*]`) that tests and tooling match on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SectionRefusal {
    /// The name is empty, too long, or contains a character the object format
    /// cannot carry faithfully (whitespace, control, quote, `,` on ELF).
    MalformedName,
    /// The name belongs to a section the writer, linker or loader owns.
    ReservedName,
    /// Data placed in an executable section.
    ExecutableSection,
    /// Code placed in a data, zero-fill, thread-local or constructor-table
    /// section.
    DataSection,
    /// A zero-fill (`SHT_NOBITS`) section requested for a global whose
    /// initial image has a nonzero byte or a relocated pointer slot: NOBITS
    /// has no file bytes to hold the value or for a relocation to patch.
    ZeroFillSection,
    /// The legacy `.ctors` / `.dtors` tables, whose run order is reversed
    /// relative to `.init_array` / `.fini_array`.
    LegacyConstructorTable,
    /// A thread-local global outside a TLS section, or a non-TLS global in one.
    ThreadLocalMismatch,
    /// A mutable global in a read-only (or read-only-after-relocation)
    /// section, or a relocated pointer in a read-only section.
    ReadOnlyMismatch,
    /// A constructor/destructor table whose content is not a whole number of
    /// relocated pointer slots.
    PointerTableShape,
    /// Globals sharing one section name derive different types or flags.
    FlagConflict,
    /// A Mach-O name that is not a valid `segment,section` pair.
    MachOPair,
    /// A Mach-O segment this emitter does not place data in.
    MachOSegment,
    /// A Mach-O section type or attribute this emitter does not honor.
    MachOAttribute,
    /// An IMPORT with a section: it places no bytes in this object.
    Import,
    /// The target's object emitter has no explicit-section placement.
    TargetUnsupported,
}

impl SectionRefusal {
    /// The stable diagnostic code.
    pub const fn code(self) -> &'static str {
        match self {
            Self::MalformedName => "TCG-SECTION-NAME",
            Self::ReservedName => "TCG-SECTION-RESERVED",
            Self::ExecutableSection => "TCG-SECTION-EXEC",
            Self::DataSection => "TCG-SECTION-DATA",
            Self::ZeroFillSection => "TCG-SECTION-NOBITS",
            Self::LegacyConstructorTable => "TCG-SECTION-CTORS",
            Self::ThreadLocalMismatch => "TCG-SECTION-TLS",
            Self::ReadOnlyMismatch => "TCG-SECTION-READONLY",
            Self::PointerTableShape => "TCG-SECTION-POINTER-TABLE",
            Self::FlagConflict => "TCG-SECTION-FLAGS",
            Self::MachOPair => "TCG-SECTION-MACHO-PAIR",
            Self::MachOSegment => "TCG-SECTION-MACHO-SEGMENT",
            Self::MachOAttribute => "TCG-SECTION-MACHO-ATTR",
            Self::Import => "TCG-SECTION-IMPORT",
            Self::TargetUnsupported => "TCG-SECTION-TARGET",
        }
    }
}

impl fmt::Display for SectionRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.code())
    }
}

/// A refusal before it is attached to a global and object format.
pub(crate) type Refusal = (SectionRefusal, String);

fn refuse<T>(code: SectionRefusal, reason: impl Into<String>) -> Result<T, Refusal> {
    Err((code, reason.into()))
}

/// The ELF section an explicit request resolves to (before `SHF_GNU_RETAIN`,
/// which the emitter ORs in per section from its members).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ElfExplicitSection {
    pub(crate) sh_type: u32,
    pub(crate) sh_flags: u64,
    pub(crate) entsize: u64,
    /// Minimum section alignment in bytes (pointer tables need 8).
    pub(crate) min_align: u32,
    /// The members' symbols are `STT_TLS`.
    pub(crate) tls: bool,
}

/// `name` equals `base` or starts with `base` followed by `.`.
fn is_dotted(name: &str, base: &str) -> bool {
    name == base
        || name
            .strip_prefix(base)
            .is_some_and(|rest| rest.starts_with('.'))
}

/// `.init_array` / `.fini_array` with an optional numeric priority suffix
/// (`.init_array.00099`, the `SORT_BY_INIT_PRIORITY` spelling).
fn is_priority_table(name: &str, base: &str) -> bool {
    match name.strip_prefix(base) {
        Some("") => true,
        Some(rest) => rest.strip_prefix('.').is_some_and(|priority| {
            (1..=5).contains(&priority.len()) && priority.bytes().all(|b| b.is_ascii_digit())
        }),
        None => false,
    }
}

/// Every 8-byte slot of a constructor/destructor table must be a relocated
/// pointer: the runtime CALLS each entry, so a raw constant (which would not
/// be rebased in a PIE) or a partial slot is never a valid entry.
fn check_pointer_table(global: &ObjectGlobal, what: &str) -> Result<(), Refusal> {
    if global.is_thread_local {
        return refuse(
            SectionRefusal::ThreadLocalMismatch,
            format!(
                "a thread-local global cannot be a {what} (the runtime reads one shared table)"
            ),
        );
    }
    let len = global.data.len();
    if len == 0 || !len.is_multiple_of(POINTER_SIZE) {
        return refuse(
            SectionRefusal::PointerTableShape,
            format!("a {what} holds whole 8-byte pointers; this global has {len} bytes"),
        );
    }
    if global.symbol_refs.len() != len / POINTER_SIZE {
        return refuse(
            SectionRefusal::PointerTableShape,
            format!(
                "a {what} of {} slots carries {} pointer relocations; every slot must hold exactly one",
                len / POINTER_SIZE,
                global.symbol_refs.len()
            ),
        );
    }
    for slot in (0..len).step_by(POINTER_SIZE) {
        if !global
            .symbol_refs
            .iter()
            .any(|symbol_ref| symbol_ref.offset == slot as u64)
        {
            return refuse(
                SectionRefusal::PointerTableShape,
                format!(
                    "{what} slot at byte {slot} is not a relocated function pointer; every entry \
                     is called by the runtime"
                ),
            );
        }
    }
    Ok(())
}

fn check_elf_name(name: &str) -> Result<(), Refusal> {
    if name.is_empty() {
        return refuse(SectionRefusal::MalformedName, "the name is empty");
    }
    if name.len() > MAX_ELF_SECTION_NAME {
        return refuse(
            SectionRefusal::MalformedName,
            format!(
                "the name is {} bytes (maximum {MAX_ELF_SECTION_NAME})",
                name.len()
            ),
        );
    }
    if name.contains(',') {
        return refuse(
            SectionRefusal::MalformedName,
            "a `,` spells a Mach-O `segment,section` pair, not an ELF section name",
        );
    }
    if let Some(bad) = name
        .chars()
        .find(|c| !(c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '$' | '-')))
    {
        return refuse(
            SectionRefusal::MalformedName,
            format!("character {bad:?} is outside [A-Za-z0-9._$-]"),
        );
    }
    Ok(())
}

/// The explicit section names LLVM 22's `TargetLoweringObjectFileELF`
/// (`getELFKindForNamedSection`) gives `SectionKind::Metadata` whatever the
/// global or function placed there: the clang coverage-mapping sections
/// (`getInstrProfSectionName` of `IPSK_covmap`, `IPSK_covfun`,
/// `IPSK_covdata` and `IPSK_covname` on ELF). llc 22.1.2 emits each one
/// `SHT_PROGBITS` with no flags at all, so the linker does not load it: a
/// program that reads such a global through its symbol, or calls such a
/// function, reads unloaded bytes or faults. The names `.llvmbc` and
/// `.llvmcmd`, the other two the same rule names, fall under the reserved
/// `.llvm` prefix. This backend places only loaded sections, so it refuses
/// these names rather than load bytes llc leaves unloaded. The section-name
/// sweep recorded with the L02-P13 second closure-audit repair compiled
/// every name LLVM 22 classifies by name with llc and this backend; these
/// four were the only names both admit with different flags.
pub(crate) const ELF_METADATA_SECTION_NAMES: [&str; 4] = [
    "__llvm_covmap",
    "__llvm_covfun",
    "__llvm_covdata",
    "__llvm_covnames",
];

/// Names whose sections the ELF writer, linker or loader owns, and the
/// names LLVM makes non-allocated metadata ([`ELF_METADATA_SECTION_NAMES`]).
fn elf_reserved_reason(name: &str) -> Option<&'static str> {
    if ELF_METADATA_SECTION_NAMES.contains(&name) {
        return Some(
            "LLVM 22 gives this coverage-mapping name SectionKind::Metadata: llc emits it without SHF_ALLOC, so its bytes are never loaded, and this backend places only loaded sections",
        );
    }
    const EXACT: [&str; 13] = [
        ".symtab",
        ".strtab",
        ".shstrtab",
        ".symtab_shndx",
        ".group",
        ".interp",
        ".hash",
        ".eh_frame",
        ".eh_frame_hdr",
        ".gcc_except_table",
        ".comment",
        ".rel",
        ".rela",
    ];
    const PREFIXES: [&str; 11] = [
        ".rela.", ".rel.", ".debug", ".zdebug", ".note", ".got", ".plt", ".dyn", ".gnu.", ".llvm",
        ".ARM.",
    ];
    if EXACT.contains(&name) {
        return Some("the object writer or linker owns this section");
    }
    if PREFIXES.iter().any(|prefix| name.starts_with(prefix)) {
        return Some("the name is in a namespace the writer, linker or loader owns");
    }
    None
}

/// The GNU linker this module's placement table was derived from.
const GNU_LD: &str = "GNU ld 2.42";
/// The LLVM linker this module's placement table was derived from.
const LLD: &str = "LLD 22.1.6";

/// Where one linker's default link (no `-T` script) puts an input section of
/// a given name. See the module doc table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ElfPlacement {
    /// No rule names the input: an orphan output of the same name, placed by
    /// the input's own flags.
    Orphan,
    /// A named output that takes its flags from its members (writable when
    /// any member is), outside `PT_GNU_RELRO`.
    ByFlags(&'static str),
    /// A named writable output after `PT_GNU_RELRO`.
    Writable(&'static str),
    /// A named output in the read-only text segment.
    ReadOnly(&'static str),
    /// A named output inside `PT_GNU_RELRO`: writable only while the loader
    /// relocates the image.
    Relro(&'static str),
    /// A named `PT_TLS` output.
    ThreadLocal(&'static str),
    /// A named executable output.
    Executable(&'static str),
    /// An output the linker parses, merges or synthesizes (the output and
    /// what the linker builds there): unwind and exception tables, the GOT,
    /// the common-symbol pseudo-section.
    LinkerOwned(&'static str, &'static str),
    /// An orphan whose output section BFD's special-section table types by
    /// name (the `sh_type` named here) rather than taking the input's
    /// `SHT_PROGBITS`.
    TypedByName(&'static str),
    /// BFD reads every INPUT section whose name matches as this kind of
    /// table, wherever the script places it (a rule outside the script,
    /// decided by name).
    ParsedByName(&'static str),
    /// A non-allocated output at address 0 (stabs, `.line`).
    Unloaded(&'static str),
    /// `/DISCARD/`.
    Discarded,
}

impl ElfPlacement {
    /// Read-only after load (text segment or `PT_GNU_RELRO`): a store faults.
    const fn write_protected(self) -> bool {
        matches!(self, Self::ReadOnly(_) | Self::Relro(_))
    }

    /// Where the placement puts the bytes, as a clause of a refusal reason.
    fn describe(self) -> String {
        match self {
            Self::Orphan => "places it as an orphan by its flags".into(),
            Self::ByFlags(out) | Self::Writable(out) => format!("places it in `{out}`"),
            Self::ReadOnly(out) => format!("places it in `{out}` in the read-only text segment"),
            Self::Relro(out) => format!("places it in `{out}` inside PT_GNU_RELRO"),
            Self::ThreadLocal(out) => format!(
                "places it in its thread-local `{out}` output (inside PT_GNU_RELRO, and part of the PT_TLS template once any member is thread-local)"
            ),
            Self::Executable(out) => format!("places it in its executable `{out}` output"),
            Self::LinkerOwned(out, role) => format!("places it in `{out}` ({role})"),
            Self::TypedByName(sh_type) => format!("types an output of that name {sh_type}"),
            Self::ParsedByName(what) => {
                format!("parses every input section so named as {what}, wherever it is placed")
            }
            Self::Unloaded(out) => format!(
                "maps it to the non-allocated `{out}` output at address 0, which fails the link"
            ),
            Self::Discarded => "discards it, which fails the link of any reference".into(),
        }
    }
}

/// One family of input-section names and where each linker's default link
/// puts it ([`ELF_NAME_RULES`]).
#[derive(Debug)]
pub(crate) struct ElfNameRule {
    /// Names as the linkers spell them: exact, or a glob where `*` matches
    /// any run of characters.
    pub(crate) patterns: &'static [&'static str],
    /// GNU ld 2.42 with its default AArch64 script.
    pub(crate) gnu: ElfPlacement,
    /// LLD 22.1.6 without a SECTIONS command.
    pub(crate) lld: ElfPlacement,
    /// The C runtime walks the output as a table of its own.
    pub(crate) runtime_table: Option<&'static str>,
}

impl ElfNameRule {
    const fn new(patterns: &'static [&'static str], gnu: ElfPlacement, lld: ElfPlacement) -> Self {
        Self {
            patterns,
            gnu,
            lld,
            runtime_table: None,
        }
    }

    /// Each linker's placement, labelled.
    const fn placements(&self) -> [(&'static str, ElfPlacement); 2] {
        [(GNU_LD, self.gnu), (LLD, self.lld)]
    }

    /// `"<linker> <placement>"` for each linker whose placement satisfies
    /// `pred`, joined with `; `; `None` when neither does.
    fn clauses(&self, pred: impl Fn(ElfPlacement) -> bool) -> Option<String> {
        let clauses: Vec<String> = self
            .placements()
            .into_iter()
            .filter(|(_, placement)| pred(*placement))
            .map(|(linker, placement)| format!("{linker} {}", placement.describe()))
            .collect();
        (!clauses.is_empty()).then(|| clauses.join("; "))
    }

    /// Why a MUTABLE global cannot live under this name: either linker puts
    /// it in a read-only or `PT_GNU_RELRO` output.
    fn write_protected_reason(&self, name: &str) -> Option<String> {
        let text_segment = self
            .placements()
            .iter()
            .any(|(_, placement)| matches!(placement, ElfPlacement::ReadOnly(_)));
        self.clauses(ElfPlacement::write_protected).map(|clauses| {
            format!(
                "`{name}` is read-only at run time: {clauses}; a mutable global would fault on its first store{}",
                if text_segment {
                    " (or, as GNU ld 2.42 links a writable member, make the text segment writable and executable)"
                } else {
                    ""
                }
            )
        })
    }

    /// Why a relocated pointer cannot live under this name: either linker
    /// puts it in the read-only text segment.
    fn text_relocation_reason(&self, name: &str) -> Option<String> {
        self.clauses(|placement| matches!(placement, ElfPlacement::ReadOnly(_)))
            .map(|clauses| {
                format!(
                    "`{name}` is read-only: {clauses}; a relocated pointer there needs a text relocation, use `.data.rel.ro`"
                )
            })
    }

    fn executable_reason(&self, name: &str) -> Option<String> {
        self.clauses(|placement| matches!(placement, ElfPlacement::Executable(_)))
            .map(|clauses| {
                format!(
                    "`{name}` is executable: {clauses}; a data global cannot be placed in an executable section"
                )
            })
    }

    fn thread_local_reason(&self, name: &str) -> Option<String> {
        self.clauses(|placement| matches!(placement, ElfPlacement::ThreadLocal(_)))
            .map(|clauses| {
                format!(
                    "`{name}` is thread-local storage: {clauses}; it holds thread-local templates only"
                )
            })
    }

    /// Why no data global may use this name: a linker parses, synthesizes,
    /// types, drops or discards the output, or the C runtime reads it as a
    /// table.
    fn special_reason(&self, name: &str) -> Option<String> {
        let linker = self.clauses(|placement| {
            matches!(
                placement,
                ElfPlacement::LinkerOwned(..)
                    | ElfPlacement::TypedByName(_)
                    | ElfPlacement::ParsedByName(_)
                    | ElfPlacement::Unloaded(_)
                    | ElfPlacement::Discarded
            )
        });
        match (linker, self.runtime_table) {
            (None, None) => None,
            (linker, runtime) => {
                let mut parts: Vec<String> = runtime.map(str::to_string).into_iter().collect();
                parts.extend(linker);
                if runtime.is_some() {
                    parts.extend(self.clauses(ElfPlacement::write_protected));
                }
                Some(format!(
                    "`{name}` is not plain data: {}; a data global there is not honoured as its own storage",
                    parts.join("; ")
                ))
            }
        }
    }
}

/// `pattern` (a linker glob: `*` matches any run, possibly empty) matches
/// `name`.
pub(crate) fn glob_matches(pattern: &str, name: &str) -> bool {
    let (pattern, name) = (pattern.as_bytes(), name.as_bytes());
    let (mut p, mut n) = (0, 0);
    let mut star: Option<(usize, usize)> = None;
    while n < name.len() {
        if p < pattern.len() && pattern[p] == b'*' {
            star = Some((p, n));
            p += 1;
        } else if p < pattern.len() && (pattern[p] == name[n] || pattern[p] == b'?') {
            p += 1;
            n += 1;
        } else if let Some((star_p, star_n)) = star {
            p = star_p + 1;
            n = star_n + 1;
            star = Some((star_p, star_n + 1));
        } else {
            return false;
        }
    }
    pattern[p..].iter().all(|&b| b == b'*')
}

/// Where GNU ld 2.42's default AArch64 script and LLD 22.1.6's built-in
/// rules put an input section, first match wins; a name no row matches is
/// an orphan under both. Derived from `ld --verbose` and from the rules BFD
/// applies by name outside the script (checked against the retained script
/// and the retained by-name list by
/// `elf_name_rules_match_the_gnu_ld_2_42_default_script`) and from LLD's
/// folding and `PT_GNU_RELRO` rules (probed; module doc). Writer-owned names
/// ([`elf_reserved_reason`]) are refused before this table is consulted.
pub(crate) const ELF_NAME_RULES: &[ElfNameRule] = {
    use ElfPlacement::{
        ByFlags, Discarded, Executable, LinkerOwned, Orphan, ParsedByName, ReadOnly, Relro,
        ThreadLocal, TypedByName, Unloaded, Writable,
    };
    const CRTSTUFF_JCR: &str =
        "it is the Java class registration table (`__JCR_LIST__`) gcc's crtstuff can walk";
    const CRTSTUFF_TM: &str = "crtbegin.o and crtend.o bracket it as `__TMC_LIST__`..`__TMC_END__` and hand it to `_ITM_registerTMCloneTable`";
    &[
        // Executable outputs.
        ElfNameRule::new(
            &[".text", ".text.*"],
            Executable(".text"),
            Executable(".text"),
        ),
        ElfNameRule::new(&[".stub"], Executable(".text"), Orphan),
        ElfNameRule::new(&[".init"], Executable(".init"), Executable(".init")),
        ElfNameRule::new(&[".fini"], Executable(".fini"), Executable(".fini")),
        ElfNameRule::new(&[".iplt"], Executable(".plt"), Executable(".iplt")),
        // Read-only outputs.
        ElfNameRule::new(
            &[".rodata", ".rodata.*"],
            ReadOnly(".rodata"),
            ByFlags(".rodata"),
        ),
        ElfNameRule::new(&[".rodata1"], ReadOnly(".rodata1"), Orphan),
        // Unwind and exception tables. BFD parses every input whose name
        // STARTS with `.eh_frame_entry` as compact unwind entries (a
        // prefix, no `.` boundary: `.eh_frame_entryx` too, although the
        // script names only `.eh_frame_entry[.*]`); beside the C runtime's
        // DWARF `.eh_frame` the link then fails.
        ElfNameRule::new(
            &[".eh_frame_entry*"],
            ParsedByName(
                "compact unwind entries (the link then fails beside the C runtime's DWARF `.eh_frame`)",
            ),
            Orphan,
        ),
        // GNU ld's ONLY_IF_RO/ONLY_IF_RW pairs.
        ElfNameRule::new(
            &[".eh_frame.*"],
            LinkerOwned(".eh_frame", "the unwind table it parses and indexes"),
            Orphan,
        ),
        ElfNameRule::new(
            &[".sframe", ".sframe.*"],
            LinkerOwned(".sframe", "the SFrame unwind table it parses and merges"),
            Orphan,
        ),
        ElfNameRule::new(
            &[".gcc_except_table.*"],
            LinkerOwned(".gcc_except_table", "the exception tables"),
            ByFlags(".gcc_except_table"),
        ),
        ElfNameRule::new(
            &[".gnu_extab*"],
            LinkerOwned(".gnu_extab", "the exception tables"),
            Orphan,
        ),
        ElfNameRule::new(
            &[".exception_ranges*"],
            LinkerOwned(".exception_ranges", "the exception tables"),
            Orphan,
        ),
        // Thread-local outputs.
        ElfNameRule::new(
            &[".tdata", ".tdata.*"],
            ThreadLocal(".tdata"),
            ThreadLocal(".tdata"),
        ),
        ElfNameRule::new(
            &[".tbss", ".tbss.*"],
            ThreadLocal(".tbss"),
            ThreadLocal(".tbss"),
        ),
        ElfNameRule::new(&[".tcommon"], ThreadLocal(".tbss"), Orphan),
        // PT_GNU_RELRO outputs.
        ElfNameRule::new(
            &[".preinit_array"],
            Relro(".preinit_array"),
            Relro(".preinit_array"),
        ),
        ElfNameRule::new(
            &[".init_array", ".init_array.*"],
            Relro(".init_array"),
            Relro(".init_array"),
        ),
        ElfNameRule::new(
            &[".fini_array", ".fini_array.*"],
            Relro(".fini_array"),
            Relro(".fini_array"),
        ),
        ElfNameRule::new(
            &[".ctors", ".ctors.*"],
            Relro(".init_array"),
            Relro(".ctors"),
        ),
        ElfNameRule::new(
            &[".dtors", ".dtors.*"],
            Relro(".fini_array"),
            Relro(".dtors"),
        ),
        ElfNameRule {
            runtime_table: Some(CRTSTUFF_JCR),
            ..ElfNameRule::new(&[".jcr"], Relro(".jcr"), Relro(".jcr"))
        },
        ElfNameRule::new(
            &[".data.rel.ro", ".data.rel.ro.*"],
            Relro(".data.rel.ro"),
            Relro(".data.rel.ro"),
        ),
        ElfNameRule::new(
            &[".igot", ".igot.plt"],
            LinkerOwned(".got", "the GOT it builds"),
            Orphan,
        ),
        ElfNameRule::new(&[".toc"], Orphan, Relro(".toc")),
        ElfNameRule::new(
            &[".relro_padding"],
            Orphan,
            LinkerOwned(".relro_padding", "the PT_GNU_RELRO padding it synthesizes"),
        ),
        // Writable data outputs.
        ElfNameRule::new(
            &[".bss.rel.ro", ".bss.rel.ro.*"],
            Writable(".bss"),
            Relro(".bss.rel.ro"),
        ),
        ElfNameRule::new(&[".data", ".data.*"], Writable(".data"), ByFlags(".data")),
        ElfNameRule::new(&[".data1"], Writable(".data1"), Orphan),
        ElfNameRule::new(&[".bss", ".bss.*"], Writable(".bss"), ByFlags(".bss")),
        ElfNameRule::new(
            &["COMMON"],
            LinkerOwned(".bss", "the name of its common-symbol pseudo-section"),
            LinkerOwned(".bss", "the name of its common-symbol pseudo-section"),
        ),
        ElfNameRule::new(&[".sbss", ".sbss.*"], Orphan, ByFlags(".sbss")),
        ElfNameRule::new(&[".lbss", ".lbss.*"], Orphan, ByFlags(".lbss")),
        ElfNameRule::new(&[".sdata", ".sdata.*"], Orphan, ByFlags(".sdata")),
        ElfNameRule::new(&[".ldata", ".ldata.*"], Orphan, ByFlags(".ldata")),
        ElfNameRule::new(&[".lrodata", ".lrodata.*"], Orphan, ByFlags(".lrodata")),
        ElfNameRule::new(&[".srodata", ".srodata.*"], Orphan, ByFlags(".srodata")),
        // Output types BFD assigns by name.
        ElfNameRule::new(&[".rela*"], TypedByName("SHT_RELA"), Orphan),
        ElfNameRule::new(&[".relr.dyn"], TypedByName("SHT_RELR"), Orphan),
        // Non-allocated and discarded outputs.
        ElfNameRule::new(
            &[
                ".stab",
                ".stabstr",
                ".stab.excl",
                ".stab.exclstr",
                ".stab.index",
                ".stab.indexstr",
            ],
            Unloaded(".stab"),
            Orphan,
        ),
        ElfNameRule::new(&[".stab*str"], TypedByName("SHT_STRTAB"), Orphan),
        ElfNameRule::new(&[".line"], Unloaded(".line"), Orphan),
        ElfNameRule::new(&[".gnu_debuglink"], Discarded, Orphan),
        // Tables the C runtime walks without a linker rule.
        ElfNameRule {
            runtime_table: Some(CRTSTUFF_TM),
            ..ElfNameRule::new(&[".tm_clone_table"], Orphan, Orphan)
        },
    ]
};

/// Whether a mutable global may be placed in an ELF section named `name`:
/// no [`ELF_NAME_RULES`] row puts that name in a read-only or
/// `PT_GNU_RELRO` output under either linker (a mutable global there is
/// refused, [`SectionRefusal::ReadOnlyMismatch`]). `.data.rel.ro`,
/// `.bss.rel.ro`, `.init_array`, `.fini_array`, `.preinit_array` and `.toc`
/// hold immutable data only; `.data`, `.bss`, their `.<name>` forms and
/// orphan names may hold mutable data.
pub(crate) fn elf_name_may_hold_mutable(name: &str) -> bool {
    !elf_name_rule(name)
        .is_some_and(|rule| rule.gnu.write_protected() || rule.lld.write_protected())
}

/// The [`ELF_NAME_RULES`] row for `name`; `None` is an orphan under both
/// linkers.
pub(crate) fn elf_name_rule(name: &str) -> Option<&'static ElfNameRule> {
    ELF_NAME_RULES.iter().find(|rule| {
        rule.patterns
            .iter()
            .any(|pattern| glob_matches(pattern, name))
    })
}

/// Resolve an explicit ELF section request for `global`.
pub(crate) fn classify_elf_section(
    global: &ObjectGlobal,
    name: &str,
) -> Result<ElfExplicitSection, Refusal> {
    check_elf_name(name)?;
    classify_elf_section_name(global, name)
}

/// [`classify_elf_section`] after the name-syntax check. The implicit
/// COMDAT name `<base>.<symbol>` takes this path directly: a symbol may be
/// longer or use more characters than an explicit request, but the linkers
/// place its section by the same rules.
fn classify_elf_section_name(
    global: &ObjectGlobal,
    name: &str,
) -> Result<ElfExplicitSection, Refusal> {
    use crate::elf::constants::{
        SHF_ALLOC, SHF_TLS, SHF_WRITE, SHT_FINI_ARRAY, SHT_INIT_ARRAY, SHT_NOBITS,
        SHT_PREINIT_ARRAY, SHT_PROGBITS,
    };

    if let Some(reason) = elf_reserved_reason(name) {
        return refuse(SectionRefusal::ReservedName, reason);
    }
    let rule = elf_name_rule(name);
    if let Some(reason) = rule.and_then(|rule| rule.executable_reason(name)) {
        return refuse(SectionRefusal::ExecutableSection, reason);
    }
    let write_protected = rule.and_then(|rule| rule.write_protected_reason(name));
    if let Some(base) = ELF_ZERO_FILL_FAMILIES
        .iter()
        .find(|base| is_dotted(name, base))
    {
        // Content is checked first, so every nonzero or relocated request
        // in a zero-fill name is a `[TCG-SECTION-NOBITS]` refusal.
        if !global.symbol_refs.is_empty() {
            return refuse(
                SectionRefusal::ZeroFillSection,
                format!(
                    "`{base}` is SHT_NOBITS; a relocated pointer slot needs file bytes to patch"
                ),
            );
        }
        if !is_elf_zero_fill(global) {
            return refuse(
                SectionRefusal::ZeroFillSection,
                format!(
                    "`{base}` is SHT_NOBITS and zero-filled at load; a nonzero initializer would be dropped"
                ),
            );
        }
        let tls = *base == ".tbss";
        if tls != global.is_thread_local {
            return refuse(
                SectionRefusal::ThreadLocalMismatch,
                if global.is_thread_local {
                    "a thread-local zero-fill template must be placed in a `.tbss` section"
                } else {
                    "a `.tbss` section holds thread-local templates only"
                },
            );
        }
        // The write-protected zero-fill names are `.bss.rel.ro[.*]`, which
        // LLD folds into its `.bss.rel.ro` output inside PT_GNU_RELRO (the
        // zero-fill twin of `.data.rel.ro`): the same mutability rule.
        if global.mutable
            && let Some(reason) = &write_protected
        {
            return refuse(SectionRefusal::ReadOnlyMismatch, reason.clone());
        }
        return Ok(ElfExplicitSection {
            sh_type: SHT_NOBITS,
            sh_flags: SHF_ALLOC | SHF_WRITE | if tls { SHF_TLS } else { 0 },
            entsize: 0,
            min_align: 1,
            tls,
        });
    }
    if is_dotted(name, ".ctors") || is_dotted(name, ".dtors") {
        return refuse(
            SectionRefusal::LegacyConstructorTable,
            "legacy .ctors/.dtors run in reverse order; use .init_array/.fini_array",
        );
    }

    let progbits = |flags: u64| ElfExplicitSection {
        sh_type: SHT_PROGBITS,
        sh_flags: flags,
        entsize: 0,
        min_align: 1,
        tls: false,
    };
    // Every constructor-table output is inside PT_GNU_RELRO under both
    // linkers: the loader writes the relocated slots, then the table is
    // read-only, so only an immutable table may name one.
    let pointer_table = |sh_type: u32, what: &str| -> Result<ElfExplicitSection, Refusal> {
        check_pointer_table(global, what)?;
        if global.mutable
            && let Some(reason) = &write_protected
        {
            return refuse(SectionRefusal::ReadOnlyMismatch, reason.clone());
        }
        Ok(ElfExplicitSection {
            sh_type,
            sh_flags: SHF_ALLOC | SHF_WRITE,
            entsize: POINTER_SIZE as u64,
            min_align: POINTER_SIZE as u32,
            tls: false,
        })
    };
    if is_priority_table(name, ".init_array") {
        return pointer_table(SHT_INIT_ARRAY, "constructor table (.init_array)");
    }
    if is_priority_table(name, ".fini_array") {
        return pointer_table(SHT_FINI_ARRAY, "destructor table (.fini_array)");
    }
    if name == ".preinit_array" {
        return pointer_table(SHT_PREINIT_ARRAY, "pre-init table (.preinit_array)");
    }
    if is_dotted(name, ".init_array")
        || is_dotted(name, ".fini_array")
        || is_dotted(name, ".preinit_array")
    {
        return refuse(
            SectionRefusal::ReservedName,
            "a constructor-table suffix must be a 1-5 digit priority (`.init_array.00099`)",
        );
    }
    // Unwind and exception tables, linker-synthesized or name-typed
    // outputs, unloaded or discarded outputs, crtstuff tables.
    if let Some(reason) = rule.and_then(|rule| rule.special_reason(name)) {
        return refuse(SectionRefusal::ReservedName, reason);
    }

    // Thread-local templates are honoured in `.tdata*` (here) and `.tbss*`
    // (the zero-fill arm) only, where both linkers build PT_TLS; GNU ld also
    // folds `.tcommon` into its `.tbss` output.
    let tls_section = is_dotted(name, ".tdata");
    if !global.is_thread_local
        && !tls_section
        && let Some(reason) = rule.and_then(|rule| rule.thread_local_reason(name))
    {
        return refuse(SectionRefusal::ThreadLocalMismatch, reason);
    }
    if tls_section != global.is_thread_local {
        return refuse(
            SectionRefusal::ThreadLocalMismatch,
            if global.is_thread_local {
                "a thread-local global must be placed in a `.tdata` section"
            } else {
                "a `.tdata` section holds thread-local templates only"
            },
        );
    }
    if tls_section {
        return Ok(ElfExplicitSection {
            tls: true,
            ..progbits(SHF_ALLOC | SHF_WRITE | SHF_TLS)
        });
    }

    // Read-only (`.rodata*`, `.rodata1`) and PT_GNU_RELRO (`.data.rel.ro*`,
    // `.toc`) outputs under either linker.
    if global.mutable
        && let Some(reason) = write_protected
    {
        return refuse(SectionRefusal::ReadOnlyMismatch, reason);
    }
    let relocated = !global.symbol_refs.is_empty();
    if let Some(reason) = rule.and_then(|rule| rule.text_relocation_reason(name)) {
        if relocated {
            return refuse(SectionRefusal::ReadOnlyMismatch, reason);
        }
        return Ok(progbits(SHF_ALLOC));
    }
    // `.data*` (an immutable `.data.rel.ro*` member included) and `.data1`
    // are writable data outputs whatever the member.
    if is_dotted(name, ".data") || name == ".data1" {
        return Ok(progbits(SHF_ALLOC | SHF_WRITE));
    }
    // An orphan under both linkers (or a folded output that takes its
    // members' flags): its flags come from the global itself, as LLVM
    // derives a section kind from the global.
    Ok(progbits(if global.mutable || relocated {
        SHF_ALLOC | SHF_WRITE
    } else {
        SHF_ALLOC
    }))
}

/// Resolve an explicit ELF section request for a FUNCTION (trust-ir v45
/// `Function.section`). An honoured name always becomes an `SHT_PROGBITS`
/// `SHF_ALLOC|SHF_EXECINSTR` section, so the only question is whether the
/// name may carry code at all.
///
/// The accepted set is an allowlist, not the complement of a deny-list: a
/// name that starts with `.text`, or a name that does not start with `.`.
/// GNU ld 2.42's default AArch64 script (`ld --verbose`) folds `.text`,
/// `.text.*` (and its `.text.hot`/`.text.unlikely`/... spellings) into the
/// `.text` output section and has no pattern for any other `.text`-prefixed
/// or any undotted input name, so those are orphans the linker places after
/// `.text` by their executable flags; lld folds exactly `.text` and `.text.*`
/// into `.text` and places the rest by flags too.
///
/// Refused, with the most specific reason first: the names
/// [`classify_elf_section`] refuses as malformed or reserved; `.init` and
/// `.fini`, whose input sections crti/crtn splice into one `_init`/`_fini`
/// body, so a whole function there would return from it; the data-class
/// names (`.data*`, `.data1`, `.rodata*`, `.rodata1`, `.bss*`, `.tbss*`,
/// `.tcommon*`, `.sbss*`, `.sdata*`, `.lbss*`, `.ldata*`, `.lrodata*`,
/// `.tdata*`, `.init_array*`, `.fini_array*`, `.preinit_array*`, `.ctors*`,
/// `.dtors*`, `.jcr*`, `.tm_clone_table*`), where the linker would merge the
/// body into non-executable or runtime-read storage
/// ([`SectionRefusal::DataSection`]); the unwind and debug families
/// (`.eh_frame*`, `.gcc_except_table*`, `.gnu_extab*`, `.exception_ranges*`,
/// `.sframe*`, `.stab*`, `.line*`), which the linker merges into unwind
/// tables or keeps unloaded ([`SectionRefusal::ReservedName`]); every
/// other dot-prefixed name, which is the toolchains' namespace
/// ([`SectionRefusal::ReservedName`]); and any remaining name an
/// [`ELF_NAME_RULES`] row places outside an executable output under either
/// linker: `COMMON`, the one undotted name, which both linkers fold into
/// `.bss` (the probe's function there ran from a writable-and-executable
/// segment), is [`SectionRefusal::DataSection`].
pub(crate) fn classify_elf_function_section(name: &str) -> Result<(), Refusal> {
    check_elf_name(name)?;
    if let Some(reason) = elf_reserved_reason(name) {
        return refuse(SectionRefusal::ReservedName, reason);
    }
    if name == ".init" || name == ".fini" {
        return refuse(
            SectionRefusal::ReservedName,
            "crti/crtn splice `.init`/`.fini` input sections into one `_init`/`_fini` body; a whole function there would return from it",
        );
    }
    const DATA_CLASS: [&str; 22] = [
        ".data",
        ".data1",
        ".rodata",
        ".rodata1",
        ".bss",
        ".tbss",
        ".tcommon",
        ".sbss",
        ".sbss2",
        ".sdata",
        ".sdata2",
        ".lbss",
        ".ldata",
        ".lrodata",
        ".tdata",
        ".init_array",
        ".fini_array",
        ".preinit_array",
        ".ctors",
        ".dtors",
        ".jcr",
        ".tm_clone_table",
    ];
    if let Some(base) = DATA_CLASS.iter().find(|base| is_dotted(name, base)) {
        return refuse(
            SectionRefusal::DataSection,
            format!(
                "`{base}` names a data, zero-fill, thread-local or runtime-read table section; the linker would merge a function body there into non-executable or runtime-read storage"
            ),
        );
    }
    // Glob prefixes, as the default scripts spell them (`.gnu_extab*`,
    // `.stab*` also match `.stabstr` and `.stab.excl`).
    const UNWIND_OR_DEBUG: [&str; 7] = [
        ".eh_frame",
        ".gcc_except_table",
        ".gnu_extab",
        ".exception_ranges",
        ".sframe",
        ".stab",
        ".line",
    ];
    if let Some(prefix) = UNWIND_OR_DEBUG
        .iter()
        .find(|prefix| name.starts_with(*prefix))
    {
        return refuse(
            SectionRefusal::ReservedName,
            format!(
                "`{prefix}*` is an unwind or debug family the linker merges into unwind tables or leaves unloaded; a function body there is not executable code"
            ),
        );
    }
    if name.starts_with('.') && !name.starts_with(".text") {
        return refuse(
            SectionRefusal::ReservedName,
            "a dot-prefixed name outside the `.text` family is the toolchains' namespace, which a default linker script may map to data, unwind or unloaded output; a function section is `.text`, `.text*` or a name without a leading `.`",
        );
    }
    if let Some(rule) = elf_name_rule(name)
        && rule
            .placements()
            .iter()
            .any(|(_, placement)| !matches!(placement, ElfPlacement::Executable(_)))
    {
        let clauses = rule
            .clauses(|placement| !matches!(placement, ElfPlacement::Executable(_)))
            .unwrap_or_default();
        return refuse(
            SectionRefusal::DataSection,
            format!(
                "`{name}` is not an executable output: {clauses}; a function body there would run from data storage"
            ),
        );
    }
    Ok(())
}

/// The explicit zero-fill name families: a name equal to one of these bases
/// or extending it after a `.` is an `SHT_NOBITS` section (`.tbss` is the
/// thread-local one).
const ELF_ZERO_FILL_FAMILIES: [&str; 4] = [".bss", ".tbss", ".sbss", ".lbss"];

/// Whether `global`'s initial image needs no file bytes: every byte is zero
/// and no relocated pointer slot must be patched into it (LLVM's
/// `isSuitableForBSS` content rule). [`ElfImplicitSection::of`] adds the
/// mutability rule for non-TLS data.
pub(crate) fn is_elf_zero_fill(global: &ObjectGlobal) -> bool {
    global.symbol_refs.is_empty() && global.data.iter().all(|&byte| byte == 0)
}

/// The implicit ELF section class of a DEFINITION without an explicit
/// section: the one decision behind both the shared implicit sections and
/// the own `<base>.<symbol>` section of a COMDAT definition (a group member)
/// or a retained one (`SHF_GNU_RETAIN`).
///
/// A retained definition gets its own section because `SHF_GNU_RETAIN`
/// keeps a whole input section: in a shared section it would keep every
/// neighbour (and the undefined references their bytes hold) through
/// `--gc-sections`. LLVM 22 places an `@llvm.used` global the same way
/// (`TargetLoweringObjectFileELF::SelectSectionForGlobal`: a retained global
/// takes a unique section, `<kind prefix>.<symbol>` without an explicit
/// name). Its name matches llc's wherever the kinds agree. They differ in
/// three places, which change no linker placement: a private global's
/// section uses its object symbol (`.data.p`) where llc uses its `.L` label
/// (`.data..Lp`); an `unnamed_addr` constant, whose permission to merge the
/// importer drops, stays in `.rodata.<symbol>` where llc may choose a
/// mergeable `.rodata.cst<N>.` or `.rodata.str<W>.<A>.` prefix; and a
/// relocated constant is always `.data.rel.ro.<symbol>`, where llc's
/// `static` model writes `.rodata.<symbol>`.
///
/// A writable all-zero definition without a relocated pointer slot is zero
/// fill (`.bss`, `SHT_NOBITS`); an immutable one keeps read-only protection
/// in `.rodata`. A thread-local image is a per-thread writable copy either
/// way, so every all-zero template without a pointer slot is `.tbss`; a
/// relocated template stays in `.tdata` even when its bytes are all zero.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ElfImplicitSection {
    Data,
    Bss,
    Rodata,
    DataRelRo,
    Tdata,
    Tbss,
}

impl ElfImplicitSection {
    /// Emission order of the shared implicit sections.
    pub(crate) const ORDER: [Self; 6] = [
        Self::Data,
        Self::Bss,
        Self::Rodata,
        Self::DataRelRo,
        Self::Tdata,
        Self::Tbss,
    ];

    /// The class of a non-import definition.
    pub(crate) fn of(global: &ObjectGlobal) -> Self {
        let zero_fill = is_elf_zero_fill(global);
        if global.is_thread_local {
            if zero_fill { Self::Tbss } else { Self::Tdata }
        } else if global.mutable {
            if zero_fill { Self::Bss } else { Self::Data }
        } else if global.symbol_refs.is_empty() {
            Self::Rodata
        } else {
            // Absolute pointers in an immutable table still need loader
            // relocations in PIE/shared images: writable during relocation,
            // then protected by the linker's PT_GNU_RELRO placement.
            Self::DataRelRo
        }
    }

    /// The section name; a COMDAT or retained definition's own section is
    /// `<base>.<symbol>`.
    pub(crate) const fn base(self) -> &'static str {
        match self {
            Self::Data => ".data",
            Self::Bss => ".bss",
            Self::Rodata => ".rodata",
            Self::DataRelRo => ".data.rel.ro",
            Self::Tdata => ".tdata",
            Self::Tbss => ".tbss",
        }
    }

    pub(crate) const fn sh_type(self) -> u32 {
        use crate::elf::constants::{SHT_NOBITS, SHT_PROGBITS};
        match self {
            Self::Bss | Self::Tbss => SHT_NOBITS,
            Self::Data | Self::Rodata | Self::DataRelRo | Self::Tdata => SHT_PROGBITS,
        }
    }

    pub(crate) const fn sh_flags(self) -> u64 {
        use crate::elf::constants::{SHF_ALLOC, SHF_TLS, SHF_WRITE};
        match self {
            Self::Rodata => SHF_ALLOC,
            Self::Data | Self::Bss | Self::DataRelRo => SHF_ALLOC | SHF_WRITE,
            Self::Tdata | Self::Tbss => SHF_ALLOC | SHF_WRITE | SHF_TLS,
        }
    }

    /// The members' symbols are `STT_TLS`.
    pub(crate) const fn tls(self) -> bool {
        matches!(self, Self::Tdata | Self::Tbss)
    }

    /// The name of a COMDAT or retained definition's own section,
    /// `<base>.<symbol>`: the spelling GCC's and LLVM's unique sections use.
    pub(crate) fn unique_section_name(global: &ObjectGlobal) -> String {
        format!("{}.{}", Self::of(global).base(), global.name)
    }

    /// The own section a COMDAT or retained definition without an explicit
    /// name gets: [`Self::unique_section_name`] with this class's type and
    /// flags (before `SHF_GROUP` and `SHF_GNU_RETAIN`, which the emitter
    /// adds).
    ///
    /// The linkers place an input section by its name (a group only decides
    /// which copy survives, retention only that it survives), so a symbol
    /// can move the name into another row of [`ELF_NAME_RULES`]: a mutable
    /// symbol literally named `rel.ro` or `rel.ro.*` makes `.data.rel.ro...`
    /// (PT_GNU_RELRO under both linkers) or `.bss.rel.ro...` (PT_GNU_RELRO
    /// under LLD). GCC and LLVM spell their unique sections the same way and
    /// rely on C identifiers and mangled names having no `.`; trust-ir
    /// symbols may contain one. Such a definition is refused by name with
    /// the explicit rule's code for that name, never renamed: a
    /// collision-free rename would be a placement no other toolchain
    /// produces for that symbol.
    pub(crate) fn unique_section(global: &ObjectGlobal) -> Result<ElfExplicitSection, Refusal> {
        let class = Self::of(global);
        let name = Self::unique_section_name(global);
        let section = ElfExplicitSection {
            sh_type: class.sh_type(),
            sh_flags: class.sh_flags(),
            entsize: 0,
            min_align: 1,
            tls: class.tls(),
        };
        check_unique_section(global, class.base(), &name)?;
        Ok(section)
    }
}

/// Admit `name`, the own `<base>.<symbol>` section of COMDAT or retained
/// `global`, only while it stays in `base`'s row of [`ELF_NAME_RULES`]
/// ([`unique_section_stays_in_rule`]); otherwise refuse it with the code
/// the explicit rule gives that name. The AArch64 implicit classes
/// ([`ElfImplicitSection::unique_section`]) and the x86-64 ELF emitter's
/// `.data`/`.rodata`/`.data.rel.ro` both ask it.
pub(crate) fn check_unique_section(
    global: &ObjectGlobal,
    base: &str,
    name: &str,
) -> Result<(), Refusal> {
    if unique_section_stays_in_rule(base, name) {
        return Ok(());
    }
    let (code, reason) = match classify_elf_section_name(global, name) {
        Err(refusal) => refusal,
        Ok(_) => (
            SectionRefusal::ReservedName,
            "the linkers place that name by another rule".to_string(),
        ),
    };
    Err((
        code,
        format!(
            "the implicit {} section of `{}` leaves the `{base}` placement rule: {reason}",
            unique_section_kind(global),
            global.name,
        ),
    ))
}

/// What gives `global` an own section, as the refusals name it: `COMDAT`
/// (a group member) or `retained` (`SHF_GNU_RETAIN`).
const fn unique_section_kind(global: &ObjectGlobal) -> &'static str {
    if global.comdat { "COMDAT" } else { "retained" }
}

/// Whether the own section `name` (`<base>.<symbol>`) of a definition stays
/// in `base`'s row of [`ELF_NAME_RULES`], so both linkers place it where they
/// place `base`.
fn unique_section_stays_in_rule(base: &str, name: &str) -> bool {
    match (elf_name_rule(name), elf_name_rule(base)) {
        (Some(member), Some(base)) => std::ptr::eq(member, base),
        _ => false,
    }
}

/// How the Mach-O emitter packs an explicit section's members.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MachOPlacement {
    /// Writable-at-load data (pointer slots become `ARM64_RELOC_UNSIGNED`).
    Data,
    /// Read-only, relocation-free bytes.
    Const,
}

/// The Mach-O section an explicit request resolves to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MachOExplicitSection {
    pub(crate) segname: String,
    pub(crate) sectname: String,
    /// `S_*` type plus attribute bits.
    pub(crate) flags: u32,
    pub(crate) placement: MachOPlacement,
    /// Minimum section alignment in bytes.
    pub(crate) min_align: u32,
}

fn macho_component_ok(component: &str) -> bool {
    (1..=MACHO_NAME_FIELD).contains(&component.len())
        && component
            .bytes()
            .all(|b| b.is_ascii_graphic() && b != b',' && b != b'"' && b != b'\'')
}

/// Section names ld64/dyld give a meaning this placement would not honor.
fn macho_reserved_reason(sectname: &str) -> Option<&'static str> {
    const EXACT: [&str; 21] = [
        "__text",
        "__stubs",
        "__stub_helper",
        "__cstring",
        "__literal4",
        "__literal8",
        "__literal16",
        "__la_symbol_ptr",
        "__nl_symbol_ptr",
        "__got",
        "__bss",
        "__common",
        "__thread_vars",
        "__thread_data",
        "__thread_bss",
        "__thread_ptrs",
        "__eh_frame",
        "__unwind_info",
        "__compact_unwind",
        "__gcc_except_tab",
        "__init_offsets",
    ];
    const PREFIXES: [&str; 3] = ["__objc_", "__auth_", "__debug_"];
    if sectname == "__mod_term_func" {
        return Some(
            "`__mod_term_func` terminators are not run by modern dyld; register a destructor with atexit",
        );
    }
    if EXACT.contains(&sectname) || PREFIXES.iter().any(|prefix| sectname.starts_with(prefix)) {
        return Some("the linker or loader gives this section a special type or meaning");
    }
    None
}

/// Resolve an explicit Mach-O section request for `global`.
pub(crate) fn classify_macho_section(
    global: &ObjectGlobal,
    name: &str,
) -> Result<MachOExplicitSection, Refusal> {
    use crate::macho::constants::{S_ATTR_NO_DEAD_STRIP, S_MOD_INIT_FUNC_POINTERS, S_REGULAR};

    let parts: Vec<&str> = name.split(',').collect();
    if !(2..=4).contains(&parts.len()) || !parts.iter().all(|part| macho_component_ok(part)) {
        return refuse(
            SectionRefusal::MachOPair,
            "a Mach-O section is `segment,section[,type[,attributes]]` with 1-16 byte printable components",
        );
    }
    let (segname, sectname) = (parts[0], parts[1]);
    if global.is_thread_local {
        return refuse(
            SectionRefusal::ThreadLocalMismatch,
            "a thread-local global is emitted through its TLV descriptor sections",
        );
    }
    if let Some(reason) = macho_reserved_reason(sectname) {
        return refuse(SectionRefusal::ReservedName, reason);
    }
    let init_table = sectname == "__mod_init_func";
    let mut flags = S_REGULAR;
    match parts.get(2).copied() {
        None | Some("regular") => {}
        Some("mod_init_funcs") if init_table => {}
        Some(other) => {
            return refuse(
                SectionRefusal::MachOAttribute,
                format!(
                    "section type `{other}` is not honored (only `regular`, or `mod_init_funcs` for `__mod_init_func`)"
                ),
            );
        }
    }
    match parts.get(3).copied() {
        None => {}
        Some("no_dead_strip") => flags |= S_ATTR_NO_DEAD_STRIP,
        Some(other) => {
            return refuse(
                SectionRefusal::MachOAttribute,
                format!("section attribute `{other}` is not honored (only `no_dead_strip`)"),
            );
        }
    }
    let relocated = !global.symbol_refs.is_empty();
    let placement = match segname {
        "__DATA" | "__DATA_CONST" if init_table => {
            check_pointer_table(global, "constructor table (__mod_init_func)")?;
            return Ok(MachOExplicitSection {
                segname: segname.to_string(),
                sectname: sectname.to_string(),
                flags: flags | S_MOD_INIT_FUNC_POINTERS,
                placement: MachOPlacement::Data,
                min_align: POINTER_SIZE as u32,
            });
        }
        "__DATA" if sectname == "__const" && global.mutable => {
            return refuse(
                SectionRefusal::ReadOnlyMismatch,
                "ld64 and the in-repo linker place `__DATA,__const` in the read-only-after-fixups `__DATA_CONST` segment; a mutable global would fault on write",
            );
        }
        "__DATA" => MachOPlacement::Data,
        "__DATA_CONST" => {
            if global.mutable {
                return refuse(
                    SectionRefusal::ReadOnlyMismatch,
                    "`__DATA_CONST` is read-only after fixups; a mutable global would fault on write",
                );
            }
            MachOPlacement::Data
        }
        "__TEXT" => {
            if global.mutable || relocated {
                return refuse(
                    SectionRefusal::ReadOnlyMismatch,
                    "the read-only `__TEXT` segment holds only immutable relocation-free data",
                );
            }
            MachOPlacement::Const
        }
        other => {
            return refuse(
                SectionRefusal::MachOSegment,
                format!(
                    "segment `{other}` is not placed by this emitter (only __DATA, __DATA_CONST, __TEXT)"
                ),
            );
        }
    };
    Ok(MachOExplicitSection {
        segname: segname.to_string(),
        sectname: sectname.to_string(),
        flags,
        placement,
        min_align: 1,
    })
}

/// The JIT's one rule for trust-ir v41 `Global.section`: a module that asks
/// for an explicit output section for any global is refused, by name.
///
/// A section name is an OBJECT-placement request. The AArch64 object emitters
/// honor a well-formed one, which is why the adapter admits it on AArch64, but
/// a JIT installs code and data without object sections: the placement, and a
/// constructor table's run-before-entry semantics, would be silently dropped.
/// Every JIT lane therefore applies this rule itself, before translation:
/// [`crate::compiler::Compiler::compile_module_to_jit_with_profile_hooks`]
/// (and so `compile_module_to_jit`) here, and a consumer that assembles its own
/// JIT lane from trust-cg parts (the adapter, the JIT LIR module step, the
/// pipeline and a raw link) calls this same function, so the rule is stated
/// once. Core JIT admission refuses every global, so it never reaches one.
pub fn refuse_jit_object_sections(
    module: &trust_ir::Module,
) -> Result<(), crate::pipeline::PipelineError> {
    let Some(global) = module
        .globals
        .iter()
        .find(|global| global.section.is_some())
    else {
        return Ok(());
    };
    Err(crate::pipeline::PipelineError::ExplicitSectionUnsupported {
        global: global.name.clone(),
        section: global.section.clone().unwrap_or_default(),
        format: "JIT",
        code: SectionRefusal::TargetUnsupported,
        reason: "the JIT installs code and data without object sections, so the placement (and \
                 any constructor table) would be dropped"
            .to_string(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elf::constants::{
        SHF_ALLOC, SHF_TLS, SHF_WRITE, SHT_FINI_ARRAY, SHT_INIT_ARRAY, SHT_PREINIT_ARRAY,
        SHT_PROGBITS,
    };
    use crate::pipeline::GlobalSymbolRef;

    fn global(data: Vec<u8>, mutable: bool) -> ObjectGlobal {
        ObjectGlobal {
            name: "G".into(),
            data,
            mutable,
            is_external: true,
            symbol_refs: vec![],
            is_thread_local: false,
            is_import: false,
            is_weak: false,
            align: 8,
            visibility: trust_ir::Visibility::Default,
            retained: false,
            section: None,
            comdat: false,
        }
    }

    fn table(slots: usize) -> ObjectGlobal {
        let mut g = global(vec![0; slots * 8], false);
        g.symbol_refs = (0..slots)
            .map(|slot| GlobalSymbolRef {
                offset: (slot * 8) as u64,
                symbol: format!("ctor{slot}"),
                addend: 0,
            })
            .collect();
        g
    }

    fn elf_code(g: &ObjectGlobal, name: &str) -> SectionRefusal {
        classify_elf_section(g, name).expect_err(name).0
    }

    #[test]
    fn elf_pointer_tables_get_their_types_and_entsize() {
        for (name, sh_type) in [
            (".init_array", SHT_INIT_ARRAY),
            (".init_array.00099", SHT_INIT_ARRAY),
            (".fini_array", SHT_FINI_ARRAY),
            (".fini_array.65535", SHT_FINI_ARRAY),
            (".preinit_array", SHT_PREINIT_ARRAY),
        ] {
            let section = classify_elf_section(&table(2), name).expect(name);
            assert_eq!(section.sh_type, sh_type, "{name}");
            assert_eq!(section.sh_flags, SHF_ALLOC | SHF_WRITE, "{name}");
            assert_eq!((section.entsize, section.min_align), (8, 8), "{name}");
        }
    }

    #[test]
    fn elf_pointer_tables_refuse_non_pointer_content() {
        // Raw constant slot, partial slot, empty table, TLS table.
        let mut raw = table(2);
        raw.symbol_refs.pop();
        assert_eq!(
            elf_code(&raw, ".init_array"),
            SectionRefusal::PointerTableShape
        );
        let mut partial = table(1);
        partial.data.push(0);
        assert_eq!(
            elf_code(&partial, ".fini_array"),
            SectionRefusal::PointerTableShape
        );
        assert_eq!(
            elf_code(&global(vec![], false), ".init_array"),
            SectionRefusal::PointerTableShape
        );
        let mut tls = table(1);
        tls.is_thread_local = true;
        assert_eq!(
            elf_code(&tls, ".init_array"),
            SectionRefusal::ThreadLocalMismatch
        );
        assert_eq!(
            elf_code(&table(1), ".init_array.x1"),
            SectionRefusal::ReservedName
        );
        assert_eq!(
            elf_code(&table(1), ".init_array.123456"),
            SectionRefusal::ReservedName
        );
    }

    /// Adversarial: the slot COUNT can match while a slot is still not a
    /// pointer. Two relocations at bytes 0 and 4 of a 16-byte table leave the
    /// slot at byte 8 a raw constant the runtime would call; only the
    /// per-slot offset check catches it (a count-only check would accept
    /// it), on ELF and Mach-O alike.
    #[test]
    fn pointer_tables_refuse_a_misplaced_relocation_with_a_matching_count() {
        let mut shifted = table(2);
        shifted.symbol_refs[1].offset = 4;
        assert_eq!(shifted.symbol_refs.len(), shifted.data.len() / 8);
        for name in [".init_array", ".fini_array.00001", ".preinit_array"] {
            assert_eq!(
                elf_code(&shifted, name),
                SectionRefusal::PointerTableShape,
                "{name}"
            );
        }
        assert_eq!(
            classify_macho_section(&shifted, "__DATA,__mod_init_func")
                .expect_err("misplaced slot")
                .0,
            SectionRefusal::PointerTableShape
        );
    }

    #[test]
    fn elf_flags_follow_the_name_kind_and_the_global() {
        let constant = global(vec![1; 8], false);
        let mutable = global(vec![1; 8], true);
        let mut relocated = table(1);
        relocated.name = "R".into();
        let flags = |g: &ObjectGlobal, name: &str| {
            let section = classify_elf_section(g, name).expect(name);
            assert_eq!(section.sh_type, SHT_PROGBITS);
            section.sh_flags
        };
        assert_eq!(flags(&constant, ".rodata.keep"), SHF_ALLOC);
        assert_eq!(flags(&constant, ".data.rel.ro.x"), SHF_ALLOC | SHF_WRITE);
        assert_eq!(flags(&relocated, ".data.rel.ro"), SHF_ALLOC | SHF_WRITE);
        assert_eq!(flags(&constant, ".data.custom"), SHF_ALLOC | SHF_WRITE);
        assert_eq!(flags(&mutable, "my_section"), SHF_ALLOC | SHF_WRITE);
        assert_eq!(flags(&relocated, "my_section"), SHF_ALLOC | SHF_WRITE);
        assert_eq!(flags(&constant, "my_section"), SHF_ALLOC);
        let mut tls = mutable.clone();
        tls.is_thread_local = true;
        let section = classify_elf_section(&tls, ".tdata.hot").unwrap();
        assert!(section.tls);
        assert_eq!(section.sh_flags, SHF_ALLOC | SHF_WRITE | SHF_TLS);
    }

    #[test]
    fn elf_refusals_are_named() {
        let constant = global(vec![1; 8], false);
        let mutable = global(vec![1; 8], true);
        let mut tls = mutable.clone();
        tls.is_thread_local = true;
        for (g, name, code) in [
            (&constant, "", SectionRefusal::MalformedName),
            (&constant, "has space", SectionRefusal::MalformedName),
            (&constant, "__DATA,__data", SectionRefusal::MalformedName),
            (&constant, ".symtab", SectionRefusal::ReservedName),
            (&constant, ".rela.data", SectionRefusal::ReservedName),
            (&constant, ".debug_info", SectionRefusal::ReservedName),
            (&constant, ".note.custom", SectionRefusal::ReservedName),
            (&constant, ".eh_frame", SectionRefusal::ReservedName),
            (&constant, ".gnu.linkonce.d.x", SectionRefusal::ReservedName),
            (&constant, ".text", SectionRefusal::ExecutableSection),
            (
                &constant,
                ".text.startup",
                SectionRefusal::ExecutableSection,
            ),
            (&constant, ".init", SectionRefusal::ExecutableSection),
            (&mutable, ".bss.x", SectionRefusal::ZeroFillSection),
            (&tls, ".tbss", SectionRefusal::ZeroFillSection),
            (&constant, ".ctors", SectionRefusal::LegacyConstructorTable),
            (
                &constant,
                ".dtors.00001",
                SectionRefusal::LegacyConstructorTable,
            ),
            (&tls, ".data", SectionRefusal::ThreadLocalMismatch),
            (&constant, ".tdata", SectionRefusal::ThreadLocalMismatch),
            (&mutable, ".rodata", SectionRefusal::ReadOnlyMismatch),
            (&mutable, ".data.rel.ro", SectionRefusal::ReadOnlyMismatch),
            (&table(1), ".rodata.table", SectionRefusal::ReadOnlyMismatch),
        ] {
            assert_eq!(elf_code(g, name), code, "{name:?}");
        }
        // A `.text` prefix without a dot boundary is an ordinary name.
        assert!(classify_elf_section(&constant, ".textual").is_ok());
        assert!(classify_elf_section(&constant, &"x".repeat(1025)).is_err());
    }

    /// The coverage-mapping names LLVM 22 makes non-allocated metadata by
    /// name are refused for every data kind and for a function, while a
    /// name one byte away (and the coverage names LLVM does not classify,
    /// `__llvm_covinit`, `__llvm_prf_*`) keeps the global's own flags.
    #[test]
    fn llvm_metadata_section_names_are_refused_for_data_and_functions() {
        let constant = global(vec![1; 8], false);
        let mutable = global(vec![1; 8], true);
        let zero = global(vec![0; 8], true);
        for name in ELF_METADATA_SECTION_NAMES {
            for g in [&constant, &mutable, &zero, &table(1)] {
                let (code, reason) = classify_elf_section(g, name).expect_err(name);
                assert_eq!(code, SectionRefusal::ReservedName, "{name}: {reason}");
                assert!(
                    reason.contains("SectionKind::Metadata") && reason.contains("SHF_ALLOC"),
                    "{name}: {reason}"
                );
            }
            assert_eq!(
                classify_elf_function_section(name).expect_err(name).0,
                SectionRefusal::ReservedName,
                "{name}"
            );
        }
        for name in [
            "__llvm_covmapx",
            "__llvm_covinit",
            "__llvm_prf_cnts",
            "__llvm_prf_data",
        ] {
            assert_eq!(
                classify_elf_section(&constant, name).expect(name).sh_flags,
                SHF_ALLOC,
                "{name}"
            );
            assert!(classify_elf_function_section(name).is_ok(), "{name}");
        }
    }

    /// Every zero-fill family is `SHT_NOBITS` for an all-zero,
    /// relocation-free global of the matching TLS kind (mutable, immutable
    /// or zero-sized), with `SHF_TLS` only on `.tbss`. A nonzero byte or a
    /// relocated pointer slot is `[TCG-SECTION-NOBITS]` in every family,
    /// ahead of any TLS mismatch; an all-zero global of the wrong TLS kind is
    /// `[TCG-SECTION-TLS]`. A mutable global in `.bss.rel.ro[.*]` (lld's
    /// RELRO zero fill) is `[TCG-SECTION-READONLY]`. A name that only shares
    /// the prefix without a `.` boundary is an ordinary PROGBITS name.
    #[test]
    fn elf_zero_fill_names_are_nobits_only_for_all_zero_relocation_free_globals() {
        use crate::elf::constants::SHT_NOBITS;
        let zero = global(vec![0; 24], true);
        let zero_constant = global(vec![0; 16], false);
        let empty = global(vec![], true);
        let mut tls_zero = global(vec![0; 32], true);
        tls_zero.is_thread_local = true;
        let mut tls_zero_constant = tls_zero.clone();
        tls_zero_constant.mutable = false;
        for (g, name) in [
            (&zero, ".bss"),
            (&zero, ".bss.tcg"),
            (&zero, ".sbss"),
            (&zero, ".sbss.x"),
            (&zero, ".lbss"),
            (&zero, ".lbss.big"),
            (&zero_constant, ".bss.constant"),
            (&empty, ".bss.empty"),
            // An immutable global may use the RELRO zero-fill sub-family.
            (&zero_constant, ".bss.rel.ro"),
            (&zero_constant, ".bss.rel.ro.x"),
            // No `.` boundary after `.bss.rel.ro`: lld folds it into `.bss`.
            (&zero, ".bss.rel.rox"),
        ] {
            let section = classify_elf_section(g, name).expect(name);
            assert_eq!(
                section,
                ElfExplicitSection {
                    sh_type: SHT_NOBITS,
                    sh_flags: SHF_ALLOC | SHF_WRITE,
                    entsize: 0,
                    min_align: 1,
                    tls: false,
                },
                "{name}"
            );
        }
        for (g, name) in [
            (&tls_zero, ".tbss"),
            (&tls_zero, ".tbss.hot"),
            (&tls_zero_constant, ".tbss.constant"),
        ] {
            let section = classify_elf_section(g, name).expect(name);
            assert_eq!(
                section,
                ElfExplicitSection {
                    sh_type: SHT_NOBITS,
                    sh_flags: SHF_ALLOC | SHF_WRITE | SHF_TLS,
                    entsize: 0,
                    min_align: 1,
                    tls: true,
                },
                "{name}"
            );
        }

        let mut nonzero_tail = global(vec![0; 24], true);
        nonzero_tail.data[23] = 1;
        let mut tls_nonzero = tls_zero.clone();
        tls_nonzero.data[0] = 9;
        // All-zero bytes, but slot 0 is a relocated pointer to patch.
        let mut zero_slot = table(1);
        zero_slot.mutable = true;
        for (g, name) in [
            (&nonzero_tail, ".bss"),
            (&nonzero_tail, ".bss.tcg"),
            (&nonzero_tail, ".sbss"),
            (&nonzero_tail, ".lbss.big"),
            (&tls_nonzero, ".tbss"),
            (&tls_nonzero, ".tbss.hot"),
            (&zero_slot, ".bss.slot"),
            (&zero_slot, ".sbss"),
            (&nonzero_tail, ".bss.rel.ro"),
            // Content is refused before the TLS kind.
            (&tls_nonzero, ".bss"),
            (&nonzero_tail, ".tbss"),
        ] {
            let (code, reason) = classify_elf_section(g, name).expect_err(name);
            assert_eq!(code, SectionRefusal::ZeroFillSection, "{name}: {reason}");
            assert_eq!(code.code(), "TCG-SECTION-NOBITS");
        }
        for (g, name) in [
            (&tls_zero, ".bss"),
            (&tls_zero, ".sbss.x"),
            (&zero, ".tbss"),
            (&zero_constant, ".tbss.x"),
        ] {
            assert_eq!(
                elf_code(g, name),
                SectionRefusal::ThreadLocalMismatch,
                "{name}"
            );
        }
        // lld folds `.bss.rel.ro[.*]` into its `.bss.rel.ro` output inside
        // PT_GNU_RELRO, so a mutable global there (empty or not) would fault
        // on its first store: the `.data.rel.ro` rule, by name.
        let empty_constant = global(vec![], false);
        assert!(classify_elf_section(&empty_constant, ".bss.rel.ro").is_ok());
        for (g, name) in [
            (&zero, ".bss.rel.ro"),
            (&zero, ".bss.rel.ro.x"),
            (&zero, ".bss.rel.ro.tcg.hot"),
            (&empty, ".bss.rel.ro"),
        ] {
            let (code, reason) = classify_elf_section(g, name).expect_err(name);
            assert_eq!(code, SectionRefusal::ReadOnlyMismatch, "{name}: {reason}");
            assert_eq!(code.code(), "TCG-SECTION-READONLY");
            assert!(reason.contains("PT_GNU_RELRO"), "{name}: {reason}");
        }
        for name in [".bssx", ".tbss_x", ".lbssy"] {
            let section = classify_elf_section(&zero, name).expect(name);
            assert_eq!(section.sh_type, SHT_PROGBITS, "{name}");
        }
    }

    /// The implicit class is one decision for the shared sections and the
    /// COMDAT `<base>.<symbol>` sections: zero fill needs every byte zero
    /// and no pointer slot, non-TLS zero fill also needs mutability, and
    /// every thread-local zero template is `.tbss`.
    #[test]
    fn elf_implicit_section_class_matrix() {
        use crate::elf::constants::SHT_NOBITS;
        let mut slot = table(1);
        slot.mutable = true;
        let immutable_slot = table(1);
        let with = |data: Vec<u8>, mutable: bool, tls: bool| {
            let mut g = global(data, mutable);
            g.is_thread_local = tls;
            g
        };
        let mut tls_slot = slot.clone();
        tls_slot.is_thread_local = true;
        for (g, class, base, sh_type, flags) in [
            (
                with(vec![1, 0], true, false),
                ElfImplicitSection::Data,
                ".data",
                SHT_PROGBITS,
                SHF_ALLOC | SHF_WRITE,
            ),
            (
                slot,
                ElfImplicitSection::Data,
                ".data",
                SHT_PROGBITS,
                SHF_ALLOC | SHF_WRITE,
            ),
            (
                with(vec![0; 8], true, false),
                ElfImplicitSection::Bss,
                ".bss",
                SHT_NOBITS,
                SHF_ALLOC | SHF_WRITE,
            ),
            (
                with(vec![], true, false),
                ElfImplicitSection::Bss,
                ".bss",
                SHT_NOBITS,
                SHF_ALLOC | SHF_WRITE,
            ),
            (
                with(vec![0; 8], false, false),
                ElfImplicitSection::Rodata,
                ".rodata",
                SHT_PROGBITS,
                SHF_ALLOC,
            ),
            (
                immutable_slot,
                ElfImplicitSection::DataRelRo,
                ".data.rel.ro",
                SHT_PROGBITS,
                SHF_ALLOC | SHF_WRITE,
            ),
            (
                with(vec![0, 3], true, true),
                ElfImplicitSection::Tdata,
                ".tdata",
                SHT_PROGBITS,
                SHF_ALLOC | SHF_WRITE | SHF_TLS,
            ),
            (
                tls_slot,
                ElfImplicitSection::Tdata,
                ".tdata",
                SHT_PROGBITS,
                SHF_ALLOC | SHF_WRITE | SHF_TLS,
            ),
            (
                with(vec![0; 8], true, true),
                ElfImplicitSection::Tbss,
                ".tbss",
                SHT_NOBITS,
                SHF_ALLOC | SHF_WRITE | SHF_TLS,
            ),
            (
                with(vec![0; 8], false, true),
                ElfImplicitSection::Tbss,
                ".tbss",
                SHT_NOBITS,
                SHF_ALLOC | SHF_WRITE | SHF_TLS,
            ),
        ] {
            let got = ElfImplicitSection::of(&g);
            assert_eq!(got, class, "{g:?}");
            assert_eq!(
                (got.base(), got.sh_type(), got.sh_flags(), got.tls()),
                (base, sh_type, flags, g.is_thread_local),
                "{g:?}"
            );
        }
        assert_eq!(ElfImplicitSection::ORDER.len(), 6);
    }

    /// A function section is executable or refused by name. Only the
    /// allowlist is honoured (`.text`-prefixed names and names without a
    /// leading `.`); the data-class families, the unwind and debug families
    /// GNU ld 2.42's default script maps to data, unwind or unloaded output
    /// (`.jcr`, `.tm_clone_table`, `.stab`, `.rodata1`, `.eh_frame.x`, ...),
    /// every other dot-prefixed name, the C-runtime `.init`/`.fini` splices
    /// and the global rule's malformed and reserved names are refused.
    #[test]
    fn elf_function_sections_accept_only_executable_names() {
        for name in [
            ".text",
            ".text.startup",
            ".text.hot.tcg",
            ".textual",
            ".text.unlikely",
            "tcg_code",
            "tcg$code-1",
            // An undotted name is an orphan even when it spells a data
            // family without the dot.
            "jcr",
            "rodata1",
            "common",
            "COMMONS",
        ] {
            classify_elf_function_section(name)
                .unwrap_or_else(|refusal| panic!("{name}: {refusal:?}"));
        }
        for (name, want) in [
            ("", SectionRefusal::MalformedName),
            ("has space", SectionRefusal::MalformedName),
            ("tab\there", SectionRefusal::MalformedName),
            ("__TEXT,__text", SectionRefusal::MalformedName),
            (".symtab", SectionRefusal::ReservedName),
            (".eh_frame", SectionRefusal::ReservedName),
            (".rela.text", SectionRefusal::ReservedName),
            (".plt", SectionRefusal::ReservedName),
            (".init", SectionRefusal::ReservedName),
            (".fini", SectionRefusal::ReservedName),
            (".data", SectionRefusal::DataSection),
            (".data.rel.ro", SectionRefusal::DataSection),
            (".data1", SectionRefusal::DataSection),
            (".rodata.str", SectionRefusal::DataSection),
            (".bss", SectionRefusal::DataSection),
            (".tbss.x", SectionRefusal::DataSection),
            (".tdata", SectionRefusal::DataSection),
            (".init_array", SectionRefusal::DataSection),
            (".fini_array.00001", SectionRefusal::DataSection),
            (".preinit_array", SectionRefusal::DataSection),
            (".ctors", SectionRefusal::DataSection),
            (".dtors.1", SectionRefusal::DataSection),
            (".jcr", SectionRefusal::DataSection),
            (".tm_clone_table", SectionRefusal::DataSection),
            (".rodata1", SectionRefusal::DataSection),
            (".tcommon", SectionRefusal::DataSection),
            (".sdata.x", SectionRefusal::DataSection),
            (".lrodata", SectionRefusal::DataSection),
            (".stab", SectionRefusal::ReservedName),
            (".stabstr", SectionRefusal::ReservedName),
            (".stab.excl", SectionRefusal::ReservedName),
            (".eh_frame.x", SectionRefusal::ReservedName),
            (".eh_frame_entry", SectionRefusal::ReservedName),
            (".gcc_except_table.f", SectionRefusal::ReservedName),
            (".gnu_extab", SectionRefusal::ReservedName),
            (".gnu_extab.f", SectionRefusal::ReservedName),
            (".exception_ranges.f", SectionRefusal::ReservedName),
            (".sframe", SectionRefusal::ReservedName),
            (".sframe.f", SectionRefusal::ReservedName),
            (".line", SectionRefusal::ReservedName),
            (".stub", SectionRefusal::ReservedName),
            (".igot", SectionRefusal::ReservedName),
            (".gnu_debuglink", SectionRefusal::ReservedName),
            (".custom_code", SectionRefusal::ReservedName),
            (".", SectionRefusal::ReservedName),
            // Both linkers fold the common-symbol pseudo-section into
            // `.bss`: the probe's function there ran from an RWX segment.
            ("COMMON", SectionRefusal::DataSection),
        ] {
            assert_eq!(
                classify_elf_function_section(name).expect_err(name).0,
                want,
                "{name:?}"
            );
        }
        assert_eq!(
            classify_elf_function_section(&"x".repeat(1025))
                .expect_err("over-long")
                .0,
            SectionRefusal::MalformedName
        );
    }

    #[test]
    fn macho_pairs_segments_and_constructor_tables() {
        use crate::macho::constants::{S_ATTR_NO_DEAD_STRIP, S_MOD_INIT_FUNC_POINTERS, S_REGULAR};
        let constant = global(vec![1; 8], false);
        let mutable = global(vec![1; 8], true);
        let ok = |g: &ObjectGlobal, name: &str| classify_macho_section(g, name).expect(name);
        let code =
            |g: &ObjectGlobal, name: &str| classify_macho_section(g, name).expect_err(name).0;

        let init = ok(&table(2), "__DATA,__mod_init_func");
        assert_eq!(init.flags, S_MOD_INIT_FUNC_POINTERS);
        assert_eq!(init.placement, MachOPlacement::Data);
        let init = ok(&table(1), "__DATA_CONST,__mod_init_func,mod_init_funcs");
        assert_eq!((init.segname.as_str(), init.min_align), ("__DATA_CONST", 8));
        let custom = ok(&mutable, "__DATA,__mydata,regular,no_dead_strip");
        assert_eq!(custom.flags, S_REGULAR | S_ATTR_NO_DEAD_STRIP);
        assert_eq!(
            ok(&constant, "__TEXT,__myconst").placement,
            MachOPlacement::Const
        );
        assert_eq!(
            ok(&constant, "__DATA_CONST,__cfg").placement,
            MachOPlacement::Data
        );
        // An immutable global may name the read-only-after-fixups
        // `__DATA,__const`; a mutable one is refused below.
        assert_eq!(
            ok(&constant, "__DATA,__const").placement,
            MachOPlacement::Data
        );

        let mut tls = mutable.clone();
        tls.is_thread_local = true;
        let mut raw = table(1);
        raw.symbol_refs.clear();
        for (g, name, want) in [
            (&constant, ".data", SectionRefusal::MachOPair),
            (&constant, "__DATA", SectionRefusal::MachOPair),
            (&constant, "__DATA,", SectionRefusal::MachOPair),
            (
                &constant,
                "__DATA,__a_name_longer_than_16",
                SectionRefusal::MachOPair,
            ),
            (&constant, "__LINKEDIT,__x", SectionRefusal::MachOSegment),
            (&constant, "__MYSEG,__x", SectionRefusal::MachOSegment),
            (&constant, "__TEXT,__text", SectionRefusal::ReservedName),
            (&constant, "__TEXT,__cstring", SectionRefusal::ReservedName),
            (
                &table(1),
                "__DATA,__mod_term_func",
                SectionRefusal::ReservedName,
            ),
            (
                &constant,
                "__DATA,__objc_data",
                SectionRefusal::ReservedName,
            ),
            (
                &constant,
                "__DATA,__x,zerofill",
                SectionRefusal::MachOAttribute,
            ),
            (
                &constant,
                "__DATA,__x,mod_init_funcs",
                SectionRefusal::MachOAttribute,
            ),
            (
                &constant,
                "__DATA,__x,regular,live_support",
                SectionRefusal::MachOAttribute,
            ),
            (&mutable, "__TEXT,__rw", SectionRefusal::ReadOnlyMismatch),
            (&table(1), "__TEXT,__ptrs", SectionRefusal::ReadOnlyMismatch),
            (
                &mutable,
                "__DATA_CONST,__rw",
                SectionRefusal::ReadOnlyMismatch,
            ),
            (&mutable, "__DATA,__const", SectionRefusal::ReadOnlyMismatch),
            (
                &raw,
                "__DATA,__mod_init_func",
                SectionRefusal::PointerTableShape,
            ),
            (&tls, "__DATA,__x", SectionRefusal::ThreadLocalMismatch),
        ] {
            assert_eq!(code(g, name), want, "{name:?}");
        }
    }

    /// One output statement of a GNU ld default script: its output name,
    /// the region the script puts it in, and its input-section patterns.
    #[derive(Debug)]
    struct ScriptStatement {
        output: String,
        region: ScriptRegion,
        patterns: Vec<String>,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum ScriptRegion {
        /// Before `DATA_SEGMENT_ALIGN`: the read-only text segment.
        ReadOnly,
        /// Between `DATA_SEGMENT_ALIGN` and `DATA_SEGMENT_RELRO_END`.
        Relro,
        /// After `DATA_SEGMENT_RELRO_END`.
        Writable,
        /// Address 0, `(INFO)`, or after `DATA_SEGMENT_END`.
        Unloaded,
        Discard,
    }

    /// The patterns inside every unqualified `*( ... )` input description
    /// of `body` (file-qualified `*crtbegin.o(...)` and `EXCLUDE_FILE` file
    /// lists are skipped: they name crt objects, not trust-cg's).
    fn script_patterns(body: &str) -> Vec<String> {
        let bytes = body.as_bytes();
        let mut patterns = Vec::new();
        let mut at = 0;
        while let Some(offset) = body[at..].find("*(") {
            let open = at + offset + 1;
            let mut depth = 0;
            let mut close = open;
            for (index, &byte) in bytes.iter().enumerate().skip(open) {
                match byte {
                    b'(' => depth += 1,
                    b')' => {
                        depth -= 1;
                        if depth == 0 {
                            close = index;
                            break;
                        }
                    }
                    _ => {}
                }
            }
            let inner = body[open + 1..close].replace(['(', ')'], " ");
            patterns.extend(
                inner
                    .split_whitespace()
                    .filter(|token| token.starts_with('.') || *token == "COMMON")
                    .map(str::to_string),
            );
            at = close + 1;
        }
        patterns
    }

    fn parse_gnu_script(script: &str) -> Vec<ScriptStatement> {
        let lines: Vec<&str> = script.lines().collect();
        let mut region = ScriptRegion::ReadOnly;
        let mut statements = Vec::new();
        let mut i = 0;
        while i < lines.len() {
            let line = lines[i];
            for (marker, next) in [
                ("DATA_SEGMENT_ALIGN (", ScriptRegion::Relro),
                ("DATA_SEGMENT_RELRO_END (", ScriptRegion::Writable),
                ("DATA_SEGMENT_END (", ScriptRegion::Unloaded),
            ] {
                if line.contains(marker) {
                    region = next;
                }
            }
            let trimmed = line.trim_start();
            let head = trimmed
                .split(|c: char| c.is_whitespace() || c == ':')
                .next()
                .unwrap_or("");
            let rest = trimmed[head.len()..].trim_start();
            let is_statement = (head == "/DISCARD/" || (head.starts_with('.') && head.len() > 1))
                && rest
                    .chars()
                    .next()
                    .is_some_and(|c| c == ':' || c == '0' || c == '(');
            if !is_statement {
                i += 1;
                continue;
            }
            let mut body = String::new();
            let mut depth = 0i32;
            let mut seen_brace = false;
            while i < lines.len() {
                body.push_str(lines[i]);
                body.push('\n');
                depth += lines[i].matches('{').count() as i32;
                depth -= lines[i].matches('}').count() as i32;
                seen_brace |= lines[i].contains('{');
                i += 1;
                if seen_brace && depth <= 0 {
                    break;
                }
            }
            let statement_region = if head == "/DISCARD/" {
                ScriptRegion::Discard
            } else if rest.starts_with('0') || rest.contains("(INFO)") {
                ScriptRegion::Unloaded
            } else {
                region
            };
            statements.push(ScriptStatement {
                output: head.to_string(),
                region: statement_region,
                patterns: script_patterns(&body[body.find('{').unwrap_or(0)..]),
            });
        }
        statements
    }

    /// Names a script or table pattern covers: every `*` as the empty run,
    /// a plain run and a `.`-separated run.
    fn representatives(pattern: &str) -> Vec<String> {
        if pattern.contains('*') {
            vec![
                pattern.replace('*', ""),
                pattern.replace('*', "q"),
                pattern.replace('*', ".q"),
            ]
        } else {
            vec![pattern.to_string()]
        }
    }

    /// One row of the retained list of rules BFD applies by name
    /// (`tests/fixtures/gnu-ld-2.42-bfd-by-name.txt`).
    #[derive(Debug)]
    struct BfdByName {
        pattern: String,
        /// `parsed`, `typed`, `owned` or `inert`.
        effect: String,
        /// What BFD parses the input as, or the output's `sh_type`.
        argument: String,
    }

    fn parse_bfd_by_name(text: &str) -> Vec<BfdByName> {
        text.lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'))
            .map(|line| {
                let fields: Vec<&str> = line.split('\t').collect();
                let effect = fields.get(1).copied().unwrap_or("");
                assert!(
                    matches!(effect, "parsed" | "typed" | "owned" | "inert"),
                    "{line}"
                );
                let argument = match effect {
                    "parsed" | "typed" => fields.get(2).copied().expect(line),
                    _ => "",
                };
                BfdByName {
                    pattern: fields[0].to_string(),
                    effect: effect.to_string(),
                    argument: argument.to_string(),
                }
            })
            .collect()
    }

    #[test]
    fn glob_matching_follows_linker_wildcards() {
        for (pattern, name, want) in [
            (".data", ".data", true),
            (".data", ".data.x", false),
            (".data.*", ".data.x", true),
            (".data.*", ".data", false),
            (".gnu_extab*", ".gnu_extab", true),
            (".gnu_extab*", ".gnu_extabx", true),
            (".text.*_unlikely", ".text.foo_unlikely", true),
            (".text.*_unlikely", ".text.foo_likely", false),
            (".stab*str", ".stabstr", true),
            (".stab*str", ".stab.indexstr", true),
            (".stab*str", ".stab.index", false),
            (".rela*", ".relative", true),
            (".rela*", ".relx", false),
        ] {
            assert_eq!(glob_matches(pattern, name), want, "{pattern} vs {name}");
        }
    }

    /// [`ELF_NAME_RULES`]' GNU column is GNU ld 2.42's default AArch64
    /// script (`ld --verbose -pie -z now -z relro`, byte-identical to the
    /// installed `aarch64linux.xdw`, retained as a fixture) plus the rules
    /// BFD applies by name outside the script (retained list
    /// `gnu-ld-2.42-bfd-by-name.txt`). For every input pattern of every
    /// output statement, every by-name rule and every table pattern: a name
    /// BFD parses by name (every `.eh_frame_entry*` input) must be the
    /// table's `ParsedByName`; otherwise the first statement that takes the
    /// name (ignoring ONLY_IF_RO/RW, which only picks between two unwind
    /// outputs) must be the table's output in the table's region; otherwise
    /// the table must say `TypedByName` exactly where BFD types the orphan
    /// by name, and `Orphan` elsewhere. A writer-owned name is refused
    /// before the table. The script's regions come from its
    /// `DATA_SEGMENT_ALIGN`/`_RELRO_END`/`_END` markers.
    #[test]
    fn elf_name_rules_match_the_gnu_ld_2_42_default_script() {
        use ElfPlacement::*;
        let script = include_str!("../tests/fixtures/gnu-ld-2.42-aarch64linux.xdw");
        assert!(script.starts_with("/* Script for -pie -z combreloc -z relro -z now */"));
        let statements = parse_gnu_script(script);
        // The parse is not vacuous: every region and the statements the
        // table leans on are present.
        assert!(statements.len() >= 70, "{} statements", statements.len());
        for region in [
            ScriptRegion::ReadOnly,
            ScriptRegion::Relro,
            ScriptRegion::Writable,
            ScriptRegion::Unloaded,
            ScriptRegion::Discard,
        ] {
            assert!(statements.iter().any(|s| s.region == region), "{region:?}");
        }
        for (output, region, pattern) in [
            (".rodata1", ScriptRegion::ReadOnly, ".rodata1"),
            (".tbss", ScriptRegion::Relro, ".tcommon"),
            (".jcr", ScriptRegion::Relro, ".jcr"),
            (".data.rel.ro", ScriptRegion::Relro, ".data.rel.ro.local*"),
            (".got", ScriptRegion::Relro, ".igot"),
            (".bss", ScriptRegion::Writable, "COMMON"),
            (".line", ScriptRegion::Unloaded, ".line"),
            ("/DISCARD/", ScriptRegion::Discard, ".gnu_debuglink"),
        ] {
            assert!(
                statements.iter().any(|s| s.output == output
                    && s.region == region
                    && s.patterns.iter().any(|p| p == pattern)),
                "{output} {region:?} {pattern}"
            );
        }
        let first_statement = |name: &str| {
            statements
                .iter()
                .find(|s| s.patterns.iter().any(|p| glob_matches(p, name)))
        };
        let by_name = parse_bfd_by_name(include_str!(
            "../tests/fixtures/gnu-ld-2.42-bfd-by-name.txt"
        ));
        let first_by_name = |name: &str| {
            by_name
                .iter()
                .find(|rule| glob_matches(&rule.pattern, name))
        };
        const EXECUTABLE_OUTPUTS: [&str; 4] = [".init", ".plt", ".text", ".fini"];
        // GNU ld's disposition of `name` is, in order: writer-owned (refused
        // before the table); a BFD rule that parses every input of that name
        // wherever it goes; the first script statement; an orphan that BFD
        // types by name; a plain orphan. The table's GNU column must say the
        // same, so a by-name placement in the table is derived from the
        // retained list, never asserted.
        let check = |name: &str, context: &str| {
            let rule = first_by_name(name);
            if rule.is_some_and(|rule| rule.effect == "owned") {
                assert!(
                    elf_reserved_reason(name).is_some(),
                    "{context}: BFD owns `{name}` by name but the writer's reserved list does not cover it"
                );
            }
            if elf_reserved_reason(name).is_some() {
                return;
            }
            let gnu = elf_name_rule(name).map_or(Orphan, |rule| rule.gnu);
            if let Some(rule) = rule.filter(|rule| rule.effect == "parsed") {
                assert!(
                    matches!(gnu, ParsedByName(what) if what.starts_with(&rule.argument)),
                    "{context}: BFD parses every input named `{name}` as {} (`{}`) but the table says {gnu:?}",
                    rule.argument,
                    rule.pattern
                );
                return;
            }
            match first_statement(name) {
                None => match rule.filter(|rule| rule.effect == "typed") {
                    Some(rule) => assert!(
                        matches!(gnu, TypedByName(sh_type) if sh_type == rule.argument),
                        "{context}: BFD types an orphan output named `{name}` {} (`{}`) but the table says {gnu:?}",
                        rule.argument,
                        rule.pattern
                    ),
                    None => assert!(
                        gnu == Orphan,
                        "{context}: `{name}` matches no GNU ld statement and no BFD by-name rule (an orphan) but the table says {gnu:?}"
                    ),
                },
                Some(statement) => {
                    let out = statement.output.as_str();
                    let tls = matches!(out, ".tdata" | ".tbss");
                    let ok = match (gnu, statement.region) {
                        (Executable(o), ScriptRegion::ReadOnly) => {
                            o == out && EXECUTABLE_OUTPUTS.contains(&o)
                        }
                        (ReadOnly(o), ScriptRegion::ReadOnly) => {
                            o == out && !EXECUTABLE_OUTPUTS.contains(&o)
                        }
                        (Relro(o), ScriptRegion::Relro) => o == out && !tls,
                        (ThreadLocal(o), ScriptRegion::Relro) => o == out && tls,
                        (Writable(o), ScriptRegion::Writable) => o == out,
                        (LinkerOwned(o, _), _) => o == out,
                        (Unloaded(_), ScriptRegion::Unloaded) => true,
                        (Discarded, ScriptRegion::Discard) => true,
                        _ => false,
                    };
                    assert!(
                        ok,
                        "{context}: GNU ld places `{name}` in `{out}` ({:?}) but the table says {gnu:?}",
                        statement.region
                    );
                }
            }
        };
        let mut checked = 0;
        for statement in &statements {
            for pattern in &statement.patterns {
                for name in representatives(pattern) {
                    check(
                        &name,
                        &format!("script `{}` <- `{pattern}`", statement.output),
                    );
                    checked += 1;
                }
            }
        }
        for rule in ELF_NAME_RULES {
            for pattern in rule.patterns {
                for name in representatives(pattern) {
                    check(&name, &format!("table `{pattern}`"));
                    checked += 1;
                }
            }
        }
        for rule in &by_name {
            for name in representatives(&rule.pattern) {
                check(&name, &format!("BFD by-name `{}`", rule.pattern));
                checked += 1;
            }
        }
        // Every spelling BFD's `.eh_frame_entry` prefix takes, and the
        // boundary one character short of it.
        for name in [
            ".eh_frame_entryx",
            ".eh_frame_entry1",
            ".eh_frame_entry_x",
            ".eh_frame_entry-x",
            ".eh_frame_entry$x",
        ] {
            check(name, "BFD prefix control");
            assert!(first_statement(name).is_none(), "{name}");
            assert!(matches!(
                elf_name_rule(name).map(|rule| rule.gnu),
                Some(ParsedByName(_))
            ));
            checked += 1;
        }
        check(".eh_frame_entq", "BFD prefix boundary");
        assert!(elf_name_rule(".eh_frame_entq").is_none());
        // Names neither the script nor BFD's by-name rules name stay orphans.
        for name in [
            ".textual",
            ".bssx",
            ".tbss_x",
            ".lbssy",
            ".jcrx",
            ".eh_framex",
            ".sframex",
            ".gcc_except_tablex",
            ".tcommon.x",
            ".rodata1.x",
            ".linex",
            ".stabq",
            ".relro",
            ".relr",
            ".tdata1",
            ".noinit",
            ".gnu_debugaltlink",
            ".eh_frame_entq",
            ".eh_frame_hdrx",
            ".relr.dynx",
            "tcg_custom",
        ] {
            check(name, "orphan control");
            assert!(first_statement(name).is_none(), "{name}");
            checked += 1;
        }
        // One character past a RELRO family is plain writable data.
        for (name, output) in [(".data.rel.rox", ".data"), (".bss.rel.rox", ".bss")] {
            check(name, "writable control");
            let statement = first_statement(name).expect(name);
            assert_eq!(
                (statement.output.as_str(), statement.region),
                (output, ScriptRegion::Writable),
                "{name}"
            );
        }
        // Not vacuous: the rules the table leans on are listed (checked last,
        // so a narrowed list fails the derivation above first).
        for (pattern, effect) in [
            (".eh_frame_entry*", "parsed"),
            (".rela*", "typed"),
            (".relr.dyn", "typed"),
            (".stab*str", "typed"),
        ] {
            assert!(
                by_name
                    .iter()
                    .any(|rule| rule.pattern == pattern && rule.effect == effect),
                "{pattern} {effect}"
            );
        }
        assert!(checked > 300, "{checked} names checked");
    }

    /// Data globals against every derived family: the independent
    /// verifier's list (`.tcommon`, `.gnu_extab`, `.gcc_except_table.x`,
    /// `.exception_ranges`, `.sframe`, `.eh_frame.x`, `.jcr`) and a sample of
    /// each class are refused by name with the exact code for every global
    /// shape; mutable globals in read-only or PT_GNU_RELRO outputs of either
    /// linker are `[TCG-SECTION-READONLY]` while the immutable ones keep
    /// their placement; boundary names no rule matches keep the global's own
    /// flags.
    #[test]
    fn elf_linker_special_names_are_refused_for_data_globals() {
        use crate::elf::constants::SHT_NOBITS;
        use SectionRefusal::{
            ExecutableSection as Exec, ReadOnlyMismatch as ReadOnly, ReservedName as Reserved,
            ThreadLocalMismatch as Tls,
        };
        let mutable_zero = global(vec![0; 8], true);
        let mutable = global(vec![7, 0, 0, 0, 0, 0, 0, 0], true);
        let constant = global(vec![7, 0, 0, 0, 0, 0, 0, 0], false);
        let relocated = table(1);
        let mut tls = mutable.clone();
        tls.is_thread_local = true;
        let mut mutable_table = table(1);
        mutable_table.mutable = true;
        let shapes: [(&str, &ObjectGlobal); 5] = [
            ("mutable zero", &mutable_zero),
            ("mutable", &mutable),
            ("immutable", &constant),
            ("relocated", &relocated),
            ("tls", &tls),
        ];
        // Refused for every non-TLS shape with one code; a TLS global is
        // refused too (by the same code, or as a TLS mismatch).
        for (name, code) in [
            // The verifier's list.
            (".tcommon", Tls),
            (".gnu_extab", Reserved),
            (".gcc_except_table.x", Reserved),
            (".exception_ranges", Reserved),
            (".sframe", Reserved),
            (".eh_frame.x", Reserved),
            (".jcr", Reserved),
            // Unwind and exception families.
            (".gnu_extab.x", Reserved),
            (".gnu_extabx", Reserved),
            (".exception_ranges.x", Reserved),
            (".exception_rangesx", Reserved),
            (".sframe.x", Reserved),
            (".eh_frame.", Reserved),
            (".eh_frame_entry", Reserved),
            (".eh_frame_entry.x", Reserved),
            // BFD's by-name prefix: no `.` boundary.
            (".eh_frame_entryx", Reserved),
            (".eh_frame_entry1", Reserved),
            (".eh_frame_entry_x", Reserved),
            (".eh_frame_entry-x", Reserved),
            (".eh_frame_entry$x", Reserved),
            // Executable outputs.
            (".stub", Exec),
            (".iplt", Exec),
            (".text.x", Exec),
            (".init", Exec),
            // Linker-owned, name-typed, unloaded and discarded outputs.
            (".igot", Reserved),
            (".igot.plt", Reserved),
            (".relro_padding", Reserved),
            ("COMMON", Reserved),
            (".rela_x", Reserved),
            (".relative", Reserved),
            (".relr.dyn", Reserved),
            (".stab", Reserved),
            (".stabstr", Reserved),
            (".stab.excl", Reserved),
            (".stab.indexstr", Reserved),
            (".stabqstr", Reserved),
            (".line", Reserved),
            (".gnu_debuglink", Reserved),
            // crtstuff tables.
            (".tm_clone_table", Reserved),
        ] {
            for (shape, g) in shapes {
                let (got, reason) = classify_elf_section(g, name)
                    .expect_err(&format!("{name} ({shape}) must be refused"));
                if shape == "tls" && got == Tls {
                    continue;
                }
                assert_eq!(got, code, "{name} ({shape}): {reason}");
                assert!(reason.contains(name), "{name} ({shape}): {reason}");
            }
        }
        // Read-only or PT_GNU_RELRO under either linker: immutable only;
        // the read-only text segment also refuses a relocated pointer.
        for (name, read_only) in [
            (".rodata1", true),
            (".rodata", true),
            (".rodata.x", true),
            (".data.rel.ro", false),
            (".data.rel.ro.local", false),
            (".toc", false),
        ] {
            for g in [&mutable_zero, &mutable] {
                let (code, reason) = classify_elf_section(g, name).expect_err(name);
                assert_eq!(code, ReadOnly, "{name}: {reason}");
                assert!(
                    reason.contains("PT_GNU_RELRO") || reason.contains("read-only text segment"),
                    "{name}: {reason}"
                );
            }
            let section = classify_elf_section(&constant, name).expect(name);
            assert_eq!(section.sh_type, SHT_PROGBITS, "{name}");
            let immutable_flags = if name.starts_with(".data") {
                SHF_ALLOC | SHF_WRITE
            } else {
                SHF_ALLOC
            };
            assert_eq!(section.sh_flags, immutable_flags, "{name}");
            if read_only {
                assert_eq!(elf_code(&relocated, name), ReadOnly, "{name}");
            } else {
                let section = classify_elf_section(&relocated, name).expect(name);
                assert_eq!(section.sh_flags, SHF_ALLOC | SHF_WRITE, "{name}");
            }
        }
        // LLD's `.toc` rule: the store faults under LLD only, but the name
        // is refused for a mutable global regardless of the linker.
        assert!(
            classify_elf_section(&mutable, ".toc")
                .expect_err(".toc")
                .1
                .contains(LLD)
        );
        // Constructor tables are inside PT_GNU_RELRO under both linkers.
        for name in [
            ".init_array",
            ".init_array.00100",
            ".fini_array",
            ".preinit_array",
        ] {
            let (code, reason) = classify_elf_section(&mutable_table, name).expect_err(name);
            assert_eq!(code, ReadOnly, "{name}: {reason}");
            assert!(
                reason.contains(GNU_LD) && reason.contains(LLD) && reason.contains("PT_GNU_RELRO"),
                "{name}: {reason}"
            );
            assert!(classify_elf_section(&table(1), name).is_ok(), "{name}");
        }
        // Boundary names no rule matches: orphans under both linkers, so the
        // global keeps its own flags (probed: the store runs under both).
        for name in [
            ".tcommon.x",
            ".jcrx",
            ".eh_framex",
            ".sframex",
            ".gcc_except_tablex",
            ".eh_frame_entq",
            ".eh_frame_hdrx",
            ".rodata1.x",
            ".stabq",
            ".stabx",
            ".linex",
            ".lineage",
            ".relro",
            ".relx",
            ".relr",
            ".tdata1",
            ".gnu_debugaltlink",
            ".noinit",
            ".persistent",
            ".toc.x",
            ".ipltx",
            ".stubs",
            "COMMONS",
            "common",
            "tcg_custom",
            // Folded by LLD by flags, orphans under GNU ld.
            ".ldata.x",
            ".lrodata",
            ".sdata",
            ".srodata.x",
            // Named writable outputs.
            ".data.tcg",
            ".data.rel.rox",
            ".data1",
        ] {
            for g in [&mutable_zero, &mutable] {
                let section =
                    classify_elf_section(g, name).unwrap_or_else(|r| panic!("{name}: {r:?}"));
                assert_eq!(
                    (section.sh_type, section.sh_flags, section.tls),
                    (SHT_PROGBITS, SHF_ALLOC | SHF_WRITE, false),
                    "{name}"
                );
            }
            let section = classify_elf_section(&constant, name).expect(name);
            let want = if is_dotted(name, ".data") || name == ".data1" {
                SHF_ALLOC | SHF_WRITE
            } else {
                SHF_ALLOC
            };
            assert_eq!(section.sh_flags, want, "{name}");
            assert_eq!(elf_code(&tls, name), Tls, "{name}");
        }
        // Zero fill keeps its placement except in LLD's RELRO sub-family.
        for name in [".bss.tcg", ".bss.rel.rox", ".sbss.x", ".lbss.tcg"] {
            let section = classify_elf_section(&mutable_zero, name).expect(name);
            assert_eq!(section.sh_type, SHT_NOBITS, "{name}");
        }
        for name in [".bss.rel.ro", ".bss.rel.ro.x"] {
            let (code, reason) = classify_elf_section(&mutable_zero, name).expect_err(name);
            assert_eq!(code, ReadOnly, "{name}: {reason}");
            assert!(
                reason.contains(LLD) && reason.contains("PT_GNU_RELRO"),
                "{reason}"
            );
            assert!(
                !reason.contains(GNU_LD),
                "GNU ld folds it into `.bss`: {reason}"
            );
        }
    }

    /// A COMDAT definition's implicit `<base>.<symbol>` must stay in its
    /// base's placement rule. A mutable symbol literally named `rel.ro` or
    /// `rel.ro.*` would make `.data.rel.ro...` (PT_GNU_RELRO under both
    /// linkers) or, all-zero, `.bss.rel.ro...` (PT_GNU_RELRO under LLD): it
    /// is refused by name as `[TCG-SECTION-READONLY]`. Every other class
    /// keeps its section for the same symbol, and so does a dotted,
    /// over-long or unusual symbol that stays in its rule.
    #[test]
    fn elf_implicit_comdat_names_stay_in_their_base_rule() {
        use crate::elf::constants::SHT_NOBITS;
        let named = |name: &str, data: Vec<u8>, mutable: bool, tls: bool| {
            let mut g = global(data, mutable);
            g.name = name.to_string();
            g.comdat = true;
            g.is_weak = true;
            g.is_thread_local = tls;
            g
        };
        for (g, section) in [
            (named("rel.ro", vec![7], true, false), ".data.rel.ro"),
            (
                named("rel.ro.local", vec![7], true, false),
                ".data.rel.ro.local",
            ),
            (named("rel.ro", vec![0; 8], true, false), ".bss.rel.ro"),
            (named("rel.ro.x", vec![0; 8], true, false), ".bss.rel.ro.x"),
        ] {
            assert_eq!(ElfImplicitSection::unique_section_name(&g), section);
            let (code, reason) = ElfImplicitSection::unique_section(&g).expect_err(section);
            assert_eq!(
                code,
                SectionRefusal::ReadOnlyMismatch,
                "{section}: {reason}"
            );
            assert!(
                reason.contains("implicit COMDAT") && reason.contains("PT_GNU_RELRO"),
                "{section}: {reason}"
            );
            // A retained definition's own section follows the same rule and
            // names its own reason.
            let mut retained = g.clone();
            retained.comdat = false;
            retained.is_weak = false;
            retained.retained = true;
            assert_eq!(ElfImplicitSection::unique_section_name(&retained), section);
            let (code, reason) = ElfImplicitSection::unique_section(&retained).expect_err(section);
            assert_eq!(
                code,
                SectionRefusal::ReadOnlyMismatch,
                "{section}: {reason}"
            );
            assert!(
                reason.contains("implicit retained section") && reason.contains("PT_GNU_RELRO"),
                "{section}: {reason}"
            );
        }
        let mut relocated = table(1);
        relocated.name = "rel.ro".into();
        relocated.comdat = true;
        relocated.is_weak = true;
        for (g, section, sh_type, flags) in [
            (
                named("rel.ro", vec![7], false, false),
                ".rodata.rel.ro",
                SHT_PROGBITS,
                SHF_ALLOC,
            ),
            (
                relocated,
                ".data.rel.ro.rel.ro",
                SHT_PROGBITS,
                SHF_ALLOC | SHF_WRITE,
            ),
            (
                named("rel.ro", vec![7], true, true),
                ".tdata.rel.ro",
                SHT_PROGBITS,
                SHF_ALLOC | SHF_WRITE | SHF_TLS,
            ),
            (
                named("rel.ro", vec![0; 8], true, true),
                ".tbss.rel.ro",
                SHT_NOBITS,
                SHF_ALLOC | SHF_WRITE | SHF_TLS,
            ),
            (
                named("rel.rox", vec![7], true, false),
                ".data.rel.rox",
                SHT_PROGBITS,
                SHF_ALLOC | SHF_WRITE,
            ),
            (
                named("rel", vec![7], true, false),
                ".data.rel",
                SHT_PROGBITS,
                SHF_ALLOC | SHF_WRITE,
            ),
            (
                named("anon.x.0", vec![0; 8], true, false),
                ".bss.anon.x.0",
                SHT_NOBITS,
                SHF_ALLOC | SHF_WRITE,
            ),
            (
                named("_ZN3tcg5stateE", vec![7], true, false),
                ".data._ZN3tcg5stateE",
                SHT_PROGBITS,
                SHF_ALLOC | SHF_WRITE,
            ),
        ] {
            assert_eq!(ElfImplicitSection::unique_section_name(&g), section);
            let got = ElfImplicitSection::unique_section(&g)
                .unwrap_or_else(|refusal| panic!("{section}: {refusal:?}"));
            assert_eq!((got.sh_type, got.sh_flags), (sh_type, flags), "{section}");
            let class = ElfImplicitSection::of(&g);
            assert_eq!(
                (got.sh_type, got.sh_flags, got.tls),
                (class.sh_type(), class.sh_flags(), class.tls()),
                "{section}"
            );
        }
        // The implicit name is not an explicit request: a symbol longer than
        // an explicit name may be, or with characters one may not use, keeps
        // its section while it stays in its rule.
        let long = named(&"x".repeat(2000), vec![7], true, false);
        assert!(ElfImplicitSection::unique_section(&long).is_ok());
        let odd = named("a b<c>", vec![7], true, false);
        assert!(ElfImplicitSection::unique_section(&odd).is_ok());
    }

    #[test]
    fn refusal_codes_are_stable_and_distinct() {
        let all = [
            SectionRefusal::MalformedName,
            SectionRefusal::ReservedName,
            SectionRefusal::ExecutableSection,
            SectionRefusal::DataSection,
            SectionRefusal::ZeroFillSection,
            SectionRefusal::LegacyConstructorTable,
            SectionRefusal::ThreadLocalMismatch,
            SectionRefusal::ReadOnlyMismatch,
            SectionRefusal::PointerTableShape,
            SectionRefusal::FlagConflict,
            SectionRefusal::MachOPair,
            SectionRefusal::MachOSegment,
            SectionRefusal::MachOAttribute,
            SectionRefusal::Import,
            SectionRefusal::TargetUnsupported,
        ];
        let codes: std::collections::BTreeSet<&str> = all.iter().map(|c| c.code()).collect();
        assert_eq!(codes.len(), all.len());
        assert!(codes.iter().all(|code| code.starts_with("TCG-SECTION-")));
        assert_eq!(
            SectionRefusal::FlagConflict.to_string(),
            "TCG-SECTION-FLAGS"
        );
    }

    /// The JIT rule refuses the FIRST sectioned global by name, whatever its
    /// kind or position, and admits a module whose globals request none.
    #[test]
    fn the_jit_refuses_any_explicit_global_section_by_name() {
        let plain = |name: &str| trust_ir::Global {
            name: name.to_string(),
            ty: trust_ir::Ty::U64,
            mutable: false,
            initializer: Some(trust_ir::Constant::Int(7)),
            linkage: trust_ir::Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        };
        let mut module = trust_ir::Module::new("jit_sections");
        assert!(refuse_jit_object_sections(&module).is_ok(), "no globals");
        module.globals = vec![plain("a"), plain("b"), plain("c")];
        assert!(refuse_jit_object_sections(&module).is_ok(), "no section");
        module.globals[1].section = Some("__DATA,__mod_init_func".to_string());
        module.globals[2].section = Some("__DATA,__const".to_string());
        let error = refuse_jit_object_sections(&module).expect_err("a sectioned JIT module");
        match &error {
            crate::pipeline::PipelineError::ExplicitSectionUnsupported {
                global,
                section,
                format,
                code,
                ..
            } => {
                assert_eq!(global, "b");
                assert_eq!(section, "__DATA,__mod_init_func");
                assert_eq!(*format, "JIT");
                assert_eq!(*code, SectionRefusal::TargetUnsupported);
            }
            other => panic!("expected ExplicitSectionUnsupported, got {other:?}"),
        }
        assert!(
            error.to_string().contains("[TCG-SECTION-TARGET]"),
            "{error}"
        );
        // Any name, even one an object emitter would honor, and on an import.
        module.globals.truncate(1);
        module.globals[0].section = Some(".rodata".to_string());
        module.globals[0].initializer = None;
        assert!(refuse_jit_object_sections(&module).is_err());
    }
}
