// trust-cg-codegen — per-compile ELF object reparse gate (ENC-9 sibling)
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// WHAT THIS IS (honest labeling)
// ------------------------------
// The ELF twin of the ENC-9 Mach-O reparse gate (`macho/reparse.rs`): a
// per-compile, fail-closed REDUNDANCY gate one level ABOVE the instruction
// encoder. The ELF object WRITER (`elf/writer.rs`) lays out the header,
// section data, `.rela.*` records, symbol table, string tables, and section
// header table; it is otherwise trusted (golden-tested only). After
// `ElfWriter::write` produces the object bytes, this gate RE-PARSES those
// bytes with an INDEPENDENT, spec-driven ELF64 reader (written from the
// System V gABI `Elf64_Ehdr`/`Elf64_Shdr`/`Elf64_Sym`/`Elf64_Rela` layouts,
// NOT by calling the writer's own `encode()` helpers) and structurally
// compares the reparsed structure against the INTENDED object description.
// Any disagreement — a section whose name/type/flags/align/size/bytes do not
// re-parse to intent, a symbol whose binding/type/section/value/size
// disagrees, or a relocation record whose (r_offset, symbol index, type,
// r_addend) does not re-parse to intent, or the wrong count/placement of any
// of these — is a would-be malformed object = FAIL CLOSED.
//
// This is NOT a proof. Two independent artifacts (the writer + this reader)
// must agree per compile. It is COMPLEMENTARY to the proven relocation
// FORMULAS (`elf_data_reloc_proofs.rs` / `elf_call_reloc_proofs.rs` in
// trust-cg-verify prove the VALUE a relocation kind computes); this gate
// proves the relocation RECORD (and the whole object skeleton) was laid down
// faithfully. Per the project soundness doctrine, reparse-agreement is
// REDUNDANCY, never counted in a "proven" numerator. It is the per-object
// BINDING half of the object-relocation inventory's Certified composition
// (`trust_cg_verify::ObjectProofBinding::ElfReparseEnforced`).
//
// SCOPE
// -----
// ELF object emission (all three machines share `ElfWriter`, so this is a
// shared investment). The COFF writer remains a TRUSTED ISLAND with no
// reparse gate.
//
// ROLLOUT (soundness-doctrine gate rollout, §2.4 — mirrors ENC-9)
// ----------------------------------------------------------------
//   TCG_ELF_REPARSE = off | warn | enforce   (default: enforce — default-ON)
//   TCG_NO_ELF_REPARSE = 1                    triage opt-out (mirrors
//                                             TCG_NO_MACHO_REPARSE; never
//                                             weakens a default silently)
//   TCG_TRACE_ELF_REPARSE = 1                 per-object trace + summary
//
// `warn` records telemetry and prints every disagreement LOUDLY (P0 evidence
// of a live writer bug) WITHOUT failing the compile. In `enforce` a
// disagreement is fail-closed (the checked write funnel aborts rather than
// return a malformed object) — and the object-relocation inventory only
// claims the ELF binding when the mode is `enforce`, so downgrading the gate
// re-fails proof promotion closed.

use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

// ---------------------------------------------------------------------------
// ELF ABI constants — re-declared LOCALLY so this reader is an independent
// artifact (it does NOT import the writer's layout code). Values are from the
// System V gABI / psABI headers, identical to what any external tool
// (readelf/llvm-readobj) uses.
// ---------------------------------------------------------------------------

const ELF_MAGIC: [u8; 4] = [0x7f, b'E', b'L', b'F'];
const ELFCLASS64: u8 = 2;
const ELFDATA2LSB: u8 = 1;
const ET_REL: u16 = 1;

const EHDR_SIZE: usize = 64;
const SHDR_SIZE: usize = 64;
const SYM_SIZE: usize = 24;
const RELA_SIZE: usize = 24;

const SHT_SYMTAB: u32 = 2;
const SHT_STRTAB: u32 = 3;
const SHT_RELA: u32 = 4;
const SHT_NOBITS: u32 = 8;

const STB_LOCAL: u8 = 0;
const STB_GLOBAL: u8 = 1;
const STB_WEAK: u8 = 2;

// ---------------------------------------------------------------------------
// Rollout mode
// ---------------------------------------------------------------------------

/// Rollout mode for the ELF reparse gate.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ElfReparseMode {
    /// Gate disabled (no reparse, no check). Triage-only.
    Off,
    /// Reparse and compare; a disagreement is logged loudly but does NOT fail
    /// the compile. Telemetry is still recorded. Gate-rollout warm-up.
    Warn,
    /// Reparse and compare; a disagreement FAILS the compile (default-ON).
    Enforce,
}

/// Resolve the gate mode from the environment (cached process-wide).
pub fn elf_reparse_mode() -> ElfReparseMode {
    static MODE: OnceLock<ElfReparseMode> = OnceLock::new();
    *MODE.get_or_init(|| {
        // Triage opt-out takes precedence, mirroring TCG_NO_MACHO_REPARSE.
        if std::env::var_os("TCG_NO_ELF_REPARSE").is_some() {
            return ElfReparseMode::Off;
        }
        match std::env::var("TCG_ELF_REPARSE").ok().as_deref() {
            Some("off") | Some("0") | Some("false") => ElfReparseMode::Off,
            Some("warn") => ElfReparseMode::Warn,
            Some("enforce") | Some("1") | Some("on") | Some("true") => ElfReparseMode::Enforce,
            // DEFAULT-ON: any unset / unrecognized value enforces.
            _ => ElfReparseMode::Enforce,
        }
    })
}

/// Whether per-object tracing is enabled (`TCG_TRACE_ELF_REPARSE=1`).
pub fn elf_reparse_trace_enabled() -> bool {
    static TRACE: OnceLock<bool> = OnceLock::new();
    *TRACE.get_or_init(|| std::env::var_os("TCG_TRACE_ELF_REPARSE").is_some())
}

// ---------------------------------------------------------------------------
// Telemetry (process-wide; used by the warn-only rollout + tests)
// ---------------------------------------------------------------------------

static N_OBJECTS_CHECKED: AtomicU64 = AtomicU64::new(0);
static N_OBJECTS_MATCHED: AtomicU64 = AtomicU64::new(0);
static N_OBJECTS_MISMATCHED: AtomicU64 = AtomicU64::new(0);
static N_SECTIONS_CHECKED: AtomicU64 = AtomicU64::new(0);
static N_SYMBOLS_CHECKED: AtomicU64 = AtomicU64::new(0);
static N_RELOCS_CHECKED: AtomicU64 = AtomicU64::new(0);

/// Snapshot of the ELF reparse-gate telemetry counters.
#[derive(Clone, Debug, Default)]
pub struct ElfReparseCounters {
    /// Objects reparsed and structurally compared.
    pub objects_checked: u64,
    /// Objects that fully matched intent.
    pub objects_matched: u64,
    /// Objects that disagreed with intent (P0 in enforce mode).
    pub objects_mismatched: u64,
    /// Section headers compared across all objects.
    pub sections_checked: u64,
    /// Symbol table entries compared across all objects.
    pub symbols_checked: u64,
    /// Relocation records compared across all objects.
    pub relocs_checked: u64,
}

/// Read the current telemetry counters.
pub fn elf_reparse_counters() -> ElfReparseCounters {
    ElfReparseCounters {
        objects_checked: N_OBJECTS_CHECKED.load(Ordering::Relaxed),
        objects_matched: N_OBJECTS_MATCHED.load(Ordering::Relaxed),
        objects_mismatched: N_OBJECTS_MISMATCHED.load(Ordering::Relaxed),
        sections_checked: N_SECTIONS_CHECKED.load(Ordering::Relaxed),
        symbols_checked: N_SYMBOLS_CHECKED.load(Ordering::Relaxed),
        relocs_checked: N_RELOCS_CHECKED.load(Ordering::Relaxed),
    }
}

// ---------------------------------------------------------------------------
// Intended object description (built from the writer's high-level input model)
// ---------------------------------------------------------------------------

/// One intended user section: what the writer was told to emit (NOT the
/// computed file layout — offsets are derived from the reparsed bytes and
/// cross-checked, so a layout bug in the writer cannot hide).
#[derive(Clone, Debug)]
pub struct ElfSectionIntent {
    /// Section name (e.g. `.text`).
    pub name: String,
    /// Section type (`SHT_PROGBITS`, `SHT_NOBITS`, ...).
    pub sh_type: u32,
    /// Section flags.
    pub sh_flags: u64,
    /// Alignment in bytes (`sh_addralign`).
    pub align: u64,
    /// The exact content bytes the writer was told to place in this section.
    /// For `SHT_NOBITS` only the LENGTH is meaningful (no file bytes exist).
    pub data: Vec<u8>,
}

/// One intended symbol.
#[derive(Clone, Debug)]
pub struct ElfSymbolIntent {
    /// Symbol name.
    pub name: String,
    /// Section header table index (0 = undefined).
    pub section: u16,
    /// Offset within the section (defined) or 0 (undefined).
    pub value: u64,
    /// Symbol size in bytes.
    pub size: u64,
    /// Whether the symbol is externally visible (`STB_GLOBAL`).
    pub is_global: bool,
    /// Whether the symbol is weak (`STB_WEAK`; lives in the global partition).
    pub is_weak: bool,
    /// Symbol type (`STT_*`).
    pub sym_type: u8,
}

/// One intended `Elf64_Rela` record's fields.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ElfRelocIntent {
    /// `r_offset`: byte offset within the target section.
    pub r_offset: u64,
    /// Final symbol table index (accounting for the null symbol at 0).
    pub symbol_index: u32,
    /// Relocation type value (lower 32 bits of `r_info`).
    pub reloc_type: u32,
    /// Explicit constant addend.
    pub r_addend: i64,
}

/// The complete intended object: what `ElfWriter::write` was asked to emit.
#[derive(Clone, Debug)]
pub struct ElfObjectIntent {
    /// Expected `e_machine` value.
    pub machine: u16,
    /// Intended user sections, in emission order.
    pub sections: Vec<ElfSectionIntent>,
    /// Intended relocations per user section (same index as `sections`), in
    /// the writer's emission order.
    pub section_relocs: Vec<Vec<ElfRelocIntent>>,
    /// Intended symbols, in insertion order (the reader validates the
    /// spec-mandated locals-then-globals partition the writer must produce).
    pub symbols: Vec<ElfSymbolIntent>,
}

// ---------------------------------------------------------------------------
// Error
// ---------------------------------------------------------------------------

/// A structural disagreement between the intended object and the reparsed
/// bytes. In enforce mode this becomes a fail-closed abort of the emit funnel.
#[derive(Clone, Debug)]
pub struct ElfReparseError {
    /// Human-readable description (intended vs reparsed).
    pub message: String,
}

impl core::fmt::Display for ElfReparseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "[elf-reparse] {}", self.message)
    }
}

fn err<T>(message: String) -> Result<T, ElfReparseError> {
    Err(ElfReparseError { message })
}

// ---------------------------------------------------------------------------
// Independent, spec-driven little-endian reader
// ---------------------------------------------------------------------------

fn rd_u16(b: &[u8], off: usize) -> Result<u16, ElfReparseError> {
    b.get(off..off + 2)
        .map(|s| u16::from_le_bytes([s[0], s[1]]))
        .ok_or_else(|| ElfReparseError {
            message: format!("truncated: u16 at {off} (len {})", b.len()),
        })
}

fn rd_u32(b: &[u8], off: usize) -> Result<u32, ElfReparseError> {
    b.get(off..off + 4)
        .map(|s| u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
        .ok_or_else(|| ElfReparseError {
            message: format!("truncated: u32 at {off} (len {})", b.len()),
        })
}

fn rd_u64(b: &[u8], off: usize) -> Result<u64, ElfReparseError> {
    b.get(off..off + 8)
        .map(|s| u64::from_le_bytes([s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]]))
        .ok_or_else(|| ElfReparseError {
            message: format!("truncated: u64 at {off} (len {})", b.len()),
        })
}

fn rd_i64(b: &[u8], off: usize) -> Result<i64, ElfReparseError> {
    rd_u64(b, off).map(|v| v as i64)
}

/// A parsed `Elf64_Shdr` (all fields the gate checks).
#[derive(Clone, Debug)]
struct ParsedShdr {
    name: String,
    sh_type: u32,
    sh_flags: u64,
    sh_offset: u64,
    sh_size: u64,
    sh_link: u32,
    sh_info: u32,
    sh_addralign: u64,
}

/// A parsed `Elf64_Sym` entry with its resolved name.
#[derive(Clone, Debug)]
struct ParsedSym {
    name: String,
    st_bind: u8,
    st_type: u8,
    st_shndx: u16,
    st_value: u64,
    st_size: u64,
}

/// The reparsed object skeleton.
#[derive(Debug)]
struct ParsedElf {
    machine: u16,
    shdrs: Vec<ParsedShdr>,
    /// Symbol table entries (index 0 is the null symbol), or empty when no
    /// SHT_SYMTAB exists.
    symbols: Vec<ParsedSym>,
    /// `sh_info` of the symtab (one past the last local), if a symtab exists.
    symtab_sh_info: Option<u32>,
    /// Section header index of the symtab, if any.
    symtab_shndx: Option<usize>,
    /// (target section header index, records) per SHT_RELA section, in
    /// section header table order, plus each RELA's sh_link.
    rela_sections: Vec<(usize, u32, Vec<ElfRelocIntent>)>,
}

/// Resolve a NUL-terminated name out of a string table region.
fn strtab_name(
    b: &[u8],
    tab_off: usize,
    tab_size: usize,
    index: usize,
    what: &str,
) -> Result<String, ElfReparseError> {
    let start = tab_off.checked_add(index).ok_or_else(|| ElfReparseError {
        message: format!("{what}: string index overflows"),
    })?;
    let tab_end = tab_off + tab_size;
    if start > tab_end || start > b.len() {
        return err(format!("{what}: string index {index} outside its table"));
    }
    let end = b[start..tab_end.min(b.len())]
        .iter()
        .position(|&c| c == 0)
        .map(|p| start + p)
        .unwrap_or(tab_end.min(b.len()));
    Ok(String::from_utf8_lossy(&b[start..end]).into_owned())
}

/// Independently parse an ELF64 relocatable object from raw bytes (header,
/// section header table, symtab + strtab, and every `.rela.*` record). Spec
/// layout only — no writer code is consulted.
fn parse_elf(b: &[u8]) -> Result<ParsedElf, ElfReparseError> {
    if b.len() < EHDR_SIZE {
        return err(format!(
            "object too small ({} bytes) for Elf64_Ehdr",
            b.len()
        ));
    }
    if b[0..4] != ELF_MAGIC {
        return err("bad ELF magic".to_string());
    }
    if b[4] != ELFCLASS64 {
        return err(format!("e_ident class {} is not ELFCLASS64", b[4]));
    }
    if b[5] != ELFDATA2LSB {
        return err(format!("e_ident data {} is not ELFDATA2LSB", b[5]));
    }
    let e_type = rd_u16(b, 16)?;
    if e_type != ET_REL {
        return err(format!("e_type {e_type} is not ET_REL"));
    }
    let machine = rd_u16(b, 18)?;
    let e_shoff = rd_u64(b, 40)? as usize;
    let e_shentsize = rd_u16(b, 58)? as usize;
    let e_shnum = rd_u16(b, 60)? as usize;
    let e_shstrndx = rd_u16(b, 62)? as usize;
    if e_shentsize != SHDR_SIZE {
        return err(format!("e_shentsize {e_shentsize} != {SHDR_SIZE}"));
    }
    if e_shoff + e_shnum * SHDR_SIZE > b.len() {
        return err(format!(
            "section header table {e_shoff}+{} exceeds object size {}",
            e_shnum * SHDR_SIZE,
            b.len()
        ));
    }
    if e_shstrndx >= e_shnum {
        return err(format!("e_shstrndx {e_shstrndx} out of range ({e_shnum})"));
    }

    // First pass: raw headers (names resolved in a second pass via shstrtab).
    struct RawShdr {
        sh_name: u32,
        sh_type: u32,
        sh_flags: u64,
        sh_offset: u64,
        sh_size: u64,
        sh_link: u32,
        sh_info: u32,
        sh_addralign: u64,
    }
    let mut raw = Vec::with_capacity(e_shnum);
    for i in 0..e_shnum {
        let o = e_shoff + i * SHDR_SIZE;
        raw.push(RawShdr {
            sh_name: rd_u32(b, o)?,
            sh_type: rd_u32(b, o + 4)?,
            sh_flags: rd_u64(b, o + 8)?,
            sh_offset: rd_u64(b, o + 24)?,
            sh_size: rd_u64(b, o + 32)?,
            sh_link: rd_u32(b, o + 40)?,
            sh_info: rd_u32(b, o + 44)?,
            sh_addralign: rd_u64(b, o + 48)?,
        });
    }
    let shstr = &raw[e_shstrndx];
    if shstr.sh_type != SHT_STRTAB {
        return err(format!(
            "e_shstrndx section has type {:#x}, not SHT_STRTAB",
            shstr.sh_type
        ));
    }
    let (shstr_off, shstr_size) = (shstr.sh_offset as usize, shstr.sh_size as usize);
    let mut shdrs = Vec::with_capacity(e_shnum);
    for r in &raw {
        shdrs.push(ParsedShdr {
            name: strtab_name(b, shstr_off, shstr_size, r.sh_name as usize, "shstrtab")?,
            sh_type: r.sh_type,
            sh_flags: r.sh_flags,
            sh_offset: r.sh_offset,
            sh_size: r.sh_size,
            sh_link: r.sh_link,
            sh_info: r.sh_info,
            sh_addralign: r.sh_addralign,
        });
    }

    // Symbol table (at most one SHT_SYMTAB in a relocatable object).
    let mut symbols = Vec::new();
    let mut symtab_sh_info = None;
    let mut symtab_shndx = None;
    for (i, sh) in shdrs.iter().enumerate() {
        if sh.sh_type != SHT_SYMTAB {
            continue;
        }
        if symtab_shndx.is_some() {
            return err("object has more than one SHT_SYMTAB".to_string());
        }
        symtab_shndx = Some(i);
        symtab_sh_info = Some(sh.sh_info);
        if sh.sh_size % SYM_SIZE as u64 != 0 {
            return err(format!(
                "symtab size {} not a multiple of {SYM_SIZE}",
                sh.sh_size
            ));
        }
        let strtab = shdrs
            .get(sh.sh_link as usize)
            .ok_or_else(|| ElfReparseError {
                message: format!("symtab sh_link {} out of range", sh.sh_link),
            })?;
        if strtab.sh_type != SHT_STRTAB {
            return err(format!(
                "symtab sh_link section has type {:#x}, not SHT_STRTAB",
                strtab.sh_type
            ));
        }
        let (str_off, str_size) = (strtab.sh_offset as usize, strtab.sh_size as usize);
        let nsyms = (sh.sh_size / SYM_SIZE as u64) as usize;
        for k in 0..nsyms {
            let e = sh.sh_offset as usize + k * SYM_SIZE;
            let st_name = rd_u32(b, e)?;
            let st_info = *b.get(e + 4).ok_or_else(|| ElfReparseError {
                message: format!("truncated st_info at {}", e + 4),
            })?;
            let st_shndx = rd_u16(b, e + 6)?;
            let st_value = rd_u64(b, e + 8)?;
            let st_size = rd_u64(b, e + 16)?;
            symbols.push(ParsedSym {
                name: strtab_name(b, str_off, str_size, st_name as usize, "strtab")?,
                st_bind: st_info >> 4,
                st_type: st_info & 0x0F,
                st_shndx,
                st_value,
                st_size,
            });
        }
    }

    // Relocation sections.
    let mut rela_sections = Vec::new();
    for sh in shdrs.iter() {
        if sh.sh_type != SHT_RELA {
            continue;
        }
        if sh.sh_size % RELA_SIZE as u64 != 0 {
            return err(format!(
                "rela section {} size {} not a multiple of {RELA_SIZE}",
                sh.name, sh.sh_size
            ));
        }
        let n = (sh.sh_size / RELA_SIZE as u64) as usize;
        let mut recs = Vec::with_capacity(n);
        for j in 0..n {
            let e = sh.sh_offset as usize + j * RELA_SIZE;
            let r_offset = rd_u64(b, e)?;
            let r_info = rd_u64(b, e + 8)?;
            let r_addend = rd_i64(b, e + 16)?;
            recs.push(ElfRelocIntent {
                r_offset,
                symbol_index: (r_info >> 32) as u32,
                reloc_type: (r_info & 0xFFFF_FFFF) as u32,
                r_addend,
            });
        }
        rela_sections.push((sh.sh_info as usize, sh.sh_link, recs));
    }

    Ok(ParsedElf {
        machine,
        shdrs,
        symbols,
        symtab_sh_info,
        symtab_shndx,
        rela_sections,
    })
}

// ---------------------------------------------------------------------------
// Structural comparison: reparsed object == intent
// ---------------------------------------------------------------------------

/// The gABI-mandated final symbol order the writer must produce: the null
/// symbol, then locals (insertion order), then globals/weak (insertion
/// order). Reconstructed from the spec so the element-wise comparison also
/// validates the ordering the writer produced.
fn intent_symbol_order(intent: &ElfObjectIntent) -> Vec<usize> {
    let mut locals = Vec::new();
    let mut globals = Vec::new();
    for (i, s) in intent.symbols.iter().enumerate() {
        if s.is_global || s.is_weak {
            globals.push(i);
        } else {
            locals.push(i);
        }
    }
    locals.into_iter().chain(globals).collect()
}

/// Compare a reparsed object against its intent. Returns the FIRST
/// disagreement as an `Err` (used for enforce mode and the mutation negative
/// controls); a faithful object returns `Ok(())`. Pure and mode-agnostic.
pub fn check_object(intent: &ElfObjectIntent, bytes: &[u8]) -> Result<(), ElfReparseError> {
    let po = parse_elf(bytes)?;

    // --- Header ---
    if po.machine != intent.machine {
        return err(format!(
            "e_machine {} != intended {}",
            po.machine, intent.machine
        ));
    }

    // --- User sections ---
    // The user sections are every section header that is not the null entry,
    // not a writer-generated `.rela.*`/symtab/string table. Identify them
    // structurally (by type), preserving order, and record their actual
    // header-table indices for the relocation targeting check below.
    let mut user: Vec<(usize, &ParsedShdr)> = Vec::new();
    for (i, sh) in po.shdrs.iter().enumerate().skip(1) {
        if matches!(sh.sh_type, SHT_RELA | SHT_SYMTAB | SHT_STRTAB) {
            continue;
        }
        user.push((i, sh));
    }
    if user.len() != intent.sections.len() {
        return err(format!(
            "user section count {} != intended {}",
            user.len(),
            intent.sections.len()
        ));
    }
    for (k, ((shndx, ps), si)) in user.iter().zip(intent.sections.iter()).enumerate() {
        if ps.name != si.name {
            return err(format!(
                "section {k} name {:?} != intended {:?}",
                ps.name, si.name
            ));
        }
        if ps.sh_type != si.sh_type {
            return err(format!(
                "section {k} ({}) type {:#x} != intended {:#x}",
                si.name, ps.sh_type, si.sh_type
            ));
        }
        if ps.sh_flags != si.sh_flags {
            return err(format!(
                "section {k} ({}) flags {:#x} != intended {:#x}",
                si.name, ps.sh_flags, si.sh_flags
            ));
        }
        if ps.sh_addralign != si.align {
            return err(format!(
                "section {k} ({}) addralign {} != intended {}",
                si.name, ps.sh_addralign, si.align
            ));
        }
        let want_size = si.data.len() as u64;
        if ps.sh_size != want_size {
            return err(format!(
                "section {k} ({}) size {} != intended {}",
                si.name, ps.sh_size, want_size
            ));
        }
        if si.sh_type != SHT_NOBITS {
            // Offset alignment + bounds, then a full BYTE compare of the
            // emitted content against intent — this binds the header's
            // claimed offset/size to the bytes actually laid down.
            if si.align > 1 && ps.sh_offset % si.align != 0 {
                return err(format!(
                    "section {k} ({}) file offset {} is not {}-byte aligned",
                    si.name, ps.sh_offset, si.align
                ));
            }
            let start = ps.sh_offset as usize;
            let end = start
                .checked_add(si.data.len())
                .ok_or_else(|| ElfReparseError {
                    message: format!("section {k} ({}) data range overflows", si.name),
                })?;
            let region = bytes.get(start..end).ok_or_else(|| ElfReparseError {
                message: format!(
                    "section {k} ({}) data range {start}..{end} out of bounds (len {})",
                    si.name,
                    bytes.len()
                ),
            })?;
            if region != si.data.as_slice() {
                return err(format!(
                    "section {k} ({}) emitted bytes at offset {start} do not match intended content",
                    si.name
                ));
            }
        }
        let _ = shndx;
        N_SECTIONS_CHECKED.fetch_add(1, Ordering::Relaxed);
    }

    // --- Symbols (element-wise in the locals-then-globals partition) ---
    let expected_syms = 1 + intent.symbols.len(); // + null symbol
    if intent.symbols.is_empty() {
        // The writer always emits a symtab (with just the null symbol);
        // accept either absent or null-only.
        if !po.symbols.is_empty() && po.symbols.len() != 1 {
            return err(format!(
                "object has {} symbols but none were intended",
                po.symbols.len() - 1
            ));
        }
    } else {
        if po.symbols.len() != expected_syms {
            return err(format!(
                "symbol count {} != intended {} (incl. null)",
                po.symbols.len(),
                expected_syms
            ));
        }
        // Null symbol at index 0.
        let null = &po.symbols[0];
        if !null.name.is_empty() || null.st_bind != STB_LOCAL || null.st_shndx != 0 {
            return err("symbol 0 is not the null symbol".to_string());
        }
        let order = intent_symbol_order(intent);
        let mut n_locals = 0u32;
        for (slot, &ii) in order.iter().enumerate() {
            let want = &intent.symbols[ii];
            let got = &po.symbols[slot + 1];
            if got.name != want.name {
                return err(format!(
                    "symbol slot {} name {:?} != intended {:?}",
                    slot + 1,
                    got.name,
                    want.name
                ));
            }
            let want_bind = if want.is_weak {
                STB_WEAK
            } else if want.is_global {
                STB_GLOBAL
            } else {
                n_locals += 1;
                STB_LOCAL
            };
            if got.st_bind != want_bind {
                return err(format!(
                    "symbol {:?} binding {} != intended {}",
                    want.name, got.st_bind, want_bind
                ));
            }
            if got.st_type != want.sym_type {
                return err(format!(
                    "symbol {:?} type {} != intended {}",
                    want.name, got.st_type, want.sym_type
                ));
            }
            if got.st_shndx != want.section {
                return err(format!(
                    "symbol {:?} st_shndx {} != intended section {}",
                    want.name, got.st_shndx, want.section
                ));
            }
            if got.st_value != want.value {
                return err(format!(
                    "symbol {:?} st_value {:#x} != intended {:#x}",
                    want.name, got.st_value, want.value
                ));
            }
            if got.st_size != want.size {
                return err(format!(
                    "symbol {:?} st_size {} != intended {}",
                    want.name, got.st_size, want.size
                ));
            }
            N_SYMBOLS_CHECKED.fetch_add(1, Ordering::Relaxed);
        }
        // symtab sh_info must be one past the last local (incl. null).
        let want_info = 1 + n_locals;
        if po.symtab_sh_info != Some(want_info) {
            return err(format!(
                "symtab sh_info {:?} != intended {want_info}",
                po.symtab_sh_info
            ));
        }
    }

    // --- Relocations (per user section, in emission order) ---
    // Map each SHT_RELA section to the user section its sh_info targets, and
    // require its sh_link to reference the symtab.
    let mut seen_rela_for: Vec<bool> = vec![false; intent.sections.len()];
    for (target_shndx, sh_link, recs) in &po.rela_sections {
        let Some(user_pos) = user.iter().position(|(i, _)| i == target_shndx) else {
            return err(format!(
                "rela section targets header index {target_shndx}, which is not a user section"
            ));
        };
        if po.symtab_shndx != Some(*sh_link as usize) {
            return err(format!(
                "rela section for user section {user_pos} links symtab {sh_link}, expected {:?}",
                po.symtab_shndx
            ));
        }
        if seen_rela_for[user_pos] {
            return err(format!(
                "duplicate rela section for user section {user_pos}"
            ));
        }
        seen_rela_for[user_pos] = true;
        let want = &intent.section_relocs[user_pos];
        if recs.len() != want.len() {
            return err(format!(
                "user section {user_pos} relocation count {} != intended {}",
                recs.len(),
                want.len()
            ));
        }
        for (j, (got, wr)) in recs.iter().zip(want.iter()).enumerate() {
            if got != wr {
                return err(format!(
                    "user section {user_pos} relocation {j}: reparsed {got:?} != intended {wr:?}"
                ));
            }
            N_RELOCS_CHECKED.fetch_add(1, Ordering::Relaxed);
        }
    }
    // Every intended non-empty relocation list must have been matched by an
    // emitted `.rela.*` section (an omitted record set must not pass).
    for (user_pos, want) in intent.section_relocs.iter().enumerate() {
        if !want.is_empty() && !seen_rela_for[user_pos] {
            return err(format!(
                "user section {user_pos} intended {} relocation(s) but no rela section was emitted",
                want.len()
            ));
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Gate driver (Off / Warn / Enforce) + telemetry
// ---------------------------------------------------------------------------

/// Run the reparse gate over one emitted object. Returns `Err` ONLY in
/// [`ElfReparseMode::Enforce`] on a disagreement; in [`ElfReparseMode::Warn`]
/// it logs the disagreement loudly (P0 evidence of a live writer bug) and
/// returns `Ok`. Off is a no-op.
pub fn run_elf_reparse_gate(
    intent: &ElfObjectIntent,
    bytes: &[u8],
    mode: ElfReparseMode,
) -> Result<(), ElfReparseError> {
    if mode == ElfReparseMode::Off {
        return Ok(());
    }
    let trace = elf_reparse_trace_enabled();
    N_OBJECTS_CHECKED.fetch_add(1, Ordering::Relaxed);
    match check_object(intent, bytes) {
        Ok(()) => {
            N_OBJECTS_MATCHED.fetch_add(1, Ordering::Relaxed);
            if trace {
                let c = elf_reparse_counters();
                eprintln!(
                    "elf-reparse OK [machine {}] {} bytes, {} sections, {} symbols \
                     (totals: objects={} sections={} symbols={} relocs={})",
                    intent.machine,
                    bytes.len(),
                    intent.sections.len(),
                    intent.symbols.len(),
                    c.objects_checked,
                    c.sections_checked,
                    c.symbols_checked,
                    c.relocs_checked,
                );
            }
            Ok(())
        }
        Err(e) => {
            N_OBJECTS_MISMATCHED.fetch_add(1, Ordering::Relaxed);
            match mode {
                ElfReparseMode::Warn => {
                    eprintln!("elf-reparse WARN (P0 candidate): {e}");
                    Ok(())
                }
                ElfReparseMode::Enforce => Err(e),
                ElfReparseMode::Off => unreachable!(),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elf::constants::{SHF_ALLOC, SHT_PROGBITS, STT_FUNC, STT_OBJECT};
    use crate::elf::header::ElfMachine;
    use crate::elf::reloc::{Elf64Rela, X86_64RelocType};
    use crate::elf::writer::ElfWriter;

    // A representative x86-64 object: text + data + rodata, local + global +
    // weak + undefined symbols, and text + data relocations of every kind
    // the x86-64 ELF emitter produces.
    fn build_x86_writer() -> ElfWriter {
        let mut w = ElfWriter::new(ElfMachine::X86_64);
        w.add_text_section(&[0x90, 0x90, 0xE8, 0, 0, 0, 0, 0xC3]);
        w.add_symbol("batch_a", 1, 0, 8, true, STT_FUNC);
        w.add_symbol("local_helper", 1, 2, 6, false, STT_FUNC);
        let data_idx = w.add_data_section(&[1, 2, 3, 4, 5, 6, 7, 8]);
        w.add_symbol("G", data_idx, 0, 8, true, STT_OBJECT);
        w.add_weak_symbol("W", data_idx, 4, 4, STT_OBJECT);
        w.add_section(".rodata", &[9, 9], SHT_PROGBITS, SHF_ALLOC, 8);
        w.add_symbol("SHARED_TAB", 0, 0, 0, true, STT_OBJECT);
        // Text relocations: PLT32 call + PC32 GlobalRef + GOTPCREL extern.
        w.add_relocation(0, Elf64Rela::x86_64(3, 1, X86_64RelocType::Plt32, -4));
        w.add_relocation(0, Elf64Rela::x86_64(4, 3, X86_64RelocType::Pc32, -4));
        w.add_relocation(0, Elf64Rela::x86_64(5, 5, X86_64RelocType::GotPcRel, -4));
        // Data relocation: abs64 pointer slot with a nonzero addend.
        w.add_relocation(1, Elf64Rela::x86_64(0, 1, X86_64RelocType::Abs64, 16));
        w
    }

    #[test]
    fn positive_x86_object_passes() {
        let w = build_x86_writer();
        let bytes = w.write();
        let intent = w.reparse_object_intent();
        assert!(
            check_object(&intent, &bytes).is_ok(),
            "a faithful x86-64 ELF object must pass the reparse gate: {:?}",
            check_object(&intent, &bytes)
        );
    }

    #[test]
    fn write_checked_returns_same_bytes() {
        let w = build_x86_writer();
        let plain = w.write();
        let checked = w.write_checked().expect("faithful object must pass");
        assert_eq!(plain, checked);
    }

    #[test]
    fn empty_object_is_consistent() {
        let w = ElfWriter::new(ElfMachine::X86_64);
        let bytes = w.write();
        let intent = w.reparse_object_intent();
        assert!(check_object(&intent, &bytes).is_ok());
    }

    /// Locate the first `.rela.*` section's (offset, target header index)
    /// by an independent walk (test-only).
    fn first_rela_offset(b: &[u8]) -> usize {
        let shoff = u64::from_le_bytes(b[40..48].try_into().unwrap()) as usize;
        let shnum = u16::from_le_bytes(b[60..62].try_into().unwrap()) as usize;
        for i in 0..shnum {
            let o = shoff + i * SHDR_SIZE;
            let sh_type = u32::from_le_bytes(b[o + 4..o + 8].try_into().unwrap());
            if sh_type == SHT_RELA {
                return u64::from_le_bytes(b[o + 24..o + 32].try_into().unwrap()) as usize;
            }
        }
        panic!("no SHT_RELA section found");
    }

    // Refutation 1: corrupt a relocation's r_addend (the addend IS the
    // correctness carrier on ELF — a flipped addend is a live miscompile).
    #[test]
    fn refutation_corrupt_reloc_addend_fails_closed() {
        let w = build_x86_writer();
        let mut bytes = w.write();
        let intent = w.reparse_object_intent();
        let rela_off = first_rela_offset(&bytes);
        bytes[rela_off + 16] ^= 0xFF; // low byte of r_addend of record 0
        assert!(
            check_object(&intent, &bytes).is_err(),
            "a corrupted relocation addend must be rejected"
        );
    }

    // Refutation 2: corrupt a relocation's type (r_info low 32 bits).
    #[test]
    fn refutation_corrupt_reloc_type_fails_closed() {
        let w = build_x86_writer();
        let mut bytes = w.write();
        let intent = w.reparse_object_intent();
        let rela_off = first_rela_offset(&bytes);
        bytes[rela_off + 8] ^= 0x01; // PLT32 (4) -> wrong type
        assert!(
            check_object(&intent, &bytes).is_err(),
            "a corrupted relocation type must be rejected"
        );
    }

    // Refutation 3: corrupt a relocation's symbol index (r_info high bits).
    #[test]
    fn refutation_corrupt_reloc_symbol_fails_closed() {
        let w = build_x86_writer();
        let mut bytes = w.write();
        let intent = w.reparse_object_intent();
        let rela_off = first_rela_offset(&bytes);
        bytes[rela_off + 12] ^= 0x01; // low byte of the symbol index
        assert!(
            check_object(&intent, &bytes).is_err(),
            "a corrupted relocation symbol index must be rejected"
        );
    }

    // Refutation 4: corrupt a symbol's st_value.
    #[test]
    fn refutation_corrupt_symbol_value_fails_closed() {
        let w = build_x86_writer();
        let mut bytes = w.write();
        let intent = w.reparse_object_intent();
        // Find the symtab by independent walk; corrupt entry 1's st_value.
        let shoff = u64::from_le_bytes(bytes[40..48].try_into().unwrap()) as usize;
        let shnum = u16::from_le_bytes(bytes[60..62].try_into().unwrap()) as usize;
        let mut symoff = None;
        for i in 0..shnum {
            let o = shoff + i * SHDR_SIZE;
            let sh_type = u32::from_le_bytes(bytes[o + 4..o + 8].try_into().unwrap());
            if sh_type == SHT_SYMTAB {
                symoff =
                    Some(u64::from_le_bytes(bytes[o + 24..o + 32].try_into().unwrap()) as usize);
            }
        }
        let symoff = symoff.expect("symtab");
        bytes[symoff + SYM_SIZE + 8] ^= 0xFF;
        assert!(
            check_object(&intent, &bytes).is_err(),
            "a corrupted symbol value must be rejected"
        );
    }

    // Refutation 5: corrupt a section content byte.
    #[test]
    fn refutation_corrupt_section_data_fails_closed() {
        let w = build_x86_writer();
        let mut bytes = w.write();
        let intent = w.reparse_object_intent();
        // .text starts at the first 16-aligned offset after the 64-byte
        // header; find it via the parsed section table instead of assuming.
        let po = parse_elf(&bytes).expect("parse");
        let text = po
            .shdrs
            .iter()
            .find(|s| s.name == ".text")
            .expect(".text section");
        bytes[text.sh_offset as usize] ^= 0xFF;
        assert!(
            check_object(&intent, &bytes).is_err(),
            "corrupted section content must be rejected"
        );
    }

    // Refutation 6: drop the whole .rela.data record set (an omitted record
    // set must not pass — flip its type so the reader no longer sees RELA).
    #[test]
    fn refutation_missing_rela_section_fails_closed() {
        let w = build_x86_writer();
        let mut bytes = w.write();
        let intent = w.reparse_object_intent();
        let shoff = u64::from_le_bytes(bytes[40..48].try_into().unwrap()) as usize;
        let shnum = u16::from_le_bytes(bytes[60..62].try_into().unwrap()) as usize;
        // Flip the LAST rela section (the data one) to SHT_PROGBITS... but
        // that leaves a stray user section; instead the count mismatch is
        // itself the fail-closed signal.
        let mut last_rela = None;
        for i in 0..shnum {
            let o = shoff + i * SHDR_SIZE;
            let sh_type = u32::from_le_bytes(bytes[o + 4..o + 8].try_into().unwrap());
            if sh_type == SHT_RELA {
                last_rela = Some(o);
            }
        }
        let o = last_rela.expect("rela section");
        bytes[o + 4..o + 8].copy_from_slice(&SHT_STRTAB.to_le_bytes());
        assert!(
            check_object(&intent, &bytes).is_err(),
            "an object missing an intended relocation record set must be rejected"
        );
    }

    #[test]
    fn refutation_wrong_machine_fails_closed() {
        let w = build_x86_writer();
        let mut bytes = w.write();
        let intent = w.reparse_object_intent();
        bytes[18] = 183u8; // EM_AARCH64 low byte (EM_X86_64 = 62)
        assert!(check_object(&intent, &bytes).is_err());
    }
}
