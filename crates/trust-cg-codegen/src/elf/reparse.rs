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
// `ElfWriter::write_checked` lays down the object bytes, this gate RE-PARSES those
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
//
// `warn` records telemetry and prints every disagreement LOUDLY (P0 evidence
// of a live writer bug) WITHOUT failing the compile. In `enforce` a
// disagreement is fail-closed (the checked write funnel aborts rather than
// return a malformed object) — and the object-relocation inventory only
// claims the ELF binding when the mode is `enforce`, so downgrading the gate
// re-fails proof promotion closed.

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
const SHT_GROUP: u32 = 17;
/// The section of `Elf32_Word` section indices of the symbols whose
/// `st_shndx` is `SHN_XINDEX` (extended section numbering).
const SHT_SYMTAB_SHNDX: u32 = 18;
/// `SHN_LORESERVE`: a `st_shndx` at or above it names no section.
const SHN_LORESERVE: u16 = 0xff00;
/// `SHN_XINDEX`: the real index is elsewhere (`e_shstrndx` in section 0's
/// `sh_link`; a symbol's in its `SHT_SYMTAB_SHNDX` entry).
const SHN_XINDEX: u16 = 0xffff;

const SHF_INFO_LINK: u64 = 0x40;
const SHF_GROUP: u64 = 0x200;
const GRP_COMDAT: u32 = 1;
const GROUP_ENTRY_SIZE: u64 = 4;

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

/// Resolve the gate mode for the current compile request.
pub fn elf_reparse_mode() -> ElfReparseMode {
    // Triage opt-out takes precedence, mirroring TCG_NO_MACHO_REPARSE.
    if trust_cg_process_env::var_os("TCG_NO_ELF_REPARSE").is_some() {
        return ElfReparseMode::Off;
    }
    match trust_cg_process_env::var("TCG_ELF_REPARSE").ok().as_deref() {
        Some("off") | Some("0") | Some("false") => ElfReparseMode::Off,
        Some("warn") => ElfReparseMode::Warn,
        Some("enforce") | Some("1") | Some("on") | Some("true") => ElfReparseMode::Enforce,
        // DEFAULT-ON: any unset / unrecognized value enforces.
        _ => ElfReparseMode::Enforce,
    }
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
    /// Entry size in bytes (`sh_entsize`); 0 for sections without a table of
    /// fixed-size entries.
    pub entsize: u64,
    /// `sh_size`: the content length, or for `SHT_NOBITS` the zero-fill
    /// length (which has no content bytes at all).
    pub size: u64,
    /// The exact content bytes the writer was told to place in this section:
    /// `size` bytes, except for `SHT_NOBITS`, which holds none (the loader
    /// supplies the zeros, so the writer never materialises them). For
    /// `SHT_GROUP` the content is derived from final indices and is checked
    /// against [`ElfObjectIntent::groups`] instead.
    pub data: Vec<u8>,
}

/// One intended COMDAT section group.
#[derive(Clone, Debug)]
pub struct ElfGroupIntent {
    /// Position (in [`ElfObjectIntent::sections`]) of the group's own
    /// `SHT_GROUP` section.
    pub section: usize,
    /// Name of the group's signature symbol.
    pub signature: String,
    /// Positions (in [`ElfObjectIntent::sections`]) of the member sections.
    pub members: Vec<usize>,
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
    /// Symbol visibility (`STV_*`, the low two bits of `st_other`).
    pub visibility: u8,
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

/// The complete intended object: what `ElfWriter::write_checked` was asked to emit.
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
    /// Intended COMDAT section groups.
    pub groups: Vec<ElfGroupIntent>,
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
    sh_entsize: u64,
}

/// A parsed `Elf64_Sym` entry with its resolved name.
#[derive(Clone, Debug)]
struct ParsedSym {
    name: String,
    st_bind: u8,
    st_type: u8,
    /// `st_other & 0x3`: the `STV_*` visibility.
    st_visibility: u8,
    st_shndx: u16,
    /// The symbol's `SHT_SYMTAB_SHNDX` entry when `st_shndx` is
    /// `SHN_XINDEX`.
    st_shndx_extended: Option<u32>,
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
    /// (own header index, target header index, sh_flags) per SHT_RELA
    /// section, in section header table order.
    rela_headers: Vec<(usize, usize, u64)>,
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
    let e_shoff = usize::try_from(rd_u64(b, 40)?).unwrap_or(usize::MAX);
    let e_shentsize = rd_u16(b, 58)? as usize;
    let e_shnum = rd_u16(b, 60)? as usize;
    let e_shstrndx = rd_u16(b, 62)?;
    if e_shentsize != SHDR_SIZE {
        return err(format!("e_shentsize {e_shentsize} != {SHDR_SIZE}"));
    }
    // Extended section numbering (65,280 sections or more): `e_shnum` is 0
    // and the count is section 0's `sh_size`; `e_shstrndx` is `SHN_XINDEX`
    // and the index is section 0's `sh_link`.
    let e_shnum = if e_shnum == 0 && e_shoff != 0 {
        usize::try_from(rd_u64(b, e_shoff.saturating_add(32))?).unwrap_or(usize::MAX)
    } else {
        e_shnum
    };
    let e_shstrndx = if e_shstrndx == SHN_XINDEX && e_shoff != 0 {
        rd_u32(b, e_shoff.saturating_add(40))? as usize
    } else {
        usize::from(e_shstrndx)
    };
    let table_end = e_shnum
        .checked_mul(SHDR_SIZE)
        .and_then(|size| e_shoff.checked_add(size));
    if table_end.is_none_or(|end| end > b.len()) {
        return err(format!(
            "section header table of {e_shnum} entries at {e_shoff} exceeds object size {}",
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
        sh_entsize: u64,
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
            sh_entsize: rd_u64(b, o + 56)?,
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
            sh_entsize: r.sh_entsize,
        });
    }

    // Symbol table (at most one SHT_SYMTAB in a relocatable object).
    let mut symbols = Vec::new();
    // The extended section indices of each symbol table, by its index.
    let extended: Vec<(usize, &ParsedShdr)> = shdrs
        .iter()
        .filter(|sh| sh.sh_type == SHT_SYMTAB_SHNDX)
        .map(|sh| (sh.sh_link as usize, sh))
        .collect();
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
        let indices = match extended
            .iter()
            .filter(|(link, _)| *link == i)
            .collect::<Vec<_>>()[..]
        {
            [] => None,
            [(_, indices)] => Some(*indices),
            _ => return err("symtab has more than one SHT_SYMTAB_SHNDX".to_string()),
        };
        for k in 0..nsyms {
            let e = sh.sh_offset as usize + k * SYM_SIZE;
            let st_name = rd_u32(b, e)?;
            let st_info = *b.get(e + 4).ok_or_else(|| ElfReparseError {
                message: format!("truncated st_info at {}", e + 4),
            })?;
            let st_other = *b.get(e + 5).ok_or_else(|| ElfReparseError {
                message: format!("truncated st_other at {}", e + 5),
            })?;
            let st_shndx = rd_u16(b, e + 6)?;
            let st_value = rd_u64(b, e + 8)?;
            let st_size = rd_u64(b, e + 16)?;
            let st_shndx_extended = if st_shndx == SHN_XINDEX {
                let Some(indices) = indices.filter(|indices| {
                    (k as u64)
                        .checked_mul(4)
                        .is_some_and(|at| at + 4 <= indices.sh_size)
                }) else {
                    return err(format!(
                        "symbol {k} has st_shndx SHN_XINDEX and no SHT_SYMTAB_SHNDX entry"
                    ));
                };
                Some(rd_u32(
                    b,
                    (indices.sh_offset as usize).saturating_add(k * 4),
                )?)
            } else {
                None
            };
            symbols.push(ParsedSym {
                name: strtab_name(b, str_off, str_size, st_name as usize, "strtab")?,
                st_bind: st_info >> 4,
                st_type: st_info & 0x0F,
                st_visibility: st_other & 0x03,
                st_shndx,
                st_shndx_extended,
                st_value,
                st_size,
            });
        }
    }

    // Relocation sections.
    let mut rela_sections = Vec::new();
    let mut rela_headers = Vec::new();
    for (index, sh) in shdrs.iter().enumerate() {
        if sh.sh_type != SHT_RELA {
            continue;
        }
        rela_headers.push((index, sh.sh_info as usize, sh.sh_flags));
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
        rela_headers,
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
/// ARTIFACT-LEVEL relocation-row digest: the sorted multiset of relocation
/// type values parsed from the EMITTED OBJECT BYTES themselves (every
/// `SHT_RELA` record's `r_type`, all sections).
///
/// This is the independent half of the proof-inventory cross-check. The
/// inventory is constructed by MIRRORING emitter bookkeeping (the fixup list
/// plus the expected writer-internal rows such as `.eh_frame` FDE pointers),
/// and the reparse gate proves only `bytes == writer intent` — so a
/// writer-side relocation the bookkeeping never anticipated would pass the
/// gate while shipping uninventoried. Digesting the artifact and requiring
/// the inventory to match it closes that seam (the recorded pre-emission
/// mirror follow-up).
pub fn reloc_type_digest(bytes: &[u8]) -> Result<Vec<u32>, ElfReparseError> {
    let po = parse_elf(bytes)?;
    let mut digest: Vec<u32> = po
        .rela_sections
        .iter()
        .flat_map(|(_, _, recs)| recs.iter().map(|r| r.reloc_type))
        .collect();
    digest.sort_unstable();
    Ok(digest)
}

/// One section header read back by the independent reader.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ElfSectionRecord {
    /// Section name resolved through `.shstrtab`.
    pub name: String,
    /// `sh_type`.
    pub sh_type: u32,
    /// `sh_flags`.
    pub sh_flags: u64,
    /// `sh_size` in bytes (for `SHT_NOBITS`, the zero-filled size).
    pub size: u64,
    /// `sh_addralign`.
    pub align: u64,
    /// `sh_offset`: where the section's bytes start in the object (a
    /// `SHT_NOBITS` section has none). A consumer that reads the bytes checks
    /// `[offset, offset + size)` against the object itself.
    pub offset: u64,
}

/// One symbol-table entry read back by the independent reader.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ElfSymbolRecord {
    /// Symbol name resolved through the symtab's linked string table.
    pub name: String,
    /// `STB_*` binding.
    pub binding: u8,
    /// `STT_*` type.
    pub symbol_type: u8,
    /// `STV_*` visibility.
    pub visibility: u8,
    /// `st_shndx` (0 = `SHN_UNDEF`).
    pub section_index: u16,
    /// The symbol's `SHT_SYMTAB_SHNDX` entry when `st_shndx` is
    /// `SHN_XINDEX` (extended section numbering); read the section that
    /// holds the symbol with [`ElfSymbolRecord::defining_section`].
    pub extended_section_index: Option<u32>,
    /// `st_value` (section offset in a relocatable object).
    pub value: u64,
    /// `st_size`.
    pub size: u64,
}

impl ElfSymbolRecord {
    /// Whether this is a named undefined reference (`SHN_UNDEF`, non-null).
    pub fn is_undefined_reference(&self) -> bool {
        self.section_index == 0 && !self.name.is_empty()
    }

    /// The section header index of the section that holds the symbol, or
    /// `None` when it names none (`SHN_UNDEF`, `SHN_ABS`, `SHN_COMMON` and
    /// the other reserved indices). A `SHN_XINDEX` symbol's index is its
    /// `SHT_SYMTAB_SHNDX` entry.
    pub fn defining_section(&self) -> Option<usize> {
        match self.section_index {
            0 => None,
            SHN_XINDEX => self
                .extended_section_index
                .and_then(|index| usize::try_from(index).ok()),
            index if index < SHN_LORESERVE => Some(usize::from(index)),
            _ => None,
        }
    }
}

/// One `Elf64_Rela` record plus the section header index it patches.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ElfRelocationRecord {
    /// Section header index of the patched section (`sh_info` of the RELA).
    pub target_section: usize,
    /// The record's fields.
    pub record: ElfRelocIntent,
}

/// Sections, symbols and relocation records of an ELF64 relocatable object,
/// read by the same spec-driven reader the reparse gate uses. No writer state
/// is consulted, so consumers (runtime-dependency manifests, relocation-window
/// checks) observe exactly the emitted bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ElfObjectRecords {
    /// `e_machine`.
    pub machine: u16,
    /// Section headers in table order (index 0 is the null section).
    pub sections: Vec<ElfSectionRecord>,
    /// Symbol table entries (index 0 is the null symbol).
    pub symbols: Vec<ElfSymbolRecord>,
    /// Every relocation record in section header table order.
    pub relocations: Vec<ElfRelocationRecord>,
}

/// Read an ELF64 little-endian relocatable object's sections, symbols and
/// relocation records independently of the writer.
pub fn read_object_records(bytes: &[u8]) -> Result<ElfObjectRecords, ElfReparseError> {
    let parsed = parse_elf(bytes)?;
    Ok(ElfObjectRecords {
        machine: parsed.machine,
        sections: parsed
            .shdrs
            .iter()
            .map(|shdr| ElfSectionRecord {
                name: shdr.name.clone(),
                sh_type: shdr.sh_type,
                sh_flags: shdr.sh_flags,
                size: shdr.sh_size,
                align: shdr.sh_addralign,
                offset: shdr.sh_offset,
            })
            .collect(),
        symbols: parsed
            .symbols
            .iter()
            .map(|symbol| ElfSymbolRecord {
                name: symbol.name.clone(),
                binding: symbol.st_bind,
                symbol_type: symbol.st_type,
                visibility: symbol.st_visibility,
                section_index: symbol.st_shndx,
                extended_section_index: symbol.st_shndx_extended,
                value: symbol.st_value,
                size: symbol.st_size,
            })
            .collect(),
        relocations: parsed
            .rela_sections
            .iter()
            .flat_map(|(target, _, records)| {
                records.iter().map(|record| ElfRelocationRecord {
                    target_section: *target,
                    record: *record,
                })
            })
            .collect(),
    })
}

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
        if ps.sh_entsize != si.entsize {
            return err(format!(
                "section {k} ({}) entsize {} != intended {}",
                si.name, ps.sh_entsize, si.entsize
            ));
        }
        if si.sh_type == SHT_GROUP {
            // Content is derived from final indices: checked by
            // `check_groups` against the independently reparsed layout.
            N_SECTIONS_CHECKED.fetch_add(1, Ordering::Relaxed);
            continue;
        }
        let want_size = si.size;
        if ps.sh_size != want_size {
            return err(format!(
                "section {k} ({}) size {} != intended {}",
                si.name, ps.sh_size, want_size
            ));
        }
        if si.sh_type != SHT_NOBITS {
            if si.data.len() as u64 != si.size {
                return err(format!(
                    "section {k} ({}) intent holds {} content byte(s) but records size {}",
                    si.name,
                    si.data.len(),
                    si.size
                ));
            }
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
        } else if !si.data.is_empty() {
            // A NOBITS section has no file bytes; the loader supplies zeros.
            // Intended content would be silently dropped (and an all-zero
            // image is a writer that materialised its zero-fill).
            let nonzero = if si.data.iter().any(|&byte| byte != 0) {
                "non-zero "
            } else {
                ""
            };
            return err(format!(
                "section {k} ({}) is SHT_NOBITS but its intent carries {} {nonzero}content byte(s) (zero-fill has no file bytes to carry them)",
                si.name,
                si.data.len()
            ));
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
            if got.st_visibility != want.visibility {
                return err(format!(
                    "symbol {:?} visibility {} != intended {}",
                    want.name, got.st_visibility, want.visibility
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
        if intent.sections[user_pos].sh_type == SHT_NOBITS {
            // A relocation patches file bytes; a zero-fill section has none.
            return err(format!(
                "rela section targets SHT_NOBITS user section {user_pos} ({})",
                intent.sections[user_pos].name
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

    check_groups(intent, bytes, &po, &user)?;

    Ok(())
}

/// Check every COMDAT section group against the reparsed layout.
///
/// For each intended group the `SHT_GROUP` header must link the symbol
/// table, carry `sh_entsize` 4 and no flags, name (by `sh_info`) a non-local
/// symbol with the intended signature name, PRECEDE every member in the
/// section header table, and hold exactly `GRP_COMDAT` followed by the
/// reparsed header index of every intended member and then of every
/// member's `.rela.*` section. `SHF_GROUP` must be set on exactly the group
/// members (user and relocation sections), so no section can join or leave
/// a group silently.
fn check_groups(
    intent: &ElfObjectIntent,
    bytes: &[u8],
    po: &ParsedElf,
    user: &[(usize, &ParsedShdr)],
) -> Result<(), ElfReparseError> {
    let mut member_of: Vec<Option<usize>> = vec![None; intent.sections.len()];
    for (g, group) in intent.groups.iter().enumerate() {
        let Some(&(group_shndx, group_sh)) = user.get(group.section) else {
            return err(format!(
                "group {g} names user section {} which does not exist",
                group.section
            ));
        };
        if intent.sections[group.section].sh_type != SHT_GROUP || group_sh.sh_type != SHT_GROUP {
            return err(format!("group {g} section {group_shndx} is not SHT_GROUP"));
        }
        if po.symtab_shndx != Some(group_sh.sh_link as usize) {
            return err(format!(
                "group {g} ({}) sh_link {} is not the symbol table {:?}",
                group.signature, group_sh.sh_link, po.symtab_shndx
            ));
        }
        if group_sh.sh_entsize != GROUP_ENTRY_SIZE || group_sh.sh_flags != 0 {
            return err(format!(
                "group {g} ({}) has entsize {} / flags {:#x}; expected 4 / 0",
                group.signature, group_sh.sh_entsize, group_sh.sh_flags
            ));
        }
        let signature = po
            .symbols
            .get(group_sh.sh_info as usize)
            .filter(|_| group_sh.sh_info != 0)
            .ok_or_else(|| ElfReparseError {
                message: format!(
                    "group {g} ({}) sh_info {} names no symbol",
                    group.signature, group_sh.sh_info
                ),
            })?;
        if signature.name != group.signature || signature.st_bind == STB_LOCAL {
            return err(format!(
                "group {g} signature symbol {:?} (bind {}) != intended non-local {:?}",
                signature.name, signature.st_bind, group.signature
            ));
        }
        if group.members.is_empty() {
            return err(format!("group {g} ({}) has no members", group.signature));
        }
        let mut words = vec![GRP_COMDAT];
        let mut rela_words = Vec::new();
        for &member in &group.members {
            let Some(&(member_shndx, _)) = user.get(member) else {
                return err(format!("group {g} member {member} is not a user section"));
            };
            if member_shndx <= group_shndx {
                return err(format!(
                    "group {g} ({}) at section {group_shndx} does not precede member section {member_shndx}",
                    group.signature
                ));
            }
            if member_of[member].replace(g).is_some() {
                return err(format!(
                    "user section {member} is a member of more than one group"
                ));
            }
            words.push(member_shndx as u32);
            if let Some(&(rela_shndx, _, _)) = po
                .rela_headers
                .iter()
                .find(|(_, target, _)| *target == member_shndx)
            {
                rela_words.push(rela_shndx as u32);
            }
        }
        words.extend(rela_words);
        let start = group_sh.sh_offset as usize;
        let len = words.len() * GROUP_ENTRY_SIZE as usize;
        if group_sh.sh_size != len as u64 {
            return err(format!(
                "group {g} ({}) size {} != intended {len}",
                group.signature, group_sh.sh_size
            ));
        }
        let region = bytes
            .get(start..start + len)
            .ok_or_else(|| ElfReparseError {
                message: format!("group {g} data {start}+{len} out of bounds"),
            })?;
        for (w, want) in words.iter().enumerate() {
            let got = rd_u32(region, w * 4)?;
            if got != *want {
                return err(format!(
                    "group {g} ({}) word {w} is {got}, intended {want}",
                    group.signature
                ));
            }
        }
    }
    for (pos, (shndx, sh)) in user.iter().enumerate() {
        let grouped = member_of[pos].is_some();
        if (sh.sh_flags & SHF_GROUP != 0) != grouped {
            return err(format!(
                "section {shndx} ({}) SHF_GROUP={} but group membership={grouped}",
                sh.name,
                sh.sh_flags & SHF_GROUP != 0
            ));
        }
    }
    for &(rela_shndx, target, flags) in &po.rela_headers {
        let grouped = user
            .iter()
            .position(|(shndx, _)| *shndx == target)
            .is_some_and(|pos| member_of[pos].is_some());
        let want = SHF_INFO_LINK | if grouped { SHF_GROUP } else { 0 };
        if flags != want {
            return err(format!(
                "rela section {rela_shndx} flags {flags:#x} != intended {want:#x}"
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
    N_OBJECTS_CHECKED.fetch_add(1, Ordering::Relaxed);
    match check_object(intent, bytes) {
        Ok(()) => {
            N_OBJECTS_MATCHED.fetch_add(1, Ordering::Relaxed);
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
    use crate::elf::reloc::{AArch64RelocType, Elf64Rela, X86_64RelocType};
    use crate::elf::writer::ElfWriter;

    // A representative x86-64 object: text + data + rodata, local + global +
    // weak + undefined symbols, and text + data relocations of every kind
    // the x86-64 ELF emitter produces.
    fn build_x86_writer() -> ElfWriter {
        let mut w = ElfWriter::new(ElfMachine::X86_64);
        // Ten bytes so the GOTPCREL field at offset 5 ends inside `.text`
        // (`ElfWriter::write_checked` refuses a field crossing the end).
        w.add_text_section(&[0x90, 0x90, 0xE8, 0, 0, 0, 0, 0xC3, 0x90, 0x90]);
        w.add_symbol("batch_a", 1, 0, 8, true, STT_FUNC);
        w.add_symbol("local_helper", 1, 2, 6, false, STT_FUNC);
        let data_idx = w.add_data_section(&[1, 2, 3, 4, 5, 6, 7, 8]);
        w.add_symbol("G", data_idx, 0, 8, true, STT_OBJECT);
        w.add_weak_symbol("W", data_idx, 4, 4, STT_OBJECT);
        w.add_section(".rodata", &[9, 9], SHT_PROGBITS, SHF_ALLOC, 8)
            .unwrap();
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
        let bytes = w.write_checked().unwrap();
        let intent = w.reparse_object_intent();
        assert!(
            check_object(&intent, &bytes).is_ok(),
            "a faithful x86-64 ELF object must pass the reparse gate: {:?}",
            check_object(&intent, &bytes)
        );
    }

    #[test]
    fn write_checked_is_deterministic() {
        let w = build_x86_writer();
        let first = w.write_checked().expect("faithful object must pass");
        let second = w.write_checked().expect("faithful object must pass");
        assert_eq!(first, second);
    }

    #[test]
    fn empty_object_is_consistent() {
        let w = ElfWriter::new(ElfMachine::X86_64);
        let bytes = w.write_checked().unwrap();
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
        let mut bytes = w.write_checked().unwrap();
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
        let mut bytes = w.write_checked().unwrap();
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
        let mut bytes = w.write_checked().unwrap();
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
        let mut bytes = w.write_checked().unwrap();
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
        let mut bytes = w.write_checked().unwrap();
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
        let mut bytes = w.write_checked().unwrap();
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

    /// An AArch64 object with `.bss`/`.tbss` zero-fill definitions.
    fn build_nobits_writer() -> ElfWriter {
        use crate::elf::constants::{SHF_TLS, SHF_WRITE, STT_TLS};
        let mut w = ElfWriter::new(ElfMachine::AArch64);
        w.add_text_section(&[0; 8]);
        let bss = w
            .add_nobits_section(".bss", 4096, SHF_ALLOC | SHF_WRITE, 64)
            .unwrap();
        let tbss = w
            .add_nobits_section(".tbss", 48, SHF_ALLOC | SHF_WRITE | SHF_TLS, 16)
            .unwrap();
        w.add_symbol("ZERO", bss, 64, 4032, true, STT_OBJECT);
        w.add_symbol("TLS_ZERO", tbss, 16, 32, true, STT_TLS);
        w
    }

    /// Section header offset of the named section (independent walk).
    fn section_header_offset(b: &[u8], name: &str) -> usize {
        let po = parse_elf(b).expect("parse");
        let index = po
            .shdrs
            .iter()
            .position(|s| s.name == name)
            .expect("section present");
        u64::from_le_bytes(b[40..48].try_into().unwrap()) as usize + index * SHDR_SIZE
    }

    #[test]
    fn nobits_object_passes_and_binds_size_and_flags() {
        let w = build_nobits_writer();
        let bytes = w.write_checked().expect("faithful NOBITS object must pass");
        let intent = w.reparse_object_intent();
        for (name, flag_bit) in [(".bss", 0x1u64), (".tbss", 0x400)] {
            // Size and flags are bound: a shrunken zero-fill region or a lost
            // SHF_TLS / SHF_WRITE bit is a would-be miscompile.
            let header = section_header_offset(&bytes, name);
            let mut shrunk = bytes.clone();
            shrunk[header + 32] ^= 0x10;
            assert!(check_object(&intent, &shrunk).is_err(), "{name} size");
            let mut flags = bytes.clone();
            flags[header + 8..header + 16]
                .copy_from_slice(&(SHF_ALLOC | (0x401 & !flag_bit)).to_le_bytes());
            assert!(check_object(&intent, &flags).is_err(), "{name} flags");
        }
    }

    #[test]
    fn refutation_nonzero_nobits_content_fails_closed() {
        use crate::elf::constants::SHF_WRITE;
        use crate::elf::writer::ElfSectionError;
        let mut w = ElfWriter::new(ElfMachine::AArch64);
        w.add_text_section(&[0; 4]);
        // The writer refuses the image before it holds it...
        let error = w
            .add_section(".bss", &[0, 1, 0, 0], SHT_NOBITS, SHF_ALLOC | SHF_WRITE, 4)
            .expect_err("non-zero NOBITS content must fail closed");
        assert_eq!(
            error,
            ElfSectionError::NobitsWithContent {
                name: ".bss".to_string(),
                offset: 1
            }
        );
        assert_eq!(
            w.reparse_object_intent().sections.len(),
            1,
            "writer unchanged"
        );
        // ...and the gate refuses an intent that carries zero-fill content,
        // zero or not: NOBITS has no file bytes to hold it.
        w.add_nobits_section(".bss", 4, SHF_ALLOC | SHF_WRITE, 4)
            .unwrap();
        let bytes = w.write_checked().expect("faithful NOBITS object");
        for (content, nonzero) in [(vec![0, 1, 0, 0], true), (vec![0; 4], false)] {
            let mut intent = w.reparse_object_intent();
            intent.sections[1].data = content;
            let error = check_object(&intent, &bytes)
                .expect_err("NOBITS content in the intent must fail closed");
            assert!(
                error.message.contains("SHT_NOBITS")
                    && error.message.contains("non-zero") == nonzero,
                "{error}"
            );
        }
    }

    #[test]
    fn refutation_relocation_against_nobits_section_fails_closed() {
        let mut w = build_nobits_writer();
        w.add_relocation(1, Elf64Rela::aarch64(0, 1, AArch64RelocType::Abs64, 0));
        let error = w
            .write_checked()
            .expect_err("a relocation into zero-fill must fail closed");
        assert!(
            error
                .message
                .contains("zero-fill section `.bss` carries 1 relocation"),
            "{error}"
        );
        // The gate refuses the same shape in bytes: a `.text` relocation
        // section retargeted (`sh_info`) at `.bss`, header index 2.
        let mut w = build_nobits_writer();
        w.add_relocation(0, Elf64Rela::aarch64(0, 1, AArch64RelocType::Abs64, 0));
        let bytes = w.write_checked().expect("a text relocation is faithful");
        let intent = w.reparse_object_intent();
        let rela = section_header_offset(&bytes, ".rela.text");
        let mut retargeted = bytes.clone();
        retargeted[rela + 44..rela + 48].copy_from_slice(&2u32.to_le_bytes());
        let error = check_object(&intent, &retargeted)
            .expect_err("a relocation section targeting zero-fill must fail closed");
        assert!(
            error.message.contains("targets SHT_NOBITS user section"),
            "{error}"
        );
    }

    /// An AArch64 object whose COMDAT groups each hold one zero-fill member,
    /// as the pipeline emits a zero-initialized link-once global
    /// (`.bss.lo_zero`) and an all-zero link-once TLS template
    /// (`.tbss.lo_tls`), next to an ungrouped `.bss`.
    fn build_grouped_nobits_writer() -> ElfWriter {
        use crate::elf::constants::{SHF_TLS, SHF_WRITE, STT_TLS};
        use crate::elf::writer::ElfSymbol;
        let mut w = ElfWriter::new(ElfMachine::AArch64);
        w.add_text_section(&[0; 8]);
        let zero = vec![0u8; 4096];
        let bss_group = w.add_comdat_group();
        let bss = w
            .add_group_member_section(
                bss_group,
                ".bss.lo_zero",
                &zero,
                SHT_NOBITS,
                SHF_ALLOC | SHF_WRITE,
                64,
                0,
            )
            .unwrap();
        let tbss_group = w.add_comdat_group();
        let tbss = w
            .add_group_member_section(
                tbss_group,
                ".tbss.lo_tls",
                &[0; 48],
                SHT_NOBITS,
                SHF_ALLOC | SHF_WRITE | SHF_TLS,
                16,
                0,
            )
            .unwrap();
        let plain = w
            .add_nobits_section(".bss", 16, SHF_ALLOC | SHF_WRITE, 8)
            .unwrap();
        let weak = |name: &str, section: u16, size: u64, sym_type: u8| ElfSymbol {
            name: name.into(),
            section,
            value: 0,
            size,
            is_global: false,
            sym_type,
            is_weak: true,
            visibility: 0,
        };
        let zero_id = w
            .add_checked_symbol(weak("lo_zero", bss, 4096, STT_OBJECT))
            .unwrap();
        w.bind_comdat_group_signature(bss_group, zero_id).unwrap();
        let tls_id = w
            .add_checked_symbol(weak("lo_tls", tbss, 48, STT_TLS))
            .unwrap();
        w.bind_comdat_group_signature(tbss_group, tls_id).unwrap();
        w.add_symbol("plain_zero", plain, 0, 16, true, STT_OBJECT);
        w
    }

    /// Grouped NOBITS members pass the gate, occupy no file bytes, and have
    /// their type, size, `SHF_GROUP`/`SHF_TLS`/`SHF_WRITE` flags and group
    /// payload bound: each byte mutation is refused.
    #[test]
    fn grouped_nobits_members_pass_and_bind_type_size_flags_and_membership() {
        let w = build_grouped_nobits_writer();
        let bytes = w
            .write_checked()
            .expect("faithful grouped NOBITS object must pass");
        assert!(
            bytes.len() < 4096,
            "zero fill took {} file bytes",
            bytes.len()
        );
        let intent = w.reparse_object_intent();
        let po = parse_elf(&bytes).unwrap();
        let index_of = |name: &str| po.shdrs.iter().position(|s| s.name == name).unwrap();
        for name in [".bss.lo_zero", ".tbss.lo_tls"] {
            let shdr = &po.shdrs[index_of(name)];
            assert_eq!(shdr.sh_type, SHT_NOBITS, "{name}");
            assert_ne!(shdr.sh_flags & SHF_GROUP, 0, "{name}");
        }
        assert_eq!(po.shdrs[index_of(".bss")].sh_flags & SHF_GROUP, 0);

        let mutated = |name: &str, field: usize, value: &[u8]| {
            let mut copy = bytes.clone();
            let at = section_header_offset(&bytes, name) + field;
            copy[at..at + value.len()].copy_from_slice(value);
            copy
        };
        let flags = |bits: u64| bits.to_le_bytes().to_vec();
        for (label, copy) in [
            (
                "grouped .bss type PROGBITS",
                mutated(".bss.lo_zero", 4, &SHT_PROGBITS.to_le_bytes()),
            ),
            (
                "grouped .bss without SHF_GROUP",
                mutated(".bss.lo_zero", 8, &flags(0x3)),
            ),
            (
                "grouped .bss without SHF_WRITE",
                mutated(".bss.lo_zero", 8, &flags(SHF_ALLOC | SHF_GROUP)),
            ),
            (
                "grouped .bss shrunk",
                mutated(".bss.lo_zero", 32, &4080u64.to_le_bytes()),
            ),
            (
                "grouped .tbss without SHF_TLS",
                mutated(".tbss.lo_tls", 8, &flags(0x3 | SHF_GROUP)),
            ),
            (
                "grouped .tbss type PROGBITS",
                mutated(".tbss.lo_tls", 4, &SHT_PROGBITS.to_le_bytes()),
            ),
            (
                "ungrouped .bss claims SHF_GROUP",
                mutated(".bss", 8, &flags(0x3 | SHF_GROUP)),
            ),
        ] {
            assert!(check_object(&intent, &copy).is_err(), "{label}");
        }
        // The `.bss.lo_zero` group's member word names the ungrouped `.bss`.
        let group = po
            .shdrs
            .iter()
            .position(|s| {
                s.sh_type == SHT_GROUP && po.symbols[s.sh_info as usize].name == "lo_zero"
            })
            .unwrap();
        let payload = po.shdrs[group].sh_offset as usize;
        assert_eq!(rd_u32(&bytes, payload).unwrap(), GRP_COMDAT);
        assert_eq!(
            rd_u32(&bytes, payload + 4).unwrap() as usize,
            index_of(".bss.lo_zero")
        );
        let mut retargeted = bytes.clone();
        retargeted[payload + 4..payload + 8]
            .copy_from_slice(&(index_of(".bss") as u32).to_le_bytes());
        assert!(check_object(&intent, &retargeted).is_err(), "group payload");
    }

    #[test]
    fn refutation_nonzero_grouped_nobits_content_fails_closed() {
        use crate::elf::constants::SHF_WRITE;
        let mut w = ElfWriter::new(ElfMachine::AArch64);
        w.add_text_section(&[0; 8]);
        let group = w.add_comdat_group();
        let mut zero = vec![0u8; 4096];
        zero[4095] = 1;
        let error = w
            .add_group_member_section(
                group,
                ".bss.lo_zero",
                &zero,
                SHT_NOBITS,
                SHF_ALLOC | SHF_WRITE,
                64,
                0,
            )
            .expect_err("non-zero grouped NOBITS content must fail closed");
        let message = error.to_string();
        assert!(
            message.contains(".bss.lo_zero")
                && message.contains("SHT_NOBITS")
                && message.contains("offset 4095"),
            "{message}"
        );
    }

    #[test]
    fn refutation_relocation_against_grouped_nobits_member_fails_closed() {
        let mut w = build_grouped_nobits_writer();
        // User section 2 is `.bss.lo_zero` (text, group, member, ...).
        w.add_relocation(2, Elf64Rela::aarch64(0, 1, AArch64RelocType::Abs64, 0));
        let error = w
            .write_checked()
            .expect_err("a relocation into a grouped zero-fill member must fail closed");
        assert!(
            error
                .message
                .contains("zero-fill section `.bss.lo_zero` carries 1 relocation"),
            "{error}"
        );
    }

    /// An AArch64 TLSDESC access (`ADRP x0 / LDR x1,[x0] / ADD x0,x0 /
    /// BLR x1` against an undefined `STT_TLS` symbol) as the `pic` emitters
    /// write it.
    fn build_tlsdesc_writer() -> ElfWriter {
        use crate::elf::constants::STT_TLS;
        let mut w = ElfWriter::new(ElfMachine::AArch64);
        let mut text = Vec::new();
        for word in [0x9000_0000u32, 0xf940_0001, 0x9100_0000, 0xd63f_0020] {
            text.extend_from_slice(&word.to_le_bytes());
        }
        w.add_text_section(&text);
        w.add_symbol("addr_tv", 1, 0, 16, true, STT_FUNC);
        w.add_symbol("tv", 0, 0, 0, true, STT_TLS);
        for (offset, kind) in [
            (0, AArch64RelocType::TlsdescAdrPage21),
            (4, AArch64RelocType::TlsdescLd64Lo12),
            (8, AArch64RelocType::TlsdescAddLo12),
            (12, AArch64RelocType::TlsdescCall),
        ] {
            w.add_relocation(0, Elf64Rela::aarch64(offset, 2, kind, 0));
        }
        w
    }

    #[test]
    fn tlsdesc_records_pass_and_enter_the_type_digest() {
        let w = build_tlsdesc_writer();
        let bytes = w.write_checked().expect("faithful TLSDESC object");
        let mut digest = reloc_type_digest(&bytes).expect("digest");
        digest.sort_unstable();
        assert_eq!(digest, vec![0x232, 0x233, 0x234, 0x239]);
    }

    #[test]
    fn refutation_tlsdesc_call_marker_retyped_fails_closed() {
        let w = build_tlsdesc_writer();
        let mut bytes = w.write_checked().unwrap();
        let intent = w.reparse_object_intent();
        let rela = first_rela_offset(&bytes);
        let call = (0..4)
            .map(|index| rela + index * 24)
            .find(|&record| {
                u32::from_le_bytes(bytes[record + 8..record + 12].try_into().unwrap()) == 0x239
            })
            .expect("TLSDESC_CALL record");
        // R_AARCH64_TLSDESC_CALL (0x239) -> R_AARCH64_TLSDESC_ADD (0x238): the
        // linker would no longer recognise the call slot for relaxation.
        bytes[call + 8] = 0x38;
        assert!(check_object(&intent, &bytes).is_err());
    }

    #[test]
    fn refutation_wrong_machine_fails_closed() {
        let w = build_x86_writer();
        let mut bytes = w.write_checked().unwrap();
        let intent = w.reparse_object_intent();
        bytes[18] = 183u8; // EM_AARCH64 low byte (EM_X86_64 = 62)
        assert!(check_object(&intent, &bytes).is_err());
    }

    /// `bytes` rewritten with extended section numbering, as an assembler
    /// writes an object of 65,280 sections or more: `e_shnum` 0 with the
    /// count in section 0's `sh_size`, `e_shstrndx` `SHN_XINDEX` with the
    /// index in section 0's `sh_link`, and the symbol `symbol`'s `st_shndx`
    /// `SHN_XINDEX` with its index in a new `SHT_SYMTAB_SHNDX` section
    /// (appended with the section header table, when `with_indices`).
    fn with_extended_numbering(bytes: &[u8], symbol: usize, with_indices: bool) -> Vec<u8> {
        let u16_at = |b: &[u8], at: usize| u16::from_le_bytes(b[at..at + 2].try_into().unwrap());
        let u32_at = |b: &[u8], at: usize| u32::from_le_bytes(b[at..at + 4].try_into().unwrap());
        let u64_at = |b: &[u8], at: usize| u64::from_le_bytes(b[at..at + 8].try_into().unwrap());
        let mut out = bytes.to_vec();
        let shoff = u64_at(bytes, 40) as usize;
        let shnum = usize::from(u16_at(bytes, 60));
        let shstrndx = u16_at(bytes, 62);
        let header = |index: usize| shoff + index * SHDR_SIZE;
        let symtab = (0..shnum)
            .find(|index| u32_at(bytes, header(*index) + 4) == SHT_SYMTAB)
            .unwrap();
        let symoff = u64_at(bytes, header(symtab) + 24) as usize;
        let count = u64_at(bytes, header(symtab) + 32) as usize / SYM_SIZE;
        let entry = symoff + symbol * SYM_SIZE;
        let real = u16_at(bytes, entry + 6);
        out[entry + 6..entry + 8].copy_from_slice(&SHN_XINDEX.to_le_bytes());
        let mut indices = vec![0u32; count];
        indices[symbol] = u32::from(real);
        out.resize(out.len().next_multiple_of(8), 0);
        let indices_at = out.len();
        for index in &indices {
            out.extend(index.to_le_bytes());
        }
        out.resize(out.len().next_multiple_of(8), 0);
        let table_at = out.len();
        out.extend_from_slice(&bytes[shoff..shoff + shnum * SHDR_SIZE]);
        let mut total = shnum;
        if with_indices {
            let mut added = vec![0u8; SHDR_SIZE];
            added[4..8].copy_from_slice(&SHT_SYMTAB_SHNDX.to_le_bytes());
            added[24..32].copy_from_slice(&(indices_at as u64).to_le_bytes());
            added[32..40].copy_from_slice(&((count * 4) as u64).to_le_bytes());
            added[40..44].copy_from_slice(&(symtab as u32).to_le_bytes());
            added[56..64].copy_from_slice(&4u64.to_le_bytes());
            out.extend(added);
            total += 1;
        }
        out[40..48].copy_from_slice(&(table_at as u64).to_le_bytes());
        out[60..62].copy_from_slice(&0u16.to_le_bytes());
        out[62..64].copy_from_slice(&SHN_XINDEX.to_le_bytes());
        out[table_at + 32..table_at + 40].copy_from_slice(&(total as u64).to_le_bytes());
        out[table_at + 40..table_at + 44].copy_from_slice(&u32::from(shstrndx).to_le_bytes());
        out
    }

    /// An object with extended section numbering (`e_shnum` 0, `e_shstrndx`
    /// `SHN_XINDEX`, a symbol's `st_shndx` `SHN_XINDEX` resolved through
    /// `SHT_SYMTAB_SHNDX`) reads as the same sections, symbols and
    /// relocations; a `SHN_XINDEX` symbol without its entry is an error.
    /// g++ wrote such an object for a 6,000-class translation unit.
    #[test]
    fn extended_section_numbering_is_read() {
        let bytes = build_x86_writer().write_checked().unwrap();
        let plain = read_object_records(&bytes).unwrap();
        let symbol = plain
            .symbols
            .iter()
            .position(|symbol| symbol.name == "G")
            .unwrap();
        let defining = plain.symbols[symbol].defining_section().unwrap();
        assert!(defining > 0);
        let extended = with_extended_numbering(&bytes, symbol, true);
        let read = read_object_records(&extended).unwrap();
        assert_eq!(read.sections.len(), plain.sections.len() + 1);
        // Section 0 holds the count.
        assert_eq!(read.sections[0].size, read.sections.len() as u64);
        assert_eq!(read.sections[1..plain.sections.len()], plain.sections[1..]);
        assert_eq!(read.relocations, plain.relocations);
        assert_eq!(read.symbols[symbol].section_index, SHN_XINDEX);
        assert_eq!(read.symbols[symbol].defining_section(), Some(defining));
        for (index, (read, plain)) in read.symbols.iter().zip(&plain.symbols).enumerate() {
            if index != symbol {
                assert_eq!(read, plain);
            }
        }
        let missing = with_extended_numbering(&bytes, symbol, false);
        let error = read_object_records(&missing).unwrap_err();
        assert!(
            error
                .message
                .contains("SHN_XINDEX and no SHT_SYMTAB_SHNDX entry"),
            "{error:?}"
        );
    }
}
