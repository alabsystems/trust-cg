// trust-cg-codegen — ENC-9: per-compile Mach-O object reparse gate
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// WHAT THIS IS (honest labeling)
// ------------------------------
// A per-compile, fail-closed REDUNDANCY gate that closes trusted-island-3 one
// level ABOVE the instruction encoder (ENC-3 / `decode_check`). The Mach-O
// object WRITER (`macho/writer.rs`) lays out the header, load commands, section
// table, symbol table, string table, and relocation records; it is otherwise
// trusted (golden-tested only). After `MachOWriter::write` produces the object
// bytes, this gate RE-PARSES those bytes with an INDEPENDENT, spec-driven
// Mach-O reader (written from `<mach-o/loader.h>` / `<mach-o/nlist.h>` /
// `<mach-o/reloc.h>`, NOT by calling the writer's own `Section64::write` /
// `encode_relocation` / `write_nlist64`) and structurally compares the reparsed
// structure against the INTENDED object description (the sections/symbols/
// relocations the writer was told to emit). Any disagreement — a section whose
// name/size/align/flags/offset/bytes do not re-parse to intent, a symbol whose
// type/section/value/weak-flag disagrees, or a relocation record whose
// (r_address, r_symbolnum, r_type, r_pcrel, r_length, r_extern) does not
// re-parse to intent, or the wrong count/placement of any of these — is a
// would-be malformed object = FAIL CLOSED.
//
// This is NOT a proof. Two independent artifacts (the writer + this reader)
// must agree per compile. It is COMPLEMENTARY to the proven relocation FORMULA
// (`macho_data_reloc_proofs.rs` proves the patched VALUE a fixup computes); this
// gate proves the relocation RECORD (and the whole object skeleton) was laid
// down faithfully. Per the project soundness doctrine, reparse-agreement is
// REDUNDANCY, never counted in a "proven" numerator.
//
// SCOPE
// -----
// Mach-O object emission ONLY (both arches share this writer, so this is a
// shared investment). The following remain TRUSTED ISLANDS, tracked as explicit
// follow-ons:
//   * ELF (`macho`-sibling `elf/`) and COFF (`coff/`) object writers — a
//     separate reparse gate (the riscv/bdefs bridge exercises the ELF path).
//   * The in-house Mach-O LINKER (`macho/linker.rs`) applied-fixup byte ranges
//     (ENC-9 "Gate 2": recompute the proven formula over the final layout and
//     byte-compare the linked image) — a separate hook one level up.
//
// ROLLOUT (soundness-doctrine gate rollout, §2.4)
// -----------------------------------------------
//   TCG_MACHO_REPARSE = off | warn | enforce   (default: enforce — default-ON)
//   TCG_NO_MACHO_REPARSE = 1                    triage opt-out (mirrors
//                                               TCG_NO_PROOF_CERTS / ENC-3's
//                                               TCG_NO_DECODE_CHECK; never
//                                               weakens a default silently)
//   TCG_TRACE_MACHO_REPARSE = 1                 per-object trace + summary
//
// `warn` records telemetry and prints every disagreement LOUDLY (P0 evidence of
// a live writer bug) WITHOUT failing the compile — used to run the full
// differential corpus to 0 disagreements before flipping the default to
// `enforce`. In `enforce` a disagreement is fail-closed (the writer's public
// `write()` funnel aborts rather than return a malformed object).

use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

use super::writer::MachOTarget;

// ---------------------------------------------------------------------------
// Mach-O ABI constants — re-declared LOCALLY so this reader is an independent
// artifact (it does NOT import the writer's layout code). Values are from the
// Mach-O ABI headers, identical to what any external tool (otool/llvm-readobj)
// uses.
// ---------------------------------------------------------------------------

const MH_MAGIC_64: u32 = 0xFEED_FACF;
const MH_OBJECT: u32 = 0x1;
const CPU_TYPE_X86_64: u32 = 0x0100_0007;
const CPU_TYPE_ARM64: u32 = 0x0100_000C;

const LC_SEGMENT_64: u32 = 0x19;
const LC_SYMTAB: u32 = 0x02;
const LC_DYSYMTAB: u32 = 0x0B;

const MACH_HEADER_64_SIZE: usize = 32;
const SEGMENT_COMMAND_64_BASE: usize = 72;
const SECTION_64_SIZE: usize = 80;
const NLIST_64_SIZE: usize = 16;
const RELOCATION_INFO_SIZE: usize = 8;

// nlist n_type bits.
const N_EXT: u8 = 0x01;
const N_TYPE_MASK: u8 = 0x0E;
const N_UNDF: u8 = 0x00;
const N_SECT: u8 = 0x0E;

// nlist n_desc weak flags.
const N_WEAK_REF: u16 = 0x0040;
const N_WEAK_DEF: u16 = 0x0080;

// ---------------------------------------------------------------------------
// Rollout mode
// ---------------------------------------------------------------------------

/// Rollout mode for the Mach-O reparse gate.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MachoReparseMode {
    /// Gate disabled (no reparse, no check). Triage-only.
    Off,
    /// Reparse and compare; a disagreement is logged loudly but does NOT fail
    /// the compile. Telemetry is still recorded. Gate-rollout warm-up.
    Warn,
    /// Reparse and compare; a disagreement FAILS the compile (default-ON).
    Enforce,
}

/// Resolve the gate mode from the environment (cached process-wide).
pub fn macho_reparse_mode() -> MachoReparseMode {
    static MODE: OnceLock<MachoReparseMode> = OnceLock::new();
    *MODE.get_or_init(|| {
        // Triage opt-out takes precedence, mirroring TCG_NO_PROOF_CERTS.
        if std::env::var_os("TCG_NO_MACHO_REPARSE").is_some() {
            return MachoReparseMode::Off;
        }
        match std::env::var("TCG_MACHO_REPARSE").ok().as_deref() {
            Some("off") | Some("0") | Some("false") => MachoReparseMode::Off,
            Some("warn") => MachoReparseMode::Warn,
            Some("enforce") | Some("1") | Some("on") | Some("true") => MachoReparseMode::Enforce,
            // DEFAULT-ON: any unset / unrecognized value enforces.
            _ => MachoReparseMode::Enforce,
        }
    })
}

/// Whether per-object tracing is enabled (`TCG_TRACE_MACHO_REPARSE=1`).
pub fn macho_reparse_trace_enabled() -> bool {
    static TRACE: OnceLock<bool> = OnceLock::new();
    *TRACE.get_or_init(|| std::env::var_os("TCG_TRACE_MACHO_REPARSE").is_some())
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

/// Snapshot of the reparse-gate telemetry counters.
#[derive(Clone, Debug, Default)]
pub struct MachoReparseCounters {
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
pub fn macho_reparse_counters() -> MachoReparseCounters {
    MachoReparseCounters {
        objects_checked: N_OBJECTS_CHECKED.load(Ordering::Relaxed),
        objects_matched: N_OBJECTS_MATCHED.load(Ordering::Relaxed),
        objects_mismatched: N_OBJECTS_MISMATCHED.load(Ordering::Relaxed),
        sections_checked: N_SECTIONS_CHECKED.load(Ordering::Relaxed),
        symbols_checked: N_SYMBOLS_CHECKED.load(Ordering::Relaxed),
        relocs_checked: N_RELOCS_CHECKED.load(Ordering::Relaxed),
    }
}

/// Reset all telemetry counters (test-only helper).
pub fn reset_macho_reparse_counters() {
    N_OBJECTS_CHECKED.store(0, Ordering::Relaxed);
    N_OBJECTS_MATCHED.store(0, Ordering::Relaxed);
    N_OBJECTS_MISMATCHED.store(0, Ordering::Relaxed);
    N_SECTIONS_CHECKED.store(0, Ordering::Relaxed);
    N_SYMBOLS_CHECKED.store(0, Ordering::Relaxed);
    N_RELOCS_CHECKED.store(0, Ordering::Relaxed);
}

// ---------------------------------------------------------------------------
// Intended object description (built from the writer's high-level input model)
// ---------------------------------------------------------------------------

/// One intended section: what the writer was told to emit (NOT the computed
/// file layout — offsets/addresses are derived from the reparsed bytes and
/// cross-checked, so a layout bug in the writer cannot hide).
#[derive(Clone, Debug)]
pub struct SectionIntent {
    /// Section name (e.g. `b"__text"`), unpadded.
    pub sectname: Vec<u8>,
    /// Segment name (e.g. `b"__TEXT"`), unpadded.
    pub segname: Vec<u8>,
    /// Alignment as a power of two.
    pub align: u32,
    /// Section flags (type | attributes).
    pub flags: u32,
    /// The exact content bytes the writer was told to place in this section.
    pub data: Vec<u8>,
}

/// One intended symbol.
#[derive(Clone, Debug)]
pub struct SymbolIntent {
    /// Symbol name (as stored — the writer does not add a prefix).
    pub name: String,
    /// 1-based section ordinal, or 0 for an undefined symbol.
    pub section: u8,
    /// Offset within the section (defined) or 0 (undefined).
    pub value: u64,
    /// Whether the symbol is externally visible.
    pub is_global: bool,
    /// Whether the symbol is weak.
    pub is_weak: bool,
}

/// One intended relocation record's fields (arch-neutral `relocation_info`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RelocIntent {
    /// `r_address`: byte offset within the section.
    pub r_address: u32,
    /// `r_symbolnum`: symbol table index or section ordinal.
    pub r_symbolnum: u32,
    /// `r_pcrel`.
    pub r_pcrel: bool,
    /// `r_length`: log2 of the fixup size.
    pub r_length: u8,
    /// `r_extern`.
    pub r_extern: bool,
    /// `r_type`: the relocation type value.
    pub r_type: u8,
}

/// The complete intended object: what `MachOWriter::write` was asked to emit.
#[derive(Clone, Debug)]
pub struct MachoObjectIntent {
    /// Target CPU (selects the expected `cputype`).
    pub target: MachOTarget,
    /// Intended sections, in emission order.
    pub sections: Vec<SectionIntent>,
    /// Intended relocations per section (same index as `sections`), in the
    /// writer's emission order (AArch64 records then x86-64 records).
    pub section_relocs: Vec<Vec<RelocIntent>>,
    /// Intended symbols, in insertion order.
    pub symbols: Vec<SymbolIntent>,
}

// ---------------------------------------------------------------------------
// Error
// ---------------------------------------------------------------------------

/// A structural disagreement between the intended object and the reparsed
/// bytes. In enforce mode this becomes a fail-closed abort of the emit funnel.
#[derive(Clone, Debug)]
pub struct MachoReparseError {
    /// Human-readable description (intended vs reparsed).
    pub message: String,
}

impl core::fmt::Display for MachoReparseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "[macho-reparse] {}", self.message)
    }
}

fn err<T>(message: String) -> Result<T, MachoReparseError> {
    Err(MachoReparseError { message })
}

// ---------------------------------------------------------------------------
// Independent, spec-driven little-endian reader
// ---------------------------------------------------------------------------

fn rd_u16(b: &[u8], off: usize) -> Result<u16, MachoReparseError> {
    b.get(off..off + 2)
        .map(|s| u16::from_le_bytes([s[0], s[1]]))
        .ok_or_else(|| MachoReparseError {
            message: format!("truncated: u16 at {off} (len {})", b.len()),
        })
}

fn rd_u32(b: &[u8], off: usize) -> Result<u32, MachoReparseError> {
    b.get(off..off + 4)
        .map(|s| u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
        .ok_or_else(|| MachoReparseError {
            message: format!("truncated: u32 at {off} (len {})", b.len()),
        })
}

fn rd_u64(b: &[u8], off: usize) -> Result<u64, MachoReparseError> {
    b.get(off..off + 8)
        .map(|s| u64::from_le_bytes([s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]]))
        .ok_or_else(|| MachoReparseError {
            message: format!("truncated: u64 at {off} (len {})", b.len()),
        })
}

/// A 16-byte fixed name field, trimmed of trailing NULs.
fn rd_name16(b: &[u8], off: usize) -> Result<Vec<u8>, MachoReparseError> {
    let raw = b.get(off..off + 16).ok_or_else(|| MachoReparseError {
        message: format!("truncated: name16 at {off} (len {})", b.len()),
    })?;
    let end = raw.iter().position(|&c| c == 0).unwrap_or(16);
    Ok(raw[..end].to_vec())
}

/// A parsed `section_64` header (only the fields the gate checks).
#[derive(Clone, Debug)]
struct ParsedSection {
    sectname: Vec<u8>,
    segname: Vec<u8>,
    addr: u64,
    size: u64,
    offset: u32,
    align: u32,
    reloff: u32,
    nreloc: u32,
    flags: u32,
}

/// A parsed `nlist_64` entry with its resolved name.
#[derive(Clone, Debug)]
struct ParsedSymbol {
    name: String,
    n_type: u8,
    n_sect: u8,
    n_desc: u16,
    n_value: u64,
}

/// The reparsed object skeleton.
#[derive(Debug)]
struct ParsedObject {
    cputype: u32,
    filetype: u32,
    sections: Vec<ParsedSection>,
    symbols: Vec<ParsedSymbol>,
    /// Per-section relocation records (same index as `sections`).
    section_relocs: Vec<Vec<RelocIntent>>,
    dysymtab: Option<(u32, u32, u32)>, // (nlocalsym, nextdefsym, nundefsym)
}

/// Parse a `relocation_info` (8 bytes) at `off` into its arch-neutral fields.
fn parse_reloc(b: &[u8], off: usize) -> Result<RelocIntent, MachoReparseError> {
    let r_word0 = rd_u32(b, off)?;
    let r_word1 = rd_u32(b, off + 4)?;
    Ok(RelocIntent {
        r_address: r_word0,
        r_symbolnum: r_word1 & 0x00FF_FFFF,
        r_pcrel: (r_word1 >> 24) & 1 != 0,
        r_length: ((r_word1 >> 25) & 3) as u8,
        r_extern: (r_word1 >> 27) & 1 != 0,
        r_type: ((r_word1 >> 28) & 0xF) as u8,
    })
}

/// Independently parse a Mach-O object from raw bytes (header, load commands,
/// section table, symtab + strtab, and per-section relocation records). Spec
/// layout only — no writer code is consulted.
fn parse_object(b: &[u8]) -> Result<ParsedObject, MachoReparseError> {
    if b.len() < MACH_HEADER_64_SIZE {
        return err(format!(
            "object too small ({} bytes) for a mach_header_64",
            b.len()
        ));
    }
    let magic = rd_u32(b, 0)?;
    if magic != MH_MAGIC_64 {
        return err(format!("bad magic {magic:#010x} (expected MH_MAGIC_64)"));
    }
    let cputype = rd_u32(b, 4)?;
    let filetype = rd_u32(b, 12)?;
    let ncmds = rd_u32(b, 16)?;

    let mut sections: Vec<ParsedSection> = Vec::new();
    let mut symtab: Option<(u32, u32, u32, u32)> = None; // symoff, nsyms, stroff, strsize
    let mut dysymtab: Option<(u32, u32, u32)> = None;

    // Walk the load commands generically by (cmd, cmdsize).
    let mut lc = MACH_HEADER_64_SIZE;
    for i in 0..ncmds {
        let cmd = rd_u32(b, lc)?;
        let cmdsize = rd_u32(b, lc + 4)? as usize;
        if cmdsize < 8 || lc + cmdsize > b.len() {
            return err(format!(
                "load command {i} at {lc} has invalid cmdsize {cmdsize} (buffer len {})",
                b.len()
            ));
        }
        match cmd {
            LC_SEGMENT_64 => {
                let nsects = rd_u32(b, lc + 64)?;
                let mut so = lc + SEGMENT_COMMAND_64_BASE;
                for _ in 0..nsects {
                    sections.push(ParsedSection {
                        sectname: rd_name16(b, so)?,
                        segname: rd_name16(b, so + 16)?,
                        addr: rd_u64(b, so + 32)?,
                        size: rd_u64(b, so + 40)?,
                        offset: rd_u32(b, so + 48)?,
                        align: rd_u32(b, so + 52)?,
                        reloff: rd_u32(b, so + 56)?,
                        nreloc: rd_u32(b, so + 60)?,
                        flags: rd_u32(b, so + 64)?,
                    });
                    so += SECTION_64_SIZE;
                }
            }
            LC_SYMTAB => {
                symtab = Some((
                    rd_u32(b, lc + 8)?,
                    rd_u32(b, lc + 12)?,
                    rd_u32(b, lc + 16)?,
                    rd_u32(b, lc + 20)?,
                ));
            }
            LC_DYSYMTAB => {
                // nlocalsym @ +12, nextdefsym @ +20, nundefsym @ +28.
                dysymtab = Some((
                    rd_u32(b, lc + 12)?,
                    rd_u32(b, lc + 20)?,
                    rd_u32(b, lc + 28)?,
                ));
            }
            _ => {}
        }
        lc += cmdsize;
    }

    // Symbols.
    let mut symbols: Vec<ParsedSymbol> = Vec::new();
    if let Some((symoff, nsyms, stroff, strsize)) = symtab {
        let strtab_end = stroff as usize + strsize as usize;
        for k in 0..nsyms as usize {
            let e = symoff as usize + k * NLIST_64_SIZE;
            let n_strx = rd_u32(b, e)?;
            let n_type = *b.get(e + 4).ok_or_else(|| MachoReparseError {
                message: format!("truncated nlist n_type at {}", e + 4),
            })?;
            let n_sect = *b.get(e + 5).ok_or_else(|| MachoReparseError {
                message: format!("truncated nlist n_sect at {}", e + 5),
            })?;
            let n_desc = rd_u16(b, e + 6)?;
            let n_value = rd_u64(b, e + 8)?;
            // Resolve the name from the string table (NUL-terminated).
            let name_start = stroff as usize + n_strx as usize;
            if name_start > strtab_end || name_start > b.len() {
                return err(format!(
                    "symbol {k} n_strx {n_strx} points outside the string table"
                ));
            }
            let name_end = b[name_start..strtab_end.min(b.len())]
                .iter()
                .position(|&c| c == 0)
                .map(|p| name_start + p)
                .unwrap_or(strtab_end.min(b.len()));
            let name = String::from_utf8_lossy(&b[name_start..name_end]).into_owned();
            symbols.push(ParsedSymbol {
                name,
                n_type,
                n_sect,
                n_desc,
                n_value,
            });
        }
    }

    // Per-section relocations.
    let mut section_relocs: Vec<Vec<RelocIntent>> = Vec::with_capacity(sections.len());
    for sec in &sections {
        let mut recs = Vec::with_capacity(sec.nreloc as usize);
        for j in 0..sec.nreloc as usize {
            recs.push(parse_reloc(
                b,
                sec.reloff as usize + j * RELOCATION_INFO_SIZE,
            )?);
        }
        section_relocs.push(recs);
    }

    Ok(ParsedObject {
        cputype,
        filetype,
        sections,
        symbols,
        section_relocs,
        dysymtab,
    })
}

// ---------------------------------------------------------------------------
// Structural comparison: reparsed object == intent
// ---------------------------------------------------------------------------

/// Expected `cputype` for a target.
fn expected_cputype(t: MachOTarget) -> u32 {
    match t {
        MachOTarget::X86_64 => CPU_TYPE_X86_64,
        MachOTarget::AArch64 => CPU_TYPE_ARM64,
    }
}

/// The Mach-O dysymtab-mandated final symbol order: locals (insertion order),
/// then external defined, then undefined. Reconstructed from the spec so the
/// element-wise comparison also validates the ordering the writer produced.
fn intent_symbol_order(intent: &MachoObjectIntent) -> Vec<usize> {
    let mut locals = Vec::new();
    let mut extdef = Vec::new();
    let mut undef = Vec::new();
    for (i, s) in intent.symbols.iter().enumerate() {
        if !s.is_global {
            locals.push(i);
        } else if s.section == 0 {
            undef.push(i);
        } else {
            extdef.push(i);
        }
    }
    locals.into_iter().chain(extdef).chain(undef).collect()
}

/// Compare a reparsed object against its intent. Returns the FIRST disagreement
/// as an `Err` (used for enforce mode and the mutation negative controls); a
/// faithful object returns `Ok(())`. Pure and mode-agnostic.
pub fn check_object(intent: &MachoObjectIntent, bytes: &[u8]) -> Result<(), MachoReparseError> {
    let po = parse_object(bytes)?;

    // --- Header ---
    if po.filetype != MH_OBJECT {
        return err(format!(
            "filetype {:#x} is not MH_OBJECT ({:#x})",
            po.filetype, MH_OBJECT
        ));
    }
    let want_cpu = expected_cputype(intent.target);
    if po.cputype != want_cpu {
        return err(format!(
            "cputype {:#010x} != intended {:#010x} for {:?}",
            po.cputype, want_cpu, intent.target
        ));
    }

    // --- Section count ---
    if po.sections.len() != intent.sections.len() {
        return err(format!(
            "section count {} != intended {}",
            po.sections.len(),
            intent.sections.len()
        ));
    }

    // --- Per-section: name/seg/size/align/flags/offset + BYTE content ---
    for (i, (ps, si)) in po.sections.iter().zip(intent.sections.iter()).enumerate() {
        if ps.sectname != si.sectname {
            return err(format!(
                "section {i} sectname {:?} != intended {:?}",
                String::from_utf8_lossy(&ps.sectname),
                String::from_utf8_lossy(&si.sectname)
            ));
        }
        if ps.segname != si.segname {
            return err(format!(
                "section {i} ({}) segname {:?} != intended {:?}",
                String::from_utf8_lossy(&si.sectname),
                String::from_utf8_lossy(&ps.segname),
                String::from_utf8_lossy(&si.segname)
            ));
        }
        let want_size = si.data.len() as u64;
        if ps.size != want_size {
            return err(format!(
                "section {i} ({}) size {} != intended {}",
                String::from_utf8_lossy(&si.sectname),
                ps.size,
                want_size
            ));
        }
        if ps.align != si.align {
            return err(format!(
                "section {i} ({}) align {} != intended {}",
                String::from_utf8_lossy(&si.sectname),
                ps.align,
                si.align
            ));
        }
        if ps.flags != si.flags {
            return err(format!(
                "section {i} ({}) flags {:#x} != intended {:#x}",
                String::from_utf8_lossy(&si.sectname),
                ps.flags,
                si.flags
            ));
        }
        // Offset alignment + bounds, then a full BYTE compare of the emitted
        // content against intent — this binds the header's claimed offset/size
        // to the bytes actually laid down (catches a wrong offset or a
        // scrambled data region).
        let alignment = 1u64
            .checked_shl(ps.align)
            .ok_or_else(|| MachoReparseError {
                message: format!(
                    "section {i} ({}) carries unrepresentable alignment exponent {}",
                    String::from_utf8_lossy(&si.sectname),
                    ps.align
                ),
            })?;
        let align_mask = alignment - 1;
        if ps.align > 0 && (ps.offset as u64 & align_mask) != 0 {
            return err(format!(
                "section {i} ({}) file offset {} is not {}-byte aligned",
                String::from_utf8_lossy(&si.sectname),
                ps.offset,
                alignment
            ));
        }
        let start = ps.offset as usize;
        let end = start
            .checked_add(si.data.len())
            .ok_or_else(|| MachoReparseError {
                message: format!(
                    "section {i} ({}) data range overflows host usize",
                    String::from_utf8_lossy(&si.sectname)
                ),
            })?;
        let region = bytes.get(start..end).ok_or_else(|| MachoReparseError {
            message: format!(
                "section {i} ({}) data range {start}..{end} out of bounds (len {})",
                String::from_utf8_lossy(&si.sectname),
                bytes.len()
            ),
        })?;
        if region != si.data.as_slice() {
            return err(format!(
                "section {i} ({}) emitted bytes at offset {start} do not match intended content",
                String::from_utf8_lossy(&si.sectname)
            ));
        }
        N_SECTIONS_CHECKED.fetch_add(1, Ordering::Relaxed);
    }

    // --- Symbols (element-wise in dysymtab order) ---
    if po.symbols.len() != intent.symbols.len() {
        return err(format!(
            "symbol count {} != intended {}",
            po.symbols.len(),
            intent.symbols.len()
        ));
    }
    let order = intent_symbol_order(intent);
    for (slot, &ii) in order.iter().enumerate() {
        let want = &intent.symbols[ii];
        let got = &po.symbols[slot];
        if got.name != want.name {
            return err(format!(
                "symbol slot {slot} name {:?} != intended {:?}",
                got.name, want.name
            ));
        }
        // n_type: N_EXT bit + N_UNDF/N_SECT type class.
        let want_ext = want.is_global;
        let got_ext = got.n_type & N_EXT != 0;
        if got_ext != want_ext {
            return err(format!(
                "symbol {:?} N_EXT {} != intended {}",
                want.name, got_ext, want_ext
            ));
        }
        let want_type = if want.section == 0 { N_UNDF } else { N_SECT };
        if got.n_type & N_TYPE_MASK != want_type {
            return err(format!(
                "symbol {:?} n_type class {:#x} != intended {:#x}",
                want.name,
                got.n_type & N_TYPE_MASK,
                want_type
            ));
        }
        if got.n_sect != want.section {
            return err(format!(
                "symbol {:?} n_sect {} != intended section {}",
                want.name, got.n_sect, want.section
            ));
        }
        // n_desc weak flag.
        let want_desc: u16 = if !want.is_weak {
            0
        } else if want.section == 0 {
            N_WEAK_REF
        } else {
            N_WEAK_DEF
        };
        if got.n_desc != want_desc {
            return err(format!(
                "symbol {:?} n_desc {:#x} != intended {:#x} (weak flags)",
                want.name, got.n_desc, want_desc
            ));
        }
        // n_value: for a defined symbol, the section's reparsed base vaddr plus
        // the intended offset; for undefined, zero. Using the reparsed section
        // `addr` cross-checks the writer's symbol-address computation against the
        // section table it also emitted.
        let want_value = if want.section == 0 {
            0
        } else {
            let sec_idx = (want.section - 1) as usize;
            let base = po
                .sections
                .get(sec_idx)
                .ok_or_else(|| MachoReparseError {
                    message: format!(
                        "symbol {:?} references section ordinal {} but only {} section(s) exist",
                        want.name,
                        want.section,
                        po.sections.len()
                    ),
                })?
                .addr;
            base.checked_add(want.value)
                .ok_or_else(|| MachoReparseError {
                    message: format!(
                        "symbol {:?} value overflows its section base address",
                        want.name
                    ),
                })?
        };
        if got.n_value != want_value {
            return err(format!(
                "symbol {:?} n_value {:#x} != intended {:#x}",
                want.name, got.n_value, want_value
            ));
        }
        N_SYMBOLS_CHECKED.fetch_add(1, Ordering::Relaxed);
    }

    // --- DYSYMTAB partition counts (must match the intended partition) ---
    if let Some((nlocal, nextdef, nundef)) = po.dysymtab {
        let (mut wl, mut we, mut wu) = (0u32, 0u32, 0u32);
        for s in &intent.symbols {
            if !s.is_global {
                wl += 1;
            } else if s.section == 0 {
                wu += 1;
            } else {
                we += 1;
            }
        }
        if (nlocal, nextdef, nundef) != (wl, we, wu) {
            return err(format!(
                "dysymtab partition (local {nlocal}, extdef {nextdef}, undef {nundef}) != \
                 intended (local {wl}, extdef {we}, undef {wu})"
            ));
        }
    } else if !intent.symbols.is_empty() {
        return err("object has symbols but no LC_DYSYMTAB was emitted".to_string());
    }

    // --- Relocations (per section, in emission order) ---
    for (i, (recs, want)) in po
        .section_relocs
        .iter()
        .zip(intent.section_relocs.iter())
        .enumerate()
    {
        if recs.len() != want.len() {
            return err(format!(
                "section {i} relocation count {} != intended {}",
                recs.len(),
                want.len()
            ));
        }
        for (j, (got, wr)) in recs.iter().zip(want.iter()).enumerate() {
            if got != wr {
                return err(format!(
                    "section {i} relocation {j}: reparsed {got:?} != intended {wr:?}"
                ));
            }
            N_RELOCS_CHECKED.fetch_add(1, Ordering::Relaxed);
        }
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// Gate driver (Off / Warn / Enforce) + telemetry
// ---------------------------------------------------------------------------

/// Run the reparse gate over one emitted object. Returns `Err` ONLY in
/// [`MachoReparseMode::Enforce`] on a disagreement; in [`MachoReparseMode::Warn`]
/// it logs the disagreement loudly (P0 evidence of a live writer bug) and
/// returns `Ok`. Off is a no-op.
pub fn run_macho_reparse_gate(
    intent: &MachoObjectIntent,
    bytes: &[u8],
    mode: MachoReparseMode,
) -> Result<(), MachoReparseError> {
    if mode == MachoReparseMode::Off {
        return Ok(());
    }
    let trace = macho_reparse_trace_enabled();
    N_OBJECTS_CHECKED.fetch_add(1, Ordering::Relaxed);
    match check_object(intent, bytes) {
        Ok(()) => {
            N_OBJECTS_MATCHED.fetch_add(1, Ordering::Relaxed);
            if trace {
                let c = macho_reparse_counters();
                eprintln!(
                    "macho-reparse OK [{:?}] {} bytes, {} sections, {} symbols \
                     (totals: objects={} sections={} symbols={} relocs={})",
                    intent.target,
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
                MachoReparseMode::Warn => {
                    eprintln!("macho-reparse WARN (P0 candidate): {e}");
                    Ok(())
                }
                MachoReparseMode::Enforce => Err(e),
                MachoReparseMode::Off => unreachable!(),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::macho::reloc::Relocation;
    use crate::macho::writer::{MachOTarget, MachOWriter};
    use crate::macho::x86_64_reloc::X86_64Relocation;

    // A representative x86-64 object: two sections, local + global + undefined
    // symbols, and a branch relocation.
    fn build_x86_writer() -> MachOWriter {
        let mut w = MachOWriter::for_target(MachOTarget::X86_64);
        // __text: a couple of RET/NOP bytes.
        w.add_text_section(&[0x90, 0x90, 0xC3, 0x55, 0x5D, 0xC3]);
        // __data: 8 bytes.
        w.add_data_section(&[1, 2, 3, 4, 5, 6, 7, 8]);
        w.add_symbol("_main", 1, 0, true).unwrap(); // global defined @ __text+0
        w.add_symbol("_helper", 1, 3, false).unwrap(); // local defined @ __text+3
        w.add_symbol("_g", 2, 0, true).unwrap(); // global defined @ __data+0
        w.add_symbol("_ext", 0, 0, true).unwrap(); // undefined external
        // Branch reloc at offset 2 referencing symbol index 3 (final order).
        w.add_x86_64_relocation(0, X86_64Relocation::branch(2, 3))
            .unwrap();
        w
    }

    fn build_aarch64_writer() -> MachOWriter {
        let mut w = MachOWriter::new(); // AArch64 default
        w.add_text_section(&[0x00, 0x00, 0x80, 0xD2, 0xC0, 0x03, 0x5F, 0xD6]);
        w.add_symbol("_start", 1, 0, true).unwrap();
        w.add_weak_symbol("_wextern", 0, 0, true).unwrap(); // weak undefined
        w.add_relocation(0, Relocation::branch26(0, 1)).unwrap();
        w
    }

    #[test]
    fn positive_x86_object_passes() {
        let w = build_x86_writer();
        let bytes = w.write().unwrap();
        let intent = w.reparse_object_intent().unwrap();
        assert!(
            check_object(&intent, &bytes).is_ok(),
            "a faithful x86 object must pass the reparse gate"
        );
    }

    #[test]
    fn positive_aarch64_object_passes() {
        let w = build_aarch64_writer();
        let bytes = w.write().unwrap();
        let intent = w.reparse_object_intent().unwrap();
        assert!(
            check_object(&intent, &bytes).is_ok(),
            "a faithful aarch64 object must pass the reparse gate"
        );
    }

    // Refutation 1: flip a section SIZE field in the emitted section header.
    #[test]
    fn refutation_corrupt_section_size_fails_closed() {
        let w = build_x86_writer();
        let mut bytes = w.write().unwrap();
        let intent = w.reparse_object_intent().unwrap();
        // section_64[0].size is at: header(32) + segment_base(72) + 32.
        let size_off = MACH_HEADER_64_SIZE + SEGMENT_COMMAND_64_BASE + 32;
        bytes[size_off] ^= 0xFF; // corrupt low byte of __text size
        assert!(
            check_object(&intent, &bytes).is_err(),
            "a corrupted section size must be rejected"
        );
    }

    #[test]
    fn refutation_unrepresentable_section_alignment_returns_error_without_panicking() {
        let w = build_x86_writer();
        let mut bytes = w.write().unwrap();
        let intent = w.reparse_object_intent().unwrap();
        // section_64[0].align is at header(32) + segment_base(72) + 52.
        let align_off = MACH_HEADER_64_SIZE + SEGMENT_COMMAND_64_BASE + 52;
        bytes[align_off..align_off + 4].copy_from_slice(&64u32.to_le_bytes());
        assert!(check_object(&intent, &bytes).is_err());
    }

    // Refutation 2: flip a relocation r_address (offset) in the reloc record.
    #[test]
    fn refutation_corrupt_reloc_offset_fails_closed() {
        let w = build_x86_writer();
        let mut bytes = w.write().unwrap();
        let intent = w.reparse_object_intent().unwrap();
        let po = parse_object(&bytes).expect("parse");
        let reloff = po.sections[0].reloff as usize;
        assert!(po.sections[0].nreloc >= 1);
        bytes[reloff] ^= 0xFF; // corrupt r_address low byte of reloc 0
        assert!(
            check_object(&intent, &bytes).is_err(),
            "a corrupted relocation offset must be rejected"
        );
    }

    // Refutation 3: flip a symbol n_value in an nlist entry.
    #[test]
    fn refutation_corrupt_symbol_value_fails_closed() {
        let w = build_x86_writer();
        let mut bytes = w.write().unwrap();
        let intent = w.reparse_object_intent().unwrap();
        // Locate LC_SYMTAB symoff by an independent walk, then corrupt slot 0's
        // n_value (a local defined symbol here); n_value is at nlist offset +8.
        let symoff = symtab_offset(&bytes).expect("symtab offset");
        bytes[symoff + 8] ^= 0xFF;
        assert!(
            check_object(&intent, &bytes).is_err(),
            "a corrupted symbol value must be rejected"
        );
    }

    // Refutation 4: corrupt a section's content byte (data region).
    #[test]
    fn refutation_corrupt_section_data_fails_closed() {
        let w = build_x86_writer();
        let mut bytes = w.write().unwrap();
        let intent = w.reparse_object_intent().unwrap();
        let po = parse_object(&bytes).expect("parse");
        let off = po.sections[0].offset as usize;
        bytes[off] ^= 0xFF; // corrupt first code byte
        assert!(
            check_object(&intent, &bytes).is_err(),
            "corrupted section content must be rejected"
        );
    }

    // Helper: find the LC_SYMTAB symoff by an independent walk (test-only).
    fn symtab_offset(b: &[u8]) -> Option<usize> {
        let ncmds = rd_u32(b, 16).ok()?;
        let mut lc = MACH_HEADER_64_SIZE;
        for _ in 0..ncmds {
            let cmd = rd_u32(b, lc).ok()?;
            let cmdsize = rd_u32(b, lc + 4).ok()? as usize;
            if cmd == LC_SYMTAB {
                return Some(rd_u32(b, lc + 8).ok()? as usize);
            }
            lc += cmdsize;
        }
        None
    }

    #[test]
    fn empty_object_is_consistent() {
        let w = MachOWriter::for_target(MachOTarget::X86_64);
        let bytes = w.write().unwrap();
        let intent = w.reparse_object_intent().unwrap();
        assert!(check_object(&intent, &bytes).is_ok());
    }

    // Overhead measurement (run explicitly:
    //   TRUST_CG_RUN_MEASUREMENT_TESTS=1 cargo test -p trust-cg-codegen \
    //     --lib --release reparse::tests::bench -- --nocapture
    // ). Reports the reparse-gate cost relative to producing the object bytes.
    #[test]
    fn bench_reparse_overhead() {
        if !matches!(
            std::env::var("TRUST_CG_RUN_MEASUREMENT_TESTS").as_deref(),
            Ok("1")
        ) {
            eprintln!(
                "measurement campaign not requested; \
                 set TRUST_CG_RUN_MEASUREMENT_TESTS=1 to run"
            );
            return;
        }

        use std::time::Instant;
        // A realistic-scale object: 64 KiB __text, 8 KiB __data, 400 symbols,
        // 300 relocations.
        let mut w = MachOWriter::for_target(MachOTarget::X86_64);
        let text: Vec<u8> = (0..65536u32).map(|i| (i * 7) as u8).collect();
        let data: Vec<u8> = (0..8192u32).map(|i| (i * 3) as u8).collect();
        w.add_text_section(&text);
        w.add_data_section(&data);
        for i in 0..200u32 {
            w.add_symbol(&format!("_f{i}"), 1, (i as u64) * 16, true)
                .unwrap();
            w.add_symbol(&format!("_l{i}"), 1, (i as u64) * 16 + 8, false)
                .unwrap();
        }
        for i in 0..300u32 {
            w.add_x86_64_relocation(0, X86_64Relocation::branch(i * 4, i % 400))
                .unwrap();
        }
        let bytes = w.write().unwrap();
        let intent = w.reparse_object_intent().unwrap();
        let n = 2000;
        // Gate cost.
        let t0 = Instant::now();
        for _ in 0..n {
            check_object(&intent, &bytes).unwrap();
        }
        let t_gate = t0.elapsed();
        // Object production cost (serialize + intent-build + gate — the whole
        // write()). Subtracting the gate isolates pure serialization.
        let t1 = Instant::now();
        for _ in 0..n {
            let b = w.write().unwrap();
            std::hint::black_box(&b);
        }
        let t_write = t1.elapsed();
        let gate_ns = t_gate.as_nanos() as f64 / n as f64;
        let write_ns = t_write.as_nanos() as f64 / n as f64;
        let serialize_ns = (write_ns - gate_ns).max(1.0);
        eprintln!(
            "macho-reparse bench: object={} bytes | gate={:.1} us/obj | write(incl gate)={:.1} \
             us/obj | serialize~={:.1} us/obj | gate/serialize = {:.2}%",
            bytes.len(),
            gate_ns / 1000.0,
            write_ns / 1000.0,
            serialize_ns / 1000.0,
            gate_ns / serialize_ns * 100.0,
        );
    }
}
