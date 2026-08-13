// trust-cg-codegen/macho/fixup.rs - Fixup layer for late relocation encoding
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The fixup layer sits between instruction encoding and relocation emission.
// During instruction encoding, fixups are recorded with placeholder values.
// After final layout (when section offsets are known), fixups are resolved
// into relocations and the instruction bytes are patched.

//! Fixup layer for deferred relocation resolution.
//!
//! When instructions are encoded, branch targets and address references may not
//! have their final values yet (e.g., forward references to labels, cross-section
//! references). The fixup layer records these unresolved references as [`Fixup`]
//! entries. After layout assigns final addresses, fixups are resolved: the
//! instruction bytes are patched with computed values, and [`Relocation`] entries
//! are generated for the linker.

use super::reloc::{AArch64RelocKind, Relocation};
use thiserror::Error;
use trust_cg_ir::TlsModel;

/// Error type for fixup resolution.
///
/// Fixup resolution depends on the user-supplied symbol table (via
/// `resolve_named_symbols` lookup callback) and on the required call order
/// (`resolve_named_symbols` before `resolve_to_relocations`). Both failure
/// modes reflect external input / API misuse at a boundary and must surface
/// to callers as recoverable errors rather than crashing the pipeline.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum FixupError {
    /// A `NamedSymbol` fixup target could not be resolved to a symbol-table
    /// index by the caller-provided lookup function.
    #[error("unresolved symbol in fixup: '{name}'")]
    UnresolvedSymbol {
        /// The symbol name that was not found by the lookup callback.
        name: String,
    },

    /// `resolve_to_relocations` was called while at least one `NamedSymbol`
    /// fixup remained in the list. Callers must invoke
    /// [`FixupList::resolve_named_symbols`] first.
    #[error(
        "unresolved named symbol in fixup at offset {offset:#x}: '{name}'. \
         Call resolve_named_symbols() before resolve_to_relocations()."
    )]
    UnresolvedNamedSymbolAtOffset {
        /// Byte offset within the section where the fixup applies.
        offset: u32,
        /// The unresolved symbol name still present in the fixup list.
        name: String,
    },

    /// Mach-O's non-scattered `relocation_info.r_address` is a signed i32.
    /// Setting bit 31 changes the record interpretation to a scattered
    /// relocation, so an apparently valid `u32` section offset above
    /// `i32::MAX` must never be serialized as an ordinary relocation.
    #[error("Mach-O relocation offset {offset:#x} exceeds the non-scattered signed-i32 range")]
    RelocationAddressOutOfRange {
        /// Byte offset within the section where the fixup applies.
        offset: u32,
    },

    /// FINDING #7: an `ARM64_RELOC_ADDEND` addend does not fit in the signed
    /// 24-bit field (`symbol_index`) it is packed into. Previously the addend
    /// was silently truncated by `& 0x00FF_FFFF`, encoding a *different*
    /// (wrong) addend and defeating the downstream `encode_relocation` assert.
    /// The addend must be representable both as `i32` and within
    /// `[-(1<<23), (1<<23))`.
    #[error(
        "ARM64_RELOC_ADDEND addend {addend} at offset {offset:#x} is out of \
         signed 24-bit range [-8388608, 8388607]"
    )]
    AddendOutOfRange {
        /// Byte offset within the section where the fixup applies.
        offset: u32,
        /// The out-of-range addend value.
        addend: i64,
    },

    /// An ELF-only fixup kind (`ElfTlsleAddTprelHi12` / `ElfTlsleAddTprelLo12Nc` /
    /// `ElfTlsieAdrGottprelPage21` / `ElfTlsieLd64GottprelLo12Nc`)
    /// reached Mach-O relocation conversion. These kinds have no Mach-O
    /// `relocation_info` r_type (their discriminants are outside 0..=11) and
    /// may only be consumed by the ELF emitter's `aarch64_elf_reloc_kind`
    /// mapping; converting one here would serialize a malformed/foreign
    /// r_type. Fail closed instead.
    #[error(
        "ELF-only fixup kind {kind:?} at offset {offset:#x} cannot be emitted          as a Mach-O relocation (ELF TLS local-exec/initial-exec fixups are only          valid for ELF object emission)"
    )]
    ElfOnlyFixupKind {
        /// The ELF-only relocation kind that reached Mach-O conversion.
        kind: AArch64RelocKind,
        /// Byte offset within the section where the fixup applies.
        offset: u32,
    },

    /// FINDING #10b: a standalone `apply_*` relocation patch was given an
    /// out-of-range or misaligned offset. Previously these conditions tripped
    /// release-active `assert!`s that aborted the process; they now surface as
    /// a recoverable error, mirroring `LinkerError::RelocationOverflow`.
    #[error("relocation out of range: {detail}")]
    RelocationOverflow {
        /// Human-readable description of the overflow / misalignment.
        detail: String,
    },
}

/// The target of a fixup — what the fixup points at.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FixupTarget {
    /// A named symbol (index into the symbol table).
    /// This generates an external relocation (r_extern=1).
    Symbol(u32),

    /// A section-relative offset. The `u32` is the section ordinal (1-based).
    /// Used for local references within or between sections.
    /// This generates a local relocation (r_extern=0).
    Section(u32),

    /// An expression: symbol + section offset.
    /// Used when we know both the symbol and want to add a section-relative
    /// adjustment (e.g., for .got stubs).
    SymbolPlusOffset {
        symbol_index: u32,
        section_offset: u64,
    },

    /// A named symbol reference (resolved to a symbol index during module emission).
    /// Used when encoding cross-function BL/B instructions before the symbol
    /// table is built. The module-level emitter resolves this to a `Symbol(u32)`
    /// after all functions have been laid out and symbols assigned indices.
    NamedSymbol(String),
}

/// A pending fixup that will be resolved after layout.
///
/// Fixups are created during instruction encoding when the final value is not
/// yet known. Each fixup records:
/// - Where in the section to apply the fix (`offset`)
/// - What kind of relocation it needs (`kind`)
/// - Optional TLS model provenance (`tls_model`)
/// - What it points at (`target`)
/// - An optional constant addend (`addend`)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Fixup {
    /// Byte offset within the containing section where the fixup applies.
    /// This is the same as `relocation_info.r_address`.
    pub offset: u32,

    /// The ARM64 relocation kind. Determines how the value is encoded into
    /// the instruction and what relocation type is emitted.
    pub kind: AArch64RelocKind,

    /// TLS model provenance for TLS fixups.
    ///
    /// Mach-O relocation records do not encode this separately; it is a
    /// pipeline-side guardrail for non-Mach-O emission so ELF/COFF paths do not
    /// infer a TLS relocation model from Darwin TLVP relocation kinds.
    pub tls_model: Option<TlsModel>,

    /// What this fixup points at — a symbol, section, or expression.
    pub target: FixupTarget,

    /// Constant addend. For most instruction-embedded relocations this is 0.
    /// Non-zero addends on Branch26/Page21/Pageoff12 require an
    /// `ARM64_RELOC_ADDEND` relocation pair.
    pub addend: i64,
}

impl Fixup {
    /// Create a fixup for a branch instruction (B/BL) targeting a symbol.
    pub fn branch(offset: u32, symbol_index: u32) -> Self {
        Self {
            offset,
            kind: AArch64RelocKind::Branch26,
            tls_model: None,
            target: FixupTarget::Symbol(symbol_index),
            addend: 0,
        }
    }

    /// Create a fixup for a branch instruction (B/BL) targeting a named symbol.
    ///
    /// Used during instruction encoding when the symbol table index is not yet
    /// known. The module-level emitter resolves the name to an index.
    pub fn branch_sym(offset: u32, symbol_name: String) -> Self {
        Self {
            offset,
            kind: AArch64RelocKind::Branch26,
            tls_model: None,
            target: FixupTarget::NamedSymbol(symbol_name),
            addend: 0,
        }
    }

    /// Create a fixup for an ADRP instruction targeting a symbol's page.
    pub fn adrp(offset: u32, symbol_index: u32) -> Self {
        Self {
            offset,
            kind: AArch64RelocKind::Page21,
            tls_model: None,
            target: FixupTarget::Symbol(symbol_index),
            addend: 0,
        }
    }

    /// Create a fixup for an ADD/LDR page offset targeting a symbol.
    pub fn pageoff(offset: u32, symbol_index: u32) -> Self {
        Self {
            offset,
            kind: AArch64RelocKind::Pageoff12,
            tls_model: None,
            target: FixupTarget::Symbol(symbol_index),
            addend: 0,
        }
    }

    /// Create a fixup for an ADRP to a GOT entry.
    pub fn got_adrp(offset: u32, symbol_index: u32) -> Self {
        Self {
            offset,
            kind: AArch64RelocKind::GotLoadPage21,
            tls_model: None,
            target: FixupTarget::Symbol(symbol_index),
            addend: 0,
        }
    }

    /// Create a fixup for an LDR GOT page offset.
    pub fn got_ldr(offset: u32, symbol_index: u32) -> Self {
        Self {
            offset,
            kind: AArch64RelocKind::GotLoadPageoff12,
            tls_model: None,
            target: FixupTarget::Symbol(symbol_index),
            addend: 0,
        }
    }

    /// Create a fixup for an ADRP to a TLV descriptor.
    pub fn tlvp_adrp(offset: u32, symbol_index: u32) -> Self {
        Self {
            offset,
            kind: AArch64RelocKind::TlvpLoadPage21,
            tls_model: Some(TlsModel::Tlv),
            target: FixupTarget::Symbol(symbol_index),
            addend: 0,
        }
    }

    /// Create a fixup for an LDR TLV descriptor page offset.
    pub fn tlvp_ldr(offset: u32, symbol_index: u32) -> Self {
        Self {
            offset,
            kind: AArch64RelocKind::TlvpLoadPageoff12,
            tls_model: Some(TlsModel::Tlv),
            target: FixupTarget::Symbol(symbol_index),
            addend: 0,
        }
    }

    /// Create a fixup for a 64-bit absolute pointer.
    pub fn pointer(offset: u32, symbol_index: u32) -> Self {
        Self {
            offset,
            kind: AArch64RelocKind::Unsigned,
            tls_model: None,
            target: FixupTarget::Symbol(symbol_index),
            addend: 0,
        }
    }

    /// Create a fixup with an addend.
    pub fn with_addend(mut self, addend: i64) -> Self {
        self.addend = addend;
        self
    }

    /// Returns true if this fixup has a non-zero addend that requires an
    /// `ARM64_RELOC_ADDEND` relocation pair.
    pub fn needs_addend_reloc(&self) -> bool {
        self.addend != 0
            && matches!(
                self.kind,
                AArch64RelocKind::Branch26 | AArch64RelocKind::Page21 | AArch64RelocKind::Pageoff12
            )
    }
}

/// A collection of fixups for a single section.
///
/// During instruction encoding, fixups are accumulated here. After layout,
/// [`resolve_fixups`] converts them to relocations and patches the instruction
/// bytes.
#[derive(Debug, Clone, Default)]
pub struct FixupList {
    fixups: Vec<Fixup>,
}

impl FixupList {
    /// Create an empty fixup list.
    pub fn new() -> Self {
        Self { fixups: Vec::new() }
    }

    /// Add a fixup to the list.
    pub fn push(&mut self, fixup: Fixup) {
        self.fixups.push(fixup);
    }

    /// Number of fixups in the list.
    pub fn len(&self) -> usize {
        self.fixups.len()
    }

    /// Whether the list is empty.
    pub fn is_empty(&self) -> bool {
        self.fixups.is_empty()
    }

    /// Iterate over fixups.
    pub fn iter(&self) -> impl Iterator<Item = &Fixup> {
        self.fixups.iter()
    }

    /// Mutable slice view of the fixup list.
    ///
    /// Used by the JIT block-splice path (issue #364) to shift each fixup's
    /// byte offset when trampolines are inserted before basic blocks. Kept
    /// narrower than a general-purpose `iter_mut` so callers cannot add or
    /// remove fixups through this accessor; use [`Self::push`] for that.
    pub fn as_mut_slice(&mut self) -> &mut [Fixup] {
        &mut self.fixups
    }

    /// Get a fixup by index.
    pub fn get(&self, index: usize) -> Option<&Fixup> {
        self.fixups.get(index)
    }

    /// Resolve named symbol fixups to numeric indices.
    ///
    /// Takes a lookup function that maps symbol names to symbol table indices.
    /// All `NamedSymbol` targets are replaced with `Symbol(index)`.
    ///
    /// # Errors
    /// Returns [`FixupError::UnresolvedSymbol`] if the lookup callback returns
    /// `None` for any `NamedSymbol`. The list is left partially mutated: any
    /// fixups that were resolved before the failing one are already updated.
    /// Callers should treat this as a hard module-emission error.
    pub fn resolve_named_symbols<F>(&mut self, lookup: F) -> Result<(), FixupError>
    where
        F: Fn(&str) -> Option<u32>,
    {
        for fixup in &mut self.fixups {
            if let FixupTarget::NamedSymbol(ref name) = fixup.target {
                let index = lookup(name)
                    .ok_or_else(|| FixupError::UnresolvedSymbol { name: name.clone() })?;
                fixup.target = FixupTarget::Symbol(index);
            }
        }
        Ok(())
    }

    /// Resolve all fixups into relocations.
    ///
    /// This converts each fixup into one or more `Relocation` entries suitable
    /// for writing into the Mach-O relocation table. Fixups with non-zero
    /// addends on Branch26/Page21/Pageoff12 produce an additional
    /// `ARM64_RELOC_ADDEND` relocation.
    ///
    /// Note: this does NOT patch the instruction bytes. The caller is responsible
    /// for applying fixup values to the section data based on final layout.
    /// The relocations tell the linker what adjustments are needed at link time.
    ///
    /// # Errors
    /// Returns [`FixupError::UnresolvedNamedSymbolAtOffset`] if any
    /// `NamedSymbol` fixup targets remain unresolved. Call
    /// [`resolve_named_symbols`](Self::resolve_named_symbols) first.
    pub fn resolve_to_relocations(&self) -> Result<Vec<Relocation>, FixupError> {
        // At most two records are emitted per fixup. Avoid multiplying an
        // attacker-influenced count before validation; Vec growth remains
        // fallible at the allocator boundary without integer wraparound here.
        let mut relocs = Vec::new();

        for fixup in &self.fixups {
            if fixup.offset > i32::MAX as u32 {
                return Err(FixupError::RelocationAddressOutOfRange {
                    offset: fixup.offset,
                });
            }
            // ELF-only kinds (discriminants outside the Mach-O r_type range
            // 0..=11) must never serialize into Mach-O relocation records.
            if matches!(
                fixup.kind,
                AArch64RelocKind::ElfTlsleAddTprelHi12
                    | AArch64RelocKind::ElfTlsleAddTprelLo12Nc
                    | AArch64RelocKind::ElfTlsieAdrGottprelPage21
                    | AArch64RelocKind::ElfTlsieLd64GottprelLo12Nc
            ) {
                return Err(FixupError::ElfOnlyFixupKind {
                    kind: fixup.kind,
                    offset: fixup.offset,
                });
            }
            let (symbol_index, is_extern) = match &fixup.target {
                FixupTarget::Symbol(idx) => (*idx, true),
                FixupTarget::Section(ordinal) => (*ordinal, false),
                FixupTarget::SymbolPlusOffset { symbol_index, .. } => (*symbol_index, true),
                FixupTarget::NamedSymbol(name) => {
                    return Err(FixupError::UnresolvedNamedSymbolAtOffset {
                        offset: fixup.offset,
                        name: name.clone(),
                    });
                }
            };

            // Emit addend relocation first if needed
            // Per Mach-O ABI: ARM64_RELOC_ADDEND must precede the main relocation
            if fixup.needs_addend_reloc() {
                // FINDING #7: the addend is packed into the 24-bit `symbol_index`
                // field as `(addend as i32 as u32) & 0x00FF_FFFF`. Range-check
                // BEFORE packing — the addend must fit in i32 (it is cast `as i32`
                // first) AND in the signed 24-bit field; otherwise the mask would
                // silently encode a *different* addend (defeating the downstream
                // encode_relocation assert).
                let addend = fixup.addend;
                const ADDEND_MIN: i64 = -(1 << 23);
                const ADDEND_MAX: i64 = (1 << 23) - 1;
                if addend < i64::from(i32::MIN)
                    || addend > i64::from(i32::MAX)
                    || !(ADDEND_MIN..=ADDEND_MAX).contains(&addend)
                {
                    return Err(FixupError::AddendOutOfRange {
                        offset: fixup.offset,
                        addend,
                    });
                }
                let addend_i32 = addend as i32;
                relocs.push(Relocation {
                    offset: fixup.offset,
                    symbol_index: (addend_i32 as u32) & 0x00FF_FFFF,
                    kind: AArch64RelocKind::Addend,
                    pc_relative: false,
                    length: 2,
                    is_extern: false,
                });
            }

            relocs.push(Relocation {
                offset: fixup.offset,
                symbol_index,
                kind: fixup.kind,
                pc_relative: fixup.kind.is_pc_relative(),
                length: fixup.kind.default_log2_size(),
                is_extern,
            });
        }

        Ok(relocs)
    }
}

/// Apply a Branch26 fixup value to instruction bytes.
///
/// The Branch26 value is a signed 26-bit word offset (byte offset >> 2).
/// It occupies bits [25:0] of the B/BL instruction encoding.
///
/// # Arguments
/// - `insn_bytes`: Mutable slice of 4 instruction bytes (little-endian).
/// - `byte_offset`: Signed byte offset from the instruction to the target.
///
/// # Errors
/// FINDING #10b: returns [`FixupError::RelocationOverflow`] if the offset is
/// not 4-byte aligned or exceeds +/-128 MB. Previously these conditions tripped
/// release-active `assert!`s that aborted the process; they now surface as a
/// recoverable error mirroring `LinkerError::RelocationOverflow`.
pub fn apply_branch26(insn_bytes: &mut [u8; 4], byte_offset: i64) -> Result<(), FixupError> {
    if byte_offset & 3 != 0 {
        return Err(FixupError::RelocationOverflow {
            detail: format!("Branch26 offset must be 4-byte aligned, got {byte_offset}"),
        });
    }

    let word_offset = byte_offset >> 2;
    if !(-(1 << 25)..(1 << 25)).contains(&word_offset) {
        return Err(FixupError::RelocationOverflow {
            detail: format!(
                "Branch26 offset out of range: {word_offset} words ({byte_offset} bytes)"
            ),
        });
    }

    let imm26 = (word_offset as u32) & 0x03FF_FFFF;
    let insn = u32::from_le_bytes(*insn_bytes);
    let patched = (insn & 0xFC00_0000) | imm26;
    *insn_bytes = patched.to_le_bytes();
    Ok(())
}

/// Apply a Page21 fixup value to ADRP instruction bytes.
///
/// The ADRP instruction encodes a 21-bit signed page offset as:
/// - `immhi` = bits [23:5] of the instruction (19 bits)
/// - `immlo` = bits [30:29] of the instruction (2 bits)
/// - Full value = `(immhi << 2) | immlo`, sign-extended from 21 bits
///
/// # Arguments
/// - `insn_bytes`: Mutable slice of 4 instruction bytes (little-endian).
/// - `page_offset`: Signed page offset (number of 4KB pages).
///
/// # Errors
/// FINDING #10b: returns [`FixupError::RelocationOverflow`] if the page offset
/// exceeds +/-4 GB (21-bit signed range). Previously a release-active `assert!`
/// aborted the process; it now surfaces as a recoverable error.
pub fn apply_page21(insn_bytes: &mut [u8; 4], page_offset: i64) -> Result<(), FixupError> {
    if !(-(1 << 20)..(1 << 20)).contains(&page_offset) {
        return Err(FixupError::RelocationOverflow {
            detail: format!("Page21 offset out of range: {page_offset} pages"),
        });
    }

    let imm21 = (page_offset as u32) & 0x001F_FFFF;
    let immlo = imm21 & 0x3;
    let immhi = (imm21 >> 2) & 0x7_FFFF;

    let insn = u32::from_le_bytes(*insn_bytes);
    let patched = (insn & 0x9F00_001F) | (immlo << 29) | (immhi << 5);
    *insn_bytes = patched.to_le_bytes();
    Ok(())
}

/// Apply a Pageoff12 fixup value to ADD/LDR instruction bytes.
///
/// The 12-bit page offset is stored in bits [21:10] of the instruction.
/// For LDR instructions, the offset may be scaled by the access size.
///
/// # Arguments
/// - `insn_bytes`: Mutable slice of 4 instruction bytes (little-endian).
/// - `page_offset`: 12-bit unsigned offset within a 4KB page.
/// - `shift`: Scale factor (log2 of access size, 0 for ADD, 2 for LDR W, 3 for LDR X).
///
/// # Panics
/// Panics if the offset exceeds 12 bits or is not aligned to the shift.
pub fn apply_pageoff12(insn_bytes: &mut [u8; 4], page_offset: u32, shift: u8) {
    assert!(
        page_offset < 4096,
        "Pageoff12 value must be < 4096, got {}",
        page_offset
    );

    let scaled_offset = if shift > 0 {
        assert!(
            page_offset & ((1 << shift) - 1) == 0,
            "Pageoff12 value {} not aligned to {} bytes",
            page_offset,
            1 << shift
        );
        page_offset >> shift
    } else {
        page_offset
    };

    assert!(
        scaled_offset < (1 << 12),
        "Scaled pageoff12 value {} exceeds 12-bit field",
        scaled_offset
    );

    let insn = u32::from_le_bytes(*insn_bytes);
    let patched = (insn & 0xFFC0_03FF) | ((scaled_offset & 0xFFF) << 10);
    *insn_bytes = patched.to_le_bytes();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fixup_branch() {
        let fixup = Fixup::branch(0x10, 5);
        assert_eq!(fixup.offset, 0x10);
        assert_eq!(fixup.kind, AArch64RelocKind::Branch26);
        assert_eq!(fixup.target, FixupTarget::Symbol(5));
        assert_eq!(fixup.addend, 0);
        assert!(!fixup.needs_addend_reloc());
    }

    #[test]
    fn test_fixup_with_addend() {
        let fixup = Fixup::branch(0x10, 5).with_addend(0x100);
        assert_eq!(fixup.addend, 0x100);
        assert!(fixup.needs_addend_reloc());
    }

    #[test]
    fn test_fixup_adrp_pageoff_pair() {
        let adrp = Fixup::adrp(0x00, 3);
        let add = Fixup::pageoff(0x04, 3);

        assert_eq!(adrp.kind, AArch64RelocKind::Page21);
        assert_eq!(add.kind, AArch64RelocKind::Pageoff12);
    }

    #[test]
    fn test_fixup_got_pair() {
        let got_adrp = Fixup::got_adrp(0x00, 7);
        let got_ldr = Fixup::got_ldr(0x04, 7);

        assert_eq!(got_adrp.kind, AArch64RelocKind::GotLoadPage21);
        assert_eq!(got_ldr.kind, AArch64RelocKind::GotLoadPageoff12);
    }

    #[test]
    fn test_fixup_tlvp_pair() {
        let tlvp_adrp = Fixup::tlvp_adrp(0x00, 9);
        let tlvp_ldr = Fixup::tlvp_ldr(0x04, 9);

        assert_eq!(tlvp_adrp.kind, AArch64RelocKind::TlvpLoadPage21);
        assert_eq!(tlvp_ldr.kind, AArch64RelocKind::TlvpLoadPageoff12);
        assert_eq!(tlvp_adrp.tls_model, Some(TlsModel::Tlv));
        assert_eq!(tlvp_ldr.tls_model, Some(TlsModel::Tlv));
        assert_eq!(tlvp_adrp.target, FixupTarget::Symbol(9));
        assert_eq!(tlvp_ldr.target, FixupTarget::Symbol(9));
    }

    #[test]
    fn test_fixup_list_resolve_got_pair() {
        let mut list = FixupList::new();
        list.push(Fixup::got_adrp(0x00, 5));
        list.push(Fixup::got_ldr(0x04, 5));

        let relocs = list
            .resolve_to_relocations()
            .expect("all Symbol-targeted fixups");
        assert_eq!(relocs.len(), 2);

        assert_eq!(relocs[0].kind, AArch64RelocKind::GotLoadPage21);
        assert_eq!(relocs[0].symbol_index, 5);
        assert!(relocs[0].is_extern);
        assert!(relocs[0].pc_relative);

        assert_eq!(relocs[1].kind, AArch64RelocKind::GotLoadPageoff12);
        assert_eq!(relocs[1].symbol_index, 5);
        assert!(relocs[1].is_extern);
        assert!(!relocs[1].pc_relative);
    }

    #[test]
    fn test_fixup_list_resolve_tlvp_pair() {
        let mut list = FixupList::new();
        list.push(Fixup::tlvp_adrp(0x00, 9));
        list.push(Fixup::tlvp_ldr(0x04, 9));

        let relocs = list
            .resolve_to_relocations()
            .expect("all Symbol-targeted fixups");
        assert_eq!(relocs.len(), 2);

        assert_eq!(relocs[0].kind, AArch64RelocKind::TlvpLoadPage21);
        assert_eq!(relocs[0].symbol_index, 9);
        assert!(relocs[0].is_extern);
        assert!(relocs[0].pc_relative);

        assert_eq!(relocs[1].kind, AArch64RelocKind::TlvpLoadPageoff12);
        assert_eq!(relocs[1].symbol_index, 9);
        assert!(relocs[1].is_extern);
        assert!(!relocs[1].pc_relative);
    }

    #[test]
    fn test_fixup_list_resolve() {
        let mut list = FixupList::new();
        list.push(Fixup::branch(0x00, 1));
        list.push(Fixup::adrp(0x04, 2));
        list.push(Fixup::pageoff(0x08, 2));

        let relocs = list
            .resolve_to_relocations()
            .expect("all Symbol-targeted fixups");
        assert_eq!(relocs.len(), 3);

        assert_eq!(relocs[0].kind, AArch64RelocKind::Branch26);
        assert_eq!(relocs[0].symbol_index, 1);
        assert!(relocs[0].is_extern);

        assert_eq!(relocs[1].kind, AArch64RelocKind::Page21);
        assert_eq!(relocs[1].symbol_index, 2);

        assert_eq!(relocs[2].kind, AArch64RelocKind::Pageoff12);
        assert_eq!(relocs[2].symbol_index, 2);
    }

    #[test]
    fn test_fixup_list_resolve_with_addend() {
        let mut list = FixupList::new();
        list.push(Fixup::branch(0x00, 1).with_addend(4));

        let relocs = list
            .resolve_to_relocations()
            .expect("all Symbol-targeted fixups");
        assert_eq!(relocs.len(), 2); // addend + branch26

        assert_eq!(relocs[0].kind, AArch64RelocKind::Addend);
        assert_eq!(relocs[0].symbol_index, 4); // the addend value
        assert!(!relocs[0].is_extern);

        assert_eq!(relocs[1].kind, AArch64RelocKind::Branch26);
        assert_eq!(relocs[1].symbol_index, 1);
        assert!(relocs[1].is_extern);
    }

    #[test]
    fn test_addend_out_of_range_returns_err() {
        // FINDING #7: an addend that exceeds the signed 24-bit field would be
        // silently truncated by `& 0x00FF_FFFF`, encoding a *different* addend.
        // 1<<23 (0x0080_0000) fits in i32 but is the first value out of signed
        // 24-bit range, so it must now return AddendOutOfRange.
        let mut list = FixupList::new();
        list.push(Fixup::branch(0x00, 1).with_addend(1 << 23));
        let err = list.resolve_to_relocations();
        assert!(
            matches!(
                err,
                Err(FixupError::AddendOutOfRange { addend, .. }) if addend == (1 << 23)
            ),
            "expected AddendOutOfRange, got {err:?}"
        );

        // Negative side: -(1<<23) - 1 is just below the signed-24-bit minimum.
        let mut list = FixupList::new();
        list.push(Fixup::branch(0x00, 1).with_addend(-(1 << 23) - 1));
        assert!(matches!(
            list.resolve_to_relocations(),
            Err(FixupError::AddendOutOfRange { .. })
        ));

        // A value beyond i32 range must also be rejected (it would wrap even
        // before the 24-bit mask).
        let mut list = FixupList::new();
        list.push(Fixup::branch(0x00, 1).with_addend(0x1_0000_0000));
        assert!(matches!(
            list.resolve_to_relocations(),
            Err(FixupError::AddendOutOfRange { .. })
        ));
    }

    #[test]
    fn test_addend_in_range_boundaries_still_encode() {
        // FINDING #7 boundary: the extreme in-range signed-24-bit addends must
        // still resolve and pack the identical (masked) symbol_index bits.
        let mut list = FixupList::new();
        list.push(Fixup::branch(0x00, 1).with_addend((1 << 23) - 1)); // max
        let relocs = list.resolve_to_relocations().unwrap();
        assert_eq!(relocs[0].kind, AArch64RelocKind::Addend);
        assert_eq!(relocs[0].symbol_index, ((1u32 << 23) - 1) & 0x00FF_FFFF);

        let mut list = FixupList::new();
        list.push(Fixup::branch(0x00, 1).with_addend(-(1 << 23))); // min
        let relocs = list.resolve_to_relocations().unwrap();
        assert_eq!(relocs[0].kind, AArch64RelocKind::Addend);
        assert_eq!(relocs[0].symbol_index, (-(1i32 << 23) as u32) & 0x00FF_FFFF);
    }

    #[test]
    fn test_macho_relocation_address_signed_boundary() {
        let mut boundary = FixupList::new();
        boundary.push(Fixup::branch(i32::MAX as u32, 1));
        assert_eq!(
            boundary.resolve_to_relocations().unwrap()[0].offset,
            i32::MAX as u32,
        );

        let mut scattered_bit = FixupList::new();
        scattered_bit.push(Fixup::branch(i32::MAX as u32 + 1, 1));
        assert_eq!(
            scattered_bit.resolve_to_relocations(),
            Err(FixupError::RelocationAddressOutOfRange {
                offset: i32::MAX as u32 + 1,
            }),
        );
    }

    #[test]
    fn test_fixup_list_resolve_section_relative() {
        let mut list = FixupList::new();
        list.push(Fixup {
            offset: 0x10,
            kind: AArch64RelocKind::Unsigned,
            tls_model: None,
            target: FixupTarget::Section(2), // section ordinal
            addend: 0,
        });

        let relocs = list
            .resolve_to_relocations()
            .expect("Section-targeted fixups resolve");
        assert_eq!(relocs.len(), 1);
        assert!(!relocs[0].is_extern);
        assert_eq!(relocs[0].symbol_index, 2);
    }

    #[test]
    fn test_apply_branch26_forward() {
        // BL instruction: opcode = 0x94000000
        let mut insn = 0x9400_0000_u32.to_le_bytes();
        // Branch forward 16 bytes = 4 words
        apply_branch26(&mut insn, 16).unwrap();
        let result = u32::from_le_bytes(insn);
        assert_eq!(result & 0x03FF_FFFF, 4); // imm26 = 4
        assert_eq!(result & 0xFC00_0000, 0x9400_0000); // opcode preserved
    }

    #[test]
    fn test_apply_branch26_backward() {
        // B instruction: opcode = 0x14000000
        let mut insn = 0x1400_0000_u32.to_le_bytes();
        // Branch backward 8 bytes = -2 words
        apply_branch26(&mut insn, -8).unwrap();
        let result = u32::from_le_bytes(insn);
        // -2 in 26-bit two's complement = 0x03FF_FFFE
        assert_eq!(result & 0x03FF_FFFF, 0x03FF_FFFE);
        assert_eq!(result & 0xFC00_0000, 0x1400_0000); // opcode preserved
    }

    #[test]
    fn test_apply_page21() {
        // ADRP x0, target_page: 0x90000000
        let mut insn = 0x9000_0000_u32.to_le_bytes();
        // Page offset of 1
        apply_page21(&mut insn, 1).unwrap();
        let result = u32::from_le_bytes(insn);

        // immhi = (1 >> 2) & 0x7FFFF = 0, immlo = 1 & 3 = 1
        // result should have immlo=1 at bits [30:29] and immhi=0 at bits [23:5]
        let immlo = (result >> 29) & 3;
        let immhi = (result >> 5) & 0x7_FFFF;
        assert_eq!(immlo, 1);
        assert_eq!(immhi, 0);
    }

    #[test]
    fn test_apply_page21_large() {
        let mut insn = 0x9000_0000_u32.to_le_bytes();
        // Page offset = 5 = 0b101 → immlo=01, immhi=1
        apply_page21(&mut insn, 5).unwrap();
        let result = u32::from_le_bytes(insn);

        let immlo = (result >> 29) & 3;
        let immhi = (result >> 5) & 0x7_FFFF;
        assert_eq!((immhi << 2) | immlo, 5);
    }

    #[test]
    fn test_apply_page21_boundary_max_in_range() {
        // FINDING #10b boundary: the largest in-range page offsets still encode.
        let mut insn = 0x9000_0000_u32.to_le_bytes();
        apply_page21(&mut insn, (1 << 20) - 1).unwrap();
        let mut insn = 0x9000_0000_u32.to_le_bytes();
        apply_page21(&mut insn, -(1 << 20)).unwrap();
    }

    #[test]
    fn test_apply_pageoff12_add() {
        // ADD x0, x0, #imm12: 0x91000000
        let mut insn = 0x9100_0000_u32.to_le_bytes();
        // Page offset = 0x10
        apply_pageoff12(&mut insn, 0x10, 0);
        let result = u32::from_le_bytes(insn);

        let imm12 = (result >> 10) & 0xFFF;
        assert_eq!(imm12, 0x10);
        assert_eq!(result & 0xFFC0_03FF, 0x9100_0000); // rest preserved
    }

    #[test]
    fn test_apply_pageoff12_ldr_x() {
        // LDR x0, [x0, #imm12]: 0xF9400000
        let mut insn = 0xF940_0000_u32.to_le_bytes();
        // Page offset = 0x10 (aligned to 8 bytes), shift=3
        apply_pageoff12(&mut insn, 0x10, 3);
        let result = u32::from_le_bytes(insn);

        let imm12 = (result >> 10) & 0xFFF;
        assert_eq!(imm12, 0x10 >> 3); // scaled by 8
    }

    #[test]
    fn test_apply_branch26_unaligned() {
        // FINDING #10b: an unaligned offset must now return a typed Err
        // (RelocationOverflow), not panic via assert!.
        let mut insn = 0x9400_0000_u32.to_le_bytes();
        let err = apply_branch26(&mut insn, 6); // not aligned
        assert!(
            matches!(err, Err(FixupError::RelocationOverflow { .. })),
            "expected RelocationOverflow, got {err:?}"
        );
        // The instruction bytes must be untouched on the error path.
        assert_eq!(insn, 0x9400_0000_u32.to_le_bytes());
    }

    #[test]
    fn test_apply_branch26_overflow() {
        // FINDING #10b: an out-of-range offset must now return a typed Err,
        // not panic. 256 MB = 67108864 words, exceeds 26-bit signed range.
        let mut insn = 0x9400_0000_u32.to_le_bytes();
        let err = apply_branch26(&mut insn, 256 * 1024 * 1024);
        assert!(
            matches!(err, Err(FixupError::RelocationOverflow { .. })),
            "expected RelocationOverflow, got {err:?}"
        );
    }

    #[test]
    fn test_apply_page21_overflow() {
        // FINDING #10b: page offset beyond the 21-bit signed range must Err.
        let mut insn = 0x9000_0000_u32.to_le_bytes();
        let err = apply_page21(&mut insn, 1 << 20);
        assert!(
            matches!(err, Err(FixupError::RelocationOverflow { .. })),
            "expected RelocationOverflow, got {err:?}"
        );
    }

    #[test]
    fn test_apply_branch26_boundary_max_in_range() {
        // FINDING #10b boundary: the largest in-range byte offsets still encode.
        // Max positive word offset = (1<<25)-1, in bytes << 2.
        let mut insn = 0x9400_0000_u32.to_le_bytes();
        apply_branch26(&mut insn, ((1i64 << 25) - 1) * 4).unwrap();
        let result = u32::from_le_bytes(insn);
        assert_eq!(result & 0x03FF_FFFF, ((1u32 << 25) - 1) & 0x03FF_FFFF);
        // Min negative word offset = -(1<<25), in bytes.
        let mut insn = 0x1400_0000_u32.to_le_bytes();
        apply_branch26(&mut insn, -(1i64 << 25) * 4).unwrap();
    }

    #[test]
    #[should_panic(expected = "not aligned")]
    fn test_apply_pageoff12_unaligned() {
        let mut insn = 0xF940_0000_u32.to_le_bytes();
        apply_pageoff12(&mut insn, 0x11, 3); // 0x11 not aligned to 8
    }

    #[test]
    fn test_fixup_list_empty() {
        let list = FixupList::new();
        assert!(list.is_empty());
        assert_eq!(list.len(), 0);
        assert_eq!(
            list.resolve_to_relocations()
                .expect("empty list resolves")
                .len(),
            0
        );
    }

    // ---- Error paths for Phase 1 of #386 ----

    #[test]
    fn test_resolve_named_symbols_missing_returns_err() {
        // A NamedSymbol whose name the lookup cannot resolve must return
        // FixupError::UnresolvedSymbol rather than panicking.
        let mut list = FixupList::new();
        list.push(Fixup::branch_sym(0x00, "missing_fn".to_string()));

        let err = list
            .resolve_named_symbols(|_name| None)
            .expect_err("missing named symbol must be an error");
        assert_eq!(
            err,
            FixupError::UnresolvedSymbol {
                name: "missing_fn".to_string()
            }
        );
    }

    #[test]
    fn test_resolve_to_relocations_unresolved_named_returns_err() {
        // If resolve_named_symbols was never called (or left a NamedSymbol
        // behind), resolve_to_relocations must return the API-misuse error
        // rather than panicking.
        let mut list = FixupList::new();
        list.push(Fixup::branch_sym(0x20, "callee".to_string()));

        let err = list
            .resolve_to_relocations()
            .expect_err("unresolved NamedSymbol must be an error");
        assert_eq!(
            err,
            FixupError::UnresolvedNamedSymbolAtOffset {
                offset: 0x20,
                name: "callee".to_string()
            }
        );
    }

    #[test]
    fn test_resolve_named_symbols_happy_path_returns_ok() {
        let mut list = FixupList::new();
        list.push(Fixup::branch_sym(0x00, "callee".to_string()));
        list.resolve_named_symbols(|name| if name == "callee" { Some(7) } else { None })
            .expect("lookup succeeds");

        let relocs = list
            .resolve_to_relocations()
            .expect("all NamedSymbol fixups were resolved");
        assert_eq!(relocs.len(), 1);
        assert_eq!(relocs[0].kind, AArch64RelocKind::Branch26);
        assert_eq!(relocs[0].symbol_index, 7);
        assert!(relocs[0].is_extern);
    }
}
