// trust-cg-codegen — ENC-EHDC: the DWARF eh_frame unwind-table decode-check gate
//
// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//
// An INDEPENDENT, clean-room DWARF Call-Frame-Information decoder that parses
// the emitted `__eh_frame` bytes back into CIE/FDE structures and re-checks
// that every decoded field EQUALS what the emitter intended (the
// [`DwarfCfiSection`] the emitter built). A disagreement, an undecodable byte,
// a malformed length prefix, a bad CIE id / CIE pointer, or trailing junk is a
// fail-closed defect.
//
// WHY (proven-ness / honesty)
// ---------------------------
// The x86-64 pipeline emits `__eh_frame` CFI for functions whose frame needs
// CFA rules (dynamic stack allocation): see
// `x86_64/pipeline.rs::build_x86_64_eh_frame_cfi` -> `DwarfCfiSection::to_bytes`.
// Until this gate, those unwind bytes were a TRUSTED surface — the emitter was
// believed to serialize a well-formed CIE/FDE, with nothing re-reading the
// bytes. This module SHRINKS that trusted island: it is the eh_frame analogue
// of ENC-3 (`x86_64/decode_check.rs`, per-instruction decode-check) and ENC-9
// (`macho/reparse.rs`, Mach-O reparse gate). A decoder/validator can only ever
// STRENGTHEN soundness (reject a malformed table) — it can never introduce a
// miscompile — so it is sound-in-isolation.
//
// INDEPENDENCE (honest labeling)
// ------------------------------
// This is a fail-closed REDUNDANCY / round-trip gate, not a proof. Its LEB128
// and field decoders are written from the DWARF-5 §6.4 / LSB `.eh_frame` byte
// layout, NOT by reading `dwarf_cfi.rs::to_bytes`. `decode(emit(intent)) ==
// intent` therefore catches any FUTURE encoder regression that drifts the bytes
// away from the intended CFI program (wrong ULEB/SLEB, wrong length prefix,
// wrong CIE id / CIE pointer, misplaced or wrong-count padding, a corrupted
// augmentation string, a wrong CFA offset). Its external anchor is the offline
// `objdump --macho --dwarf=frames` differential lane in
// `tests/dwarf_cfi_objdump_differential.rs`, which pins the emitted CIE/FDE
// fields against a real external disassembler for a representative function.
//
// SCOPE
// -----
// COVERED: the full CIE + FDE structural round-trip for the `.eh_frame` /
// `__eh_frame` sections both the x86-64 default path (zR, frame-walking) and the
// AArch64 EH path (zR and zPLR) emit — length prefixes, CIE id, version,
// augmentation string, code/data alignment factors, return-address register,
// augmentation data (personality encoding+pointer, LSDA encoding, FDE pointer
// encoding), the initial instruction program, per-FDE CIE pointer, PC begin/
// range, per-FDE LSDA augmentation, the call-frame instruction program, the
// 8-byte padding contract, and the zero terminator.
//
// SCOPED OUT (follow-on): the `__gcc_except_tab` LSDA call-site/action/type
// tables (`exception_handling.rs`). This decode-check covers the CIE/FDE
// round-trip only; a byte-level LSDA table round-trip is a clean same-shape
// follow-on. The x86-64 pipeline DOES emit and reference the LSDA on the
// unwinding path (`x86_lsda_for_function`, wired at `x86_64/pipeline.rs`), and
// the `_Unwind_Resume` continue-unwind path is live (the full-coverage call-site
// synthesis propagates a re-raise past a cleanup pad — proven by
// `e2e_x86_64_eh_resume_trust_ir`).

use crate::dwarf_cfi::{DwarfCfiSection, DwarfCie, DwarfFde};

// ---------------------------------------------------------------------------
// Error type
// ---------------------------------------------------------------------------

/// A structural disagreement between the intended CFI program and the decoded
/// `__eh_frame` bytes. When wired per-emission this becomes a fail-closed
/// pipeline error — trust-cg refuses to emit an unwind table it cannot decode
/// back to its own intent.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EhFrameDecodeError {
    /// Human-readable description (which field, intended vs decoded).
    pub message: String,
}

impl core::fmt::Display for EhFrameDecodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "[eh-frame-decode-check] {}", self.message)
    }
}

impl std::error::Error for EhFrameDecodeError {}

fn err<T>(message: String) -> Result<T, EhFrameDecodeError> {
    Err(EhFrameDecodeError { message })
}

/// Structural equality check with a precise, self-describing failure message.
fn check_eq<T: PartialEq + core::fmt::Debug>(
    field: &str,
    decoded: T,
    intent: T,
) -> Result<(), EhFrameDecodeError> {
    if decoded == intent {
        Ok(())
    } else {
        err(format!(
            "{field} mismatch: decoded {decoded:?} != emitter intent {intent:?}"
        ))
    }
}

// ---------------------------------------------------------------------------
// DWARF eh_frame constants (re-declared here, independently of the emitter)
// ---------------------------------------------------------------------------

/// DW_CFA_nop — the padding opcode.
const DW_CFA_NOP: u8 = 0x00;
/// eh_frame CIE id (distinguishes a CIE from an FDE).
const CIE_ID: u32 = 0;
/// DW_EH_PE size nibble: sdata4 / udata4.
const DW_EH_PE_SDATA4_NIBBLE: u8 = 0x0B;
/// DW_EH_PE size nibble: sdata8 / udata8.
const DW_EH_PE_SDATA8_NIBBLE: u8 = 0x0C;

/// Byte width of a DW_EH_PE-encoded pointer, derived independently from the
/// low nibble of the encoding (LP64 Darwin: absptr = 8).
fn pointer_encoding_size(encoding: u8) -> usize {
    match encoding & 0x0F {
        0x00 => 8, // DW_EH_PE_absptr — native pointer (8 on LP64)
        DW_EH_PE_SDATA4_NIBBLE => 4,
        DW_EH_PE_SDATA8_NIBBLE => 8,
        _ => 8,
    }
}

// ---------------------------------------------------------------------------
// Independent byte / LEB128 reader
// ---------------------------------------------------------------------------

/// A forward byte cursor with bounds-checked primitive + LEB128 reads. Every
/// read that runs off the end is a fail-closed decode error (truncated table).
struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, pos: 0 }
    }

    fn remaining(&self) -> usize {
        self.bytes.len().saturating_sub(self.pos)
    }

    fn at_end(&self) -> bool {
        self.pos >= self.bytes.len()
    }

    fn u8(&mut self) -> Result<u8, EhFrameDecodeError> {
        let b = *self.bytes.get(self.pos).ok_or_else(|| EhFrameDecodeError {
            message: format!("truncated: need 1 byte at offset {}", self.pos),
        })?;
        self.pos += 1;
        Ok(b)
    }

    fn u32_le(&mut self) -> Result<u32, EhFrameDecodeError> {
        let end = self.pos + 4;
        let slice = self
            .bytes
            .get(self.pos..end)
            .ok_or_else(|| EhFrameDecodeError {
                message: format!("truncated: need 4 bytes (u32) at offset {}", self.pos),
            })?;
        let v = u32::from_le_bytes(slice.try_into().unwrap());
        self.pos = end;
        Ok(v)
    }

    /// Read `size` bytes (4 or 8) as a sign-extended little-endian value.
    fn sized_le(&mut self, size: usize) -> Result<i64, EhFrameDecodeError> {
        let end = self.pos + size;
        let slice = self
            .bytes
            .get(self.pos..end)
            .ok_or_else(|| EhFrameDecodeError {
                message: format!(
                    "truncated: need {size} bytes (sized ptr) at offset {}",
                    self.pos
                ),
            })?;
        let v = match size {
            4 => i64::from(i32::from_le_bytes(slice.try_into().unwrap())),
            8 => i64::from_le_bytes(slice.try_into().unwrap()),
            other => {
                return err(format!("unsupported DW_EH_PE pointer size {other}"));
            }
        };
        self.pos = end;
        Ok(v)
    }

    fn take(&mut self, n: usize) -> Result<&'a [u8], EhFrameDecodeError> {
        let end = self.pos + n;
        let slice = self
            .bytes
            .get(self.pos..end)
            .ok_or_else(|| EhFrameDecodeError {
                message: format!("truncated: need {n} bytes at offset {}", self.pos),
            })?;
        self.pos = end;
        Ok(slice)
    }

    /// Read a null-terminated string, INCLUDING the terminating NUL (to match
    /// the emitter's `augmentation: Vec<u8>` which stores the trailing NUL).
    fn cstr_with_nul(&mut self) -> Result<Vec<u8>, EhFrameDecodeError> {
        let start = self.pos;
        loop {
            let b = self.u8()?;
            if b == 0 {
                return Ok(self.bytes[start..self.pos].to_vec());
            }
            if self.pos - start > 64 {
                return err("augmentation string is not NUL-terminated within 64 bytes".to_string());
            }
        }
    }

    /// Independent ULEB128 decoder (DWARF-5 §7.6, written from the spec).
    fn uleb128(&mut self) -> Result<u64, EhFrameDecodeError> {
        let mut result: u64 = 0;
        let mut shift = 0u32;
        loop {
            let byte = self.u8()?;
            if shift >= 64 {
                return err("ULEB128 overflows u64".to_string());
            }
            result |= u64::from(byte & 0x7F) << shift;
            if byte & 0x80 == 0 {
                return Ok(result);
            }
            shift += 7;
        }
    }

    /// Independent SLEB128 decoder (DWARF-5 §7.6, written from the spec).
    fn sleb128(&mut self) -> Result<i64, EhFrameDecodeError> {
        let mut result: i64 = 0;
        let mut shift = 0u32;
        loop {
            let byte = self.u8()?;
            if shift >= 64 {
                return err("SLEB128 overflows i64".to_string());
            }
            result |= i64::from(byte & 0x7F) << shift;
            shift += 7;
            if byte & 0x80 == 0 {
                // Sign-extend if the sign bit of the final group is set.
                if shift < 64 && byte & 0x40 != 0 {
                    result |= -1i64 << shift;
                }
                return Ok(result);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Public entry point
// ---------------------------------------------------------------------------

/// Decode-check the emitted `__eh_frame` bytes against the [`DwarfCfiSection`]
/// the emitter built. Returns `Ok(())` iff every decoded CIE/FDE field equals
/// the emitter's intent and the section is well-formed (length prefixes, CIE
/// id, per-FDE CIE pointers, padding contract, zero terminator, no trailing
/// junk). Any deviation is a fail-closed [`EhFrameDecodeError`].
///
/// `bytes` must be the RAW serialized section (`section.to_bytes()`), i.e.
/// BEFORE any object-writer relocation-addend patching (which rewrites the
/// per-FDE PC-begin field from the intent value `0` to a section-relative
/// addend; that reloc surface is covered separately by the proven reloc
/// formulas + `fde_pc_begin_relocation_offsets`).
pub fn verify_eh_frame_roundtrip(
    section: &DwarfCfiSection,
    bytes: &[u8],
) -> Result<(), EhFrameDecodeError> {
    // An empty section emits no bytes.
    if section.fdes().is_empty() {
        if bytes.is_empty() {
            return Ok(());
        }
        return err(format!(
            "section has no FDEs but emitted {} bytes (expected empty)",
            bytes.len()
        ));
    }

    let mut r = Reader::new(bytes);

    // ---- CIE ----
    let cie = section.cie();
    let cie_start = r.pos;
    let (pc_size, lsda_size) = decode_and_check_cie(&mut r, cie)?;
    let cie_end = r.pos;
    // Sanity: the CIE occupies a whole number of bytes and starts at 0.
    debug_assert_eq!(cie_start, 0);
    let _ = cie_end;

    // ---- FDEs ----
    for (i, fde) in section.fdes().iter().enumerate() {
        let fde_start = r.pos;
        // The emitter's CIE pointer = (offset of the CIE-pointer field) - (CIE
        // start). The CIE-pointer field sits at fde_start + 4; the CIE starts at
        // cie_start (0). This is recomputed here independently from byte offsets.
        let expected_cie_pointer = (fde_start as u32 + 4) - cie_start as u32;
        decode_and_check_fde(&mut r, fde, i, expected_cie_pointer, pc_size, lsda_size)?;
    }

    // ---- Terminator: a zero-length entry (4 zero bytes) ----
    if r.remaining() < 4 {
        return err(format!(
            "missing 4-byte zero terminator (only {} bytes left after last FDE)",
            r.remaining()
        ));
    }
    let term = r.u32_le()?;
    if term != 0 {
        return err(format!(
            "terminator is 0x{term:08x}, expected a zero-length (0) entry"
        ));
    }

    // ---- No trailing junk ----
    if !r.at_end() {
        return err(format!(
            "{} unexpected trailing bytes after the eh_frame terminator",
            r.remaining()
        ));
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// CIE decode + intent compare
// ---------------------------------------------------------------------------

/// Decode one CIE and check every field against `cie`. Returns
/// `(pc_size, lsda_size)` derived from the decoded FDE / LSDA pointer encodings
/// (used to parse the following FDEs) — matching the emitter's own choice.
fn decode_and_check_cie(
    r: &mut Reader<'_>,
    cie: &DwarfCie,
) -> Result<(usize, usize), EhFrameDecodeError> {
    let length = r.u32_le()? as usize;
    let body_start = r.pos;
    let entry_end = body_start + length;
    if entry_end > r.bytes.len() {
        return err(format!(
            "CIE length {length} runs past end of section ({} bytes available)",
            r.bytes.len() - body_start
        ));
    }
    // eh_frame alignment contract: the whole entry (4-byte length + body) is a
    // multiple of the pointer size (8 on LP64 Darwin).
    if !(length + 4).is_multiple_of(8) {
        return err(format!(
            "CIE total size {} is not 8-byte aligned",
            length + 4
        ));
    }

    // CIE id must be 0 in eh_frame.
    let cie_id = r.u32_le()?;
    check_eq("CIE id", cie_id, CIE_ID)?;

    // Version.
    let version = r.u8()?;
    check_eq("CIE version", version, cie.version)?;

    // Augmentation string (with trailing NUL).
    let augmentation = r.cstr_with_nul()?;
    check_eq(
        "CIE augmentation string",
        augmentation.clone(),
        cie.augmentation.clone(),
    )?;

    // Code / data alignment factors, return-address register.
    let code_alignment_factor = r.uleb128()?;
    check_eq(
        "CIE code_alignment_factor",
        code_alignment_factor,
        cie.code_alignment_factor,
    )?;
    let data_alignment_factor = r.sleb128()?;
    check_eq(
        "CIE data_alignment_factor",
        data_alignment_factor,
        cie.data_alignment_factor,
    )?;
    let return_address_register = r.uleb128()?;
    check_eq(
        "CIE return_address_register",
        return_address_register,
        cie.return_address_register,
    )?;

    // Augmentation data (only present when the string begins with 'z').
    let has_z = augmentation.first() == Some(&b'z');
    if !has_z {
        return err(format!(
            "unexpected non-'z' augmentation {augmentation:?}: emitter always emits 'z'-prefixed"
        ));
    }
    let aug_data_len = r.uleb128()? as usize;
    let aug_data = r.take(aug_data_len)?.to_vec();

    // Parse the augmentation data in the exact order the letters appear after
    // 'z' — 'P' personality (encoding byte + pointer), 'L' LSDA encoding byte,
    // 'R' FDE pointer encoding byte — independently of the emitter.
    let mut ar = Reader::new(&aug_data);
    let mut decoded_fde_ptr_enc: Option<u8> = None;
    let mut decoded_lsda_enc: Option<u8> = None;
    let mut decoded_personality_enc: Option<u8> = None;
    let mut decoded_personality_ptr: Option<u32> = None;
    // Letters after the leading 'z', up to (not including) the NUL.
    for &letter in augmentation.iter().skip(1) {
        match letter {
            0 => break,
            b'P' => {
                let enc = ar.u8()?;
                decoded_personality_enc = Some(enc);
                // The emitter serializes the personality pointer as a fixed
                // 4-byte (u32) placeholder regardless of the encoding.
                let ptr = ar.u32_le()?;
                decoded_personality_ptr = Some(ptr);
            }
            b'L' => {
                decoded_lsda_enc = Some(ar.u8()?);
            }
            b'R' => {
                decoded_fde_ptr_enc = Some(ar.u8()?);
            }
            other => {
                return err(format!(
                    "unknown augmentation letter '{}' (0x{other:02x})",
                    other as char
                ));
            }
        }
    }
    if !ar.at_end() {
        return err(format!(
            "CIE augmentation data has {} unconsumed trailing byte(s)",
            ar.remaining()
        ));
    }

    // Compare augmentation-data-derived fields against intent.
    check_eq(
        "CIE personality_encoding",
        decoded_personality_enc,
        cie.personality_encoding,
    )?;
    check_eq(
        "CIE personality_pointer",
        decoded_personality_ptr,
        cie.personality_pointer,
    )?;
    check_eq("CIE lsda_encoding", decoded_lsda_enc, cie.lsda_encoding)?;
    let fde_ptr_enc = decoded_fde_ptr_enc.ok_or_else(|| EhFrameDecodeError {
        message: "CIE augmentation 'R' (FDE pointer encoding) missing".to_string(),
    })?;
    check_eq(
        "CIE fde_pointer_encoding",
        fde_ptr_enc,
        cie.fde_pointer_encoding,
    )?;

    // Initial instructions + padding fill the rest of the entry body.
    let region = r.take(entry_end - r.pos)?;
    check_instruction_region(
        "CIE initial instructions",
        region,
        &cie.initial_instructions,
    )?;

    debug_assert_eq!(r.pos, entry_end);

    // Sizes used to parse the FDEs (the emitter derives lsda_size from the LSDA
    // encoding when present, else it defaults to the FDE pointer size).
    let pc_size = pointer_encoding_size(fde_ptr_enc);
    let lsda_size = decoded_lsda_enc
        .map(pointer_encoding_size)
        .unwrap_or(pc_size);
    Ok((pc_size, lsda_size))
}

// ---------------------------------------------------------------------------
// FDE decode + intent compare
// ---------------------------------------------------------------------------

fn decode_and_check_fde(
    r: &mut Reader<'_>,
    fde: &DwarfFde,
    index: usize,
    expected_cie_pointer: u32,
    pc_size: usize,
    lsda_size: usize,
) -> Result<(), EhFrameDecodeError> {
    let field = |name: &str| format!("FDE[{index}] {name}");

    let length = r.u32_le()? as usize;
    let body_start = r.pos;
    let entry_end = body_start + length;
    if entry_end > r.bytes.len() {
        return err(format!(
            "{}: length {length} runs past end of section",
            field("")
        ));
    }
    if !(length + 4).is_multiple_of(8) {
        return err(format!(
            "{}: total size {} not 8-byte aligned",
            field(""),
            length + 4
        ));
    }

    // CIE pointer — nonzero in eh_frame, and equal to the recomputed offset.
    let cie_pointer = r.u32_le()?;
    if cie_pointer == 0 {
        return err(format!(
            "{}: CIE pointer is 0 (would parse as a CIE, not an FDE)",
            field("")
        ));
    }
    check_eq(&field("CIE pointer"), cie_pointer, expected_cie_pointer)?;

    // PC begin / PC range use the CIE's FDE pointer encoding size.
    let pc_begin = r.sized_le(pc_size)?;
    check_eq(&field("PC begin"), pc_begin, fde.function_offset as i64)?;
    let pc_range = r.sized_le(pc_size)?;
    check_eq(&field("PC range"), pc_range, i64::from(fde.function_length))?;

    // FDE augmentation data: length ULEB, then (for a "zPLR" CIE with an LSDA)
    // the LSDA pointer. The length is self-describing.
    let aug_data_len = r.uleb128()? as usize;
    match fde.lsda_pointer {
        Some(intent_lsda) => {
            check_eq(&field("LSDA aug data length"), aug_data_len, lsda_size)?;
            let lsda = r.sized_le(lsda_size)?;
            check_eq(&field("LSDA pointer"), lsda, intent_lsda)?;
        }
        None => {
            check_eq(&field("aug data length"), aug_data_len, 0usize)?;
        }
    }

    // Call-frame instructions + padding fill the rest of the entry body.
    let region = r.take(entry_end - r.pos)?;
    check_instruction_region(&field("call-frame instructions"), region, &fde.instructions)?;

    debug_assert_eq!(r.pos, entry_end);
    Ok(())
}

// ---------------------------------------------------------------------------
// Instruction-region (program + padding) comparison
// ---------------------------------------------------------------------------

/// A CFI instruction region is `intent` followed by DW_CFA_nop padding. Verify
/// the decoded region is exactly `intent` as a prefix and that the remainder is
/// all-NOP padding of MINIMAL length (< 8, the emitter pads only up to the next
/// 8-byte boundary). This catches wrong instruction bytes, a wrong length
/// prefix (which shifts the region size), and corrupted / over-long padding.
fn check_instruction_region(
    what: &str,
    region: &[u8],
    intent: &[u8],
) -> Result<(), EhFrameDecodeError> {
    if region.len() < intent.len() {
        return err(format!(
            "{what}: decoded region is {} bytes, shorter than the {} intended instruction bytes",
            region.len(),
            intent.len()
        ));
    }
    let (prefix, padding) = region.split_at(intent.len());
    if prefix != intent {
        return err(format!(
            "{what}: decoded program {prefix:02x?} != emitter intent {intent:02x?}"
        ));
    }
    if padding.len() >= 8 {
        return err(format!(
            "{what}: {} padding bytes exceed the 8-byte alignment slack (wrong length prefix?)",
            padding.len()
        ));
    }
    if let Some(bad) = padding.iter().position(|&b| b != DW_CFA_NOP) {
        return err(format!(
            "{what}: padding byte {} is 0x{:02x}, expected DW_CFA_nop (0x00)",
            bad, padding[bad]
        ));
    }
    Ok(())
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dwarf_cfi::{DwarfCfiSection, DwarfFde, x86_64_fde_from_prologue};
    use trust_cg_ir::x86_64_regs::{R12, R13, R14, R15, RBX};

    // ---- Representative x86-64 sections (the real default-path emitter) ----

    /// A minimal x86-64 frame-walking section: PUSH RBP / MOV RBP,RSP, no
    /// callee-saves, no locals — the FDE the default path emits for a small
    /// dynamic-alloc function.
    fn x86_64_simple_section() -> DwarfCfiSection {
        let mut section = DwarfCfiSection::new_x86_64();
        let fde = x86_64_fde_from_prologue(&[], 0, 0, 96, 0);
        section.add_fde(fde);
        section
    }

    /// A richer x86-64 section: several callee-saved pushes + a large frame,
    /// exercising multiple DW_CFA_offset instructions and advance_loc encodings.
    fn x86_64_rich_section() -> DwarfCfiSection {
        let mut section = DwarfCfiSection::new_x86_64();
        let callee = [RBX, R12, R13, R14, R15];
        let fde = x86_64_fde_from_prologue(&callee, 4096, 0, 512, 3);
        section.add_fde(fde);
        section
    }

    /// Two functions in one section (two FDEs sharing the CIE).
    fn x86_64_two_fde_section() -> DwarfCfiSection {
        let mut section = DwarfCfiSection::new_x86_64();
        section.add_fde(x86_64_fde_from_prologue(&[RBX], 16, 0, 64, 1));
        section.add_fde(x86_64_fde_from_prologue(&[R12, R13], 256, 0, 200, 2));
        section
    }

    // ================= Positive round-trips (decoded == intent) =============

    #[test]
    fn roundtrip_x86_64_simple() {
        let section = x86_64_simple_section();
        let bytes = section.to_bytes();
        verify_eh_frame_roundtrip(&section, &bytes).expect("simple x86 eh_frame must round-trip");
    }

    #[test]
    fn roundtrip_x86_64_rich() {
        let section = x86_64_rich_section();
        let bytes = section.to_bytes();
        verify_eh_frame_roundtrip(&section, &bytes).expect("rich x86 eh_frame must round-trip");
    }

    #[test]
    fn roundtrip_x86_64_two_fdes() {
        let section = x86_64_two_fde_section();
        let bytes = section.to_bytes();
        verify_eh_frame_roundtrip(&section, &bytes).expect("two-FDE x86 eh_frame must round-trip");
    }

    #[test]
    fn roundtrip_x86_64_with_eh_zplr() {
        // The zPLR augmentation (personality + LSDA) round-trip. Not on the
        // default x86 path yet, but the decoder covers it.
        let mut section = DwarfCfiSection::new_x86_64_with_eh();
        let fde = x86_64_fde_from_prologue(&[RBX], 32, 0, 128, 1).with_lsda();
        section.add_fde(fde);
        let bytes = section.to_bytes();
        verify_eh_frame_roundtrip(&section, &bytes).expect("zPLR x86 eh_frame must round-trip");
    }

    #[test]
    fn roundtrip_aarch64() {
        use crate::frame::{CalleeSavedPair, FrameLayout};
        use trust_cg_ir::regs::{X19, X20, X29, X30};
        let layout = FrameLayout {
            callee_saved_pairs: vec![
                CalleeSavedPair {
                    reg1: X29,
                    reg2: X30,
                    fp_offset: 0,
                    is_fpr: false,
                },
                CalleeSavedPair {
                    reg1: X19,
                    reg2: X20,
                    fp_offset: -16,
                    is_fpr: false,
                },
            ],
            callee_saved_area_size: 32,
            spill_area_size: 0,
            local_area_size: 0,
            outgoing_arg_area_size: 0,
            total_frame_size: 32,
            uses_frame_pointer: true,
            is_leaf: false,
            uses_red_zone: false,
            fp_to_spill_offset: -32,
            has_dynamic_alloc: true,
        };
        let mut section = DwarfCfiSection::new();
        section.add_fde(DwarfFde::from_layout(&layout, 0, 200, 0));
        let bytes = section.to_bytes();
        verify_eh_frame_roundtrip(&section, &bytes).expect("aarch64 eh_frame must round-trip");
    }

    #[test]
    fn roundtrip_empty_section() {
        let section = DwarfCfiSection::new_x86_64();
        let bytes = section.to_bytes();
        assert!(bytes.is_empty());
        verify_eh_frame_roundtrip(&section, &bytes).expect("empty section round-trips");
    }

    // ========================= TEETH / tamper tests =========================
    //
    // A decode-check that passes a corrupt table is worthless. Every corruption
    // below MUST be rejected (Err). We corrupt the REAL emitted bytes.

    /// Flip byte at `idx` (XOR a bit) and assert the round-trip rejects it.
    fn assert_rejects_flip(section: &DwarfCfiSection, idx: usize, bit: u8, what: &str) {
        let mut bytes = section.to_bytes();
        bytes[idx] ^= bit;
        let res = verify_eh_frame_roundtrip(section, &bytes);
        assert!(
            res.is_err(),
            "TEETH FAILURE: corruption `{what}` at byte {idx} was NOT rejected"
        );
    }

    #[test]
    fn teeth_cie_length_prefix() {
        // Byte 0 is the low byte of the CIE length.
        assert_rejects_flip(&x86_64_simple_section(), 0, 0x08, "CIE length prefix");
    }

    #[test]
    fn teeth_cie_id_nonzero() {
        // Bytes 4..8 are the CIE id (must be 0).
        assert_rejects_flip(&x86_64_simple_section(), 4, 0x01, "CIE id -> nonzero");
    }

    #[test]
    fn teeth_cie_version() {
        // Byte 8 is the CIE version.
        assert_rejects_flip(&x86_64_simple_section(), 8, 0x02, "CIE version");
    }

    #[test]
    fn teeth_cie_augmentation_char() {
        // Byte 9 is 'z', byte 10 is 'R' of the "zR\0" augmentation.
        assert_rejects_flip(&x86_64_simple_section(), 9, 0x20, "augmentation 'z'");
        assert_rejects_flip(&x86_64_simple_section(), 10, 0x20, "augmentation 'R'");
    }

    #[test]
    fn teeth_cie_fde_pointer_encoding() {
        // The FDE pointer encoding byte lives in the CIE augmentation data.
        // Locate it: length(4)+id(4)+ver(1)+"zR\0"(3)+codeAlign(1)+dataAlign(1)
        // +raReg(1)+augDataLen(1) = 16, then the single aug-data byte at 16.
        let section = x86_64_simple_section();
        // Flipping the size nibble (sdata4 -> sdata8) desynchronizes FDE parsing.
        assert_rejects_flip(&section, 16, 0x01, "FDE pointer encoding size nibble");
    }

    #[test]
    fn teeth_cie_initial_instruction_cfa_offset() {
        // Corrupt a byte inside the CIE initial instruction program (the
        // DW_CFA_def_cfa RSP, 8 / DW_CFA_offset RIP, 1 sequence begins at 17).
        let section = x86_64_simple_section();
        assert_rejects_flip(&section, 18, 0x0F, "CIE initial-instruction CFA operand");
    }

    #[test]
    fn teeth_fde_cie_pointer() {
        // Find the FDE start (= CIE length) and flip its CIE-pointer field.
        let section = x86_64_simple_section();
        let bytes = section.to_bytes();
        let cie_len = u32::from_le_bytes(bytes[0..4].try_into().unwrap()) as usize;
        let fde_start = 4 + cie_len;
        // CIE-pointer field is at fde_start + 4.
        assert_rejects_flip(&section, fde_start + 4, 0x10, "FDE CIE pointer");
    }

    #[test]
    fn teeth_fde_cfi_instruction() {
        // Corrupt a call-frame instruction byte in the FDE program.
        let section = x86_64_rich_section();
        let bytes = section.to_bytes();
        let cie_len = u32::from_le_bytes(bytes[0..4].try_into().unwrap()) as usize;
        let fde_start = 4 + cie_len;
        // Skip length(4)+cie_ptr(4)+pc_begin(4)+pc_range(4)+augLen(1) = 17 into
        // the FDE to land on the first CFI instruction byte.
        assert_rejects_flip(&section, fde_start + 17, 0x0F, "FDE CFI instruction");
    }

    #[test]
    fn teeth_fde_pc_range() {
        // Flip a PC-range byte: length(4)+cie_ptr(4)+pc_begin(4) = 12 into FDE.
        let section = x86_64_simple_section();
        let bytes = section.to_bytes();
        let cie_len = u32::from_le_bytes(bytes[0..4].try_into().unwrap()) as usize;
        let fde_start = 4 + cie_len;
        assert_rejects_flip(&section, fde_start + 12, 0x01, "FDE PC range");
    }

    #[test]
    fn teeth_padding_nop_corrupted() {
        // Turn a trailing NOP-padding byte into a non-NOP. Padding is the last
        // bytes before the FDE's 8-byte boundary; the last body byte of the FDE
        // is very likely padding for these small programs.
        let section = x86_64_simple_section();
        let bytes = section.to_bytes();
        // Terminator is the last 4 bytes; the byte just before it is the final
        // padding byte of the last FDE.
        let pad_idx = bytes.len() - 5;
        assert_eq!(bytes[pad_idx], 0x00, "expected NOP padding at {pad_idx}");
        assert_rejects_flip(&section, pad_idx, 0x11, "FDE NOP padding -> non-NOP");
    }

    #[test]
    fn teeth_terminator_nonzero() {
        // Flip a terminator byte (last 4 bytes must be zero).
        let section = x86_64_simple_section();
        let bytes = section.to_bytes();
        let idx = bytes.len() - 1;
        assert_rejects_flip(&section, idx, 0x01, "zero terminator");
    }

    #[test]
    fn teeth_truncation() {
        // A truncated section (missing the terminator) must be rejected.
        let section = x86_64_simple_section();
        let bytes = section.to_bytes();
        let truncated = &bytes[..bytes.len() - 2];
        assert!(
            verify_eh_frame_roundtrip(&section, truncated).is_err(),
            "TEETH FAILURE: truncated eh_frame was not rejected"
        );
    }

    #[test]
    fn teeth_trailing_junk() {
        // Extra bytes after the terminator must be rejected.
        let section = x86_64_simple_section();
        let mut bytes = section.to_bytes();
        bytes.extend_from_slice(&[0xAA, 0xBB, 0xCC, 0xDD]);
        assert!(
            verify_eh_frame_roundtrip(&section, &bytes).is_err(),
            "TEETH FAILURE: trailing junk after terminator not rejected"
        );
    }

    #[test]
    fn teeth_wrong_intent_rejected() {
        // Bytes from one section must NOT validate against a DIFFERENT section's
        // intent (guards against a vacuous "always Ok" gate).
        let simple = x86_64_simple_section();
        let rich = x86_64_rich_section();
        let rich_bytes = rich.to_bytes();
        assert!(
            verify_eh_frame_roundtrip(&simple, &rich_bytes).is_err(),
            "TEETH FAILURE: rich bytes validated against simple intent"
        );
    }

    // ---- Independent LEB128 decoder sanity (spec byte patterns) ----

    #[test]
    fn uleb128_decoder_matches_spec_examples() {
        // DWARF-5 §7.6 examples.
        let cases: &[(&[u8], u64)] = &[
            (&[0x00], 0),
            (&[0x02], 2),
            (&[0x7f], 127),
            (&[0x80, 0x01], 128),
            (&[0x81, 0x01], 129),
            (&[0xe5, 0x8e, 0x26], 624485),
        ];
        for (bytes, expected) in cases {
            let mut r = Reader::new(bytes);
            assert_eq!(r.uleb128().unwrap(), *expected, "uleb {bytes:02x?}");
        }
    }

    #[test]
    fn sleb128_decoder_matches_spec_examples() {
        // DWARF-5 §7.6 examples (signed).
        let cases: &[(&[u8], i64)] = &[
            (&[0x02], 2),
            (&[0x7e], -2),
            (&[0xff, 0x00], 127),
            (&[0x81, 0x7f], -127),
            (&[0x80, 0x01], 128),
            (&[0x80, 0x7f], -128),
        ];
        for (bytes, expected) in cases {
            let mut r = Reader::new(bytes);
            assert_eq!(r.sleb128().unwrap(), *expected, "sleb {bytes:02x?}");
        }
    }
}
