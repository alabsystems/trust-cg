// trust-cg-codegen - In-memory unwind tables for AArch64 JIT publications
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: LSB Core 5.0, Section 10.6 (.eh_frame layout, DW_EH_PE encodings)
// Reference: Itanium C++ ABI Exception Handling (LSDA, personality)
// Reference: libunwind UnwindLevel1-gcc-ext.c (`__register_frame` takes one
//            FDE on Apple platforms) and libgcc unwind-dw2-fde.c
//            (`__register_frame` takes the start of a terminated section)
// Reference: Arm ARM DDI 0487, C6.2.273 STP and C6.2.4 ADD (immediate)

//! In-memory `.eh_frame` unwind tables for AArch64 JIT-published functions.
//!
//! An exception or Rust panic that crosses a JIT frame needs three things the
//! AOT object path gets from the linker: an FDE describing the frame, the
//! function's LSDA, and the personality routine named by the CIE. This module
//! builds all three into the tail of the JIT image, after the code and
//! veneers, and binds every pointer field through an explicit relocation list:
//!
//! * FDE `pc_begin` fields and LSDA pointers are `DW_EH_PE_pcrel|sdata4`
//!   fields resolved against in-image offsets.
//! * The CIE personality field is `DW_EH_PE_indirect|pcrel|sdata4` and points
//!   at an 8-byte slot in the image that holds the resolved personality
//!   address. The address comes from the caller's explicit binding or, when
//!   the JIT policy permits, process symbol lookup; the manifest records which.
//!
//! The pointer fields are checked twice before publication: the unrelocated
//! section must round-trip through the existing ENC-EHDC decoder, and an
//! independent decoder in this module re-reads the relocated bytes and checks
//! every resolved pointer against the manifest. Each FP frame's prologue words
//! are decoded from the Arm ARM field layout and compared with the frame
//! layout the CFI program was generated from. The same decoder then runs each
//! FDE's CFA program (DWARF 5, 6.4.2) and requires its final rules to match
//! the saves and frame-pointer placement decoded from the prologue words
//! alone, without consulting the layout.
//!
//! Registration uses the platform unwinder's dynamic-FDE interface after the
//! mapping is read-execute: one `__register_frame` call per FDE on Darwin
//! (libunwind), one call for the whole terminated section on Linux (libgcc).
//! Every registered function is then looked up with `_Unwind_Find_FDE`, and
//! publication fails closed unless the unwinder returns the exact FDE. The
//! registration is released before the mapping is unmapped, following the
//! buffer's teardown policy.
//!
//! Evidence boundary: these are structural and native-execution checks, not
//! proofs. Typed catches (`JitError::JitUnwindTypedCatchUnsupported`: the
//! image carries no typeinfo indirection slot for the LSDA's TType entries)
//! and multiple personalities (`JitUnwindMultiplePersonalities`) stay refused
//! by name although Mach-O AOT emission supports both, filters have no
//! trust-ir surface, and proof-grade JIT modes refuse any unwind tables
//! because this path has no proof obligation. An image whose tables carry
//! exception handling is also decided against the exception-table
//! obligations of ledger L03-P14 before it is mapped
//! (`crate::pipeline::eh_obligation_intent::check_jit_image`): independent
//! decoders, the machine IR's landing pads and invokes, and the frame state
//! at every call. Those decisions are testing grade, not proof.

use crate::dwarf_cfi::{DwarfCfiSection, DwarfFde};
use crate::exception_handling::{canonical_personality_symbol, generate_lsda_from_pads};
use crate::frame::FrameLayout;
use crate::jit::JitError;

/// `DW_EH_PE_pcrel | DW_EH_PE_sdata4`.
const PCREL_SDATA4: u8 = 0x1b;
/// `DW_EH_PE_indirect | DW_EH_PE_pcrel | DW_EH_PE_sdata4`.
const INDIRECT_PCREL_SDATA4: u8 = 0x9b;
/// `DW_EH_PE_omit`.
const OMIT: u8 = 0xff;
/// `DW_EH_PE_uleb128`.
const ULEB128: u8 = 0x01;

/// Frame layouts and walk-through policy for one JIT module.
///
/// The compiler supplies the layout recorded by frame lowering for each
/// prepared function, in the same order as the machine functions. The raw
/// `JitCompiler::compile_raw` API has no such authority and keeps refusing
/// exception-handling functions.
#[derive(Debug, Clone)]
pub(crate) struct Aarch64JitUnwindRequest {
    frame_layouts: Vec<Option<FrameLayout>>,
    walk_through: bool,
}

impl Aarch64JitUnwindRequest {
    /// `walk_through` registers frame-only tables for every function even when
    /// no function carries exception-handling metadata (`panic_unwind`).
    pub(crate) fn new(frame_layouts: Vec<Option<FrameLayout>>, walk_through: bool) -> Self {
        Self {
            frame_layouts,
            walk_through,
        }
    }

    pub(crate) fn walk_through(&self) -> bool {
        self.walk_through
    }

    pub(crate) fn function_count(&self) -> usize {
        self.frame_layouts.len()
    }

    pub(crate) fn frame_layout(&self, ordinal: usize) -> Option<&FrameLayout> {
        self.frame_layouts.get(ordinal).and_then(Option::as_ref)
    }
}

/// One published function as seen by the unwind-table builder.
pub(crate) struct JitUnwindFunctionInput<'a> {
    pub(crate) name: &'a str,
    /// Image offset of the function entry (the LSDA's region start).
    pub(crate) code_offset: u64,
    /// Encoded length; the FDE and the LSDA call-site table cover exactly this.
    pub(crate) code_len: u32,
    pub(crate) layout: &'a FrameLayout,
    /// `(lsda_bytes, personality)` for a function carrying EH metadata.
    pub(crate) lsda: Option<(&'a [u8], &'a str)>,
}

/// Width and meaning of one relocated unwind-table field.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum JitUnwindRelocationKind {
    /// Signed 32-bit PC-relative field (`DW_EH_PE_pcrel | DW_EH_PE_sdata4`).
    Prel32,
    /// 64-bit absolute address stored in the personality indirection slot.
    Abs64,
}

/// What a relocated unwind-table field refers to.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum JitUnwindRelocationTarget {
    /// The entry of a published function (an FDE `pc_begin`).
    FunctionEntry { function: String },
    /// A function's LSDA (an FDE augmentation pointer).
    Lsda { function: String },
    /// The personality indirection slot (the CIE personality field).
    PersonalitySlot,
    /// The personality routine itself (the slot contents).
    PersonalityRoutine { symbol: String },
}

/// One explicitly bound pointer in the JIT unwind tables.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct JitUnwindRelocation {
    /// Image offset of the patched field.
    pub field_offset: u64,
    pub kind: JitUnwindRelocationKind,
    pub target: JitUnwindRelocationTarget,
    /// Image offset of an in-image target; `None` for the personality routine.
    pub target_offset: Option<u64>,
    /// Absolute address written for the personality routine.
    pub target_address: Option<u64>,
}

/// Where the personality address came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum JitPersonalitySource {
    /// The caller's explicit extern-symbol binding.
    ExplicitBinding,
    /// Process symbol lookup, permitted by the JIT resolution policy.
    ProcessLookup,
}

/// The personality routine named by the module's CIE.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct JitPersonalityBinding {
    /// Canonical linker-level personality name (no object-format prefix).
    pub symbol: String,
    pub address: u64,
    pub source: JitPersonalitySource,
}

/// How the tables are handed to the platform unwinder.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum JitUnwindRegistrationScheme {
    /// Darwin libunwind: one `__register_frame` call per FDE.
    PerFde,
    /// Linux libgcc: one `__register_frame` call for the terminated section.
    WholeSection,
}

/// Per-function unwind record.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct JitUnwindFunctionRecord {
    pub function: String,
    pub code_offset: u64,
    pub code_len: u32,
    /// Image offset of this function's FDE.
    pub fde_offset: u64,
    /// Image offset of this function's LSDA, when the module carries EH.
    pub lsda_offset: Option<u64>,
    /// Whether the LSDA is the synthetic no-handler filler of a non-EH frame.
    pub lsda_is_filler: bool,
    /// Whether the FDE describes a frame-pointer prologue (otherwise a
    /// zero-frame leaf whose CIE rule is exact for the whole body).
    pub frame_pointer: bool,
}

/// Published description of a JIT image's unwind tables.
///
/// Offsets are relative to the start of the executable image. These are the
/// publisher's own records, checked by an independent decoder before
/// publication; they are not a proof that the CFI program is complete.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct JitUnwindManifest {
    pub eh_frame_offset: u64,
    /// Length including the zero terminator.
    pub eh_frame_len: u64,
    pub personality: Option<JitPersonalityBinding>,
    pub personality_slot_offset: Option<u64>,
    pub functions: Vec<JitUnwindFunctionRecord>,
    pub relocations: Vec<JitUnwindRelocation>,
    pub registration_scheme: JitUnwindRegistrationScheme,
}

impl JitUnwindManifest {
    /// Record for `function`, if it is covered by the tables.
    pub fn function(&self, function: &str) -> Option<&JitUnwindFunctionRecord> {
        self.functions
            .iter()
            .find(|record| record.function == function)
    }

    /// Whether any function carries a real (non-filler) LSDA.
    pub fn carries_exception_handling(&self) -> bool {
        self.functions
            .iter()
            .any(|record| record.lsda_offset.is_some() && !record.lsda_is_filler)
    }
}

/// The registration scheme of the running host's unwinder.
pub(crate) const fn host_registration_scheme() -> JitUnwindRegistrationScheme {
    if cfg!(target_os = "macos") {
        JitUnwindRegistrationScheme::PerFde
    } else {
        JitUnwindRegistrationScheme::WholeSection
    }
}

fn table_error(detail: impl Into<String>) -> JitError {
    JitError::JitUnwindTableRejected {
        detail: detail.into(),
    }
}

/// The single personality routine named by the module's EH functions.
pub(crate) fn module_personality(
    functions: &[JitUnwindFunctionInput<'_>],
) -> Result<Option<String>, JitError> {
    let mut names: Vec<&str> = functions
        .iter()
        .filter_map(|function| {
            function
                .lsda
                .map(|(_, personality)| canonical_personality_symbol(personality))
        })
        .collect();
    names.sort_unstable();
    names.dedup();
    match names.as_slice() {
        [] => Ok(None),
        [single] => Ok(Some((*single).to_owned())),
        many => Err(JitError::JitUnwindMultiplePersonalities {
            personalities: many.iter().map(|name| (*name).to_owned()).collect(),
        }),
    }
}

// ---------------------------------------------------------------------------
// Prologue decode (independent of the frame emitter)
// ---------------------------------------------------------------------------

/// A decoded 64-bit STP (GPR X or FP D register pair).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct DecodedStp {
    fpr: bool,
    pre_index: bool,
    offset: i64,
    rt: u8,
    rt2: u8,
    rn: u8,
}

/// Decode STP (64-bit GPR or D-register pair, signed-offset or pre-index)
/// from the Arm ARM field layout: `opc:2 101 V 0 mode:3 L imm7 Rt2 Rn Rt`
/// with `mode` in bits 25..23 (`010` signed offset, `011` pre-index).
fn decode_stp64(word: u32) -> Option<DecodedStp> {
    if (word >> 27) & 0b111 != 0b101 || (word >> 22) & 1 != 0 {
        return None;
    }
    let pre_index = match (word >> 23) & 0b111 {
        0b011 => true,
        0b010 => false,
        _ => return None,
    };
    let fpr = match ((word >> 30) & 0b11, (word >> 26) & 1) {
        (0b10, 0) => false,
        (0b01, 1) => true,
        _ => return None,
    };
    let imm7 = ((word >> 15) & 0x7f) as i64;
    let imm7 = if imm7 & 0x40 != 0 { imm7 - 0x80 } else { imm7 };
    Some(DecodedStp {
        fpr,
        pre_index,
        offset: imm7 * 8,
        rt: (word & 0x1f) as u8,
        rt2: ((word >> 10) & 0x1f) as u8,
        rn: ((word >> 5) & 0x1f) as u8,
    })
}

/// Decode `ADD Xd, Xn|SP, #imm12` (64-bit, unshifted): `1 0 0 100010 0
/// imm12 Rn Rd`. `MOV Xd, SP` is this form with a zero immediate.
fn decode_add_x_imm(word: u32) -> Option<(u8, u8, u32)> {
    if word & 0xffc0_0000 != 0x9100_0000 {
        return None;
    }
    Some((
        (word & 0x1f) as u8,
        ((word >> 5) & 0x1f) as u8,
        (word >> 10) & 0xfff,
    ))
}

fn read_word(image: &[u8], offset: u64) -> Option<u32> {
    let start = usize::try_from(offset).ok()?;
    let bytes = image.get(start..start.checked_add(4)?)?;
    Some(u32::from_le_bytes(bytes.try_into().ok()?))
}

/// Check that the function's first instructions are exactly the prologue the
/// frame layout (and therefore the FDE's CFI program) describes. Returns
/// whether the frame uses a frame pointer.
fn check_frame_prologue(
    function: &JitUnwindFunctionInput<'_>,
    image: &[u8],
) -> Result<bool, JitError> {
    let layout = function.layout;
    let shape = |detail: String| JitError::JitUnwindFrameShapeUnsupported {
        function: function.name.to_owned(),
        detail,
    };
    let mismatch = |detail: String| JitError::JitUnwindPrologueMismatch {
        function: function.name.to_owned(),
        detail,
    };
    if !layout.uses_frame_pointer {
        // A zero-frame leaf: the CIE's `CFA = SP + 0` and the unmodified
        // X30 describe its whole body. Anything else would need SP rows.
        if !layout.callee_saved_pairs.is_empty()
            || layout.total_frame_size != 0
            || layout.callee_saved_area_size != 0
            || layout.has_dynamic_alloc
        {
            return Err(shape(format!(
                "frame without a frame pointer has pairs={}, total={}, csa={}, dynamic={}",
                layout.callee_saved_pairs.len(),
                layout.total_frame_size,
                layout.callee_saved_area_size,
                layout.has_dynamic_alloc
            )));
        }
        return Ok(false);
    }
    let pairs = &layout.callee_saved_pairs;
    let Some(first) = pairs.first() else {
        return Err(shape("frame-pointer frame has no FP/LR pair".to_owned()));
    };
    if first.is_fpr || first.reg1.hw_enc() != 29 || first.reg2.hw_enc() != 30 {
        return Err(shape("first callee-saved pair is not X29/X30".to_owned()));
    }
    // `DwarfFde::from_layout` describes D8-D15 saves with
    // `DW_CFA_offset_extended` (DWARF 72-79) and the independent decoder
    // accepts them, but no native control yet restores an FP/SIMD
    // callee-saved pair across a JIT landing pad. Refuse such frames until
    // one does.
    if let Some(pair) = pairs.iter().find(|pair| pair.is_fpr) {
        return Err(shape(format!(
            "callee-saved FP/SIMD pair D{}/D{} is not yet covered by a native unwind control",
            pair.reg1.hw_enc(),
            pair.reg2.hw_enc()
        )));
    }
    let num_pairs = pairs.len();
    let csa = i64::from(layout.callee_saved_area_size);
    if csa != 16 * num_pairs as i64 || csa > 504 {
        return Err(shape(format!(
            "callee-saved area {csa} does not hold exactly {num_pairs} pairs in one STP pre-index"
        )));
    }
    let words_needed = (num_pairs + 1) as u64 * 4;
    if u64::from(function.code_len) < words_needed {
        return Err(mismatch(format!(
            "code length {} cannot hold the {num_pairs}-pair prologue",
            function.code_len
        )));
    }
    let word = |index: usize| {
        read_word(image, function.code_offset + index as u64 * 4)
            .ok_or_else(|| mismatch(format!("prologue word {index} is outside the image")))
    };
    let num_extra = num_pairs - 1;
    // Extra pairs from the bottom of the area upward, each stored with its
    // registers reversed; the first store allocates the whole area.
    for j in 0..num_extra {
        let pair = &pairs[num_pairs - 1 - j];
        let decoded = decode_stp64(word(j)?)
            .ok_or_else(|| mismatch(format!("prologue word {j} is not a 64-bit STP")))?;
        let expected_offset = if j == 0 { -csa } else { j as i64 * 16 };
        let expected = DecodedStp {
            fpr: pair.is_fpr,
            pre_index: j == 0,
            offset: expected_offset,
            rt: pair.reg2.hw_enc(),
            rt2: pair.reg1.hw_enc(),
            rn: 31,
        };
        if decoded != expected {
            return Err(mismatch(format!(
                "prologue word {j} decodes as {decoded:?}, layout requires {expected:?}"
            )));
        }
    }
    let fp_lr = decode_stp64(word(num_extra)?)
        .ok_or_else(|| mismatch(format!("prologue word {num_extra} is not a 64-bit STP")))?;
    let expected_fp_lr = DecodedStp {
        fpr: false,
        pre_index: num_extra == 0,
        offset: if num_extra == 0 { -csa } else { csa - 16 },
        rt: 29,
        rt2: 30,
        rn: 31,
    };
    if fp_lr != expected_fp_lr {
        return Err(mismatch(format!(
            "FP/LR store decodes as {fp_lr:?}, layout requires {expected_fp_lr:?}"
        )));
    }
    let establish = decode_add_x_imm(word(num_pairs)?);
    if establish != Some((29, 31, (csa - 16) as u32)) {
        return Err(mismatch(format!(
            "frame-pointer setup decodes as {establish:?}, layout requires ADD X29, SP, #{}",
            csa - 16
        )));
    }
    Ok(true)
}

// ---------------------------------------------------------------------------
// Table construction and relocation
// ---------------------------------------------------------------------------

fn align_image(image: &mut Vec<u8>, alignment: usize) {
    while !image.len().is_multiple_of(alignment) {
        image.push(0);
    }
}

fn to_u64(value: usize) -> u64 {
    value as u64
}

fn field_range(
    image: &[u8],
    offset: u64,
    width: usize,
) -> Result<std::ops::Range<usize>, JitError> {
    let start = usize::try_from(offset)
        .map_err(|_| table_error(format!("field offset {offset} exceeds the host")))?;
    let end = start
        .checked_add(width)
        .filter(|&end| end <= image.len())
        .ok_or_else(|| {
            table_error(format!(
                "{width}-byte field at {offset} is outside the image"
            ))
        })?;
    Ok(start..end)
}

fn apply_relocation(image: &mut [u8], relocation: &JitUnwindRelocation) -> Result<(), JitError> {
    match relocation.kind {
        JitUnwindRelocationKind::Prel32 => {
            let range = field_range(image, relocation.field_offset, 4)?;
            if image[range.clone()] != [0; 4] {
                return Err(table_error(format!(
                    "PREL32 field at {} is not an unpatched placeholder",
                    relocation.field_offset
                )));
            }
            let target = relocation.target_offset.ok_or_else(|| {
                table_error("PREL32 relocation has no in-image target".to_owned())
            })?;
            let delta = i128::from(target) - i128::from(relocation.field_offset);
            let value =
                i32::try_from(delta).map_err(|_| JitError::JitUnwindRelocationOutOfRange {
                    field_offset: relocation.field_offset,
                    target_offset: target,
                })?;
            image[range].copy_from_slice(&value.to_le_bytes());
        }
        JitUnwindRelocationKind::Abs64 => {
            let range = field_range(image, relocation.field_offset, 8)?;
            if image[range.clone()] != [0; 8] {
                return Err(table_error(format!(
                    "ABS64 slot at {} is not an unpatched placeholder",
                    relocation.field_offset
                )));
            }
            let address = relocation
                .target_address
                .ok_or_else(|| table_error("ABS64 relocation has no absolute target".to_owned()))?;
            image[range].copy_from_slice(&address.to_le_bytes());
        }
    }
    Ok(())
}

/// Append LSDAs, the personality slot and a terminated `.eh_frame` to
/// `image`, bind every pointer field, and independently re-decode the result.
///
/// `personality` must be `Some` exactly when a function carries an LSDA, and
/// must name the module's single personality routine.
pub(crate) fn append_aarch64_jit_unwind_tables(
    image: &mut Vec<u8>,
    functions: &[JitUnwindFunctionInput<'_>],
    personality: Option<JitPersonalityBinding>,
) -> Result<JitUnwindManifest, JitError> {
    if functions.is_empty() {
        return Err(table_error("no published function to describe".to_owned()));
    }
    let required = module_personality(functions)?;
    match (&required, &personality) {
        (None, None) => {}
        (Some(required), Some(binding))
            if canonical_personality_symbol(&binding.symbol) == required.as_str()
                && binding.address != 0 => {}
        _ => {
            return Err(table_error(format!(
                "personality binding {:?} does not match the module requirement {required:?}",
                personality.as_ref().map(|binding| &binding.symbol)
            )));
        }
    }
    let code_end = image.len();
    for function in functions {
        let end = function
            .code_offset
            .checked_add(u64::from(function.code_len))
            .filter(|&end| end <= to_u64(code_end) && function.code_len != 0);
        if end.is_none() {
            return Err(table_error(format!(
                "function `{}` range [{}, +{}) is outside the code image of {code_end} bytes",
                function.name, function.code_offset, function.code_len
            )));
        }
    }
    let frame_pointer = functions
        .iter()
        .map(|function| check_frame_prologue(function, image))
        .collect::<Result<Vec<_>, _>>()?;
    let module_has_eh = required.is_some();

    // LSDAs: the real table of each EH function and, when the module carries
    // EH, a no-handler filler for every other frame (a zPLR CIE gives every
    // FDE an LSDA field; the filler can only say "keep unwinding").
    align_image(image, 8);
    let mut lsda_offsets = vec![None; functions.len()];
    let mut lsda_filler = vec![false; functions.len()];
    if let Some(personality) = required.as_deref() {
        for (index, function) in functions.iter().enumerate() {
            let bytes = match function.lsda {
                Some((bytes, _)) => bytes.to_vec(),
                None => {
                    lsda_filler[index] = true;
                    generate_lsda_from_pads(personality, &[], &[(0, function.code_len, 0)])
                        .map_err(|error| {
                            table_error(format!(
                                "filler LSDA for `{}` is invalid: {error}",
                                function.name
                            ))
                        })?
                }
            };
            align_image(image, 4);
            lsda_offsets[index] = Some(to_u64(image.len()));
            image.extend_from_slice(&bytes);
        }
    }
    align_image(image, 8);
    let personality_slot_offset = module_has_eh.then(|| {
        let offset = to_u64(image.len());
        image.extend_from_slice(&[0; 8]);
        offset
    });

    let mut cfi = if module_has_eh {
        DwarfCfiSection::new_aarch64_elf_with_eh()
    } else {
        DwarfCfiSection::new_aarch64_elf()
    };
    for (index, function) in functions.iter().enumerate() {
        let mut fde = if frame_pointer[index] {
            DwarfFde::from_layout(function.layout, 0, function.code_len, 0)
        } else {
            DwarfFde {
                function_offset: 0,
                function_length: function.code_len,
                symbol_index: 0,
                instructions: Vec::new(),
                lsda_pointer: None,
            }
        };
        if module_has_eh {
            fde = fde.with_lsda();
        }
        cfi.add_fde(fde);
    }
    let section = cfi.to_bytes();
    crate::dwarf_cfi_decode_check::verify_eh_frame_roundtrip(&cfi, &section)
        .map_err(|error| table_error(error.to_string()))?;
    align_image(image, 8);
    let eh_frame_offset = to_u64(image.len());
    image.extend_from_slice(&section);

    let pc_fields = cfi.fde_pc_begin_relocation_offsets();
    let lsda_fields = cfi.fde_lsda_relocation_offsets();
    if pc_fields.len() != functions.len() || (module_has_eh && lsda_fields.len() != functions.len())
    {
        return Err(table_error(format!(
            "section reports {} pc_begin and {} LSDA fields for {} functions",
            pc_fields.len(),
            lsda_fields.len(),
            functions.len()
        )));
    }
    let mut relocations = Vec::with_capacity(functions.len() * 2 + 2);
    let mut records = Vec::with_capacity(functions.len());
    for (index, function) in functions.iter().enumerate() {
        let pc_field = eh_frame_offset + u64::from(pc_fields[index]);
        relocations.push(JitUnwindRelocation {
            field_offset: pc_field,
            kind: JitUnwindRelocationKind::Prel32,
            target: JitUnwindRelocationTarget::FunctionEntry {
                function: function.name.to_owned(),
            },
            target_offset: Some(function.code_offset),
            target_address: None,
        });
        if let Some(lsda_offset) = lsda_offsets[index] {
            relocations.push(JitUnwindRelocation {
                field_offset: eh_frame_offset + u64::from(lsda_fields[index]),
                kind: JitUnwindRelocationKind::Prel32,
                target: JitUnwindRelocationTarget::Lsda {
                    function: function.name.to_owned(),
                },
                target_offset: Some(lsda_offset),
                target_address: None,
            });
        }
        records.push(JitUnwindFunctionRecord {
            function: function.name.to_owned(),
            code_offset: function.code_offset,
            code_len: function.code_len,
            // The FDE's pc_begin field follows its length and CIE pointer.
            fde_offset: pc_field - 8,
            lsda_offset: lsda_offsets[index],
            lsda_is_filler: lsda_filler[index],
            frame_pointer: frame_pointer[index],
        });
    }
    if let (Some(binding), Some(slot)) = (&personality, personality_slot_offset) {
        let field = cfi
            .cie_personality_relocation_offset()
            .ok_or_else(|| table_error("EH module CIE has no personality field".to_owned()))?;
        relocations.push(JitUnwindRelocation {
            field_offset: eh_frame_offset + u64::from(field),
            kind: JitUnwindRelocationKind::Prel32,
            target: JitUnwindRelocationTarget::PersonalitySlot,
            target_offset: Some(slot),
            target_address: None,
        });
        relocations.push(JitUnwindRelocation {
            field_offset: slot,
            kind: JitUnwindRelocationKind::Abs64,
            target: JitUnwindRelocationTarget::PersonalityRoutine {
                symbol: binding.symbol.clone(),
            },
            target_offset: None,
            target_address: Some(binding.address),
        });
    }
    for relocation in &relocations {
        apply_relocation(image, relocation)?;
    }
    let manifest = JitUnwindManifest {
        eh_frame_offset,
        eh_frame_len: to_u64(section.len()),
        personality,
        personality_slot_offset,
        functions: records,
        relocations,
        registration_scheme: host_registration_scheme(),
    };
    verify_relocated_unwind_tables(image, &manifest)?;
    Ok(manifest)
}

// ---------------------------------------------------------------------------
// Independent decode of the relocated tables
// ---------------------------------------------------------------------------

struct Cursor<'a> {
    image: &'a [u8],
    position: usize,
    end: usize,
}

/// Fixed-width view of `slice`, which the caller has already bounded to
/// exactly `N` bytes. A length mismatch is a decoder defect and is reported
/// as a table error rather than a panic.
fn fixed<const N: usize>(slice: &[u8], what: &str) -> Result<[u8; N], JitError> {
    <[u8; N]>::try_from(slice)
        .map_err(|_| table_error(format!("{what}: expected {N} bytes, found {}", slice.len())))
}

impl<'a> Cursor<'a> {
    fn new(image: &'a [u8], position: usize, end: usize) -> Result<Self, JitError> {
        if position > end || end > image.len() {
            return Err(table_error(format!(
                "decode window [{position}, {end}) is outside the image"
            )));
        }
        Ok(Self {
            image,
            position,
            end,
        })
    }

    fn bytes(&mut self, count: usize) -> Result<&'a [u8], JitError> {
        let end = self
            .position
            .checked_add(count)
            .filter(|&end| end <= self.end)
            .ok_or_else(|| table_error(format!("truncated at image offset {}", self.position)))?;
        let slice = &self.image[self.position..end];
        self.position = end;
        Ok(slice)
    }

    fn u8(&mut self) -> Result<u8, JitError> {
        Ok(self.bytes(1)?[0])
    }

    fn u32(&mut self) -> Result<u32, JitError> {
        Ok(u32::from_le_bytes(fixed(self.bytes(4)?, "u32 field")?))
    }

    /// Decode a PC-relative sdata4 field to the image offset it designates.
    fn pcrel_sdata4(&mut self) -> Result<u64, JitError> {
        let field = self.position as i128;
        let value = i32::from_le_bytes(fixed(self.bytes(4)?, "sdata4 field")?);
        u64::try_from(field + i128::from(value)).map_err(|_| {
            table_error(format!(
                "PC-relative field at {field} points below the image"
            ))
        })
    }

    fn uleb(&mut self) -> Result<u64, JitError> {
        let mut value = 0u64;
        let mut shift = 0u32;
        loop {
            let byte = self.u8()?;
            if shift > 63 {
                return Err(table_error("ULEB128 overflow".to_owned()));
            }
            value |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return Ok(value);
            }
            shift += 7;
        }
    }

    fn sleb(&mut self) -> Result<i64, JitError> {
        let mut value = 0i64;
        let mut shift = 0u32;
        loop {
            let byte = self.u8()?;
            if shift > 63 {
                return Err(table_error("SLEB128 overflow".to_owned()));
            }
            value |= i64::from(byte & 0x7f) << shift;
            shift += 7;
            if byte & 0x80 == 0 {
                if shift < 64 && byte & 0x40 != 0 {
                    value |= -1i64 << shift;
                }
                return Ok(value);
            }
        }
    }
}

fn expect_eq<T: PartialEq + std::fmt::Debug>(
    what: &str,
    actual: T,
    expected: T,
) -> Result<(), JitError> {
    if actual == expected {
        Ok(())
    } else {
        Err(table_error(format!(
            "{what}: decoded {actual:?}, expected {expected:?}"
        )))
    }
}

/// Re-read the relocated `.eh_frame` and each LSDA from `image` and check
/// every resolved pointer and range against `manifest`.
pub(crate) fn verify_relocated_unwind_tables(
    image: &[u8],
    manifest: &JitUnwindManifest,
) -> Result<(), JitError> {
    let section_start = usize::try_from(manifest.eh_frame_offset)
        .map_err(|_| table_error("eh_frame offset exceeds the host".to_owned()))?;
    let section_end = usize::try_from(manifest.eh_frame_len)
        .ok()
        .and_then(|len| section_start.checked_add(len))
        .ok_or_else(|| table_error("eh_frame extent overflows".to_owned()))?;
    let mut section = Cursor::new(image, section_start, section_end)?;
    let has_personality = manifest.personality.is_some();

    // CIE.
    let cie_start = section.position;
    let cie_len = section.u32()? as usize;
    let cie_end = section.position + cie_len;
    let mut cie = Cursor::new(image, section.position, cie_end)?;
    expect_eq("CIE id", cie.u32()?, 0)?;
    expect_eq("CIE version", cie.u8()?, 1)?;
    let augmentation: &[u8] = if has_personality { b"zPLR\0" } else { b"zR\0" };
    expect_eq(
        "CIE augmentation",
        cie.bytes(augmentation.len())?,
        augmentation,
    )?;
    expect_eq("code alignment", cie.uleb()?, 4)?;
    expect_eq("data alignment", cie.sleb()?, -8)?;
    expect_eq("return-address register", cie.uleb()?, 30)?;
    let augmentation_len = cie.uleb()? as usize;
    let augmentation_end = cie.position + augmentation_len;
    if has_personality {
        expect_eq("personality encoding", cie.u8()?, INDIRECT_PCREL_SDATA4)?;
        let slot = cie.pcrel_sdata4()?;
        expect_eq(
            "personality slot",
            Some(slot),
            manifest.personality_slot_offset,
        )?;
        let slot_range = field_range(image, slot, 8)?;
        let address = u64::from_le_bytes(fixed(&image[slot_range], "personality slot")?);
        expect_eq(
            "personality address",
            Some(address),
            manifest.personality.as_ref().map(|binding| binding.address),
        )?;
        expect_eq("LSDA encoding", cie.u8()?, PCREL_SDATA4)?;
    }
    expect_eq("FDE pointer encoding", cie.u8()?, PCREL_SDATA4)?;
    expect_eq("CIE augmentation length", cie.position, augmentation_end)?;
    // DW_CFA_def_cfa SP, 0, then DW_CFA_nop padding.
    expect_eq(
        "CIE initial instructions",
        cie.bytes(3)?,
        &[0x0c, 31, 0][..],
    )?;
    while cie.position < cie_end {
        expect_eq("CIE padding", cie.u8()?, 0)?;
    }
    section.position = cie_end;

    // One FDE per function, in manifest order.
    for record in &manifest.functions {
        let fde_start = section.position;
        expect_eq(
            &format!("FDE offset of `{}`", record.function),
            to_u64(fde_start),
            record.fde_offset,
        )?;
        let fde_len = section.u32()? as usize;
        if fde_len == 0 {
            return Err(table_error(format!(
                "section terminates before the FDE of `{}`",
                record.function
            )));
        }
        let fde_end = section.position + fde_len;
        let mut fde = Cursor::new(image, section.position, fde_end)?;
        let pointer_field = fde.position;
        expect_eq(
            "FDE CIE pointer",
            fde.u32()? as usize,
            pointer_field - cie_start,
        )?;
        expect_eq(
            &format!("pc_begin of `{}`", record.function),
            fde.pcrel_sdata4()?,
            record.code_offset,
        )?;
        expect_eq(
            &format!("pc_range of `{}`", record.function),
            fde.u32()?,
            record.code_len,
        )?;
        let augmentation_len = fde.uleb()?;
        if has_personality {
            expect_eq("FDE augmentation length", augmentation_len, 4)?;
            let lsda = fde.pcrel_sdata4()?;
            expect_eq(
                &format!("LSDA of `{}`", record.function),
                Some(lsda),
                record.lsda_offset,
            )?;
            verify_lsda(image, record)?;
        } else {
            expect_eq("FDE augmentation length", augmentation_len, 0)?;
            expect_eq("LSDA without personality", record.lsda_offset, None)?;
        }
        let rules = decode_cfa_program(&mut fde, &record.function)?;
        verify_frame_rules(image, record, &rules)?;
        section.position = fde_end;
    }
    expect_eq("eh_frame terminator", section.u32()?, 0)?;
    expect_eq("eh_frame end", section.position, section_end)?;
    Ok(())
}

/// Register rules in effect after an FDE's CFA program has run.
#[derive(Debug, Clone, PartialEq, Eq)]
struct CfaRules {
    cfa_register: u64,
    cfa_offset: u64,
    /// DWARF register number -> save slot offset from the CFA.
    saves: std::collections::BTreeMap<u64, i64>,
    /// Code offset (bytes from the function entry) of the last rule change.
    last_row: u64,
}

impl CfaRules {
    /// The CIE's initial rule: `CFA = SP + 0`, nothing saved.
    fn initial() -> Self {
        Self {
            cfa_register: 31,
            cfa_offset: 0,
            saves: std::collections::BTreeMap::new(),
            last_row: 0,
        }
    }
}

/// Decode an FDE's CFA program (DWARF 5, section 6.4.2) from its bytes,
/// starting from the CIE rule the section check above pinned (`CFA = SP + 0`,
/// code alignment 4, data alignment -8). Only the row, CFA and save
/// instructions a JIT FDE may carry are accepted.
fn decode_cfa_program(fde: &mut Cursor<'_>, name: &str) -> Result<CfaRules, JitError> {
    const CODE_ALIGNMENT: u64 = 4;
    const DATA_ALIGNMENT: i64 = -8;
    let mut rules = CfaRules::initial();
    let mut location = 0u64;
    let advance = |location: &mut u64, delta: u64| {
        *location = delta
            .checked_mul(CODE_ALIGNMENT)
            .and_then(|bytes| location.checked_add(bytes))
            .ok_or_else(|| table_error(format!("CFA program of `{name}` advances past 2^64")))?;
        Ok::<(), JitError>(())
    };
    let save = |rules: &mut CfaRules, register: u64, factored: u64, location: u64| {
        let offset = i64::try_from(factored)
            .ok()
            .and_then(|factored| factored.checked_mul(DATA_ALIGNMENT))
            .ok_or_else(|| table_error(format!("CFA save offset of `{name}` overflows")))?;
        if rules.saves.insert(register, offset).is_some() {
            return Err(table_error(format!(
                "CFA program of `{name}` saves DWARF register {register} twice"
            )));
        }
        rules.last_row = location;
        Ok(())
    };
    while fde.position < fde.end {
        let opcode = fde.u8()?;
        match opcode >> 6 {
            // DW_CFA_advance_loc
            0b01 => advance(&mut location, u64::from(opcode & 0x3f))?,
            // DW_CFA_offset: 6-bit register, factored ULEB128 offset
            0b10 => {
                let factored = fde.uleb()?;
                save(&mut rules, u64::from(opcode & 0x3f), factored, location)?;
            }
            0b11 => {
                return Err(table_error(format!(
                    "CFA program of `{name}` uses DW_CFA_restore"
                )));
            }
            _ => match opcode {
                // DW_CFA_nop
                0x00 => {}
                // DW_CFA_advance_loc1 / DW_CFA_advance_loc2
                0x02 => advance(&mut location, u64::from(fde.u8()?))?,
                0x03 => {
                    let delta =
                        u16::from_le_bytes(fixed(fde.bytes(2)?, "DW_CFA_advance_loc2 delta")?);
                    advance(&mut location, u64::from(delta))?;
                }
                // DW_CFA_offset_extended: ULEB128 register and factored offset
                0x05 => {
                    let register = fde.uleb()?;
                    let factored = fde.uleb()?;
                    save(&mut rules, register, factored, location)?;
                }
                // DW_CFA_def_cfa: ULEB128 register and offset
                0x0c => {
                    rules.cfa_register = fde.uleb()?;
                    rules.cfa_offset = fde.uleb()?;
                    rules.last_row = location;
                }
                // DW_CFA_def_cfa_offset
                0x0e => {
                    rules.cfa_offset = fde.uleb()?;
                    rules.last_row = location;
                }
                other => {
                    return Err(table_error(format!(
                        "CFA program of `{name}` uses unsupported opcode {other:#04x}"
                    )));
                }
            },
        }
    }
    Ok(rules)
}

/// Decode a frame-pointer prologue from its instruction words alone: every
/// leading `STP` to `[SP]` (X or D pair, pre-index or signed offset), then
/// `ADD X29, SP, #imm`. Returns the saved DWARF registers with their offsets
/// from the CFA (the entry SP), X29's offset from the CFA, and the prologue
/// length in bytes. No frame layout is consulted.
fn decode_prologue_frame(
    image: &[u8],
    record: &JitUnwindFunctionRecord,
) -> Result<(std::collections::BTreeMap<u64, i64>, i64, u64), JitError> {
    let name = &record.function;
    let mut stack_pointer = 0i64;
    let mut saves = std::collections::BTreeMap::new();
    for index in 0..u64::from(record.code_len / 4).min(64) {
        let word = read_word(image, record.code_offset + index * 4).ok_or_else(|| {
            table_error(format!(
                "prologue word {index} of `{name}` is outside the image"
            ))
        })?;
        if let Some(store) = decode_stp64(word) {
            if store.rn != 31 || (!store.fpr && (store.rt == 31 || store.rt2 == 31)) {
                return Err(table_error(format!(
                    "prologue word {index} of `{name}` is not a register-pair save to SP"
                )));
            }
            let slot = if store.pre_index {
                stack_pointer += store.offset;
                stack_pointer
            } else {
                stack_pointer + store.offset
            };
            let dwarf_base = if store.fpr { 64 } else { 0 };
            for (register, offset) in [(store.rt, slot), (store.rt2, slot + 8)] {
                if saves
                    .insert(dwarf_base + u64::from(register), offset)
                    .is_some()
                {
                    return Err(table_error(format!(
                        "prologue of `{name}` saves register {register} twice"
                    )));
                }
            }
            continue;
        }
        if let Some((29, 31, immediate)) = decode_add_x_imm(word) {
            return Ok((saves, stack_pointer + i64::from(immediate), (index + 1) * 4));
        }
        return Err(table_error(format!(
            "prologue word {index} of `{name}` ({word:#010x}) is neither a pair save nor ADD X29, SP"
        )));
    }
    Err(table_error(format!(
        "prologue of `{name}` never establishes X29"
    )))
}

/// Check the decoded CFA rules against the instructions they describe.
///
/// A zero-frame leaf must keep the CIE rule for its whole body. A
/// frame-pointer frame must, by the end of its prologue, define the CFA as
/// `X29 + k` where the prologue set `X29 = CFA - k`, and must describe exactly
/// the registers the prologue stored, at the slots it stored them to.
fn verify_frame_rules(
    image: &[u8],
    record: &JitUnwindFunctionRecord,
    rules: &CfaRules,
) -> Result<(), JitError> {
    let name = &record.function;
    if !record.frame_pointer {
        return expect_eq(
            &format!("CFA rules of the zero-frame leaf `{name}`"),
            rules,
            &CfaRules::initial(),
        );
    }
    let (saves, frame_pointer, prologue_len) = decode_prologue_frame(image, record)?;
    expect_eq(&format!("CFA register of `{name}`"), rules.cfa_register, 29)?;
    expect_eq(
        &format!("CFA offset of `{name}`"),
        i64::try_from(rules.cfa_offset).ok(),
        frame_pointer.checked_neg(),
    )?;
    expect_eq(
        &format!("saved registers of `{name}`"),
        &rules.saves,
        &saves,
    )?;
    for register in [29, 30] {
        if !saves.contains_key(&register) {
            return Err(table_error(format!(
                "prologue of `{name}` does not save X{register}"
            )));
        }
    }
    if rules.last_row > prologue_len {
        return Err(table_error(format!(
            "CFA program of `{name}` completes at {} after its {prologue_len}-byte prologue",
            rules.last_row
        )));
    }
    Ok(())
}

/// Decode one LSDA and check that its call-site table covers exactly
/// `[0, code_len)` in order, that every landing pad lies inside the function,
/// that every action chain holds only cleanup or positive catch filters, and
/// that every referenced type-table entry is the catch-all NULL (this path has
/// no typeinfo relocation authority).
fn verify_lsda(image: &[u8], record: &JitUnwindFunctionRecord) -> Result<(), JitError> {
    let offset = record
        .lsda_offset
        .ok_or_else(|| table_error(format!("`{}` has no LSDA", record.function)))?;
    let start = usize::try_from(offset)
        .map_err(|_| table_error("LSDA offset exceeds the host".to_owned()))?;
    let name = &record.function;
    let mut lsda = Cursor::new(image, start, image.len())?;
    expect_eq("LPStart encoding", lsda.u8()?, OMIT)?;
    let type_table_end = match lsda.u8()? {
        OMIT => None,
        INDIRECT_PCREL_SDATA4 => {
            let base = usize::try_from(lsda.uleb()?)
                .map_err(|_| table_error("TType base exceeds the host".to_owned()))?;
            Some(
                lsda.position
                    .checked_add(base)
                    .ok_or_else(|| table_error("TType base overflows".to_owned()))?,
            )
        }
        other => {
            return Err(table_error(format!(
                "LSDA of `{name}` has TType encoding {other:#x}"
            )));
        }
    };
    expect_eq("call-site encoding", lsda.u8()?, ULEB128)?;
    let table_len = usize::try_from(lsda.uleb()?)
        .map_err(|_| table_error("call-site table length exceeds the host".to_owned()))?;
    let table_end = lsda
        .position
        .checked_add(table_len)
        .ok_or_else(|| table_error("call-site table overflows".to_owned()))?;
    let mut covered = 0u64;
    let mut actions = Vec::new();
    while lsda.position < table_end {
        let region_start = lsda.uleb()?;
        let region_len = lsda.uleb()?;
        let landing_pad = lsda.uleb()?;
        let action = lsda.uleb()?;
        expect_eq("call-site region start", region_start, covered)?;
        if region_len == 0 {
            return Err(table_error(format!(
                "LSDA of `{name}` has an empty call-site region"
            )));
        }
        if landing_pad >= u64::from(record.code_len) {
            return Err(table_error(format!(
                "LSDA of `{name}` has landing pad {landing_pad} outside [0, {})",
                record.code_len
            )));
        }
        if landing_pad == 0 && action != 0 {
            return Err(table_error(format!(
                "LSDA of `{name}` has an action without a landing pad"
            )));
        }
        if record.lsda_is_filler && landing_pad != 0 {
            return Err(table_error(format!(
                "filler LSDA of `{name}` names a landing pad"
            )));
        }
        covered = region_start
            .checked_add(region_len)
            .ok_or_else(|| table_error("call-site region overflows".to_owned()))?;
        if action != 0 {
            actions.push(action);
        }
    }
    expect_eq("call-site table end", lsda.position, table_end)?;
    expect_eq(
        &format!("call-site coverage of `{name}`"),
        covered,
        u64::from(record.code_len),
    )?;

    // Action chains start at 1-based byte offsets into the action table,
    // which follows the call-site table. Each next-record displacement is
    // relative to its own field.
    let mut max_filter = 0u64;
    for action in actions {
        let mut position = usize::try_from(action - 1)
            .ok()
            .and_then(|offset| table_end.checked_add(offset))
            .ok_or_else(|| table_error("action offset overflows".to_owned()))?;
        let mut terminated = false;
        for _ in 0..64 {
            let mut action_record = Cursor::new(image, position, image.len())?;
            let filter = action_record.sleb()?;
            let next_field = action_record.position;
            let next = action_record.sleb()?;
            if filter < 0 {
                return Err(table_error(format!(
                    "LSDA of `{name}` uses exception-specification filter {filter}"
                )));
            }
            max_filter = max_filter.max(filter as u64);
            if next == 0 {
                terminated = true;
                break;
            }
            position = i64::try_from(next_field)
                .ok()
                .and_then(|field| field.checked_add(next))
                .and_then(|target| usize::try_from(target).ok())
                .ok_or_else(|| table_error("action chain leaves the image".to_owned()))?;
        }
        if !terminated {
            return Err(table_error(format!(
                "LSDA of `{name}` has an action chain longer than 64 records"
            )));
        }
    }
    if max_filter > 0 {
        let end = type_table_end.ok_or_else(|| {
            table_error(format!(
                "LSDA of `{name}` has catch actions but no type table"
            ))
        })?;
        for index in 1..=max_filter as usize {
            let entry_start = end
                .checked_sub(4 * index)
                .filter(|&entry| entry >= table_end)
                .ok_or_else(|| table_error(format!("type-table entry {index} underflows")))?;
            let bytes = image
                .get(entry_start..entry_start + 4)
                .ok_or_else(|| table_error(format!("type-table entry {index} is outside")))?;
            if bytes != [0; 4] {
                return Err(table_error(format!(
                    "LSDA of `{name}` type-table entry {index} is a typeinfo without relocation authority"
                )));
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Registration with the platform unwinder
// ---------------------------------------------------------------------------

/// Layout of `struct dwarf_eh_bases` shared by libgcc and libunwind.
#[repr(C)]
#[derive(Default)]
struct DwarfEhBases {
    tbase: usize,
    dbase: usize,
    func: usize,
}

type RegisterFrameFn = unsafe extern "C" fn(*const u8);
type FindFdeFn = unsafe extern "C" fn(*const u8, *mut DwarfEhBases) -> *const u8;

// Constructed only where registration is implemented; elsewhere every
// `unwinder_entry_points` call refuses before one exists.
#[cfg_attr(
    not(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))),
    allow(dead_code)
)]
struct UnwinderEntryPoints {
    register: RegisterFrameFn,
    deregister: RegisterFrameFn,
    find_fde: FindFdeFn,
}

#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn unwinder_entry_points() -> Result<UnwinderEntryPoints, JitError> {
    let lookup = |name: &str| {
        crate::jit::lookup_process_symbol(name).ok_or_else(|| {
            JitError::JitUnwindRegistrationUnavailable {
                detail: format!("the process unwinder does not export `{name}`"),
            }
        })
    };
    let register = lookup("__register_frame")?;
    let deregister = lookup("__deregister_frame")?;
    let find_fde = lookup("_Unwind_Find_FDE")?;
    // SAFETY: these are the documented C entry points of the process
    // unwinder (libunwind on Darwin, libgcc_s on Linux) with exactly these
    // signatures; dlsym returned their addresses.
    unsafe {
        Ok(UnwinderEntryPoints {
            register: std::mem::transmute::<*const u8, RegisterFrameFn>(register),
            deregister: std::mem::transmute::<*const u8, RegisterFrameFn>(deregister),
            find_fde: std::mem::transmute::<*const u8, FindFdeFn>(find_fde),
        })
    }
}

#[cfg(not(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux"))))]
fn unwinder_entry_points() -> Result<UnwinderEntryPoints, JitError> {
    Err(JitError::JitUnwindRegistrationUnavailable {
        detail: format!(
            "in-memory unwind registration is implemented for AArch64 Darwin and Linux only, not {}-{}",
            std::env::consts::ARCH,
            std::env::consts::OS
        ),
    })
}

/// The FDE the process unwinder currently associates with `pc`, if any.
///
/// This is a diagnostic readback of the live unwinder state (it calls
/// `_Unwind_Find_FDE`); a `None` result means the unwinder has no dynamic or
/// static FDE for that address.
pub fn registered_unwind_fde_for_pc(pc: u64) -> Result<Option<u64>, JitError> {
    let entry = unwinder_entry_points()?;
    let mut bases = DwarfEhBases::default();
    // SAFETY: `_Unwind_Find_FDE` only reads unwinder tables; `bases` is a
    // valid out-parameter of the shared C layout.
    let fde = unsafe { (entry.find_fde)(pc as usize as *const u8, &mut bases) };
    Ok((!fde.is_null()).then_some(fde as u64))
}

/// Live registration of one image's unwind tables.
///
/// Dropping (or [`Self::unregister`]) deregisters every handle it
/// registered. The owner must deregister before unmapping the image.
#[derive(Default)]
pub(crate) struct EhFrameJitUnwindRegistration {
    /// Addresses passed to `__register_frame` (FDEs on Darwin, the section
    /// start on Linux).
    handles: Vec<usize>,
    deregister: Option<RegisterFrameFn>,
}

// SAFETY: the registration holds only addresses inside an immutable
// read-execute mapping plus an unwinder entry point; moving it between
// threads moves only the obligation to deregister.
unsafe impl Send for EhFrameJitUnwindRegistration {}
// SAFETY: shared references expose only `is_active`.
unsafe impl Sync for EhFrameJitUnwindRegistration {}

impl EhFrameJitUnwindRegistration {
    /// Register `manifest`'s tables, which live in the read-execute mapping
    /// at `base`, and read every function's FDE back from the unwinder.
    pub(crate) fn register(
        base: *const u8,
        manifest: &JitUnwindManifest,
    ) -> Result<Self, JitError> {
        let entry = unwinder_entry_points()?;
        if manifest.registration_scheme != host_registration_scheme() {
            return Err(JitError::JitUnwindRegistrationUnavailable {
                detail: format!(
                    "tables were built for {:?} registration, this host uses {:?}",
                    manifest.registration_scheme,
                    host_registration_scheme()
                ),
            });
        }
        let base = base as usize;
        let at = |offset: u64| base + offset as usize;
        let mut registration = Self {
            handles: Vec::new(),
            deregister: Some(entry.deregister),
        };
        let handles: Vec<usize> = match manifest.registration_scheme {
            JitUnwindRegistrationScheme::PerFde => manifest
                .functions
                .iter()
                .map(|record| at(record.fde_offset))
                .collect(),
            JitUnwindRegistrationScheme::WholeSection => vec![at(manifest.eh_frame_offset)],
        };
        for handle in handles {
            // SAFETY: `handle` addresses a decoded, terminated FDE/section
            // inside the caller's live read-execute mapping, which outlives
            // this registration (the owner deregisters before unmapping).
            unsafe { (entry.register)(handle as *const u8) };
            registration.handles.push(handle);
        }
        for record in &manifest.functions {
            let pc = at(record.code_offset);
            let mut bases = DwarfEhBases::default();
            // SAFETY: read-only unwinder lookup with a valid out-parameter.
            let observed = unsafe { (entry.find_fde)(pc as *const u8, &mut bases) } as usize;
            let expected = at(record.fde_offset);
            if observed != expected || bases.func != pc {
                // Dropping `registration` deregisters what was registered.
                return Err(JitError::JitUnwindRegistrationNotObserved {
                    function: record.function.clone(),
                    expected_fde: expected as u64,
                    observed_fde: observed as u64,
                    observed_function: bases.func as u64,
                });
            }
        }
        Ok(registration)
    }

    /// Whether tables are currently registered.
    pub(crate) fn is_active(&self) -> bool {
        !self.handles.is_empty()
    }

    /// Deregister every registered handle (idempotent).
    pub(crate) fn unregister(&mut self) {
        if let Some(deregister) = self.deregister {
            for handle in self.handles.drain(..).rev() {
                // SAFETY: `handle` was registered by this value and the
                // mapping is still live (callers deregister before unmap).
                unsafe { deregister(handle as *const u8) };
            }
        }
        self.handles.clear();
    }
}

impl Drop for EhFrameJitUnwindRegistration {
    fn drop(&mut self) {
        self.unregister();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// This file's fixtures are hand-built and carry no codegen license
    /// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
    /// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
    /// them passes because it was silently refused.
    // UNUSED, and that is a flag, not a tidy-up: no test in this module calls
    // `with_codegen_license`, so by this helper's own doc above its fixtures
    // are taking the DEFAULT refusal rather than stating `Permit`. Whoever
    // owns WS7.5 (`5daaaa095`) should either wire it into the compiles here or
    // delete it with a note. Allowed rather than removed so the intent stays
    // visible; `-D dead-code` otherwise fails seven gate legs that only need
    // this crate's lib tests to compile. 2026-10-15.
    #[allow(dead_code)]
    fn permit_unlicensed() -> crate::CodegenLicensePolicy {
        crate::CodegenLicensePolicy::default().with_unlicensed(crate::UnlicensedBodyPolicy::Permit)
    }
    use crate::frame::CalleeSavedPair;
    use trust_cg_ir::aarch64_regs::{X19, X20, X29, X30};

    fn fp_layout(extra: &[(trust_cg_ir::regs::PReg, trust_cg_ir::regs::PReg)]) -> FrameLayout {
        let mut pairs = vec![CalleeSavedPair {
            reg1: X29,
            reg2: X30,
            fp_offset: 0,
            is_fpr: false,
        }];
        for (reg1, reg2) in extra {
            pairs.push(CalleeSavedPair {
                reg1: *reg1,
                reg2: *reg2,
                fp_offset: 0,
                is_fpr: false,
            });
        }
        let csa = 16 * pairs.len() as u32;
        FrameLayout {
            callee_saved_pairs: pairs,
            callee_saved_area_size: csa,
            spill_area_size: 0,
            local_area_size: 0,
            outgoing_arg_area_size: 0,
            total_frame_size: csa,
            uses_frame_pointer: true,
            is_leaf: false,
            uses_red_zone: false,
            fp_to_spill_offset: 0,
            has_dynamic_alloc: false,
        }
    }

    fn leaf_layout() -> FrameLayout {
        FrameLayout {
            callee_saved_pairs: Vec::new(),
            callee_saved_area_size: 0,
            spill_area_size: 0,
            local_area_size: 0,
            outgoing_arg_area_size: 0,
            total_frame_size: 0,
            uses_frame_pointer: false,
            is_leaf: true,
            uses_red_zone: true,
            fp_to_spill_offset: 0,
            has_dynamic_alloc: false,
        }
    }

    fn words(words: &[u32]) -> Vec<u8> {
        words.iter().flat_map(|word| word.to_le_bytes()).collect()
    }

    // stp x29, x30, [sp, #-16]!; add x29, sp, #0; bl #0; ldp; ret
    const MINIMAL: [u32; 5] = [
        0xa9bf_7bfd,
        0x9100_03fd,
        0x9400_0000,
        0xa8c1_7bfd,
        0xd65f_03c0,
    ];
    // stp x20, x19, [sp, #-32]!; stp x29, x30, [sp, #16]; add x29, sp, #16; ret
    const TWO_PAIRS: [u32; 4] = [0xa9be_4ff4, 0xa901_7bfd, 0x9100_43fd, 0xd65f_03c0];

    fn binding() -> JitPersonalityBinding {
        JitPersonalityBinding {
            symbol: "__gxx_personality_v0".to_owned(),
            address: 0x1234_5678_9abc,
            source: JitPersonalitySource::ExplicitBinding,
        }
    }

    fn cleanup_lsda(code_len: u32) -> Vec<u8> {
        use crate::exception_handling::LandingPadDesc;
        generate_lsda_from_pads(
            "__gxx_personality_v0",
            &[LandingPadDesc::cleanup(12)],
            &[(0, 8, 0), (8, 4, 12), (12, code_len - 12, 0)],
        )
        .unwrap()
    }

    #[test]
    fn prologue_decode_accepts_the_emitted_shapes_and_rejects_drift() {
        let minimal = fp_layout(&[]);
        let image = words(&MINIMAL);
        let input = JitUnwindFunctionInput {
            name: "minimal",
            code_offset: 0,
            code_len: 20,
            layout: &minimal,
            lsda: None,
        };
        assert!(check_frame_prologue(&input, &image).unwrap());
        let two = fp_layout(&[(X19, X20)]);
        let image = words(&TWO_PAIRS);
        let input = JitUnwindFunctionInput {
            name: "two",
            code_offset: 0,
            code_len: 16,
            layout: &two,
            lsda: None,
        };
        assert!(check_frame_prologue(&input, &image).unwrap());
        // Each single-field drift in the allocating store, the FP/LR store or
        // the frame-pointer setup must be refused.
        for (index, bit) in [
            (0, 15),
            (0, 0),
            (0, 10),
            (0, 24),
            (1, 15),
            (1, 5),
            (2, 10),
            (2, 0),
        ] {
            let mut drifted = TWO_PAIRS;
            drifted[index] ^= 1 << bit;
            let image = words(&drifted);
            assert!(
                matches!(
                    check_frame_prologue(&input, &image),
                    Err(JitError::JitUnwindPrologueMismatch { .. })
                ),
                "word {index} bit {bit}"
            );
        }
        // A frameless layout that still claims stack space is refused.
        let mut leaf = leaf_layout();
        leaf.total_frame_size = 16;
        let input = JitUnwindFunctionInput {
            name: "bad_leaf",
            code_offset: 0,
            code_len: 4,
            layout: &leaf,
            lsda: None,
        };
        assert!(matches!(
            check_frame_prologue(&input, &words(&[0xd65f_03c0])),
            Err(JitError::JitUnwindFrameShapeUnsupported { .. })
        ));
    }

    #[test]
    fn eh_tables_bind_every_pointer_and_survive_independent_decode() {
        let minimal = fp_layout(&[]);
        let leaf = leaf_layout();
        let mut image = words(&MINIMAL);
        image.extend(words(&[0xd65f_03c0]));
        let lsda = cleanup_lsda(20);
        let functions = [
            JitUnwindFunctionInput {
                name: "eh",
                code_offset: 0,
                code_len: 20,
                layout: &minimal,
                lsda: Some((&lsda, "__gxx_personality_v0")),
            },
            JitUnwindFunctionInput {
                name: "leaf",
                code_offset: 20,
                code_len: 4,
                layout: &leaf,
                lsda: None,
            },
        ];
        let manifest =
            append_aarch64_jit_unwind_tables(&mut image, &functions, Some(binding())).unwrap();
        assert!(manifest.carries_exception_handling());
        assert_eq!(manifest.functions.len(), 2);
        assert!(!manifest.functions[0].lsda_is_filler);
        assert!(manifest.functions[1].lsda_is_filler);
        assert!(manifest.functions[0].frame_pointer && !manifest.functions[1].frame_pointer);
        // Two pc_begin, two LSDA, the CIE personality field and the slot.
        assert_eq!(manifest.relocations.len(), 6);
        assert_eq!(
            manifest
                .relocations
                .iter()
                .filter(|relocation| relocation.kind == JitUnwindRelocationKind::Abs64)
                .count(),
            1
        );
        verify_relocated_unwind_tables(&image, &manifest).unwrap();

        // Every relocated field is load-bearing: corrupting any one of them
        // must be refused by the independent decoder.
        for relocation in &manifest.relocations {
            let mut corrupted = image.clone();
            let field = relocation.field_offset as usize;
            corrupted[field] ^= 0x04;
            assert!(
                verify_relocated_unwind_tables(&corrupted, &manifest).is_err(),
                "{relocation:?}"
            );
        }
        // So is the terminator and each LSDA's call-site coverage.
        let mut unterminated = image.clone();
        let end = (manifest.eh_frame_offset + manifest.eh_frame_len) as usize;
        unterminated[end - 1] = 1;
        assert!(verify_relocated_unwind_tables(&unterminated, &manifest).is_err());
        let mut truncated = image.clone();
        let lsda = manifest.functions[0].lsda_offset.unwrap() as usize;
        // Header: LPStart omit, TType omit, call-site encoding, table length;
        // the first region length follows the first region start.
        truncated[lsda + 5] ^= 0x01;
        assert!(verify_relocated_unwind_tables(&truncated, &manifest).is_err());
    }

    /// The CFA program is checked against the prologue words, not only
    /// round-tripped: each semantic mutation of the minimal FDE's program
    /// (a saved register, a save slot, the CFA register or offset, or a final
    /// row placed after the prologue) must be refused.
    #[test]
    fn cfa_program_mutations_are_refused_against_the_decoded_prologue() {
        let minimal = fp_layout(&[]);
        let lsda = cleanup_lsda(20);
        let functions = [JitUnwindFunctionInput {
            name: "eh",
            code_offset: 0,
            code_len: 20,
            layout: &minimal,
            lsda: Some((&lsda, "__gxx_personality_v0")),
        }];
        let mut image = words(&MINIMAL);
        let manifest =
            append_aarch64_jit_unwind_tables(&mut image, &functions, Some(binding())).unwrap();
        // Length, CIE pointer, pc_begin, pc_range, augmentation length and
        // the 4-byte LSDA pointer precede the program.
        let program = manifest.functions[0].fde_offset as usize + 4 + 4 + 4 + 4 + 1 + 4;
        // advance 1; def_cfa_offset 16; x29 at CFA-16; x30 at CFA-8;
        // advance 1; def_cfa x29, 16.
        let expected = [
            0x41, 0x0e, 0x10, 0x9d, 0x02, 0x9e, 0x01, 0x41, 0x0c, 0x1d, 0x10,
        ];
        assert_eq!(&image[program..program + expected.len()], &expected);
        for (index, value, what) in [
            (3, 0x9c, "X28 described in place of X29"),
            (4, 0x03, "X29 slot moved"),
            (5, 0x9f, "SP described in place of X30"),
            (6, 0x02, "X30 slot moved"),
            (7, 0x42, "final row after the prologue"),
            (9, 0x1c, "CFA based on X28"),
            (10, 0x20, "CFA offset 32"),
        ] {
            let mut mutated = image.clone();
            mutated[program + index] = value;
            assert!(
                matches!(
                    verify_relocated_unwind_tables(&mutated, &manifest),
                    Err(JitError::JitUnwindTableRejected { .. })
                ),
                "{what}"
            );
        }
        // A zero-frame leaf may carry no CFA rule at all.
        let leaf = leaf_layout();
        let leaf_functions = [JitUnwindFunctionInput {
            name: "leaf",
            code_offset: 0,
            code_len: 4,
            layout: &leaf,
            lsda: None,
        }];
        let mut leaf_image = words(&[0xd65f_03c0]);
        let leaf_manifest =
            append_aarch64_jit_unwind_tables(&mut leaf_image, &leaf_functions, None).unwrap();
        let leaf_program = leaf_manifest.functions[0].fde_offset as usize + 4 + 4 + 4 + 4 + 1;
        assert_eq!(
            &leaf_image[leaf_program..leaf_program + 2],
            &[0x00, 0x00],
            "leaf program is padding"
        );
        verify_relocated_unwind_tables(&leaf_image, &leaf_manifest).unwrap();
        // def_cfa_offset 16 would claim a stack allocation the leaf never made.
        leaf_image[leaf_program..leaf_program + 2].copy_from_slice(&[0x0e, 0x10]);
        assert!(verify_relocated_unwind_tables(&leaf_image, &leaf_manifest).is_err());
    }

    /// `stp d9, d8, [sp, #-32]!; stp x29, x30, [sp, #16]; add x29, sp, #16;
    /// ret` (clang-assembled) and the layout that describes it.
    const FPR_PAIR: [u32; 4] = [0x6dbe_23e9, 0xa901_7bfd, 0x9100_43fd, 0xd65f_03c0];

    fn fpr_pair_layout() -> FrameLayout {
        use trust_cg_ir::aarch64_regs::{V8, V9};
        let mut layout = fp_layout(&[]);
        layout.callee_saved_pairs.push(CalleeSavedPair {
            reg1: V8,
            reg2: V9,
            fp_offset: 0,
            is_fpr: true,
        });
        layout.callee_saved_area_size = 32;
        layout.total_frame_size = 32;
        layout
    }

    /// The JIT refuses an FP/SIMD callee-saved pair by name until a native
    /// control restores one across a landing pad. Independently of that
    /// policy, `DwarfFde::from_layout` describes D8/D9 as DWARF 72/73
    /// (`DW_CFA_offset_extended`) and the independent CFA decoder agrees with
    /// the decoded prologue, so the decoders are ready for the day the
    /// refusal lifts.
    #[test]
    fn fp_simd_callee_saves_are_refused_and_their_cfi_decodes_independently() {
        let layout = fpr_pair_layout();
        let image = words(&FPR_PAIR);
        let input = JitUnwindFunctionInput {
            name: "fpr_frame",
            code_offset: 0,
            code_len: 16,
            layout: &layout,
            lsda: None,
        };
        // The prologue words are exactly what the layout says, so only the
        // FP/SIMD pair itself can cause the refusal.
        let mut appended = image.clone();
        assert!(matches!(
            append_aarch64_jit_unwind_tables(&mut appended, &[input], None),
            Err(JitError::JitUnwindFrameShapeUnsupported { function, detail })
                if function == "fpr_frame" && detail.contains("D8/D9")
        ));

        // Independently of that refusal, the generated program agrees with
        // the prologue words register for register.
        let fde = DwarfFde::from_layout(&layout, 0, 16, 0);
        let record = JitUnwindFunctionRecord {
            function: "fpr_frame".to_owned(),
            code_offset: 0,
            code_len: 16,
            fde_offset: 0,
            lsda_offset: None,
            lsda_is_filler: false,
            frame_pointer: true,
        };
        let mut program_image = image.clone();
        let start = program_image.len();
        program_image.extend_from_slice(&fde.instructions);
        let mut cursor = Cursor::new(&program_image, start, program_image.len()).unwrap();
        let rules = decode_cfa_program(&mut cursor, "fpr_frame").unwrap();
        let (saves, _, _) = decode_prologue_frame(&program_image, &record).unwrap();
        assert_eq!(saves.get(&72), Some(&-24), "prologue stores D8 at CFA-24");
        assert_eq!(saves.get(&73), Some(&-32), "prologue stores D9 at CFA-32");
        assert_eq!(
            (rules.saves.get(&72), rules.saves.get(&73)),
            (Some(&-24), Some(&-32)),
            "the generator names DWARF 72/73 for D8/D9: {:?}",
            rules.saves
        );
        assert!(
            !rules.saves.contains_key(&8) && !rules.saves.contains_key(&9),
            "no 6-bit truncation to X8/X9: {:?}",
            rules.saves
        );
        verify_frame_rules(&program_image, &record, &rules)
            .expect("the FP/SIMD FDE agrees with its prologue");

        // Positive control: the same decoders accept a two-GPR-pair frame.
        let two = fp_layout(&[(X19, X20)]);
        let two_image = words(&TWO_PAIRS);
        let two_fde = DwarfFde::from_layout(&two, 0, 16, 0);
        let mut two_program = two_image.clone();
        let start = two_program.len();
        two_program.extend_from_slice(&two_fde.instructions);
        let mut cursor = Cursor::new(&two_program, start, two_program.len()).unwrap();
        let rules = decode_cfa_program(&mut cursor, "two").unwrap();
        let two_record = JitUnwindFunctionRecord {
            function: "two".to_owned(),
            ..record
        };
        verify_frame_rules(&two_program, &two_record, &rules).unwrap();
    }

    #[test]
    fn catch_all_type_table_must_stay_null_and_filters_are_refused() {
        use crate::exception_handling::LandingPadDesc;
        let minimal = fp_layout(&[]);
        let lsda = generate_lsda_from_pads(
            "__gxx_personality_v0",
            &[LandingPadDesc::catch_all(12)],
            &[(0, 8, 0), (8, 4, 12), (12, 8, 0)],
        )
        .unwrap();
        let functions = [JitUnwindFunctionInput {
            name: "catch",
            code_offset: 0,
            code_len: 20,
            layout: &minimal,
            lsda: Some((&lsda, "__gxx_personality_v0")),
        }];
        let mut image = words(&MINIMAL);
        let manifest =
            append_aarch64_jit_unwind_tables(&mut image, &functions, Some(binding())).unwrap();
        let start = manifest.functions[0].lsda_offset.unwrap() as usize;
        let end = start + lsda.len();
        assert_eq!(&image[start..end], lsda.as_slice());
        assert_eq!(
            &image[end - 4..end],
            &[0; 4],
            "catch-all is a NULL typeinfo"
        );

        // A typeinfo pointer without a relocation must be refused.
        let mut typed = image.clone();
        typed[end - 1] = 0x10;
        assert!(verify_relocated_unwind_tables(&typed, &manifest).is_err());

        // So must an exception-specification filter (negative action).
        let action = lsda
            .iter()
            .rposition(|&byte| byte == 0x01)
            .expect("the catch-all filter byte");
        let mut filtered = image.clone();
        filtered[start + action] = 0x7f; // SLEB128 -1
        assert!(verify_relocated_unwind_tables(&filtered, &manifest).is_err());
    }

    /// A prepared cleanup function (`invoke thrower() unwind { resume }`) and
    /// its preparation frame layout.
    #[cfg(target_arch = "aarch64")]
    fn prepared_cleanup() -> (
        Vec<trust_cg_ir::MachFunction>,
        Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
        Vec<Option<FrameLayout>>,
        trust_ir::Module,
    ) {
        use trust_ir::{
            Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Linkage, Module,
            Ty, ValueId,
        };
        let mut module = Module::new("jit_unwind_refusals");
        let void = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut thrower = Function::new(FuncId::new(0), "thrower", void, BlockId::new(0));
        thrower.linkage = Linkage::External;
        module
            .try_add_function(thrower)
            .expect("Module::try_add_function: test fixture");
        let int = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(1), "cleanup", int, BlockId::new(0));
        function.blocks = vec![
            Block {
                id: BlockId::new(0),
                params: vec![],
                body: vec![InstrNode::new(Inst::Invoke {
                    callee: FuncId::new(0),
                    args: vec![],
                    normal_dest: BlockId::new(1),
                    normal_args: vec![],
                    unwind_dest: BlockId::new(2),
                })],
            },
            Block {
                id: BlockId::new(1),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I32,
                        value: Constant::Int(0),
                    })
                    .with_result(ValueId::new(10)),
                    InstrNode::new(Inst::Return {
                        values: vec![ValueId::new(10)],
                    }),
                ],
            },
            Block {
                id: BlockId::new(2),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::LandingPad {
                        is_cleanup: true,
                        catch_type_indices: vec![],
                    })
                    .with_results(vec![ValueId::new(20), ValueId::new(21)]),
                    InstrNode::new(Inst::Resume {
                        exn: ValueId::new(20),
                    }),
                ],
            },
        ];
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
        let (lir, proofs) = trust_cg_lower::translate_function_with_license(
            &module.functions[1],
            &module,
            &permit_unlicensed(),
        )
        .unwrap();
        let (machine, metrics) = crate::pipeline::Pipeline::new(crate::pipeline::PipelineConfig {
            target_triple: if cfg!(target_os = "macos") {
                "aarch64-apple-darwin".into()
            } else {
                "aarch64-unknown-linux-gnu".into()
            },
            verify: false,
            ..Default::default()
        })
        .prepare_function_with_metrics(&lir, Some(&proofs))
        .unwrap();
        assert!(machine.eh_metadata.has_eh_info());
        assert!(metrics.frame_layout.is_some());
        (
            vec![machine],
            vec![(lir, proofs)],
            vec![metrics.frame_layout],
            module,
        )
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn jit_layer_refuses_unwind_tables_without_authority() {
        use crate::jit::{JitCompiler, JitConfig, ProfileHookMode};
        use std::collections::HashMap;
        let (machines, sources, layouts, module) = prepared_cleanup();
        let externs = HashMap::new();
        let request = Aarch64JitUnwindRequest::new(layouts, false);
        let unchecked = JitCompiler::new(JitConfig::default());

        // Raw MachIR has no frame-layout authority.
        assert!(matches!(
            unchecked.compile_raw(&machines, &externs),
            Err(JitError::RawJitEhUnsupported { function }) if function == "cleanup"
        ));
        // A request without the function's layout.
        let missing = Aarch64JitUnwindRequest::new(vec![None], false);
        assert!(matches!(
            unchecked.compile_with_lir_and_encoding_metrics(
                &machines,
                &sources,
                &module,
                &module,
                &externs,
                false,
                Some(&missing)
            ),
            Err(JitError::JitUnwindFrameLayoutMissing { function }) if function == "cleanup"
        ));
        // Relocation replay (a proof request) and verification refuse.
        assert!(matches!(
            unchecked.compile_with_lir_and_encoding_metrics(
                &machines,
                &sources,
                &module,
                &module,
                &externs,
                true,
                Some(&request)
            ),
            Err(JitError::JitUnwindProofEvidenceUnavailable { function }) if function == "cleanup"
        ));
        let verifying = JitCompiler::new(JitConfig {
            verify: true,
            ..JitConfig::default()
        });
        assert!(matches!(
            verifying.compile_with_lir_and_encoding_metrics(
                &machines,
                &sources,
                &module,
                &module,
                &externs,
                false,
                Some(&request)
            ),
            Err(JitError::JitUnwindProofEvidenceUnavailable { .. })
        ));
        // Profile hooks shift the frame the tables would describe.
        let profiled = JitCompiler::new(JitConfig {
            profile_hooks: ProfileHookMode::CallCounts,
            ..JitConfig::default()
        });
        assert!(matches!(
            profiled.compile_with_lir_and_encoding_metrics(
                &machines,
                &sources,
                &module,
                &module,
                &externs,
                false,
                Some(&request)
            ),
            Err(JitError::JitUnwindProfileHooksUnsupported { .. })
        ));
    }

    #[test]
    fn frame_only_tables_have_no_personality_or_lsda() {
        let minimal = fp_layout(&[]);
        let mut image = words(&MINIMAL);
        let functions = [JitUnwindFunctionInput {
            name: "walk",
            code_offset: 0,
            code_len: 20,
            layout: &minimal,
            lsda: None,
        }];
        let manifest = append_aarch64_jit_unwind_tables(&mut image, &functions, None).unwrap();
        assert!(!manifest.carries_exception_handling());
        assert!(manifest.personality_slot_offset.is_none());
        assert_eq!(manifest.relocations.len(), 1);
        verify_relocated_unwind_tables(&image, &manifest).unwrap();
        // A personality binding for a module without EH is refused.
        let mut image = words(&MINIMAL);
        assert!(append_aarch64_jit_unwind_tables(&mut image, &functions, Some(binding())).is_err());
    }

    #[test]
    fn personality_authority_is_single_and_exact() {
        let minimal = fp_layout(&[]);
        let lsda = cleanup_lsda(20);
        let rust_lsda = {
            use crate::exception_handling::LandingPadDesc;
            generate_lsda_from_pads(
                "rust_eh_personality",
                &[LandingPadDesc::cleanup(12)],
                &[(0, 8, 0), (8, 4, 12), (12, 8, 0)],
            )
            .unwrap()
        };
        let functions = [
            JitUnwindFunctionInput {
                name: "cxx",
                code_offset: 0,
                code_len: 20,
                layout: &minimal,
                lsda: Some((&lsda, "__gxx_personality_v0")),
            },
            JitUnwindFunctionInput {
                name: "rust",
                code_offset: 20,
                code_len: 20,
                layout: &minimal,
                lsda: Some((&rust_lsda, "rust_eh_personality")),
            },
        ];
        assert!(matches!(
            module_personality(&functions),
            Err(JitError::JitUnwindMultiplePersonalities { .. })
        ));
        // A missing, mismatched or null binding is refused before any byte is
        // appended to a caller-visible manifest.
        let single = &functions[..1];
        for personality in [
            None,
            Some(JitPersonalityBinding {
                symbol: "rust_eh_personality".to_owned(),
                ..binding()
            }),
            Some(JitPersonalityBinding {
                address: 0,
                ..binding()
            }),
        ] {
            let mut image = words(&MINIMAL);
            assert!(append_aarch64_jit_unwind_tables(&mut image, single, personality).is_err());
        }
    }

    #[test]
    fn relocation_placeholders_and_range_fail_closed() {
        let mut image = vec![0u8; 16];
        let far = JitUnwindRelocation {
            field_offset: 0,
            kind: JitUnwindRelocationKind::Prel32,
            target: JitUnwindRelocationTarget::PersonalitySlot,
            target_offset: Some(1 << 40),
            target_address: None,
        };
        assert!(matches!(
            apply_relocation(&mut image, &far),
            Err(JitError::JitUnwindRelocationOutOfRange { .. })
        ));
        image[4] = 1;
        let occupied = JitUnwindRelocation {
            field_offset: 4,
            target_offset: Some(8),
            ..far
        };
        assert!(apply_relocation(&mut image, &occupied).is_err());
    }
}
