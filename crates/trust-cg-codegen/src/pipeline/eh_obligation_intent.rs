// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0

//! The IR side of the exception-table obligations (ledger L03-P14).
//!
//! For each emitted function this states, from the final machine function
//! and the frame owner's layout alone, what its exception tables and unwind
//! description must express: the landing blocks and their clauses, the call
//! each invoke protects, the calls the IR declares unable to unwind, the
//! personality, the EH type table, and the saved-register slots of the
//! frame. Offsets come from this module's own walk of the laid-out blocks
//! (one encoded word per non-pseudo instruction, the encoder's exact-layout
//! contract), not from the resolved call-site table or the LSDA builder.
//! `trust_cg_verify::eh_obligations` then decides the obligations against
//! the emitted bytes, which it re-parses with its own decoders.

use super::*;
use trust_cg_ir::function::EhCallSiteBindings;
use trust_cg_verify::eh_obligations::{
    EhClause, EhFrameIntent, EhFunctionIntent, EhInvokeIntent, EhLandingPadIntent, EhReg,
    EhTablesIntent,
};

/// Where a JIT image's tables and functions sit (image offsets).
#[derive(Debug, Clone)]
pub struct EhJitImageLayout {
    /// Offset and length of `.eh_frame` (terminator included).
    pub eh_frame: (u64, u64),
    /// Each function's entry and FDE offsets, in intent order.
    pub functions: Vec<trust_cg_verify::eh_obligations::EhImageFunction>,
    /// The bound personality routines and their addresses.
    pub personalities: Vec<(String, u64)>,
}

/// One decided object or image: its bytes, the IR-side intent it was
/// checked against and the report of what held.
#[derive(Debug, Clone)]
pub struct EhObligationCapture {
    /// `"macho"` or `"jit"`.
    pub route: &'static str,
    /// The emitted bytes (the object, or the bound JIT image before mapping).
    pub bytes: Vec<u8>,
    /// The intent the bytes were checked against.
    pub intent: trust_cg_verify::eh_obligations::EhObjectIntent,
    /// What held.
    pub report: trust_cg_verify::eh_obligations::EhObligationReport,
    /// The image layout, for the JIT route.
    pub jit: Option<EhJitImageLayout>,
}

impl EhObligationCapture {
    /// Decide the obligations again for `bytes` (this capture's bytes, or a
    /// mutation of them) against `intent`, through the same route.
    pub fn recheck(
        &self,
        bytes: &[u8],
        intent: &trust_cg_verify::eh_obligations::EhObjectIntent,
    ) -> Result<
        trust_cg_verify::eh_obligations::EhObligationReport,
        trust_cg_verify::eh_obligations::EhObligationViolation,
    > {
        match &self.jit {
            None => trust_cg_verify::eh_obligations::check_macho_object(bytes, intent),
            Some(layout) => trust_cg_verify::eh_obligations::check_jit_image(
                &trust_cg_verify::eh_obligations::EhImage {
                    bytes,
                    base: 0,
                    eh_frame: layout.eh_frame,
                    functions: layout.functions.clone(),
                    personalities: layout.personalities.clone(),
                },
                intent,
            ),
        }
    }
}

thread_local! {
    static CAPTURE: std::cell::RefCell<Option<Vec<EhObligationCapture>>> =
        const { std::cell::RefCell::new(None) };
}

/// Run `body` and return, with its result, every exception-table obligation
/// decision the compiler made on THIS thread meanwhile (object emission runs
/// on the calling thread). Test support: corruption controls replay the
/// decision on mutated bytes against the captured intent. It changes no
/// decision and no emitted byte.
#[doc(hidden)]
pub fn capture_eh_obligations<R>(body: impl FnOnce() -> R) -> (R, Vec<EhObligationCapture>) {
    let previous = CAPTURE.with(|capture| capture.borrow_mut().replace(Vec::new()));
    let result = body();
    let captured = CAPTURE.with(|capture| {
        let mut capture = capture.borrow_mut();
        let captured = capture.take().unwrap_or_default();
        *capture = previous;
        captured
    });
    (result, captured)
}

/// Record a decision when a capture is active on this thread.
pub(crate) fn record_capture(
    route: &'static str,
    bytes: &[u8],
    intent: &trust_cg_verify::eh_obligations::EhObjectIntent,
    report: &trust_cg_verify::eh_obligations::EhObligationReport,
    jit: Option<EhJitImageLayout>,
) {
    CAPTURE.with(|capture| {
        if let Some(captured) = capture.borrow_mut().as_mut() {
            captured.push(EhObligationCapture {
                route,
                bytes: bytes.to_vec(),
                intent: intent.clone(),
                report: report.clone(),
                jit,
            });
        }
    });
}

/// The exception-table obligations failed for an emitted object or image.
pub(crate) fn obligation_error(
    violation: trust_cg_verify::eh_obligations::EhObligationViolation,
) -> PipelineError {
    PipelineError::EhTableObligation {
        function: violation.function.clone().unwrap_or_default(),
        obligation: violation.kind.name(),
        detail: violation.to_string(),
    }
}

fn preg(reg: PReg, is_fpr: bool) -> EhReg {
    if is_fpr {
        EhReg::D(reg.hw_enc())
    } else {
        EhReg::X(reg.hw_enc())
    }
}

/// The frame owner's saved-register slots, relative to the CFA, in the
/// Apple-canonical FRAME layout `frame.rs` lays out: FP/LR at CFA-16/CFA-8
/// (pair 0), then pair `i` with its first register at CFA-(16i+8) and its
/// second at CFA-16(i+1).
pub(crate) fn frame_intent(layout: &crate::frame::FrameLayout) -> EhFrameIntent {
    let mut saved = Vec::new();
    for (index, pair) in layout.callee_saved_pairs.iter().enumerate() {
        if index == 0 {
            saved.push((preg(pair.reg1, pair.is_fpr), -16));
            saved.push((preg(pair.reg2, pair.is_fpr), -8));
        } else {
            let index = index as i64;
            saved.push((preg(pair.reg1, pair.is_fpr), -(16 * index + 8)));
            saved.push((preg(pair.reg2, pair.is_fpr), -(16 * (index + 1))));
        }
    }
    EhFrameIntent {
        saved,
        uses_frame_pointer: layout.uses_frame_pointer,
        total_frame_size: layout.total_frame_size,
    }
}

/// Whether `inst` encodes as a `BL`/`BLR` word (a call the decoded words
/// show), as opposed to a tail call or a pseudo.
fn encodes_as_call(inst: &IrMachInst) -> bool {
    matches!(
        inst.opcode,
        IrOpcode::Bl
            | IrOpcode::BL
            | IrOpcode::Blr
            | IrOpcode::BLR
            | IrOpcode::BlrTlsdesc
            | IrOpcode::TlsDescCall
    )
}

/// The obligations' view of one emitted function.
///
/// `object_name` spells a linker name as it appears in the object (Mach-O
/// prefixes `_`); `code_len` is the emitted length (instructions, then the
/// jump tables the encoder appends).
pub(crate) fn function_intent(
    func: &IrMachFunction,
    text_offset: u64,
    code_len: u32,
    layout: &crate::frame::FrameLayout,
    propagation: &EhPropagation,
    object_name: &dyn Fn(&str) -> String,
) -> Result<EhFunctionIntent, String> {
    let mut block_offsets: HashMap<BlockId, u32> = HashMap::new();
    let mut inst_offsets: HashMap<InstId, u32> = HashMap::new();
    let mut nounwind_calls = Vec::new();
    let nounwind_callees = match propagation {
        EhPropagation::NounwindFrame { nounwind_callees } => Some(&**nounwind_callees),
        EhPropagation::Filler => None,
    };
    let empty = BTreeSet::new();
    let mut offset = 0u32;
    let mut jump_table_bytes = 0u32;
    for &block_id in &func.block_order {
        let block = func
            .blocks
            .get(block_id.0 as usize)
            .ok_or_else(|| format!("block_order names missing block {block_id:?}"))?;
        block_offsets.insert(block_id, offset);
        for &inst_id in &block.insts {
            let inst = func
                .insts
                .get(inst_id.0 as usize)
                .ok_or_else(|| format!("block {block_id:?} names missing {inst_id:?}"))?;
            if inst.is_pseudo() {
                continue;
            }
            inst_offsets.insert(inst_id, offset);
            if inst.opcode == IrOpcode::Adr
                && let Some(table) = inst
                    .operands
                    .iter()
                    .find_map(|operand| operand.as_jump_table_index())
            {
                let entries = func
                    .jump_tables
                    .get(table as usize)
                    .ok_or_else(|| format!("ADR names missing jump table {table}"))?
                    .targets
                    .len();
                jump_table_bytes = u32::try_from(entries)
                    .ok()
                    .and_then(|entries| entries.checked_mul(4))
                    .and_then(|bytes| jump_table_bytes.checked_add(bytes))
                    .ok_or("jump-table bytes overflow u32")?;
            }
            if encodes_as_call(inst)
                && aarch64_call_may_unwind(inst, nounwind_callees.unwrap_or(&empty)) == Some(false)
            {
                nounwind_calls.push(offset);
            }
            offset = offset
                .checked_add(4)
                .ok_or("instruction offsets overflow u32")?;
        }
    }
    let body_len = code_len
        .checked_sub(jump_table_bytes)
        .ok_or("the jump tables exceed the emitted length")?;

    let eh = &func.eh_metadata;
    let tables = if eh.has_eh_info() {
        let personality =
            crate::exception_handling::required_personality_symbol(eh.personality.as_deref())
                .map_err(|error| format!("invalid personality: {error}"))?;
        let personality = object_name(crate::exception_handling::canonical_personality_symbol(
            personality,
        ));
        let mut landing_pads = Vec::with_capacity(eh.landing_pads.len());
        let mut typeinfo = BTreeMap::new();
        for pad in &eh.landing_pads {
            let offset = *block_offsets
                .get(&pad.block)
                .ok_or_else(|| format!("landing block {:?} is not laid out", pad.block))?;
            let mut clauses = Vec::with_capacity(pad.catch_type_indices.len());
            for &index in &pad.catch_type_indices {
                if index == trust_cg_lower::function::RUST_EH_EMPTY_FILTER {
                    clauses.push(EhClause::RustEmptyFilter);
                    continue;
                }
                if index != 0
                    && let Some(symbol) = eh.eh_type_table.symbol_for_catch_index(index)
                {
                    typeinfo.insert(index, object_name(symbol));
                }
                clauses.push(EhClause::Catch(index));
            }
            landing_pads.push(EhLandingPadIntent {
                block: pad.block.0,
                offset,
                clauses,
                cleanup: pad.is_cleanup,
            });
        }
        let exact: Option<HashMap<BlockId, (InstId, BlockId)>> = match &eh.call_site_bindings {
            EhCallSiteBindings::ExactInstructions(bindings) => Some(
                bindings
                    .iter()
                    .map(|binding| {
                        (
                            binding.call_block,
                            (binding.call_inst, binding.landing_pad_block),
                        )
                    })
                    .collect(),
            ),
            EhCallSiteBindings::LegacyBlocks => None,
        };
        let mut invokes = Vec::new();
        for site in &eh.call_sites {
            let Some(landing_block) = site.landing_pad_block else {
                continue;
            };
            let call = match &exact {
                Some(exact) => {
                    let (call, bound_pad) = *exact.get(&site.call_block).ok_or_else(|| {
                        format!(
                            "handler block {:?} has no exact invoke binding",
                            site.call_block
                        )
                    })?;
                    if bound_pad != landing_block {
                        return Err(format!(
                            "handler block {:?} unwinds to {landing_block:?} but its binding names {bound_pad:?}",
                            site.call_block
                        ));
                    }
                    call
                }
                None => {
                    let block = func
                        .blocks
                        .get(site.call_block.0 as usize)
                        .ok_or_else(|| format!("missing handler block {:?}", site.call_block))?;
                    let calls: Vec<InstId> = block
                        .insts
                        .iter()
                        .copied()
                        .filter(|&id| func.insts.get(id.0 as usize).is_some_and(encodes_as_call))
                        .collect();
                    let [call] = calls.as_slice() else {
                        return Err(format!(
                            "handler block {:?} holds {} calls",
                            site.call_block,
                            calls.len()
                        ));
                    };
                    *call
                }
            };
            let call_offset = *inst_offsets
                .get(&call)
                .ok_or_else(|| format!("protected call {call:?} is not laid out"))?;
            invokes.push(EhInvokeIntent {
                call_offset,
                landing_block: landing_block.0,
            });
        }
        Some(EhTablesIntent {
            personality,
            landing_pads,
            invokes,
            type_table_len: eh.eh_type_table.len(),
            typeinfo: typeinfo.into_iter().collect(),
        })
    } else {
        None
    };

    Ok(EhFunctionIntent {
        symbol: func.name.clone(),
        text_offset,
        body_len,
        code_len,
        frame: frame_intent(layout),
        nounwind_calls,
        eh: tables,
    })
}

/// The exception-table obligations over a JIT image that carries exception
/// tables, decided before it is mapped: `image` holds the code with its
/// unwind tables appended and every table pointer bound (image offsets stand
/// for addresses; the tables are position independent but for the
/// personality slot, which holds the bound routine's absolute address).
///
/// `functions` are `(machine function, image offset, emitted length, frame
/// layout)` in the manifest's order.
pub(crate) fn check_jit_image(
    propagation: &EhPropagation,
    functions: &[(&IrMachFunction, u64, u32, &crate::frame::FrameLayout)],
    image: &[u8],
    manifest: &crate::jit_unwind::JitUnwindManifest,
) -> Result<trust_cg_verify::eh_obligations::EhObligationReport, String> {
    use trust_cg_verify::eh_obligations::{EhImage, EhImageFunction, EhObjectIntent};
    let identity = |name: &str| name.to_string();
    let mut intent = EhObjectIntent::default();
    let mut placed = Vec::with_capacity(functions.len());
    for &(function, code_offset, code_len, layout) in functions {
        let record = manifest
            .function(&function.name)
            .ok_or_else(|| format!("the unwind manifest has no record for `{}`", function.name))?;
        if record.code_offset != code_offset || record.code_len != code_len {
            return Err(format!(
                "the manifest places `{}` at {}+{}, the image at {code_offset}+{code_len}",
                function.name, record.code_offset, record.code_len
            ));
        }
        intent.functions.push(
            function_intent(
                function,
                code_offset,
                code_len,
                layout,
                propagation,
                &identity,
            )
            .map_err(|detail| format!("`{}`: {detail}", function.name))?,
        );
        placed.push(EhImageFunction {
            code_offset,
            fde_offset: record.fde_offset,
        });
    }
    let personalities = manifest
        .personality
        .iter()
        .map(|binding| (binding.symbol.clone(), binding.address))
        .collect();
    let layout = EhJitImageLayout {
        eh_frame: (manifest.eh_frame_offset, manifest.eh_frame_len),
        functions: placed,
        personalities,
    };
    let view = EhImage {
        bytes: image,
        base: 0,
        eh_frame: layout.eh_frame,
        functions: layout.functions.clone(),
        personalities: layout.personalities.clone(),
    };
    let report = trust_cg_verify::eh_obligations::check_jit_image(&view, &intent)
        .map_err(|violation| violation.to_string())?;
    record_capture("jit", image, &intent, &report, Some(layout));
    if trust_cg_verify::diag::eh_obligation_trace_enabled() {
        eprintln!("TCG_EH_OBLIGATIONS jit {}", report.summary());
    }
    Ok(report)
}
