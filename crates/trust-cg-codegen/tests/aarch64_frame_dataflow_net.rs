// trust-cg-codegen/tests/aarch64_frame_dataflow_net.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Final-stream frame dataflow net (`[TCG-A64-SPILL-SLOT]`) on real pipeline
//! output: a framed, spilling function with a call, prepared through the
//! whole AArch64 pipeline (allocation, spill materialization, post-RA passes,
//! frame lowering, branch resolution) for Darwin and Linux at O0-O3.
//!
//! The clean stream must be MODELED (not declined) with its spill reloads and
//! exit checked, and must encode. Each corruption of that exact stream — a
//! deleted spill store, a spill reload moved onto the saved frame record or
//! below the frame, a swapped reload register, a reload hoisted above the call
//! that clobbers it, a reload offset shifted by half a slot, a dropped
//! callee-save or frame-record restore, and a return lane written in the
//! epilogue — must be rejected by the encoder with the named violation. A
//! reload shifted by whole slots onto another spill cell is NOT rejected: the
//! final stream carries no spill-slot identity (see LIMITATIONS.md).
//!
//! These are compile-only controls (no execution), so both target triples run
//! on any host.

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, encode_function};
use trust_cg_ir::aarch64_regs::{SP, X0, X16, X17, X19, X28, X29};
use trust_cg_ir::{AArch64Opcode, InstFlags, InstId, MachFunction, MachInst, MachOperand, PReg};
use trust_cg_verify::post_ra_spill_slots::{
    FrameNetOutcome, SpillSlotViolationKind, analyze_frame,
};
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{BinOp, Block, Constant, Function, Inst, InstrNode, Module, Ty};

const TRIPLES: [&str; 2] = ["aarch64-apple-darwin", "aarch64-unknown-linux-gnu"];
const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const LANES: usize = 48;

struct Builder {
    next: u32,
    body: Vec<InstrNode>,
}

impl Builder {
    fn fresh(&mut self) -> ValueId {
        let value = ValueId(self.next);
        self.next += 1;
        value
    }

    fn emit(&mut self, inst: Inst) -> ValueId {
        let result = self.fresh();
        self.body.push(InstrNode::new(inst).with_result(result));
        result
    }

    fn constant(&mut self, value: i64) -> ValueId {
        self.emit(Inst::Const {
            ty: Ty::I64,
            value: Constant::i64(value),
        })
    }

    fn binop(&mut self, op: BinOp, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.emit(Inst::BinOp {
            op,
            ty: Ty::I64,
            lhs,
            rhs,
        })
    }
}

/// `caller(p) = helper(v0) + sum(v_i)` where `v_i = p[i] * k_i`: every `v_i`
/// is live across the call, forcing spills and callee-saved registers.
fn spilling_module() -> Module {
    let mut b = Builder {
        next: 0,
        body: Vec::new(),
    };
    let input = b.fresh();
    let mut live = Vec::with_capacity(LANES);
    for lane in 0..LANES {
        let index = b.constant(lane as i64);
        let address = b.emit(Inst::GEP {
            pointee_ty: Ty::I64,
            base: input,
            indices: vec![index],
            inbounds: false,
        });
        let loaded = b.emit(Inst::Load {
            ty: Ty::I64,
            ptr: address,
            volatile: false,
            align: None,
        });
        let factor = b.constant((lane as i64 % 7) + 2);
        live.push(b.binop(BinOp::Mul, loaded, factor));
    }
    let mut acc = b.emit(Inst::Call {
        callee: FuncId(1),
        args: vec![live[0]],
    });
    for value in live {
        acc = b.binop(BinOp::Add, acc, value);
    }
    b.body
        .push(InstrNode::new(Inst::Return { values: vec![acc] }));

    let mut module = Module::new("aarch64_frame_dataflow_net");
    let caller_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let helper_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut caller = Function::new(FuncId(0), "frame_net_caller", caller_ty, BlockId(0));
    let mut block = Block::new(BlockId(0)).with_param(input, Ty::Ptr);
    block.body = b.body;
    caller.blocks = vec![block];
    module
        .try_add_function(caller)
        .expect("Module::try_add_function: test fixture");

    let mut h = Builder {
        next: 0,
        body: Vec::new(),
    };
    let param = h.fresh();
    let one = h.constant(1);
    let sum = h.binop(BinOp::Add, param, one);
    h.body
        .push(InstrNode::new(Inst::Return { values: vec![sum] }));
    let mut helper = Function::new(FuncId(1), "frame_net_helper", helper_ty, BlockId(0));
    let mut helper_block = Block::new(BlockId(0)).with_param(param, Ty::I64);
    helper_block.body = h.body;
    helper.blocks = vec![helper_block];
    module
        .try_add_function(helper)
        .expect("Module::try_add_function: test fixture");
    module
}

fn prepared(triple: &str, opt_level: OptLevel) -> MachFunction {
    let module = spilling_module();
    let lir = permit_translate_module(&module).expect("fixture lowers");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        ..PipelineConfig::for_target(triple)
    });
    let (func, metrics) = pipeline
        .prepare_function_with_metrics(&lir[0].0, Some(&lir[0].1))
        .unwrap_or_else(|error| panic!("{triple} {opt_level:?}: prepare failed: {error}"));
    assert!(
        metrics.spill_slot_count > 0,
        "{triple} {opt_level:?}: the fixture must spill"
    );
    func
}

fn entry_insts(func: &MachFunction) -> Vec<InstId> {
    assert_eq!(
        func.blocks.len(),
        1,
        "the straight-line fixture stays one block"
    );
    func.blocks[func.entry.0 as usize].insts.clone()
}

fn is_spill(inst: &MachInst) -> bool {
    inst.flags.is_spill_slot_access()
}

fn mem_operand(inst: &MachInst) -> (PReg, i64) {
    inst.operands
        .iter()
        .find_map(|op| match op {
            MachOperand::MemOp { base, offset } => Some((*base, *offset)),
            _ => None,
        })
        .expect("resolved spill access")
}

fn data_reg(inst: &MachInst) -> PReg {
    match inst.operands[0] {
        MachOperand::PReg(p) => p,
        ref other => panic!("spill data operand {other:?}"),
    }
}

fn is_caller_saved_gpr(reg: PReg) -> bool {
    reg.encoding() <= 18
}

/// Position of the call and of the first spill reload after it whose
/// destination is a caller-saved register.
fn call_and_reload(func: &MachFunction) -> (usize, usize) {
    let insts = entry_insts(func);
    let call = insts
        .iter()
        .position(|id| func.insts[id.0 as usize].opcode == AArch64Opcode::Bl)
        .expect("fixture calls its helper");
    let reload = insts
        .iter()
        .enumerate()
        .skip(call + 1)
        .find(|(_, id)| {
            let inst = &func.insts[id.0 as usize];
            inst.opcode == AArch64Opcode::LdrRI
                && is_spill(inst)
                && is_caller_saved_gpr(data_reg(inst))
        })
        .map(|(pos, _)| pos)
        .expect("a spilled value is reloaded after the call");
    (call, reload)
}

fn inst_at(func: &mut MachFunction, pos: usize) -> &mut MachInst {
    let id = func.blocks[func.entry.0 as usize].insts[pos];
    &mut func.insts[id.0 as usize]
}

fn insert(func: &mut MachFunction, pos: usize, inst: MachInst) {
    let id = func.push_inst(inst);
    let entry = func.entry.0 as usize;
    func.blocks[entry].insts.insert(pos, id);
}

fn violation_kinds(func: &MachFunction) -> Vec<SpillSlotViolationKind> {
    match analyze_frame(func) {
        FrameNetOutcome::Analyzed { violations, .. } => violations.iter().map(|v| v.kind).collect(),
        FrameNetOutcome::Declined(reason) => panic!("{}: declined {}", func.name, reason.tag()),
    }
}

fn assert_rejected(func: &MachFunction, kind: SpillSlotViolationKind, what: &str) {
    let kinds = violation_kinds(func);
    assert!(
        kinds.contains(&kind),
        "{what}: expected {kind:?}, got {kinds:?}"
    );
    let error = encode_function(func).expect_err(what).to_string();
    assert!(
        error.contains("[TCG-A64-SPILL-SLOT]") && error.contains(kind.tag()),
        "{what}: encoder must fail closed with the named violation, got: {error}"
    );
}

fn for_each_stream(check: impl Fn(&str, OptLevel, MachFunction)) {
    for triple in TRIPLES {
        for opt_level in OPT_LEVELS {
            check(triple, opt_level, prepared(triple, opt_level));
        }
    }
}

#[test]
fn clean_framed_spilling_stream_is_modeled_checked_and_encodes() {
    for_each_stream(|triple, opt_level, func| {
        match analyze_frame(&func) {
            FrameNetOutcome::Analyzed { violations, stats } => {
                assert!(
                    violations.is_empty(),
                    "{triple} {opt_level:?}: {violations:#?}"
                );
                assert!(stats.framed, "{triple} {opt_level:?}: framed");
                assert!(
                    stats.spill_reloads_checked > 0,
                    "{triple} {opt_level:?}: {stats:?}"
                );
                assert!(stats.spill_stores > 0, "{triple} {opt_level:?}: {stats:?}");
                assert_eq!(stats.exits_checked, 1, "{triple} {opt_level:?}");
                assert_eq!(stats.calls, 1, "{triple} {opt_level:?}");
            }
            FrameNetOutcome::Declined(reason) => {
                panic!("{triple} {opt_level:?}: declined {}", reason.tag())
            }
        }
        encode_function(&func)
            .unwrap_or_else(|error| panic!("{triple} {opt_level:?}: encode: {error}"));
    });
}

#[test]
fn corrupt_deleted_spill_store_is_rejected() {
    for_each_stream(|triple, opt_level, mut func| {
        let (_, reload) = call_and_reload(&func);
        let slot = mem_operand(inst_at(&mut func, reload));
        let entry = func.entry.0 as usize;
        let before = func.blocks[entry].insts.len();
        let insts = func.insts.clone();
        func.blocks[entry].insts.retain(|id| {
            let inst = &insts[id.0 as usize];
            !(inst.opcode == AArch64Opcode::StrRI && is_spill(inst) && mem_operand(inst) == slot)
        });
        assert!(
            func.blocks[entry].insts.len() < before,
            "a store was deleted"
        );
        assert_rejected(
            &func,
            SpillSlotViolationKind::ReloadWithoutReachingStore,
            &format!("{triple} {opt_level:?} deleted spill store"),
        );
    });
}

#[test]
fn corrupt_spill_reload_offset_onto_frame_record_is_rejected() {
    for_each_stream(|triple, opt_level, mut func| {
        let (_, reload) = call_and_reload(&func);
        let inst = inst_at(&mut func, reload);
        inst.operands[1] = MachOperand::MemOp {
            base: X29,
            offset: 0,
        };
        assert_rejected(
            &func,
            SpillSlotViolationKind::ReloadFromNonSpillStore,
            &format!("{triple} {opt_level:?} reload offset on saved FP"),
        );
    });
}

#[test]
fn corrupt_spill_reload_offset_below_frame_is_rejected() {
    for_each_stream(|triple, opt_level, mut func| {
        let (_, reload) = call_and_reload(&func);
        let inst = inst_at(&mut func, reload);
        inst.operands[1] = MachOperand::MemOp {
            base: SP,
            offset: -16,
        };
        assert_rejected(
            &func,
            SpillSlotViolationKind::ReloadWithoutReachingStore,
            &format!("{triple} {opt_level:?} reload offset below the frame"),
        );
    });
}

/// A reload offset shifted by half a slot: on this layout every spill cell is
/// 8 bytes wide and 8-byte aligned, so the shifted reload reads the halves of
/// two neighbouring cells (both spill-stored before the call) or leaves the
/// spill area. Either way it does not read one spill store's bytes and must be
/// rejected by a reload check, whatever the neighbouring cells hold.
#[test]
fn corrupt_spill_reload_offset_shifted_by_half_a_slot_is_rejected() {
    const RELOAD_KINDS: [SpillSlotViolationKind; 4] = [
        SpillSlotViolationKind::ReloadMisalignedWithSpillStore,
        SpillSlotViolationKind::ReloadFromNonSpillStore,
        SpillSlotViolationKind::ReloadWithoutReachingStore,
        SpillSlotViolationKind::ReloadOfCallClobberedSlot,
    ];
    for_each_stream(|triple, opt_level, clean| {
        for delta in [-4i64, 4] {
            let mut func = clean.clone();
            let (_, reload) = call_and_reload(&func);
            let inst = inst_at(&mut func, reload);
            let (base, offset) = mem_operand(inst);
            inst.operands[1] = MachOperand::MemOp {
                base,
                offset: offset + delta,
            };
            let what = format!("{triple} {opt_level:?} reload offset {offset}{delta:+}");
            let kinds = violation_kinds(&func);
            let kind = RELOAD_KINDS
                .into_iter()
                .find(|kind| kinds.contains(kind))
                .unwrap_or_else(|| panic!("{what}: no reload violation in {kinds:?}"));
            assert_rejected(&func, kind, &what);
        }
    });
}

#[test]
fn corrupt_swapped_reload_register_is_rejected() {
    for_each_stream(|triple, opt_level, mut func| {
        let (_, reload) = call_and_reload(&func);
        let inst = inst_at(&mut func, reload);
        let original = data_reg(inst);
        let replacement = if original == X17 { X16 } else { X17 };
        inst.operands[0] = MachOperand::PReg(replacement);
        assert_rejected(
            &func,
            SpillSlotViolationKind::ClobberedRegisterRead,
            &format!("{triple} {opt_level:?} reload into {replacement} instead of {original}"),
        );
    });
}

#[test]
fn corrupt_reload_hoisted_across_clobbering_call_is_rejected() {
    for_each_stream(|triple, opt_level, mut func| {
        let (call, reload) = call_and_reload(&func);
        let entry = func.entry.0 as usize;
        let id = func.blocks[entry].insts.remove(reload);
        func.blocks[entry].insts.insert(call, id);
        assert_rejected(
            &func,
            SpillSlotViolationKind::ClobberedRegisterRead,
            &format!("{triple} {opt_level:?} reload hoisted above the call"),
        );
    });
}

#[test]
fn corrupt_dropped_callee_save_restore_is_rejected() {
    for_each_stream(|triple, opt_level, mut func| {
        let insts = entry_insts(&func);
        // Prefer an extra callee-saved pair restore; fall back to the frame
        // record (FP/LR), whose loss is a return-address violation.
        let restore = insts.iter().position(|id| {
            let inst = &func.insts[id.0 as usize];
            inst.opcode == AArch64Opcode::LdpRI
                && inst.operands.iter().take(2).any(|op| {
                    matches!(op, MachOperand::PReg(p) if (X19.encoding()..=X28.encoding()).contains(&p.encoding()))
                })
        });
        let (pos, kind) = match restore {
            Some(pos) => (pos, SpillSlotViolationKind::CalleeSavedNotRestored),
            None => (
                insts
                    .iter()
                    .position(|id| {
                        let inst = &func.insts[id.0 as usize];
                        inst.opcode == AArch64Opcode::LdpRI
                            && matches!(inst.operands[0], MachOperand::PReg(p) if p == X29)
                    })
                    .expect("frame-record restore"),
                SpillSlotViolationKind::ReturnAddressNotRestored,
            ),
        };
        *inst_at(&mut func, pos) =
            MachInst::with_flags(AArch64Opcode::Nop, vec![], InstFlags::IS_PSEUDO);
        assert_rejected(
            &func,
            kind,
            &format!("{triple} {opt_level:?} dropped restore"),
        );
    });
}

#[test]
fn corrupt_return_lane_written_in_epilogue_is_rejected() {
    for_each_stream(|triple, opt_level, mut func| {
        let insts = entry_insts(&func);
        let ret = insts
            .iter()
            .position(|id| func.insts[id.0 as usize].opcode == AArch64Opcode::Ret)
            .expect("return");
        insert(
            &mut func,
            ret,
            MachInst::new(
                AArch64Opcode::Movz,
                vec![MachOperand::PReg(X0), MachOperand::Imm(0)],
            ),
        );
        assert_rejected(
            &func,
            SpillSlotViolationKind::ReturnLaneClobbered,
            &format!("{triple} {opt_level:?} return lane written after teardown"),
        );
    });
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
