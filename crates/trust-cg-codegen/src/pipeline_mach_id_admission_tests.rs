// trust-cg-codegen/pipeline_mach_id_admission_tests.rs - the L10-P5 identity
// admission at the AArch64 pipeline's phase boundaries
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Each codegen boundary that hands a machine function to code that allocates
//! (the optimization entry, register allocation's entry, frame lowering's
//! first allocation, branch resolution's entry, the AOT profile
//! instrumentation entry) re-derives every live
//! identity and refuses a stale counter as [`PipelineError::MachIdAdmission`],
//! naming the boundary. These controls inject the corruption right before
//! each boundary.

use super::*;
use trust_cg_ir::function::Signature as IrSignature;
use trust_cg_ir::inst::{AArch64Opcode as IrOpcode, MachInst as IrMachInst};
use trust_cg_ir::operand::MachOperand as IrOperand;
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::{MachIdAdmissionError, MachIdDomain, MachIdSite, StackSlotId};

fn darwin(opt_level: OptLevel) -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level,
        target_triple: "aarch64-apple-darwin".into(),
        disabled_passes_override: Some(String::new()),
        ..PipelineConfig::default()
    })
}

/// `v0 = 42; v1 = v0 + 1; x0 = v1; ret`, built by the allocators.
fn small() -> IrMachFunction {
    let mut func = IrMachFunction::new(
        "small".into(),
        IrSignature::new(vec![], vec![trust_cg_ir::function::Type::I64]),
    );
    let entry = func.entry;
    let v0 = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
    let v1 = VReg::new(func.alloc_vreg(), RegClass::Gpr64);
    for inst in [
        IrMachInst::new(
            IrOpcode::MovI,
            vec![IrOperand::VReg(v0), IrOperand::Imm(42)],
        ),
        IrMachInst::new(
            IrOpcode::AddRI,
            vec![IrOperand::VReg(v1), IrOperand::VReg(v0), IrOperand::Imm(1)],
        ),
        IrMachInst::new(
            IrOpcode::MovR,
            vec![IrOperand::PReg(trust_cg_ir::regs::X0), IrOperand::VReg(v1)],
        ),
        IrMachInst::new(IrOpcode::Ret, vec![]).with_implicit_uses(&[trust_cg_ir::regs::X0]),
    ] {
        let id = func.push_inst(inst);
        func.append_inst(entry, id);
    }
    func
}

fn refusal(result: Result<impl std::fmt::Debug, PipelineError>) -> trust_cg_ir::MachIdRefusal {
    match result {
        Err(PipelineError::MachIdAdmission(refusal)) => refusal,
        other => panic!("expected an identity refusal, got {other:?}"),
    }
}

#[test]
fn the_optimization_entry_refuses_a_stale_counter_at_every_level() {
    for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let mut func = small();
        func.next_vreg = 1;
        let refused = refusal(darwin(level).run_optimization_checked(&mut func));
        assert_eq!(refused.boundary, "optimization entry", "{level:?}");
        assert_eq!(
            refused.error,
            MachIdAdmissionError::StaleCounter {
                domain: MachIdDomain::VReg,
                counter: 1,
                live_id: 1,
                site: MachIdSite::Operand {
                    inst: 1,
                    operand: 0
                },
            }
        );
        let text = PipelineError::MachIdAdmission(refused).to_string();
        assert!(
            text.starts_with(
                "machine-IR identity admission: function `small` refused at optimization \
                 entry: [TCG-MIR-STALE-ID-COUNTER]"
            ),
            "{text}"
        );
    }
}

#[test]
fn register_allocation_refuses_a_counter_made_stale_after_optimization() {
    for level in [OptLevel::O0, OptLevel::O2] {
        let pipeline = darwin(level);
        let mut func = small();
        pipeline
            .run_optimization_checked(&mut func)
            .expect("the admitted function optimizes");
        // Whatever ran between the phases left the counter below a live ID.
        func.next_vreg = 0;
        let refused = refusal(pipeline.run_regalloc(&mut func));
        assert_eq!(refused.boundary, "register allocation entry", "{level:?}");
        assert_eq!(refused.error.domain(), MachIdDomain::VReg);
    }
}

#[test]
fn register_allocation_admits_its_own_output() {
    let pipeline = darwin(OptLevel::O2);
    let mut func = small();
    pipeline
        .run_optimization_checked(&mut func)
        .expect("optimize");
    pipeline.run_regalloc(&mut func).expect("allocate");
    assert_eq!(func.admit_id_counters(), Ok(()));
}

#[test]
fn branch_resolution_refuses_a_dangling_slot_left_by_frame_lowering() {
    let pipeline = darwin(OptLevel::O2);
    let mut func = small();
    pipeline
        .run_optimization_checked(&mut func)
        .expect("optimize");
    pipeline.run_regalloc(&mut func).expect("allocate");
    lower_copies(&mut func).expect("copies");
    pipeline.run_frame_lowering(&mut func).expect("frame");
    // A debug variable bound to a slot no arena entry backs yet: the next
    // slot allocation (or a relaxation scratch slot) would alias it.
    let past = func.stack_slots.len() as u32;
    func.debug_meta
        .local_variables
        .push(trust_cg_ir::function::DebugLocalVariable {
            name: "x".into(),
            ty: trust_cg_ir::function::DebugBaseType::I64,
            storage: trust_cg_ir::function::DebugVariableStorage::StackSlot(past),
            decl_line: 1,
        });
    let refused = refusal(resolve_branches_after_authority(&mut func));
    assert_eq!(refused.boundary, "branch resolution entry");
    assert_eq!(
        refused.error,
        MachIdAdmissionError::StaleCounter {
            domain: MachIdDomain::StackSlot,
            counter: u64::from(past),
            live_id: past,
            site: MachIdSite::DebugLocal { index: 0 },
        }
    );
}

#[test]
fn the_optimization_entry_refuses_a_dangling_protector_slot() {
    // Refused at the optimization entry, although nothing reads the slot
    // before frame lowering.
    let mut func = small();
    func.stack_protector_slot = Some(StackSlotId(0));
    let refused = refusal(darwin(OptLevel::O1).run_optimization_checked(&mut func));
    assert_eq!(refused.error.domain(), MachIdDomain::StackSlot);
    assert_eq!(refused.error.code(), "TCG-MIR-STALE-ID-COUNTER");
}

#[test]
fn frame_lowering_reports_its_first_allocation_refusal_by_name() {
    let pipeline = darwin(OptLevel::O2);
    let mut func = small();
    func.stack_protector = trust_cg_ir::StackProtectorMode::StackGuard;
    pipeline
        .run_optimization_checked(&mut func)
        .expect("optimize");
    pipeline.run_regalloc(&mut func).expect("allocate");
    lower_copies(&mut func).expect("copies");
    // Left behind after the register-allocation exit: a debug variable bound
    // to the slot ID the protector slot would be given.
    let protector_id = func.stack_slots.len() as u32;
    func.debug_meta
        .local_variables
        .push(trust_cg_ir::function::DebugLocalVariable {
            name: "x".into(),
            ty: trust_cg_ir::function::DebugBaseType::I64,
            storage: trust_cg_ir::function::DebugVariableStorage::StackSlot(protector_id),
            decl_line: 1,
        });
    let refused = refusal(pipeline.run_frame_lowering(&mut func));
    assert_eq!(refused.boundary, "the first allocation in frame lowering");
    assert_eq!(refused.error.domain(), MachIdDomain::StackSlot);
    assert_eq!(func.stack_protector_slot, None, "no slot was issued");
    assert_eq!(func.stack_slots.len() as u32, protector_id);
}

#[test]
fn frame_insertion_admits_before_its_staged_numbering() {
    // Frame insertion numbers its prologue/epilogue instructions from the
    // arena length in a staged plan. A sidecar keyed by the next instruction
    // ID, left after register allocation, would name the first inserted
    // instruction and then pass every later admission; it is refused first.
    let pipeline = darwin(OptLevel::O2);
    let mut func = small();
    pipeline
        .run_optimization_checked(&mut func)
        .expect("optimize");
    pipeline.run_regalloc(&mut func).expect("allocate");
    lower_copies(&mut func).expect("copies");
    let next = trust_cg_ir::InstId(func.insts.len() as u32);
    func.lowering_provenance
        .insert(next, trust_cg_ir::LoweringProvenance::UNATTRIBUTED);
    let insts = func.insts.len();
    let refused = refusal(pipeline.run_frame_lowering(&mut func));
    assert_eq!(refused.boundary, "the first allocation in frame lowering");
    assert_eq!(refused.error.domain(), MachIdDomain::Inst);
    assert_eq!(func.insts.len(), insts, "no instruction was inserted");

    let mut clean = small();
    pipeline
        .run_optimization_checked(&mut clean)
        .expect("optimize");
    pipeline.run_regalloc(&mut clean).expect("allocate");
    lower_copies(&mut clean).expect("copies");
    pipeline.run_frame_lowering(&mut clean).expect("frame");
    assert_eq!(clean.admit_id_counters(), Ok(()));
}

#[test]
fn an_in_place_phase_is_refused_at_its_first_allocation() {
    // The CEGIS and scheduler phases run under this wrapper: a phase that
    // allocates from a counter left stale before it is refused by name, and
    // one that allocates nothing passes the function on to the next boundary.
    let mut stale = small();
    stale.next_vreg = 1;
    let refused = refusal(admit_phase_allocations(
        &mut stale,
        "the codegen scheduler",
        |func| func.alloc_vreg(),
    ));
    assert_eq!(
        refused.boundary,
        "the first allocation in the codegen scheduler"
    );
    assert_eq!(refused.error.domain(), MachIdDomain::VReg);

    let mut untouched = small();
    untouched.next_vreg = 1;
    let ran = admit_phase_allocations(&mut untouched, "CEGIS superoptimization", |_| 7);
    assert!(matches!(ran, Ok(7)), "{ran:?}");
    let later = refusal(darwin(OptLevel::O2).run_regalloc(&mut untouched));
    assert_eq!(later.boundary, "register allocation entry");
}

#[test]
fn aot_profile_instrumentation_refuses_a_stale_counter_instead_of_repairing_it() {
    // `aot_profile` numbers its counter registers above the highest live
    // register it finds; behind the admission, a stale counter is refused by
    // name and neither the function nor the site map changes.
    let sink = Arc::new(std::sync::Mutex::new(
        trust_cg_opt::pgo::CounterMap::default(),
    ));
    let mut func = small();
    func.next_vreg = 1;
    let before = format!("{func:?}");
    let refused = refusal(inject_aot_block_counters(&mut func, &sink));
    assert_eq!(refused.boundary, "AOT profile instrumentation entry");
    assert_eq!(refused.error.domain(), MachIdDomain::VReg);
    assert_eq!(format!("{func:?}"), before);
    assert_eq!(func.next_vreg, 1, "the counter is not repaired");
    assert!(sink.lock().expect("sink").sites.is_empty());

    // An admitted function is instrumented from its own counter.
    let mut clean = small();
    inject_aot_block_counters(&mut clean, &sink).expect("instrument");
    assert_eq!(sink.lock().expect("sink").sites.len(), 1);
    assert_eq!(clean.admit_id_counters(), Ok(()));
}
