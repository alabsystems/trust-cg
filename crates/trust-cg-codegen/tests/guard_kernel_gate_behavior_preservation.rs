// guard_kernel_gate_behavior_preservation.rs — report-only guard-authority regression
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Fail-closed regression for the former `TRUST_CG_GUARD_KERNEL_GATE` experiment.
//!
//! Public TrustIR annotations, public proof statuses, adapter-synthesized `Discharged` statuses, and
//! environment-variable spellings are report-only. None is proof authority. This test constructs
//! guard-bearing functions exercising both `InBounds` and `NotNull`, lowers them through the real
//! pipeline, and proves that the guards survive with the historical env flag set to either `0` or
//! `1`.
//!
//! The prepared `MachFunction` is the decisive AArch64 observation: a surviving bounds carrier
//! expands to `CMP + B.LO + BRK`, and a surviving null carrier expands to `CBNZ + BRK`. The x86
//! observation counts the corresponding `UD2` trap blocks in emitted object code.
//!
//! A pending `ProofRef` control must have the same result. This prevents downstream construction of
//! synthetic status from accidentally recovering authority under another spelling.

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::env_lock;
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::{Target, TargetSpec};
use trust_cg_ir::MachOperand;
use trust_cg_ir::function::MachFunction;
use trust_cg_ir::inst::AArch64Opcode;

use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};
use trust_ir::value::ProofId;
use trust_ir::{
    Block as TrustIrBlock, BlockId, FuncId, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module, ProofAnnotation, Ty, ValueId,
};

const ARRAY_LEN: u64 = 8;
const BOUNDS_OBLIGATION_ID: u32 = 21;
const NULL_OBLIGATION_ID: u32 = 22;

/// Which report-only public metadata spelling a fixture uses.
#[derive(Clone, Copy)]
enum ProofMode {
    /// Public safety annotations without an explicit `ProofRef`. The adapter may synthesize a
    /// report-only status, but downstream codegen must not treat it as proof authority.
    ReportOnlyAnnotations,
    /// The same annotations plus public `ProofRef`s to pending module obligations.
    PendingProofRefs,
}

/// Build a module + function exercising BOTH guard carriers in one body:
///   * `ExtractElement array[index]` carrying `InBounds`  -> bounds-check carrier
///   * `Load *ptr`                    carrying `NotNull`   -> null-check carrier
///     and returning the loaded value (so the load is live and not DCE'd).
fn build(mode: ProofMode) -> (Module, TrustIrFunction) {
    let mut module = Module::new("guard_kernel_gate_behavior_preservation");
    let elem_ty = module.add_type(Ty::I64);
    let array_ty = Ty::Array(elem_ty, ARRAY_LEN);
    let ft = module.add_func_type(FuncTy {
        // params: (array, index, ptr)
        params: vec![array_ty.clone(), Ty::I64, Ty::Ptr],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "two_guards", ft, BlockId::new(0));

    // value ids: 0=array, 1=index, 2=ptr; 3=array[index]; 4=*ptr; 5=sum
    let mut extract = InstrNode::new(Inst::ExtractElement {
        ty: Ty::I64,
        array: ValueId::new(0),
        index: ValueId::new(1),
    })
    .with_result(ValueId::new(3))
    .with_proof(ProofAnnotation::InBounds);

    let mut load = InstrNode::new(Inst::Load {
        ty: Ty::I64,
        ptr: ValueId::new(2),
        volatile: false,
        align: None,
    })
    .with_result(ValueId::new(4))
    .with_proof(ProofAnnotation::NotNull);

    if let ProofMode::PendingProofRefs = mode {
        extract = extract.with_proof(ProofAnnotation::ProofRef(ProofId::new(
            BOUNDS_OBLIGATION_ID,
        )));
        load = load.with_proof(ProofAnnotation::ProofRef(ProofId::new(NULL_OBLIGATION_ID)));
    }

    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (ValueId::new(0), array_ty),
            (ValueId::new(1), Ty::I64),
            (ValueId::new(2), Ty::Ptr),
        ],
        body: vec![
            extract,
            load,
            InstrNode::new(Inst::BinOp {
                op: trust_ir::inst::BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(3),
                rhs: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(5)],
            }),
        ],
    }];

    if let ProofMode::PendingProofRefs = mode {
        module.proof_obligations.push(ProofObligation::new(
            ProofId::new(BOUNDS_OBLIGATION_ID),
            ObligationKind::MemorySafety,
            ProofStatus::Pending,
            "array index is in bounds",
        ));
        module.proof_obligations.push(ProofObligation::new(
            ProofId::new(NULL_OBLIGATION_ID),
            ObligationKind::MemorySafety,
            ProofStatus::Pending,
            "pointer is non-null",
        ));
    }

    module.add_function(func.clone());
    (module, func)
}

// ---------------------------------------------------------------------------
// AArch64 arm.
// ---------------------------------------------------------------------------

/// The full opcode+operand stream of the prepared function, in block-layout order. Two prepared
/// functions with the same stream are observably identical at the machine-IR level (and therefore
/// encode to the same bytes).
fn opcode_stream(func: &MachFunction) -> Vec<(AArch64Opcode, Vec<MachOperand>)> {
    let mut stream = Vec::new();
    for &block_id in &func.block_order {
        for &inst_id in &func.block(block_id).insts {
            let inst = func.inst(inst_id);
            stream.push((inst.opcode, inst.operands.clone()));
        }
    }
    stream
}

fn brk_count(stream: &[(AArch64Opcode, Vec<MachOperand>)]) -> usize {
    stream
        .iter()
        .filter(|(op, _)| *op == AArch64Opcode::Brk)
        .count()
}

fn prepare_aarch64(module: &Module, func: &TrustIrFunction) -> MachFunction {
    let (lir_func, proof_ctx) =
        trust_cg_lower::translate_function(func, module).expect("adapter translate");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O2,
        verify: false,
        ..PipelineConfig::default()
    });
    pipeline
        .prepare_function_with_metrics_and_trust_ir_module(
            &lir_func,
            Some(&proof_ctx),
            module,
            func,
        )
        .map(|(prepared, _metrics)| prepared)
        .expect("prepare function")
}

/// The historical flag is a process-global env var. ALL scenarios (AArch64 + x86, spellings `0`
/// and `1`) run inside this ONE `#[test]` so the test runner's thread pool can never
/// interleave a set/remove from a sibling test. Each arm is a helper invoked serially here.
#[test]
fn report_only_annotations_never_remove_inbounds_or_notnull_guards() {
    aarch64_env_spellings_keep_inbounds_and_notnull();
    x86_env_spellings_keep_inbounds_and_notnull();
    x86_env_spellings_keep_notnull_alone();
    // Each arm runs inside an `env_lock::with_env_edits` scope that restores the
    // flag's prior value on exit, so it is always left in its default (unset)
    // state without an extra manual cleanup here.
}

/// AArch64: both report-only annotations retain their runtime guards under both env spellings.
fn aarch64_env_spellings_keep_inbounds_and_notnull() {
    let (module, func) = build(ProofMode::ReportOnlyAnnotations);

    // Historical flag spellings are deliberately inert for authority decisions.
    let (off, on, control) = env_lock::with_env_edits(|env| {
        env.set("TRUST_CG_GUARD_KERNEL_GATE", "0");
        let off = opcode_stream(&prepare_aarch64(&module, &func));

        env.set("TRUST_CG_GUARD_KERNEL_GATE", "1");
        let on = opcode_stream(&prepare_aarch64(&module, &func));

        // A pending-reference spelling must not differ from the synthesized-status spelling.
        let (ctrl_module, ctrl_func) = build(ProofMode::PendingProofRefs);
        let control = opcode_stream(&prepare_aarch64(&ctrl_module, &ctrl_func));
        (off, on, control)
    });

    assert_eq!(
        off, on,
        "AArch64: env spellings must not alter codegen or grant proof authority"
    );
    assert_eq!(
        brk_count(&off),
        2,
        "report-only annotations must retain both runtime guards with env=0"
    );
    assert_eq!(
        brk_count(&on),
        2,
        "report-only annotations must retain both runtime guards with env=1"
    );
    assert_eq!(
        control, on,
        "pending public ProofRefs must not change the fail-closed result"
    );
}

// ---------------------------------------------------------------------------
// x86-64 arm.
// ---------------------------------------------------------------------------

/// Count UD2 (0F 0B) occurrences in raw object bytes. A surviving x86 bounds-check carrier expands to
/// a UD2 trap block; the eagerly-expanded null guard ALSO ends in a UD2 trap block. So UD2 presence
/// tracks "a guard trap survives".
fn ud2_count(bytes: &[u8]) -> usize {
    bytes.windows(2).filter(|w| w == b"\x0F\x0B").count()
}

fn compile_x86_object(module: &Module) -> Vec<u8> {
    let spec = TargetSpec::parse("x86_64-apple-darwin").expect("parse x86_64-apple-darwin");
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            target: Target::X86_64,
            ..CompilerConfig::default()
        },
        spec,
    );
    compiler.compile(module).expect("x86 compile").object_code
}

/// x86: both report-only carriers remain runtime checks and emitted objects are byte-identical under
/// both historical env spellings.
fn x86_env_spellings_keep_inbounds_and_notnull() {
    let (module, _func) = build(ProofMode::ReportOnlyAnnotations);

    let (off, on, on_ud2) = env_lock::with_env_edits(|env| {
        env.set("TRUST_CG_GUARD_KERNEL_GATE", "0");
        let off = compile_x86_object(&module);
        let off_ud2 = ud2_count(&off);
        assert!(
            off_ud2 >= 2,
            "env=0 keeps BOTH guards: the bounds (CMP+Jcc+UD2) and null (TEST+Jcc+UD2) traps survive \
             (off={off_ud2})"
        );

        env.set("TRUST_CG_GUARD_KERNEL_GATE", "1");
        let on = compile_x86_object(&module);
        let on_ud2 = ud2_count(&on);
        (off, on, on_ud2)
    });

    assert_eq!(
        off, on,
        "x86: historical env spellings must be authority-inert and byte-identical"
    );
    assert!(
        on_ud2 >= 2,
        "env=1 keeps BOTH report-only guards on x86 (on={on_ud2})"
    );
}

/// Isolate the NotNull guard on x86 and prove neither env spelling removes its runtime trap.
fn x86_env_spellings_keep_notnull_alone() {
    let module = build_notnull_only();

    let (off, on, on_ud2) = env_lock::with_env_edits(|env| {
        env.set("TRUST_CG_GUARD_KERNEL_GATE", "0");
        let off = compile_x86_object(&module);
        let off_ud2 = ud2_count(&off);
        assert!(
            off_ud2 >= 1,
            "gate OFF keeps the NotNull guard: its TEST+Jcc(E)+UD2 trap survives (off={off_ud2})"
        );

        env.set("TRUST_CG_GUARD_KERNEL_GATE", "1");
        let on = compile_x86_object(&module);
        let on_ud2 = ud2_count(&on);
        (off, on, on_ud2)
    });

    assert_eq!(
        off, on,
        "x86: env spellings must not remove a report-only NotNull guard"
    );
    assert!(
        on_ud2 >= 1,
        "env=1 keeps the report-only NotNull runtime guard (on={on_ud2})"
    );
}

/// Build a module + function with ONLY a NotNull `Load` carrier (no InBounds / bounds carrier), used
/// to isolate the x86 NotNull behavior.
fn build_notnull_only() -> Module {
    let mut module = Module::new("guard_kernel_gate_notnull_only");
    let ft = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), "notnull_only", ft, BlockId::new(0));
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                volatile: false,
                align: None,
            })
            .with_result(ValueId::new(1))
            .with_proof(ProofAnnotation::NotNull),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module.add_function(func);
    module
}
