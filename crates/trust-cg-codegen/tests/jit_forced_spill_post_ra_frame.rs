#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_ir::inst::AArch64Opcode;
use trust_ir::ty::FuncTy;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{BinOp, Block, Constant, Function, Inst, InstrNode, Module, Ty};

type ForcedSpillFn = unsafe extern "C" fn(*const i64) -> i64;

struct TrustIrBuilder {
    next_value: u32,
    body: Vec<InstrNode>,
}

impl TrustIrBuilder {
    fn new() -> Self {
        Self {
            next_value: 0,
            body: Vec::new(),
        }
    }

    fn fresh_value(&mut self) -> ValueId {
        let id = ValueId(self.next_value);
        self.next_value += 1;
        id
    }

    fn reserve_params(&mut self, count: u32) -> Vec<ValueId> {
        (0..count).map(|_| self.fresh_value()).collect()
    }

    fn emit(&mut self, inst: Inst) -> ValueId {
        let result = self.fresh_value();
        self.body.push(InstrNode::new(inst).with_result(result));
        result
    }

    fn emit_void(&mut self, inst: Inst) {
        self.body.push(InstrNode::new(inst));
    }

    fn const_i64(&mut self, value: i64) -> ValueId {
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

    fn index(&mut self, base: ValueId, index: ValueId) -> ValueId {
        self.emit(Inst::GEP {
            pointee_ty: Ty::I64,
            base,
            indices: vec![index],
            inbounds: false,
        })
    }

    fn load_i64(&mut self, ptr: ValueId) -> ValueId {
        self.emit(Inst::Load {
            ty: Ty::I64,
            ptr,
            volatile: false,
            align: None,
        })
    }

    fn seal(self, block_id: BlockId, params: Vec<(ValueId, Ty)>) -> Block {
        let mut block = Block::new(block_id);
        for (value, ty) in params {
            block = block.with_param(value, ty);
        }
        block.body = self.body;
        block
    }
}

fn emit_forced_spill_kernel(lanes: usize) -> Module {
    let mut b = TrustIrBuilder::new();
    let params = b.reserve_params(1);
    let input = params[0];
    let mut live_values = Vec::with_capacity(lanes);

    for lane in 0..lanes {
        let idx = b.const_i64(lane as i64);
        let addr = b.index(input, idx);
        let loaded = b.load_i64(addr);
        let multiplier = b.const_i64(((lane as i64) % 7) + 2);
        let product = b.binop(BinOp::Mul, loaded, multiplier);
        let bias = b.const_i64((lane as i64 * 17) - 31);
        live_values.push(b.binop(BinOp::Add, product, bias));
    }
    let call_result = b.emit(Inst::Call {
        callee: FuncId(1),
        args: vec![live_values[0]],
    });
    let mut acc = call_result;
    for value in live_values {
        acc = b.binop(BinOp::Add, acc, value);
    }
    b.emit_void(Inst::Return { values: vec![acc] });

    let mut module = Module::new("jit_forced_spill_post_ra_frame");
    let caller_ty_id = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let callee_ty_id = module.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut caller = Function::new(FuncId(0), "forced_spill_reduce", caller_ty_id, BlockId(0));
    caller.blocks = vec![b.seal(BlockId(0), vec![(input, Ty::Ptr)])];
    module.add_function(caller);

    let mut callee_builder = TrustIrBuilder::new();
    let callee_params = callee_builder.reserve_params(1);
    let one = callee_builder.const_i64(1);
    let ret = callee_builder.binop(BinOp::Add, callee_params[0], one);
    callee_builder.emit_void(Inst::Return { values: vec![ret] });
    let mut callee = Function::new(
        FuncId(1),
        "forced_spill_identity_plus_one",
        callee_ty_id,
        BlockId(0),
    );
    callee.blocks = vec![callee_builder.seal(BlockId(0), vec![(callee_params[0], Ty::I64)])];
    module.add_function(callee);
    module
}

fn compile_forced_spill_module(module: &Module) -> (JitCompilationResult, ForcedSpillFn) {
    let config = CompilerConfig {
        opt_level: OptLevel::O2,
        parallel: false,
        ..CompilerConfig::default()
    };
    let compiler = Compiler::new(config);
    let result = compiler
        .compile_module_to_jit(module, &HashMap::new())
        .expect("O2 JIT compile should succeed for forced-spill regression");
    let f = unsafe {
        result
            .buffer
            .get_fn_bound::<ForcedSpillFn>("forced_spill_reduce")
            .expect("forced_spill_reduce symbol missing")
    }
    .into_inner();
    (result, f)
}

fn reference_forced_spill(input: &[i64]) -> i64 {
    let first_lane = input[0] * 2 - 31;
    first_lane
        + 1
        + input
            .iter()
            .enumerate()
            .map(|(lane, value)| value * (((lane as i64) % 7) + 2) + (lane as i64 * 17) - 31)
            .sum::<i64>()
}

#[test]
fn jit_forced_spill_o2_survives_post_ra_copy_lowering_and_frame_elimination() {
    const LANES: usize = 192;

    let module = emit_forced_spill_kernel(LANES);
    let lir_functions = trust_cg_lower::translate_module(&module)
        .expect("forced-spill trust_ir module should lower before O2 prepare");
    assert_eq!(
        lir_functions.len(),
        2,
        "expected caller plus helper function"
    );

    let pipeline_config = PipelineConfig {
        opt_level: OptLevel::O2,
        ..PipelineConfig::default()
    };
    let pipeline = Pipeline::new(pipeline_config);
    let (prepared, metrics) = pipeline
        .prepare_function_with_metrics(&lir_functions[0].0, Some(&lir_functions[0].1))
        .expect("O2 prepare should survive regalloc, post-RA, and frame lowering");

    assert!(
        metrics.spill_slot_count > 0,
        "forced-spill fixture should allocate spill slots; metrics={metrics:#?}"
    );
    assert!(
        prepared
            .insts
            .iter()
            .all(|inst| inst.opcode != AArch64Opcode::Copy),
        "post-RA copy lowering must remove Copy pseudo-ops"
    );
    assert!(
        metrics.timings.frame_lowering.is_some(),
        "prepare metrics should show the O2 path reached frame lowering"
    );

    let (_jit, f) = compile_forced_spill_module(&module);
    let input: Vec<i64> = (0..LANES)
        .map(|lane| ((lane as i64 * 13) ^ 0x55) - 200)
        .collect();
    let expected = reference_forced_spill(&input);
    let actual = unsafe { f(input.as_ptr()) };

    assert_eq!(
        actual, expected,
        "O2 forced-spill JIT result should match the reference implementation"
    );
}

/// FIX 1 regression: post-RA copy coalescing used to be gated to spill-free
/// functions, so spillful (high-register-pressure) functions — exactly the
/// ones that emit the most redundant reg-reg moves — got no coalescing at all.
/// The forced-spill kernel both spills and emits coalescible copies (call-arg
/// setup, phi-elimination commits). This asserts coalescing now fires on a
/// spillful function and that the executed result is still correct, proving the
/// transform is behavior-preserving.
#[test]
fn jit_forced_spill_o2_coalesces_redundant_copies_on_spillful_function() {
    const LANES: usize = 192;

    let module = emit_forced_spill_kernel(LANES);
    let lir_functions = trust_cg_lower::translate_module(&module)
        .expect("forced-spill trust_ir module should lower before O2 prepare");

    let pipeline_config = PipelineConfig {
        opt_level: OptLevel::O2,
        ..PipelineConfig::default()
    };
    let pipeline = Pipeline::new(pipeline_config);
    let (_prepared, metrics) = pipeline
        .prepare_function_with_metrics(&lir_functions[0].0, Some(&lir_functions[0].1))
        .expect("O2 prepare should survive regalloc, post-RA, and frame lowering");

    assert!(
        metrics.spill_slot_count > 0,
        "fixture must spill to exercise the previously-gated coalescing path; metrics={metrics:#?}"
    );
    assert!(
        metrics.post_ra_copies_coalesced > 0,
        "post-RA coalescing must now fire on a spillful function (FIX 1); metrics={metrics:#?}"
    );

    // Semantics must be preserved: coalescing only removes redundant moves.
    let (_jit, f) = compile_forced_spill_module(&module);
    let input: Vec<i64> = (0..LANES)
        .map(|lane| ((lane as i64 * 13) ^ 0x55) - 200)
        .collect();
    let expected = reference_forced_spill(&input);
    let actual = unsafe { f(input.as_ptr()) };
    assert_eq!(
        actual, expected,
        "spillful coalesced JIT result must match the reference implementation"
    );
}
