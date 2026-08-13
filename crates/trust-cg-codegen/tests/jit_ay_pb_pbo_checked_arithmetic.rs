// trust-cg-codegen/tests/jit_ay_pb_pbo_checked_arithmetic.rs
//
// ay PB/PBO checked-objective status ABI JIT smoke coverage.

#![cfg(target_arch = "aarch64")]

#[path = "common/fixture_contract.rs"]
mod fixture_contract;
use fixture_contract::FixtureContractLookup;

use std::collections::HashMap;
use std::mem::{align_of, offset_of, size_of};

use trust_cg_codegen::ay_pb_pbo_checked_arithmetic_contract::{
    AY_PB_PBO_CHECKED_OBJECTIVE_SYMBOL, AY_PB_PBO_OBJECTIVE_STATUS_RECORD,
    ay_pb_pbo_checked_objective_manifest, ay_pb_pbo_checked_objective_signature,
    ay_pb_pbo_checked_objective_symbol_lookup_contract,
};
use trust_cg_codegen::jit::{JitCompiler, JitConfig};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction,
    ICmpOp, Inst, InstrNode, Module as TrustIrModule, OverflowOp, Ty, ValueId,
};

type AYPbPboObjectiveFn =
    unsafe extern "C" fn(*const i64, *const i64, i64, *mut AYPbPboObjectiveStatusAbi);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum AYPbPboStatus {
    Ok = 0,
    Overflow = 1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum AYPbPboDeopt {
    None = 0,
    PbPboCheckedArithmeticOverflow = 1,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
struct AYPbPboObjectiveStatusAbi {
    status: u8,
    deopt: u8,
    reserved: [u8; 6],
    objective: i64,
    detail: i64,
}

impl AYPbPboObjectiveStatusAbi {
    const fn poisoned() -> Self {
        Self {
            status: 0xff,
            deopt: 0xff,
            reserved: [0xaa; 6],
            objective: i64::MIN,
            detail: i64::MIN,
        }
    }

    fn assert_matches(
        &self,
        status: AYPbPboStatus,
        deopt: AYPbPboDeopt,
        objective: i64,
        detail: i64,
    ) {
        assert_eq!(self.status, status as u8);
        assert_eq!(self.deopt, deopt as u8);
        assert_eq!(self.reserved, [0xaa; 6]);
        assert_eq!(self.objective, objective);
        assert_eq!(self.detail, detail);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PbPboObjectiveOracle {
    status: AYPbPboStatus,
    deopt: AYPbPboDeopt,
    objective: i64,
    detail: i64,
}

struct TrustIrBuilder {
    next_value: u32,
    blocks: Vec<TrustIrBlock>,
    current_block: BlockId,
    current_body: Vec<InstrNode>,
}

impl TrustIrBuilder {
    fn new(entry_block: BlockId) -> Self {
        Self {
            next_value: 0,
            blocks: Vec::new(),
            current_block: entry_block,
            current_body: Vec::new(),
        }
    }

    fn fresh_value(&mut self) -> ValueId {
        let id = ValueId::new(self.next_value);
        self.next_value += 1;
        id
    }

    fn reserve_params(&mut self, count: u32) -> Vec<ValueId> {
        (0..count).map(|_| self.fresh_value()).collect()
    }

    fn emit(&mut self, inst: Inst) -> ValueId {
        let result = self.fresh_value();
        self.current_body
            .push(InstrNode::new(inst).with_result(result));
        result
    }

    fn emit_void(&mut self, inst: Inst) {
        self.current_body.push(InstrNode::new(inst));
    }

    fn const_int(&mut self, ty: Ty, value: i128) -> ValueId {
        self.emit(Inst::Const {
            ty,
            value: Constant::Int(value),
        })
    }

    fn const_i64(&mut self, value: i64) -> ValueId {
        self.const_int(Ty::I64, i128::from(value))
    }

    fn binop(&mut self, op: BinOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.emit(Inst::BinOp { op, ty, lhs, rhs })
    }

    fn overflow(
        &mut self,
        op: OverflowOp,
        ty: Ty,
        lhs: ValueId,
        rhs: ValueId,
    ) -> (ValueId, ValueId) {
        let value = self.fresh_value();
        let flag = self.fresh_value();
        self.current_body.push(
            InstrNode::new(Inst::Overflow { op, ty, lhs, rhs })
                .with_result(value)
                .with_result(flag),
        );
        (value, flag)
    }

    fn load(&mut self, ty: Ty, ptr: ValueId) -> ValueId {
        self.emit(Inst::Load {
            ty,
            ptr,
            volatile: false,
            align: None,
        })
    }

    fn store_volatile(&mut self, ty: Ty, ptr: ValueId, value: ValueId) {
        self.emit_void(Inst::Store {
            ty,
            ptr,
            value,
            volatile: false,
            align: None,
        });
    }

    fn gep(&mut self, pointee_ty: Ty, base: ValueId, index: ValueId) -> ValueId {
        self.emit(Inst::GEP {
            pointee_ty,
            base,
            indices: vec![index],
            inbounds: false,
        })
    }

    fn icmp(&mut self, op: ICmpOp, ty: Ty, lhs: ValueId, rhs: ValueId) -> ValueId {
        self.emit(Inst::ICmp { op, ty, lhs, rhs })
    }

    fn seal_block_with_params(&mut self, params: Vec<(ValueId, Ty)>) {
        let body = std::mem::take(&mut self.current_body);
        let mut block = TrustIrBlock::new(self.current_block);
        for (value, ty) in params {
            block = block.with_param(value, ty);
        }
        block.body = body;
        self.blocks.push(block);
    }

    fn start_block(&mut self, id: BlockId) {
        self.current_block = id;
    }
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn byte_gep(b: &mut TrustIrBuilder, base: ValueId, offset: i128) -> ValueId {
    let offset = b.const_int(Ty::U64, offset);
    b.gep(Ty::U8, base, offset)
}

fn store_u8_const(b: &mut TrustIrBuilder, out: ValueId, offset: i128, byte: u8) {
    let ptr = if offset == 0 {
        out
    } else {
        byte_gep(b, out, offset)
    };
    let value = b.const_int(Ty::U8, i128::from(byte));
    b.store_volatile(Ty::U8, ptr, value);
}

fn store_i64_value(b: &mut TrustIrBuilder, out: ValueId, offset: i128, value: ValueId) {
    let ptr = byte_gep(b, out, offset);
    b.store_volatile(Ty::I64, ptr, value);
}

fn write_objective_status(
    b: &mut TrustIrBuilder,
    out: ValueId,
    status: AYPbPboStatus,
    deopt: AYPbPboDeopt,
    objective: ValueId,
    detail: ValueId,
) {
    store_u8_const(b, out, 0, status as u8);
    store_u8_const(b, out, 1, deopt as u8);
    store_i64_value(b, out, 8, objective);
    store_i64_value(b, out, 16, detail);
}

fn return_void(b: &mut TrustIrBuilder) {
    b.emit_void(Inst::Return { values: vec![] });
}

fn build_pb_pbo_checked_objective_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("jit_ay_pb_pbo_checked_arithmetic");
    let func_ty_id = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr, Ty::Ptr, Ty::I64, Ty::Ptr],
        returns: vec![],
        is_vararg: false,
    });

    let entry_id = b(0);
    let loop_header_id = b(1);
    let loop_body_id = b(2);
    let add_check_id = b(3);
    let loop_latch_id = b(4);
    let ok_id = b(5);
    let overflow_id = b(6);

    let mut b = TrustIrBuilder::new(entry_id);
    let params = b.reserve_params(4);
    let coeffs = params[0];
    let assignment = params[1];
    let len = params[2];
    let out = params[3];

    let zero_index = b.const_i64(0);
    let zero_acc = b.const_i64(0);
    b.emit_void(Inst::Br {
        target: loop_header_id,
        args: vec![zero_index, zero_acc],
    });
    b.seal_block_with_params(vec![
        (coeffs, Ty::Ptr),
        (assignment, Ty::Ptr),
        (len, Ty::I64),
        (out, Ty::Ptr),
    ]);

    b.start_block(loop_header_id);
    let header_i = b.fresh_value();
    let header_acc = b.fresh_value();
    let keep_looping = b.icmp(ICmpOp::Slt, Ty::I64, header_i, len);
    b.emit_void(Inst::CondBr {
        cond: keep_looping,
        then_target: loop_body_id,
        then_args: vec![header_i, header_acc],
        else_target: ok_id,
        else_args: vec![header_acc],
    });
    b.seal_block_with_params(vec![(header_i, Ty::I64), (header_acc, Ty::I64)]);

    b.start_block(loop_body_id);
    let body_i = b.fresh_value();
    let body_acc = b.fresh_value();
    let coeff_ptr = b.gep(Ty::I64, coeffs, body_i);
    let coeff = b.load(Ty::I64, coeff_ptr);
    let assignment_ptr = b.gep(Ty::I64, assignment, body_i);
    let assignment_value = b.load(Ty::I64, assignment_ptr);
    let (product, mul_overflow) =
        b.overflow(OverflowOp::MulOverflow, Ty::I64, coeff, assignment_value);
    b.emit_void(Inst::CondBr {
        cond: mul_overflow,
        then_target: overflow_id,
        then_args: vec![body_i],
        else_target: add_check_id,
        else_args: vec![body_i, body_acc, product],
    });
    b.seal_block_with_params(vec![(body_i, Ty::I64), (body_acc, Ty::I64)]);

    b.start_block(add_check_id);
    let add_i = b.fresh_value();
    let add_acc = b.fresh_value();
    let add_product = b.fresh_value();
    let (next_acc, add_overflow) =
        b.overflow(OverflowOp::AddOverflow, Ty::I64, add_acc, add_product);
    b.emit_void(Inst::CondBr {
        cond: add_overflow,
        then_target: overflow_id,
        then_args: vec![add_i],
        else_target: loop_latch_id,
        else_args: vec![add_i, next_acc],
    });
    b.seal_block_with_params(vec![
        (add_i, Ty::I64),
        (add_acc, Ty::I64),
        (add_product, Ty::I64),
    ]);

    b.start_block(loop_latch_id);
    let latch_i = b.fresh_value();
    let latch_acc = b.fresh_value();
    let one = b.const_i64(1);
    let next_i = b.binop(BinOp::Add, Ty::I64, latch_i, one);
    b.emit_void(Inst::Br {
        target: loop_header_id,
        args: vec![next_i, latch_acc],
    });
    b.seal_block_with_params(vec![(latch_i, Ty::I64), (latch_acc, Ty::I64)]);

    b.start_block(ok_id);
    let final_objective = b.fresh_value();
    let ok_detail = b.const_i64(0);
    write_objective_status(
        &mut b,
        out,
        AYPbPboStatus::Ok,
        AYPbPboDeopt::None,
        final_objective,
        ok_detail,
    );
    return_void(&mut b);
    b.seal_block_with_params(vec![(final_objective, Ty::I64)]);

    b.start_block(overflow_id);
    let failed_row = b.fresh_value();
    let overflow_objective = b.const_i64(0);
    write_objective_status(
        &mut b,
        out,
        AYPbPboStatus::Overflow,
        AYPbPboDeopt::PbPboCheckedArithmeticOverflow,
        overflow_objective,
        failed_row,
    );
    return_void(&mut b);
    b.seal_block_with_params(vec![(failed_row, Ty::I64)]);

    let mut func = TrustIrFunction::new(
        FuncId::new(0),
        AY_PB_PBO_CHECKED_OBJECTIVE_SYMBOL,
        func_ty_id,
        entry_id,
    );
    func.blocks = b.blocks;
    module.add_function(func);
    module
}

fn compile_objective(
    opt_level: OptLevel,
) -> (trust_cg_codegen::ExecutableBuffer, AYPbPboObjectiveFn) {
    let module = build_pb_pbo_checked_objective_module();
    let lowered =
        trust_cg_lower::translate_module(&module).expect("ay PB/PBO objective module lowers");
    assert_eq!(lowered.len(), 1, "expected one lowered objective function");

    let pipeline_config = PipelineConfig {
        opt_level,
        ..PipelineConfig::default()
    };
    let pipeline = Pipeline::new(pipeline_config);
    let mach = pipeline
        .prepare_function_with_proofs(&lowered[0].0, Some(&lowered[0].1))
        .expect("ay PB/PBO objective function prepares");

    let jit = JitCompiler::new(JitConfig {
        opt_level,
        ..JitConfig::default()
    });
    let buffer = jit
        .compile_raw(&[mach], &HashMap::new())
        .expect("ay PB/PBO objective function JIT compiles");
    let manifest = ay_pb_pbo_checked_objective_manifest();
    let contract = ay_pb_pbo_checked_objective_symbol_lookup_contract(&manifest);
    let f = unsafe {
        buffer
            .get_fixture_contract_symbol_bound::<AYPbPboObjectiveFn>(&manifest, &contract)
            .expect("ay PB/PBO objective symbol satisfies artifact contract")
            .into_fn()
    };

    (buffer, f)
}

fn run_case(
    f: AYPbPboObjectiveFn,
    coeffs: &[i64],
    assignment: &[i64],
    expected_status: AYPbPboStatus,
    expected_deopt: AYPbPboDeopt,
    expected_objective: i64,
    expected_detail: i64,
) {
    assert_eq!(coeffs.len(), assignment.len());

    let mut out = AYPbPboObjectiveStatusAbi::poisoned();
    unsafe {
        f(
            coeffs.as_ptr(),
            assignment.as_ptr(),
            coeffs.len() as i64,
            &mut out,
        );
    }
    out.assert_matches(
        expected_status,
        expected_deopt,
        expected_objective,
        expected_detail,
    );
}

fn checked_i128_to_i64(value: i128) -> Option<i64> {
    if value < i128::from(i64::MIN) || value > i128::from(i64::MAX) {
        None
    } else {
        Some(value as i64)
    }
}

fn i128_checked_objective_oracle(coeffs: &[i64], assignment: &[i64]) -> PbPboObjectiveOracle {
    assert_eq!(coeffs.len(), assignment.len());

    let mut objective = 0_i64;
    for (row, (&coeff, &assigned)) in coeffs.iter().zip(assignment).enumerate() {
        let product = i128::from(coeff) * i128::from(assigned);
        let Some(product) = checked_i128_to_i64(product) else {
            return PbPboObjectiveOracle {
                status: AYPbPboStatus::Overflow,
                deopt: AYPbPboDeopt::PbPboCheckedArithmeticOverflow,
                objective: 0,
                detail: row as i64,
            };
        };
        let sum = i128::from(objective) + i128::from(product);
        let Some(sum) = checked_i128_to_i64(sum) else {
            return PbPboObjectiveOracle {
                status: AYPbPboStatus::Overflow,
                deopt: AYPbPboDeopt::PbPboCheckedArithmeticOverflow,
                objective: 0,
                detail: row as i64,
            };
        };
        objective = sum;
    }

    PbPboObjectiveOracle {
        status: AYPbPboStatus::Ok,
        deopt: AYPbPboDeopt::None,
        objective,
        detail: 0,
    }
}

fn run_oracle_case(f: AYPbPboObjectiveFn, coeffs: &[i64], assignment: &[i64]) {
    let oracle = i128_checked_objective_oracle(coeffs, assignment);
    run_case(
        f,
        coeffs,
        assignment,
        oracle.status,
        oracle.deopt,
        oracle.objective,
        oracle.detail,
    );
}

#[test]
fn ay_pb_pbo_objective_status_abi_layout_is_ready_for_contract_type() {
    assert_eq!(size_of::<AYPbPboObjectiveStatusAbi>(), 24);
    assert_eq!(align_of::<AYPbPboObjectiveStatusAbi>(), 8);
    assert_eq!(offset_of!(AYPbPboObjectiveStatusAbi, status), 0);
    assert_eq!(offset_of!(AYPbPboObjectiveStatusAbi, deopt), 1);
    assert_eq!(offset_of!(AYPbPboObjectiveStatusAbi, objective), 8);
    assert_eq!(offset_of!(AYPbPboObjectiveStatusAbi, detail), 16);

    let manifest = ay_pb_pbo_checked_objective_manifest();
    let contract = ay_pb_pbo_checked_objective_symbol_lookup_contract(&manifest);
    manifest
        .validate_symbol_lookup(&contract)
        .expect("test-local manifest binds PB/PBO objective ABI, layout, target, and symbol");
    assert_eq!(
        manifest.symbol_signature(AY_PB_PBO_CHECKED_OBJECTIVE_SYMBOL),
        Some(&ay_pb_pbo_checked_objective_signature())
    );
    assert_eq!(
        manifest.layout.records[0].name, AY_PB_PBO_OBJECTIVE_STATUS_RECORD,
        "manifest must carry the status record layout before typed exposure"
    );
}

#[test]
fn ay_pb_pbo_checked_objective_reports_exact_and_first_overflow_o0_o2() {
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let (_buffer, f) = compile_objective(opt_level);

        run_case(f, &[], &[], AYPbPboStatus::Ok, AYPbPboDeopt::None, 0, 0);
        run_case(
            f,
            &[2, -5, 7],
            &[3, 4, -1],
            AYPbPboStatus::Ok,
            AYPbPboDeopt::None,
            -21,
            0,
        );
        run_case(
            f,
            &[i64::MAX, 1, i64::MAX],
            &[1, 1, 2],
            AYPbPboStatus::Overflow,
            AYPbPboDeopt::PbPboCheckedArithmeticOverflow,
            0,
            1,
        );
        run_case(
            f,
            &[11, i64::MAX],
            &[2, 2],
            AYPbPboStatus::Overflow,
            AYPbPboDeopt::PbPboCheckedArithmeticOverflow,
            0,
            1,
        );
    }
}

#[test]
fn ay_pb_pbo_checked_objective_matches_i128_reference_oracle_o0_o2() {
    for opt_level in [OptLevel::O0, OptLevel::O2] {
        let (_buffer, f) = compile_objective(opt_level);

        run_oracle_case(f, &[], &[]);
        run_oracle_case(f, &[2, -5, 7], &[3, 4, -1]);
        run_oracle_case(f, &[i64::MAX, 1], &[1, 1]);
        run_oracle_case(f, &[i64::MAX, 1, i64::MAX], &[1, 1, 2]);
        run_oracle_case(f, &[i64::MIN, -1], &[1, 1]);
        run_oracle_case(f, &[11, i64::MAX], &[2, 2]);
        run_oracle_case(f, &[i64::MIN, i64::MIN], &[-1, 1]);
    }
}
