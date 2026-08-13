// trust-cg-fuzz/src/trust_ir_gen.rs - Random valid trust_ir module generator
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Generates structurally valid trust_ir modules from a seed. The generated
// programs are intentionally narrow: one function, integer arithmetic only
// (i64), single entry block with a linear chain of binops, a return of the
// final value. This is the smallest useful shape that exercises ISel,
// optimization, register allocation, and encoding.
//
// "Valid" means: the interpreter can execute it, and the compiler pipeline
// (Pipeline::compile_function) should accept it. Anything else is either a
// generator bug or a compiler bug — both are interesting.
//
// Expansion roadmap (not in MVP):
//   - Multi-block CFG with CondBr
//   - Multiple integer widths (i8/i16/i32/i128)
//   - Loads/stores with alloca
//   - Multiple functions with Call
//   - Float ops

use crate::prng::Prng;
use trust_ir::{BinOp, ICmpOp, Module as TrustIrModule, Ty};
use trust_ir_build::ModuleBuilder;

/// Configuration for trust_ir random generation.
#[derive(Debug, Clone)]
pub struct GenConfig {
    /// Number of i64 parameters to the generated function.
    pub num_params: u32,
    /// Number of binop instructions in the entry block.
    pub num_ops: u32,
    /// Include division/remainder operators (which the driver must then
    /// guard against divide-by-zero in the oracle).
    pub allow_div: bool,
    /// Include shift operators.
    pub allow_shift: bool,
}

impl Default for GenConfig {
    fn default() -> Self {
        Self {
            num_params: 4,
            num_ops: 8,
            // Divisions and remainder are allowed — we handle zero-input
            // tests explicitly in the driver so the interpreter's
            // DivisionByZero error is caught rather than treated as a
            // miscompile.
            allow_div: true,
            allow_shift: true,
        }
    }
}

/// Operators we know the interpreter and the compiler both support.
fn op_pool(cfg: &GenConfig) -> &'static [BinOp] {
    // Narrow static tables depending on config flags. Using match on
    // (allow_div, allow_shift) keeps the returned slice &'static.
    match (cfg.allow_div, cfg.allow_shift) {
        (true, true) => &[
            BinOp::Add,
            BinOp::Sub,
            BinOp::Mul,
            BinOp::SDiv,
            BinOp::UDiv,
            BinOp::SRem,
            BinOp::URem,
            BinOp::And,
            BinOp::Or,
            BinOp::Xor,
            BinOp::Shl,
            BinOp::LShr,
            BinOp::AShr,
        ],
        (true, false) => &[
            BinOp::Add,
            BinOp::Sub,
            BinOp::Mul,
            BinOp::SDiv,
            BinOp::UDiv,
            BinOp::SRem,
            BinOp::URem,
            BinOp::And,
            BinOp::Or,
            BinOp::Xor,
        ],
        (false, true) => &[
            BinOp::Add,
            BinOp::Sub,
            BinOp::Mul,
            BinOp::And,
            BinOp::Or,
            BinOp::Xor,
            BinOp::Shl,
            BinOp::LShr,
            BinOp::AShr,
        ],
        (false, false) => &[
            BinOp::Add,
            BinOp::Sub,
            BinOp::Mul,
            BinOp::And,
            BinOp::Or,
            BinOp::Xor,
        ],
    }
}

/// The generated module's function always has this name so the driver can
/// look it up from the interpreter by string.
pub const FUZZ_FN_NAME: &str = "fuzz_fn";

/// Fixed output ABI used by the deterministic consumer-shape lane:
/// status:u8, deopt:u8, reserved[6], value:i64, detail:i64.
pub const CONSUMER_STATUS_BYTES: usize = 24;

/// Build a random module from a seed. The returned module has exactly one
/// function named [`FUZZ_FN_NAME`] with `cfg.num_params` i64 parameters and
/// a single i64 return.
pub fn gen_module(seed: u64, cfg: &GenConfig) -> TrustIrModule {
    let mut rng = Prng::new(seed);
    let mut mb = ModuleBuilder::new(format!("fuzz_{}", seed));

    let mut param_tys = Vec::with_capacity(cfg.num_params as usize);
    for _ in 0..cfg.num_params {
        param_tys.push(Ty::I64);
    }
    let ty = mb.add_func_type(param_tys, vec![Ty::I64]);
    let mut fb = mb.function(FUZZ_FN_NAME, ty);

    let entry = fb.create_block();
    // Bind block params.
    let mut values: Vec<_> = Vec::with_capacity((cfg.num_params + cfg.num_ops) as usize);
    for _ in 0..cfg.num_params {
        let v = fb.add_block_param(entry, Ty::I64);
        values.push(v);
    }
    fb.switch_to_block(entry);

    let ops = op_pool(cfg);
    for _ in 0..cfg.num_ops {
        // Pick two existing values as operands (may be the same one twice;
        // that's fine).
        let lhs = values[rng.gen_range_usize(values.len())];
        let rhs = values[rng.gen_range_usize(values.len())];
        let op = ops[rng.gen_range_usize(ops.len())];
        let result = fb.binop(op, Ty::I64, lhs, rhs);
        values.push(result);
    }

    // Return the final computed value.
    let last = *values.last().expect("at least one value exists (params)");
    fb.ret(vec![last]);
    fb.build();

    mb.build()
}

fn gep_byte(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    base: trust_ir::ValueId,
    offset: i128,
) -> trust_ir::ValueId {
    if offset == 0 {
        return base;
    }
    let offset = fb.iconst(Ty::U64, offset);
    fb.gep(Ty::U8, base, vec![offset])
}

fn store_u8(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    out: trust_ir::ValueId,
    offset: i128,
    value: u8,
) {
    let ptr = gep_byte(fb, out, offset);
    let value = fb.iconst(Ty::U8, value as i128);
    fb.store(Ty::U8, ptr, value);
}

fn store_i64(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    out: trust_ir::ValueId,
    offset: i128,
    value: trust_ir::ValueId,
) {
    let ptr = gep_byte(fb, out, offset);
    fb.store(Ty::I64, ptr, value);
}

fn write_status_record(
    fb: &mut trust_ir_build::FunctionBuilder<'_>,
    out: trust_ir::ValueId,
    status: u8,
    deopt: u8,
    value: trust_ir::ValueId,
    detail: trust_ir::ValueId,
) {
    store_u8(fb, out, 0, status);
    store_u8(fb, out, 1, deopt);
    store_i64(fb, out, 8, value);
    store_i64(fb, out, 16, detail);
}

/// Build a deterministic consumer-shaped module for the JIT differential lane.
///
/// Shape:
/// - `CondBr` with block arguments through stale/bounds/ok paths.
/// - Status-output-like pointer buffer writes: status/deopt/value/detail.
/// - GEP + stores, plus a reload from the output buffer on the ok path.
/// - Scalar control oracle: no callbacks and no host memory in the interpreter.
pub fn gen_consumer_shape_module(seed: u64) -> TrustIrModule {
    let mut mb = ModuleBuilder::new(format!("consumer_shape_{}", seed));
    let ty = mb.add_func_type(
        vec![Ty::I64, Ty::I64, Ty::I64, Ty::I64, Ty::Ptr],
        vec![Ty::I64],
    );
    let mut fb = mb.function(FUZZ_FN_NAME, ty);

    let entry = fb.create_block();
    let check_bounds = fb.create_block();
    let stale = fb.create_block();
    let bounds = fb.create_block();
    let ok = fb.create_block();
    let merge = fb.create_block();

    let a = fb.add_block_param(entry, Ty::I64);
    let b = fb.add_block_param(entry, Ty::I64);
    let len = fb.add_block_param(entry, Ty::I64);
    let epoch = fb.add_block_param(entry, Ty::I64);
    let out = fb.add_block_param(entry, Ty::Ptr);

    let cb_a = fb.add_block_param(check_bounds, Ty::I64);
    let cb_b = fb.add_block_param(check_bounds, Ty::I64);
    let cb_len = fb.add_block_param(check_bounds, Ty::I64);
    let cb_out = fb.add_block_param(check_bounds, Ty::Ptr);

    let stale_epoch = fb.add_block_param(stale, Ty::I64);
    let stale_expected = fb.add_block_param(stale, Ty::I64);
    let stale_out = fb.add_block_param(stale, Ty::Ptr);

    let bounds_len = fb.add_block_param(bounds, Ty::I64);
    let bounds_limit = fb.add_block_param(bounds, Ty::I64);
    let bounds_out = fb.add_block_param(bounds, Ty::Ptr);

    let ok_a = fb.add_block_param(ok, Ty::I64);
    let ok_b = fb.add_block_param(ok, Ty::I64);
    let ok_len = fb.add_block_param(ok, Ty::I64);
    let ok_out = fb.add_block_param(ok, Ty::Ptr);

    let merged = fb.add_block_param(merge, Ty::I64);

    fb.switch_to_block(entry);
    let expected_epoch = fb.iconst(Ty::I64, 7);
    let is_stale = fb.icmp(ICmpOp::Ne, Ty::I64, epoch, expected_epoch);
    fb.condbr(
        is_stale,
        stale,
        vec![epoch, expected_epoch, out],
        check_bounds,
        vec![a, b, len, out],
    );

    fb.switch_to_block(check_bounds);
    let limit = fb.iconst(Ty::I64, 4);
    let out_of_bounds = fb.icmp(ICmpOp::Sgt, Ty::I64, cb_len, limit);
    fb.condbr(
        out_of_bounds,
        bounds,
        vec![cb_len, limit, cb_out],
        ok,
        vec![cb_a, cb_b, cb_len, cb_out],
    );

    fb.switch_to_block(stale);
    write_status_record(&mut fb, stale_out, 3, 3, stale_epoch, stale_expected);
    let stale_ret = fb.iconst(Ty::I64, -3);
    fb.br(merge, vec![stale_ret]);

    fb.switch_to_block(bounds);
    write_status_record(&mut fb, bounds_out, 1, 1, bounds_len, bounds_limit);
    let bounds_ret = fb.iconst(Ty::I64, -1);
    fb.br(merge, vec![bounds_ret]);

    fb.switch_to_block(ok);
    let scale = fb.iconst(Ty::I64, 3);
    let scaled = fb.mul(Ty::I64, ok_a, scale);
    let sum = fb.add(Ty::I64, scaled, ok_b);
    let value = fb.sub(Ty::I64, sum, ok_len);
    write_status_record(&mut fb, ok_out, 0, 0, value, ok_len);
    let value_ptr = gep_byte(&mut fb, ok_out, 8);
    let reloaded = fb.load(Ty::I64, value_ptr);
    let ok_ret = fb.binop(BinOp::Xor, Ty::I64, reloaded, ok_len);
    fb.br(merge, vec![ok_ret]);

    fb.switch_to_block(merge);
    fb.ret(vec![merged]);
    fb.build();

    mb.build()
}

/// Sample test inputs for the generated function. We deliberately include
/// zeros, ones, and a few signed/unsigned extrema in addition to PRNG
/// values — these are the classes most likely to expose
/// corner-case miscompiles (divide-by-zero, INT64_MIN / -1, shift count
/// >= width, etc.).
pub fn sample_inputs(seed: u64, num_params: u32, num_samples: u32) -> Vec<Vec<i64>> {
    let mut rng = Prng::new(seed.wrapping_add(0xDEADBEEF));
    let mut out = Vec::with_capacity(num_samples as usize);

    // Fixed well-known inputs first — deterministic and useful for minimization.
    let well_known: &[i64] = &[
        0,
        1,
        -1,
        2,
        -2,
        i64::MAX,
        i64::MIN,
        0xFFFF_FFFF,
        -0x8000_0000,
    ];
    let mut slot = 0usize;
    for _ in 0..num_samples {
        let mut row = Vec::with_capacity(num_params as usize);
        for _ in 0..num_params {
            if slot < well_known.len() {
                // For the very first rows, use well-known values cycling
                // through the table.
                row.push(well_known[slot % well_known.len()]);
                slot += 1;
            } else {
                // After the well-known prefix, use the PRNG.
                row.push(rng.signed_i64(1_000_000_000));
            }
        }
        out.push(row);
    }
    out
}
