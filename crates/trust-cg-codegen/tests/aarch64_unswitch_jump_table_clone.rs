// trust-cg-codegen - loop-unswitch must give the cloned loop its own jump table
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! An innermost loop that dispatches through a dense `switch` (lowered to a
//! jump table) and then takes a loop-invariant branch, run through the JIT at
//! O0/O2/O3 and compared with the trust-ir reference interpreter.
//!
//! ```text
//! arr = [0; 8]
//! for i in 0..n {
//!     v = match i & 3 { 0 => 10, 1 => 21, 2 => 32, 3 => 43 };   // jump table
//!     if flag != 0 { arr[i & 7] += v }                         // invariant
//! }
//! return sum(arr[k] * (k + 1))
//! ```
//!
//! `loop-unswitch` versions a loop on an invariant branch: version A keeps the
//! original blocks with the branch replaced by `B taken`, version B is a clone
//! whose branch block falls through. `clone_remap` rewrites every
//! `MachOperand::Block` of the cloned instructions, but this loop's dispatch is
//! `Adr t, JumpTableIndex(0); LdrswRO; AddRR; Br`, and the table entries live
//! in `MachFunction::jump_tables`, which a clone would share. Version B's `Br`
//! would land in version A's case blocks, whose join branches unconditionally
//! to the store: with `flag == 0` the loop would add `v` to `arr` on every
//! iteration and return nonzero where the source returns 0.
//!
//! The invariant this row pins: a cloned loop version dispatches only into its
//! own blocks, through every block-addressing form (branch operands AND
//! jump-table entries). The pass reproduces only `Block`-operand edges, so it
//! declines a body that reads a jump table. The rows are bounded host
//! executions; they are tests, not a proof.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_ir::{
    BinOp, Constant, FuncId, ICmpOp, InterpretOptions, InterpretValue, Interpreter, SwitchCase, Ty,
};
use trust_ir_build::ModuleBuilder;

const ENTRY: &str = "unswitch_jump_table";
const PASS: &str = "loop-unswitch";
const TRIPLE: &str = if cfg!(target_os = "linux") {
    "aarch64-unknown-linux-gnu"
} else {
    "aarch64-apple-darwin"
};

type Kernel = extern "C" fn(u64, u64) -> u64;

/// The module of the doc comment: `(flag, n) -> checksum`. With
/// `switch == false` the dispatch block computes `v = (i & 3) * 11 + 10`
/// directly and jumps to the join: the same loop without a jump table.
fn module_with(switch: bool) -> (trust_ir::Module, FuncId) {
    let mut mb = ModuleBuilder::new("aarch64_unswitch_jump_table_clone");
    let elem = mb.add_type(Ty::U64);
    let ty = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(ENTRY, ty);
    let entry = fb.create_block();
    let flag = fb.add_block_param(entry, Ty::U64);
    let n = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let i = fb.add_block_param(header, Ty::U64);
    let dispatch = fb.create_block();
    let cases: Vec<_> = if switch {
        (0..4).map(|_| fb.create_block()).collect()
    } else {
        Vec::new()
    };
    let join = fb.create_block();
    let v = fb.add_block_param(join, Ty::U64);
    let accumulate = fb.create_block();
    let latch = fb.create_block();
    let exit = fb.create_block();
    let sum_header = fb.create_block();
    let k = fb.add_block_param(sum_header, Ty::U64);
    let acc = fb.add_block_param(sum_header, Ty::U64);
    let sum_body = fb.create_block();
    let done = fb.create_block();

    fb.switch_to_block(entry);
    let arr = fb.alloca(Ty::Array(elem, 8));
    let zero = fb.iconst(Ty::U64, 0);
    for slot in 0..8 {
        let index = fb.iconst(Ty::U64, slot);
        let p = fb.gep(Ty::U64, arr, vec![index]);
        fb.store(Ty::U64, p, zero);
    }
    fb.br(header, vec![zero]);

    fb.switch_to_block(header);
    let more = fb.icmp(ICmpOp::Ult, Ty::U64, i, n);
    fb.condbr(more, dispatch, vec![], exit, vec![]);

    fb.switch_to_block(dispatch);
    let three = fb.iconst(Ty::U64, 3);
    let sel = fb.binop(BinOp::And, Ty::U64, i, three);
    if switch {
        let table: Vec<SwitchCase> = (0..4)
            .map(|case| SwitchCase {
                value: Constant::Int(case as i128),
                target: cases[case],
                args: vec![],
            })
            .collect();
        fb.switch(sel, table, cases[0], vec![]);
    } else {
        let eleven = fb.iconst(Ty::U64, 11);
        let ten = fb.iconst(Ty::U64, 10);
        let scaled = fb.binop(BinOp::Mul, Ty::U64, sel, eleven);
        let value = fb.binop(BinOp::Add, Ty::U64, scaled, ten);
        fb.br(join, vec![value]);
    }

    for (case, &block) in cases.iter().enumerate() {
        fb.switch_to_block(block);
        let value = fb.iconst(Ty::U64, case as i128 * 11 + 10);
        fb.br(join, vec![value]);
    }

    fb.switch_to_block(join);
    let zero = fb.iconst(Ty::U64, 0);
    let flag_set = fb.icmp(ICmpOp::Ne, Ty::U64, flag, zero);
    fb.condbr(flag_set, accumulate, vec![], latch, vec![]);

    fb.switch_to_block(accumulate);
    let seven = fb.iconst(Ty::U64, 7);
    let slot = fb.binop(BinOp::And, Ty::U64, i, seven);
    let p = fb.gep(Ty::U64, arr, vec![slot]);
    let old = fb.load(Ty::U64, p);
    let new = fb.binop(BinOp::Add, Ty::U64, old, v);
    fb.store(Ty::U64, p, new);
    fb.br(latch, vec![]);

    fb.switch_to_block(latch);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.binop(BinOp::Add, Ty::U64, i, one);
    fb.br(header, vec![next]);

    fb.switch_to_block(exit);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(sum_header, vec![zero, zero]);

    fb.switch_to_block(sum_header);
    let eight = fb.iconst(Ty::U64, 8);
    let in_range = fb.icmp(ICmpOp::Ult, Ty::U64, k, eight);
    fb.condbr(in_range, sum_body, vec![], done, vec![]);

    fb.switch_to_block(sum_body);
    let p = fb.gep(Ty::U64, arr, vec![k]);
    let x = fb.load(Ty::U64, p);
    let one = fb.iconst(Ty::U64, 1);
    let k1 = fb.binop(BinOp::Add, Ty::U64, k, one);
    let weighted = fb.binop(BinOp::Mul, Ty::U64, x, k1);
    let acc2 = fb.binop(BinOp::Add, Ty::U64, acc, weighted);
    fb.br(sum_header, vec![k1, acc2]);

    fb.switch_to_block(done);
    fb.ret(vec![acc]);
    let fid = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), fid)
}

fn module() -> (trust_ir::Module, FuncId) {
    module_with(true)
}

/// The interpreter's result for `(flag, n)`.
fn reference(module: &trust_ir::Module, fid: FuncId, flag: u64, n: u64) -> u64 {
    let args: Vec<InterpretValue> = [flag, n]
        .iter()
        .map(|&v| InterpretValue::int(Ty::U64, i128::from(v)).expect("u64 argument"))
        .collect();
    let out = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 10_000_000,
            ..Default::default()
        })
        .execute_func(fid, args)
        .expect("interpreter");
    out.returns[0].as_int().expect("int").as_unsigned() as u64
}

/// The same program in plain Rust, a second oracle for the interpreter.
fn model(flag: u64, n: u64) -> u64 {
    let mut arr = [0u64; 8];
    for i in 0..n {
        let v = (i & 3) * 11 + 10;
        if flag != 0 {
            arr[(i & 7) as usize] += v;
        }
    }
    arr.iter()
        .enumerate()
        .map(|(k, &x)| x * (k as u64 + 1))
        .sum()
}

/// How many times `pass` changed the function at `opt_level`, with an explicit
/// empty disable list so the ambient `TRUST_CG_DISABLE_PASSES` cannot hide it.
fn pass_changes(module: &trust_ir::Module, opt_level: OptLevel, pass: &str) -> u32 {
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect("lowering");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        target_triple: TRIPLE.into(),
        disabled_passes_override: Some(String::new()),
        ..PipelineConfig::default()
    });
    let mut changes = 0;
    for (function, _) in &lowered {
        let (_, metrics) = pipeline
            .prepare_function_with_metrics(function, None)
            .expect("prepare");
        for (name, count) in &metrics.optimization_pass_changes {
            if name == pass {
                changes += count;
            }
        }
    }
    changes
}

fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> JitCompilationResult {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
}

const ROWS: [(u64, u64); 7] = [(0, 0), (1, 0), (0, 5), (1, 5), (0, 17), (1, 17), (7, 33)];

#[test]
fn the_interpreter_and_the_rust_model_agree() {
    let (module, fid) = module();
    for (flag, n) in ROWS {
        assert_eq!(
            reference(&module, fid, flag, n),
            model(flag, n),
            "flag = {flag}, n = {n}"
        );
    }
}

/// The loop has the one invariant branch the pass versions on, and the pass
/// must decline it: its body dispatches through a jump table.
#[test]
fn loop_unswitch_declines_the_jump_table_loop() {
    let (module, _) = module();
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        assert_eq!(
            pass_changes(&module, opt_level, PASS),
            0,
            "{opt_level:?}: {PASS} cloned a jump-table dispatch"
        );
    }
}

/// Positive control: the same loop without the jump table is still versioned,
/// and both versions compute the source's result.
#[test]
fn loop_unswitch_versions_the_jump_table_free_twin() {
    let (module, fid) = module_with(false);
    let mut failures = Vec::new();
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        assert!(
            pass_changes(&module, opt_level, PASS) > 0,
            "{opt_level:?}: {PASS} must version the twin"
        );
        let result = jit(&module, opt_level);
        // SAFETY: the signature matches the trust-ir type (u64, u64) -> u64 and
        // `result` outlives the call.
        let entry = unsafe { result.buffer.get_fn_bound::<Kernel>(ENTRY) }.expect("entry symbol");
        for (flag, n) in ROWS {
            let want = reference(&module, fid, flag, n);
            let got = entry.as_ref()(flag, n);
            if got != want {
                failures.push(format!(
                    "{opt_level:?}: flag = {flag}, n = {n}: got {got}, want {want}"
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn the_cloned_version_dispatches_into_its_own_case_blocks() {
    let (module, fid) = module();
    let mut failures = Vec::new();
    for opt_level in [OptLevel::O0, OptLevel::O2, OptLevel::O3] {
        let result = jit(&module, opt_level);
        // SAFETY: the signature matches the trust-ir type (u64, u64) -> u64 and
        // `result` outlives the call.
        let entry = unsafe { result.buffer.get_fn_bound::<Kernel>(ENTRY) }.expect("entry symbol");
        for (flag, n) in ROWS {
            let want = reference(&module, fid, flag, n);
            let got = entry.as_ref()(flag, n);
            if got != want {
                failures.push(format!(
                    "{opt_level:?}: flag = {flag}, n = {n}: got {got}, want {want}"
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
