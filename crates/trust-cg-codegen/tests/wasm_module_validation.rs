// trust-cg-codegen/tests/wasm_module_validation.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Reference-validator gate for the wasm backend: every module the backend
//! emits must pass `wasmparser::Validator` (the Bytecode Alliance spec
//! validator — the same family of checks every real engine runs at
//! instantiation). The relooper/encoder unit tests assert *our own* invariants;
//! this gate asserts an **independent** implementation of the wasm spec accepts
//! the bytes, so an ill-formed module (bad section layout, type mismatch on the
//! operand stack, unset local, wrong branch arity) fails here rather than at
//! `WebAssembly.instantiate` in someone's runtime.
//!
//! The corpus mirrors the control-flow-diverse difftest corpus
//! (`examples/wasm_difftest.rs` — examples are not importable as a library, so
//! the shapes are reconstructed here): straight-line arithmetic, if/else
//! diamonds, gcd-style loops with two back-edges, nested loops, bottom-test
//! loops, switch cascades, and the P0 canary-island shape (gcd feeding a
//! switch-in-loop mixing cascade), plus memory (alloca/GEP), direct and
//! indirect calls, and edge shapes: empty body, single block, deep cascade.
//!
//! Each shape is compiled and validated as its own module (a failure names the
//! function), and the whole corpus is also compiled as ONE module (exercising
//! the shared type section, function table, and stack-pointer global).

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::process::Command;

use trust_ir::{BinOp, CastOp, Constant, ICmpOp, SwitchCase, Ty, UnOp};
use trust_ir_build::ModuleBuilder;

use trust_cg_codegen::wasm;
use wasm::{
    ISLAND_ABI_NAMESPACE, ISLAND_MEMORY_IMPORT, ISLAND_STACK_BASE_IMPORT, WasmFuncImportPolicy,
    WasmLowerError, WasmMemoryPolicy, WasmModulePolicy, WasmStackPolicy, island_host_namespace,
};

/// One corpus shape: the (unique) name of the function it defines, and a
/// builder that registers that function (plus any callees) in a module.
struct Shape {
    name: &'static str,
    build: fn(&mut ModuleBuilder),
}

fn corpus() -> Vec<Shape> {
    vec![
        Shape {
            name: "straight_line_arith",
            build: build_straight_line_arith,
        },
        Shape {
            name: "straight_line_i64",
            build: build_straight_line_i64,
        },
        Shape {
            name: "div_rem",
            build: build_div_rem,
        },
        Shape {
            name: "const_only",
            build: build_const_only,
        },
        Shape {
            name: "empty_body",
            build: build_empty_body,
        },
        Shape {
            name: "single_block",
            build: build_single_block,
        },
        Shape {
            name: "if_else_diamond",
            build: build_if_else_diamond,
        },
        Shape {
            name: "nested_if_else",
            build: build_nested_if_else,
        },
        Shape {
            name: "gcd_sub_loop",
            build: build_gcd_sub_loop,
        },
        Shape {
            name: "gcd_mod_loop",
            build: build_gcd_mod_loop,
        },
        Shape {
            name: "counting_loop",
            build: build_counting_loop,
        },
        Shape {
            name: "nested_loops",
            build: build_nested_loops,
        },
        Shape {
            name: "do_while_sum",
            build: build_do_while_sum,
        },
        Shape {
            name: "switch_pick",
            build: build_switch_pick,
        },
        Shape {
            name: "switch_cascade_wide",
            build: build_switch_cascade_wide,
        },
        Shape {
            name: "deep_cascade",
            build: build_deep_cascade,
        },
        Shape {
            name: "canary_shape",
            build: build_canary_shape,
        },
        Shape {
            name: "alloca_roundtrip",
            build: build_alloca_roundtrip,
        },
        Shape {
            name: "array_gep",
            build: build_array_gep,
        },
        Shape {
            name: "direct_call_chain",
            build: build_direct_call_chain,
        },
        Shape {
            name: "indirect_call",
            build: build_indirect_call,
        },
        // --- P3: the value domain ---
        Shape {
            name: "narrow_arith",
            build: build_narrow_arith,
        },
        Shape {
            name: "narrow_casts",
            build: build_narrow_casts,
        },
        Shape {
            name: "subword_memory",
            build: build_subword_memory,
        },
        Shape {
            name: "float_memory",
            build: build_float_memory,
        },
        Shape {
            name: "switch_dense",
            build: |mb| build_switch(mb, "switch_dense", &[0, 1, 2, 3, 4, 5, 6, 7], false),
        },
        Shape {
            name: "switch_sparse",
            build: |mb| build_switch(mb, "switch_sparse", &[0, 500, 9000], false),
        },
        Shape {
            name: "switch_negative",
            build: |mb| build_switch(mb, "switch_negative", &[-4, -3, -2, -1, 0, 1], false),
        },
        Shape {
            name: "switch_single_case",
            build: |mb| build_switch(mb, "switch_single_case", &[7], false),
        },
        Shape {
            name: "switch_holes",
            build: |mb| build_switch(mb, "switch_holes", &[10, 11, 13, 16], false),
        },
        Shape {
            name: "switch_default_is_a_case_target",
            build: |mb| {
                build_switch(
                    mb,
                    "switch_default_is_a_case_target",
                    &[0, 1, 2, 3, 4],
                    true,
                )
            },
        },
        Shape {
            name: "static_table",
            build: build_static_table,
        },
    ]
}

/// Finish a builder into a module pinned to the wasm32 lane. `compile_module`
/// fail-closes on target-free modules, so every corpus module carries the
/// canonical wasm32 `TargetInfo`.
fn finish_wasm32(mb: ModuleBuilder) -> trust_ir::Module {
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.target_info = Some(wasm::target::wasm32_target_info());
    module
}

/// Run the reference validator over `bytes`; `what` names the failing lane.
fn validate(what: &str, bytes: &[u8]) {
    wasmparser::Validator::new()
        .validate_all(bytes)
        .unwrap_or_else(|e| {
            panic!(
                "emitted wasm for `{what}` REJECTED by the reference validator \
                 ({} bytes): {e}",
                bytes.len()
            )
        });
}

/// Compile `module` and run the reference validator; `what` names the failing
/// function (or corpus lane) in every panic message.
fn compile_and_validate(what: &str, module: &trust_ir::Module) {
    let bytes = wasm::compile_module_with_policy_and_license(
        module,
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .unwrap_or_else(|e| panic!("wasm backend failed to compile `{what}`: {e}"));
    validate(what, &bytes);
}

/// Compile `module` under `policy` and validate; returns the module bytes and
/// the host contract the policy bound.
fn compile_and_validate_with_policy(
    what: &str,
    module: &trust_ir::Module,
    policy: &WasmModulePolicy,
) -> (Vec<u8>, Vec<String>) {
    let (bytes, evidence) =
        wasm::compile_module_with_evidence_policy_and_license(module, policy, &permit_unlicensed())
            .unwrap_or_else(|e| panic!("wasm backend failed to compile `{what}`: {e}"));
    validate(what, &bytes);
    (bytes, evidence.host_contract)
}

/// Every corpus shape, compiled and validated as its own module. A failure
/// names the function.
#[test]
fn every_emitted_module_validates_per_function() {
    for shape in corpus() {
        let mut mb = ModuleBuilder::new(shape.name);
        (shape.build)(&mut mb);
        compile_and_validate(shape.name, &finish_wasm32(mb));
    }
}

/// The corpus stamping is load-bearing: a target-free module must be REFUSED
/// by `compile_module` (fail-closed), which proves the two green tests above
/// really run the wasm32 lane and not some default path.
#[test]
fn target_free_corpus_module_is_refused() {
    let mut mb = ModuleBuilder::new("target_free");
    build_if_else_diamond(&mut mb);
    let module = mb.build().expect("ModuleBuilder::build: test fixture"); // deliberately NOT stamped
    assert!(
        module.target_info.is_none(),
        "corpus builder must not stamp target_info itself"
    );
    let err = wasm::compile_module_with_policy_and_license(
        &module,
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .expect_err("a target-free module must not enter the wasm32 lane");
    let msg = err.to_string();
    assert!(
        msg.contains("target_info"),
        "refusal must name target_info: {msg}"
    );
}

/// The whole corpus as ONE module: shared type section, one function table,
/// one linear memory + shadow stack pointer across all functions.
#[test]
fn combined_corpus_module_validates() {
    let mut mb = ModuleBuilder::new("combined");
    for shape in corpus() {
        (shape.build)(&mut mb);
    }
    compile_and_validate("combined corpus module", &finish_wasm32(mb));
}

// ---------------------------------------------------------------------------
// Straight-line + edge shapes.
// ---------------------------------------------------------------------------

/// Chain of i32 binops + unary ops (no trapping ops, no control flow).
fn build_straight_line_arith(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("straight_line_arith", ft);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I32);
    let b = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    let s = fb.binop(BinOp::Add, Ty::I32, a, b);
    let d = fb.binop(BinOp::Sub, Ty::I32, s, b);
    let m = fb.binop(BinOp::Mul, Ty::I32, d, a);
    let x = fb.binop(BinOp::Xor, Ty::I32, m, b);
    let o = fb.binop(BinOp::Or, Ty::I32, x, a);
    let n = fb.binop(BinOp::And, Ty::I32, o, b);
    let c5 = fb.iconst(Ty::I32, 5);
    let sh = fb.binop(BinOp::Shl, Ty::I32, n, c5);
    let sr = fb.binop(BinOp::AShr, Ty::I32, sh, c5);
    let neg = fb.unop(UnOp::Neg, Ty::I32, sr);
    let not = fb.unop(UnOp::Not, Ty::I32, neg);
    let pop = fb.unop(UnOp::CtPop, Ty::I32, not);
    fb.ret(vec![pop]);
    fb.build();
}

/// The division family the difftest corpus exercises (idiv_s / irem_s) —
/// SDiv/UDiv/SRem/URem across both integer widths. Divisors are guarded
/// non-zero by construction (an `Or 1`), so the shape carries no trap edge
/// and the validator sees the real encoder output for every div opcode.
fn build_div_rem(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32, Ty::I64, Ty::I64], vec![Ty::I32]);
    let mut fb = mb.function("div_rem", ft);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I32);
    let b = fb.add_block_param(e, Ty::I32);
    let p = fb.add_block_param(e, Ty::I64);
    let q = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let one32 = fb.iconst(Ty::I32, 1);
    let nz_b = fb.binop(BinOp::Or, Ty::I32, b, one32);
    let sd = fb.binop(BinOp::SDiv, Ty::I32, a, nz_b);
    let ud = fb.binop(BinOp::UDiv, Ty::I32, a, nz_b);
    let sr = fb.binop(BinOp::SRem, Ty::I32, a, nz_b);
    let ur = fb.binop(BinOp::URem, Ty::I32, a, nz_b);
    let s0 = fb.binop(BinOp::Add, Ty::I32, sd, ud);
    let s1 = fb.binop(BinOp::Add, Ty::I32, sr, ur);
    let s32 = fb.binop(BinOp::Xor, Ty::I32, s0, s1);
    let one64 = fb.iconst(Ty::I64, 1);
    let nz_q = fb.binop(BinOp::Or, Ty::I64, q, one64);
    let sd64 = fb.binop(BinOp::SDiv, Ty::I64, p, nz_q);
    let ud64 = fb.binop(BinOp::UDiv, Ty::I64, p, nz_q);
    let sr64 = fb.binop(BinOp::SRem, Ty::I64, p, nz_q);
    let ur64 = fb.binop(BinOp::URem, Ty::I64, p, nz_q);
    let t0 = fb.binop(BinOp::Add, Ty::I64, sd64, ud64);
    let t1 = fb.binop(BinOp::Add, Ty::I64, sr64, ur64);
    let t64 = fb.binop(BinOp::Xor, Ty::I64, t0, t1);
    let narrowed = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, t64);
    let out = fb.binop(BinOp::Add, Ty::I32, s32, narrowed);
    fb.ret(vec![out]);
    fb.build();
}

/// The 64-bit lane: i64 params, i64 arithmetic, i64 result.
fn build_straight_line_i64(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let mut fb = mb.function("straight_line_i64", ft);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let s = fb.binop(BinOp::Add, Ty::I64, a, b);
    let m = fb.binop(BinOp::Mul, Ty::I64, s, a);
    let x = fb.binop(BinOp::Xor, Ty::I64, m, b);
    let c7 = fb.iconst(Ty::I64, 7);
    let sh = fb.binop(BinOp::LShr, Ty::I64, x, c7);
    fb.ret(vec![sh]);
    fb.build();
}

/// No params, constant return.
fn build_const_only(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![], vec![Ty::I32]);
    let mut fb = mb.function("const_only", ft);
    let e = fb.create_block();
    fb.switch_to_block(e);
    let c = fb.iconst(Ty::I32, 7);
    fb.ret(vec![c]);
    fb.build();
}

/// Edge shape: a body that does nothing — one param, zero results, immediate
/// return.
fn build_empty_body(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32], vec![]);
    let mut fb = mb.function("empty_body", ft);
    let e = fb.create_block();
    let _x = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    fb.ret(vec![]);
    fb.build();
}

/// Edge shape: exactly one block, one computation, one return.
fn build_single_block(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("single_block", ft);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I32);
    let b = fb.add_block_param(e, Ty::I32);
    let c = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    let bc = fb.mul(Ty::I32, b, c);
    let r = fb.add(Ty::I32, a, bc);
    fb.ret(vec![r]);
    fb.build();
}

// ---------------------------------------------------------------------------
// Branching shapes.
// ---------------------------------------------------------------------------

/// max(a, b): if/else diamond with a join block param.
fn build_if_else_diamond(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("if_else_diamond", ft);
    let entry = fb.create_block();
    let tb = fb.create_block();
    let eb = fb.create_block();
    let join = fb.create_block();
    let r = fb.add_block_param(join, Ty::I32);
    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    let c = fb.icmp(ICmpOp::Sge, Ty::I32, a, b);
    fb.condbr(c, tb, vec![], eb, vec![]);
    fb.switch_to_block(tb);
    fb.br(join, vec![a]);
    fb.switch_to_block(eb);
    fb.br(join, vec![b]);
    fb.switch_to_block(join);
    fb.ret(vec![r]);
    fb.build();
}

/// clamp(x, lo, hi): nested if/else, arms reading dominating values.
fn build_nested_if_else(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("nested_if_else", ft);
    let entry = fb.create_block();
    let low_b = fb.create_block();
    let mid = fb.create_block();
    let high_b = fb.create_block();
    let keep = fb.create_block();
    let join = fb.create_block();
    let r = fb.add_block_param(join, Ty::I32);
    let x = fb.add_block_param(entry, Ty::I32);
    let lo = fb.add_block_param(entry, Ty::I32);
    let hi = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    let clt = fb.icmp(ICmpOp::Slt, Ty::I32, x, lo);
    fb.condbr(clt, low_b, vec![], mid, vec![]);
    fb.switch_to_block(low_b);
    fb.br(join, vec![lo]);
    fb.switch_to_block(mid);
    let cgt = fb.icmp(ICmpOp::Sgt, Ty::I32, x, hi);
    fb.condbr(cgt, high_b, vec![], keep, vec![]);
    fb.switch_to_block(high_b);
    fb.br(join, vec![hi]);
    fb.switch_to_block(keep);
    fb.br(join, vec![x]);
    fb.switch_to_block(join);
    fb.ret(vec![r]);
    fb.build();
}

/// Edge shape: a 24-deep compare cascade — every level either exits to the
/// join or falls through to the next test (deep relooper nesting).
fn build_deep_cascade(mb: &mut ModuleBuilder) {
    const DEPTH: i128 = 24;
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("deep_cascade", ft);
    let entry = fb.create_block();
    let join = fb.create_block();
    let r = fb.add_block_param(join, Ty::I32);
    let x = fb.add_block_param(entry, Ty::I32);
    let acc = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    for k in 0..DEPTH {
        let leaf = fb.create_block();
        let next = fb.create_block();
        let kc = fb.iconst(Ty::I32, k);
        let c = fb.icmp(ICmpOp::Eq, Ty::I32, x, kc);
        fb.condbr(c, leaf, vec![], next, vec![]);
        fb.switch_to_block(leaf);
        let ten_k = fb.iconst(Ty::I32, k * 10);
        let v = fb.add(Ty::I32, acc, ten_k);
        fb.br(join, vec![v]);
        fb.switch_to_block(next);
    }
    fb.br(join, vec![acc]);
    fb.switch_to_block(join);
    fb.ret(vec![r]);
    fb.build();
}

// ---------------------------------------------------------------------------
// Loop shapes.
// ---------------------------------------------------------------------------

/// gcd(a, b) by repeated subtraction: a loop with an if/else inside and TWO
/// back-edges (the shape that surfaced the original relooper gcd bug).
fn build_gcd_sub_loop(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("gcd_sub_loop", ft);
    let entry = fb.create_block();
    let header = fb.create_block();
    let test = fb.create_block();
    let dec_a = fb.create_block();
    let dec_b = fb.create_block();
    let exit = fb.create_block();
    let a = fb.add_block_param(header, Ty::I32);
    let b = fb.add_block_param(header, Ty::I32);
    let ta = fb.add_block_param(test, Ty::I32);
    let tb = fb.add_block_param(test, Ty::I32);
    let xa = fb.add_block_param(dec_a, Ty::I32);
    let xb = fb.add_block_param(dec_a, Ty::I32);
    let ya = fb.add_block_param(dec_b, Ty::I32);
    let yb = fb.add_block_param(dec_b, Ty::I32);
    let ra = fb.add_block_param(exit, Ty::I32);
    let a0 = fb.add_block_param(entry, Ty::I32);
    let b0 = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    fb.br(header, vec![a0, b0]);
    fb.switch_to_block(header);
    let ne = fb.icmp(ICmpOp::Ne, Ty::I32, a, b);
    fb.condbr(ne, test, vec![a, b], exit, vec![a]);
    fb.switch_to_block(test);
    let gt = fb.icmp(ICmpOp::Sgt, Ty::I32, ta, tb);
    fb.condbr(gt, dec_a, vec![ta, tb], dec_b, vec![ta, tb]);
    fb.switch_to_block(dec_a);
    let na = fb.sub(Ty::I32, xa, xb);
    fb.br(header, vec![na, xb]); // back-edge 1
    fb.switch_to_block(dec_b);
    let nb = fb.sub(Ty::I32, yb, ya);
    fb.br(header, vec![ya, nb]); // back-edge 2
    fb.switch_to_block(exit);
    fb.ret(vec![ra]);
    fb.build();
}

/// gcd(a, b) by modulo — the canary island's first half: URem's divisor is the
/// branch-guarded nonzero y.
fn build_gcd_mod_loop(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("gcd_mod_loop", ft);
    let entry = fb.create_block();
    let ghead = fb.create_block();
    let gstep = fb.create_block();
    let exit = fb.create_block();
    let a0 = fb.add_block_param(entry, Ty::I32);
    let b0 = fb.add_block_param(entry, Ty::I32);
    let gx = fb.add_block_param(ghead, Ty::I32);
    let gy = fb.add_block_param(ghead, Ty::I32);
    let sx = fb.add_block_param(gstep, Ty::I32);
    let sy = fb.add_block_param(gstep, Ty::I32);
    let g = fb.add_block_param(exit, Ty::I32);
    fb.switch_to_block(entry);
    fb.br(ghead, vec![a0, b0]);
    fb.switch_to_block(ghead);
    let z = fb.iconst(Ty::I32, 0);
    let ne = fb.icmp(ICmpOp::Ne, Ty::I32, gy, z);
    fb.condbr(ne, gstep, vec![gx, gy], exit, vec![gx]);
    fb.switch_to_block(gstep);
    let rem = fb.binop(BinOp::URem, Ty::I32, sx, sy);
    fb.br(ghead, vec![sy, rem]);
    fb.switch_to_block(exit);
    fb.ret(vec![g]);
    fb.build();
}

/// sum_to(n, acc0, i0, step): a single top-test counting loop.
fn build_counting_loop(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32; 4], vec![Ty::I32]);
    let mut fb = mb.function("counting_loop", ft);
    let entry = fb.create_block();
    let header = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    let acc = fb.add_block_param(header, Ty::I32);
    let i = fb.add_block_param(header, Ty::I32);
    let bacc = fb.add_block_param(body, Ty::I32);
    let bi = fb.add_block_param(body, Ty::I32);
    let racc = fb.add_block_param(exit, Ty::I32);
    let n = fb.add_block_param(entry, Ty::I32);
    let acc0 = fb.add_block_param(entry, Ty::I32);
    let i0 = fb.add_block_param(entry, Ty::I32);
    let step = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    fb.br(header, vec![acc0, i0]);
    fb.switch_to_block(header);
    let c = fb.icmp(ICmpOp::Sle, Ty::I32, i, n);
    fb.condbr(c, body, vec![acc, i], exit, vec![acc]);
    fb.switch_to_block(body);
    let nacc = fb.add(Ty::I32, bacc, bi);
    let ni = fb.add(Ty::I32, bi, step);
    fb.br(header, vec![nacc, ni]);
    fb.switch_to_block(exit);
    fb.ret(vec![racc]);
    fb.build();
}

/// mul_loop(a, b, acc0, oi0, ii0, step): NESTED loops — an outer counting loop
/// whose body re-enters an inner counting loop.
fn build_nested_loops(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32; 6], vec![Ty::I32]);
    let mut fb = mb.function("nested_loops", ft);
    let entry = fb.create_block();
    let oh = fb.create_block();
    let oreset = fb.create_block();
    let ih = fb.create_block();
    let ibody = fb.create_block();
    let odone = fb.create_block();
    let exit = fb.create_block();
    let acc = fb.add_block_param(oh, Ty::I32);
    let oi = fb.add_block_param(oh, Ty::I32);
    let racc = fb.add_block_param(oreset, Ty::I32);
    let roi = fb.add_block_param(oreset, Ty::I32);
    let iacc = fb.add_block_param(ih, Ty::I32);
    let ioi = fb.add_block_param(ih, Ty::I32);
    let iii = fb.add_block_param(ih, Ty::I32);
    let bacc = fb.add_block_param(ibody, Ty::I32);
    let boi = fb.add_block_param(ibody, Ty::I32);
    let bii = fb.add_block_param(ibody, Ty::I32);
    let dacc = fb.add_block_param(odone, Ty::I32);
    let doi = fb.add_block_param(odone, Ty::I32);
    let facc = fb.add_block_param(exit, Ty::I32);
    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    let acc0 = fb.add_block_param(entry, Ty::I32);
    let oi0 = fb.add_block_param(entry, Ty::I32);
    let ii0 = fb.add_block_param(entry, Ty::I32);
    let step = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    fb.br(oh, vec![acc0, oi0]);
    fb.switch_to_block(oh);
    let oc = fb.icmp(ICmpOp::Slt, Ty::I32, oi, a);
    fb.condbr(oc, oreset, vec![acc, oi], exit, vec![acc]);
    fb.switch_to_block(oreset);
    fb.br(ih, vec![racc, roi, ii0]);
    fb.switch_to_block(ih);
    let ic = fb.icmp(ICmpOp::Slt, Ty::I32, iii, b);
    fb.condbr(ic, ibody, vec![iacc, ioi, iii], odone, vec![iacc, ioi]);
    fb.switch_to_block(ibody);
    let nacc = fb.add(Ty::I32, bacc, step);
    let nii = fb.add(Ty::I32, bii, step);
    fb.br(ih, vec![nacc, boi, nii]); // inner back-edge
    fb.switch_to_block(odone);
    let noi = fb.add(Ty::I32, doi, step);
    fb.br(oh, vec![dacc, noi]); // outer back-edge
    fb.switch_to_block(exit);
    fb.ret(vec![facc]);
    fb.build();
}

/// do_while_sum(n, acc0, i0, step): bottom-test self-loop — the body runs once
/// even when the condition starts false.
fn build_do_while_sum(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32; 4], vec![Ty::I32]);
    let mut fb = mb.function("do_while_sum", ft);
    let entry = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    let acc = fb.add_block_param(body, Ty::I32);
    let i = fb.add_block_param(body, Ty::I32);
    let racc = fb.add_block_param(exit, Ty::I32);
    let n = fb.add_block_param(entry, Ty::I32);
    let acc0 = fb.add_block_param(entry, Ty::I32);
    let i0 = fb.add_block_param(entry, Ty::I32);
    let step = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    fb.br(body, vec![acc0, i0]);
    fb.switch_to_block(body);
    let nacc = fb.add(Ty::I32, acc, i);
    let ni = fb.add(Ty::I32, i, step);
    let c = fb.icmp(ICmpOp::Sle, Ty::I32, ni, n);
    fb.condbr(c, body, vec![nacc, ni], exit, vec![nacc]);
    fb.switch_to_block(exit);
    fb.ret(vec![racc]);
    fb.build();
}

// ---------------------------------------------------------------------------
// Switch shapes.
// ---------------------------------------------------------------------------

/// pick(v, a, b, c): a 2-case + default switch into a join.
fn build_switch_pick(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32; 4], vec![Ty::I32]);
    let mut fb = mb.function("switch_pick", ft);
    let entry = fb.create_block();
    let c0 = fb.create_block();
    let c1 = fb.create_block();
    let def = fb.create_block();
    let join = fb.create_block();
    let r = fb.add_block_param(join, Ty::I32);
    let v = fb.add_block_param(entry, Ty::I32);
    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    let c = fb.add_block_param(entry, Ty::I32);
    fb.switch_to_block(entry);
    fb.switch(
        v,
        vec![
            SwitchCase {
                value: Constant::Int(0),
                target: c0,
                args: vec![],
            },
            SwitchCase {
                value: Constant::Int(1),
                target: c1,
                args: vec![],
            },
        ],
        def,
        vec![],
    );
    fb.switch_to_block(c0);
    fb.br(join, vec![a]);
    fb.switch_to_block(c1);
    fb.br(join, vec![b]);
    fb.switch_to_block(def);
    fb.br(join, vec![c]);
    fb.switch_to_block(join);
    fb.ret(vec![r]);
    fb.build();
}

/// A 12-case switch cascade, every case computing a distinct join value.
fn build_switch_cascade_wide(mb: &mut ModuleBuilder) {
    const CASES: i128 = 12;
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("switch_cascade_wide", ft);
    let entry = fb.create_block();
    let join = fb.create_block();
    let r = fb.add_block_param(join, Ty::I32);
    let v = fb.add_block_param(entry, Ty::I32);
    let x = fb.add_block_param(entry, Ty::I32);
    let case_blocks: Vec<_> = (0..CASES).map(|_| fb.create_block()).collect();
    let def = fb.create_block();
    fb.switch_to_block(entry);
    let cases: Vec<SwitchCase> = case_blocks
        .iter()
        .enumerate()
        .map(|(k, &target)| SwitchCase {
            value: Constant::Int(k as i128),
            target,
            args: vec![],
        })
        .collect();
    fb.switch(v, cases, def, vec![]);
    for (k, &cb) in case_blocks.iter().enumerate() {
        fb.switch_to_block(cb);
        let kc = fb.iconst(Ty::I32, (k as i128) * 3 + 1);
        let val = fb.add(Ty::I32, x, kc);
        fb.br(join, vec![val]);
    }
    fb.switch_to_block(def);
    fb.br(join, vec![x]);
    fb.switch_to_block(join);
    fb.ret(vec![r]);
    fb.build();
}

/// The P0 canary-island shape (examples/wasm_canary_island.rs): a modulo-gcd
/// loop feeding eight rounds of a data-dependent 4-way compare cascade —
/// switch-in-loop with a Bool block param riding an edge.
fn build_canary_shape(mb: &mut ModuleBuilder) {
    let sig = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("canary_shape", sig);

    let entry = fb.create_block();
    let ghead = fb.create_block();
    let gstep = fb.create_block();
    let mixin = fb.create_block();
    let round = fb.create_block();
    let t1 = fb.create_block();
    let t2 = fb.create_block();
    let r0 = fb.create_block();
    let r1 = fb.create_block();
    let r2 = fb.create_block();
    let r3 = fb.create_block();
    let join = fb.create_block();
    let exit = fb.create_block();

    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    let gx = fb.add_block_param(ghead, Ty::I32);
    let gy = fb.add_block_param(ghead, Ty::I32);
    let sx = fb.add_block_param(gstep, Ty::I32);
    let sy = fb.add_block_param(gstep, Ty::I32);
    let g = fb.add_block_param(mixin, Ty::I32);
    let h = fb.add_block_param(round, Ty::I32);
    let i = fb.add_block_param(round, Ty::I32);
    let t1h = fb.add_block_param(t1, Ty::I32);
    let t1i = fb.add_block_param(t1, Ty::I32);
    let t1s = fb.add_block_param(t1, Ty::I32);
    let t2h = fb.add_block_param(t2, Ty::I32);
    let t2i = fb.add_block_param(t2, Ty::I32);
    let t2s = fb.add_block_param(t2, Ty::I32);
    let r0h = fb.add_block_param(r0, Ty::I32);
    let r0i = fb.add_block_param(r0, Ty::I32);
    let r1h = fb.add_block_param(r1, Ty::I32);
    let r1i = fb.add_block_param(r1, Ty::I32);
    let r2h = fb.add_block_param(r2, Ty::I32);
    let r2i = fb.add_block_param(r2, Ty::I32);
    let r3h = fb.add_block_param(r3, Ty::I32);
    let r3i = fb.add_block_param(r3, Ty::I32);
    let jh = fb.add_block_param(join, Ty::I32);
    let ji = fb.add_block_param(join, Ty::I32);
    let xh = fb.add_block_param(exit, Ty::I32);

    fb.switch_to_block(entry);
    fb.br(ghead, vec![a, b]);

    // while y != 0 { (x, y) = (y, x mod y) } — branch-guarded URem.
    fb.switch_to_block(ghead);
    let z = fb.iconst(Ty::I32, 0);
    let ne = fb.icmp(ICmpOp::Ne, Ty::I32, gy, z);
    fb.condbr(ne, gstep, vec![gx, gy], mixin, vec![gx]);
    fb.switch_to_block(gstep);
    let rem = fb.binop(BinOp::URem, Ty::I32, sx, sy);
    fb.br(ghead, vec![sy, rem]);

    fb.switch_to_block(mixin);
    let golden = fb.iconst(Ty::I32, 0x9E37_79B9u32 as i32 as i128);
    let h0 = fb.binop(BinOp::Xor, Ty::I32, g, golden);
    let i0 = fb.iconst(Ty::I32, 0);
    fb.br(round, vec![h0, i0]);

    // for i in 0..8: 4-way cascade on h & 3 (Bool block param rides the edge).
    fb.switch_to_block(round);
    let eight = fb.iconst(Ty::I32, 8);
    let more = fb.icmp(ICmpOp::Ult, Ty::I32, i, eight);
    let three = fb.iconst(Ty::I32, 3);
    let sel = fb.binop(BinOp::And, Ty::I32, h, three);
    let zero = fb.iconst(Ty::I32, 0);
    let is0 = fb.icmp(ICmpOp::Eq, Ty::I32, sel, zero);
    let cascade = fb.create_block();
    let ch = fb.add_block_param(cascade, Ty::I32);
    let ci = fb.add_block_param(cascade, Ty::I32);
    let cs = fb.add_block_param(cascade, Ty::I32);
    let c0 = fb.add_block_param(cascade, Ty::Bool);
    fb.condbr(more, cascade, vec![h, i, sel, is0], exit, vec![h]);

    fb.switch_to_block(cascade);
    fb.condbr(c0, r0, vec![ch, ci], t1, vec![ch, ci, cs]);

    fb.switch_to_block(t1);
    let one = fb.iconst(Ty::I32, 1);
    let is1 = fb.icmp(ICmpOp::Eq, Ty::I32, t1s, one);
    fb.condbr(is1, r1, vec![t1h, t1i], t2, vec![t1h, t1i, t1s]);

    fb.switch_to_block(t2);
    let two = fb.iconst(Ty::I32, 2);
    let is2 = fb.icmp(ICmpOp::Eq, Ty::I32, t2s, two);
    fb.condbr(is2, r2, vec![t2h, t2i], r3, vec![t2h, t2i]);

    // 0 => h = (h + a*K0) ^ (h >> 13)
    fb.switch_to_block(r0);
    let k0 = fb.iconst(Ty::I32, 0x85EB_CA6Bu32 as i32 as i128);
    let m0 = fb.binop(BinOp::Mul, Ty::I32, a, k0);
    let s0 = fb.binop(BinOp::Add, Ty::I32, r0h, m0);
    let c13 = fb.iconst(Ty::I32, 13);
    let sh0 = fb.binop(BinOp::LShr, Ty::I32, r0h, c13);
    let n0 = fb.binop(BinOp::Xor, Ty::I32, s0, sh0);
    fb.br(join, vec![n0, r0i]);

    // 1 => h = (h ^ b*K1) + (h << 5)
    fb.switch_to_block(r1);
    let k1 = fb.iconst(Ty::I32, 0xC2B2_AE35u32 as i32 as i128);
    let m1 = fb.binop(BinOp::Mul, Ty::I32, b, k1);
    let x1 = fb.binop(BinOp::Xor, Ty::I32, r1h, m1);
    let c5 = fb.iconst(Ty::I32, 5);
    let sh1 = fb.binop(BinOp::Shl, Ty::I32, r1h, c5);
    let n1 = fb.binop(BinOp::Add, Ty::I32, x1, sh1);
    fb.br(join, vec![n1, r1i]);

    // 2 => h = (h * K2) ^ (a + b)
    fb.switch_to_block(r2);
    let k2 = fb.iconst(Ty::I32, 0x27D4_EB2Fu32 as i32 as i128);
    let m2 = fb.binop(BinOp::Mul, Ty::I32, r2h, k2);
    let ab = fb.binop(BinOp::Add, Ty::I32, a, b);
    let n2 = fb.binop(BinOp::Xor, Ty::I32, m2, ab);
    fb.br(join, vec![n2, r2i]);

    // _ => h = (h - (a ^ b)) ^ (h >> 7)
    fb.switch_to_block(r3);
    let axb = fb.binop(BinOp::Xor, Ty::I32, a, b);
    let d3 = fb.binop(BinOp::Sub, Ty::I32, r3h, axb);
    let c7 = fb.iconst(Ty::I32, 7);
    let sh3 = fb.binop(BinOp::LShr, Ty::I32, r3h, c7);
    let n3 = fb.binop(BinOp::Xor, Ty::I32, d3, sh3);
    fb.br(join, vec![n3, r3i]);

    // join: h ^= i * K3; i += 1; back to round.
    fb.switch_to_block(join);
    let k3 = fb.iconst(Ty::I32, 0x7FEB_352Du32 as i32 as i128);
    let im = fb.binop(BinOp::Mul, Ty::I32, ji, k3);
    let hx = fb.binop(BinOp::Xor, Ty::I32, jh, im);
    let one2 = fb.iconst(Ty::I32, 1);
    let ni = fb.binop(BinOp::Add, Ty::I32, ji, one2);
    fb.br(round, vec![hx, ni]);

    fb.switch_to_block(exit);
    fb.ret(vec![xh]);
    fb.build();
}

// ---------------------------------------------------------------------------
// Memory + call shapes.
// ---------------------------------------------------------------------------

/// alloca/store/load — pulls in the linear memory and shadow stack pointer.
fn build_alloca_roundtrip(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("alloca_roundtrip", ft);
    let e = fb.create_block();
    let x = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    let cell = fb.alloca(Ty::I32);
    fb.store(Ty::I32, cell, x);
    let r = fb.load(Ty::I32, cell);
    fb.ret(vec![r]);
    fb.build();
}

/// Dynamic-index array GEP over an alloca'd [i32; 4].
fn build_array_gep(mb: &mut ModuleBuilder) {
    let elem = mb.add_type(Ty::I32);
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("array_gep", ft);
    let e = fb.create_block();
    let i = fb.add_block_param(e, Ty::I32);
    let x = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    let buf = fb.alloca(Ty::Array(elem, 4));
    let p = fb.gep(Ty::I32, buf, vec![i]);
    fb.store(Ty::I32, p, x);
    let p2 = fb.gep(Ty::I32, buf, vec![i]);
    let r = fb.load(Ty::I32, p2);
    fb.ret(vec![r]);
    fb.build();
}

/// direct_call_chain(a,b,c) = addtwo(addtwo(a,b), c) — chained direct calls.
fn build_direct_call_chain(mb: &mut ModuleBuilder) {
    let ft2 = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let addtwo_id = {
        let mut fb = mb.function("direct_call_chain_addtwo", ft2);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let r = fb.add(Ty::I32, a, b);
        fb.ret(vec![r]);
        fb.build()
    };
    let ft3 = mb.add_func_type(vec![Ty::I32, Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("direct_call_chain", ft3);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I32);
    let b = fb.add_block_param(e, Ty::I32);
    let c = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    let ab = fb.call(addtwo_id, vec![a, b]);
    let abc = fb.call(addtwo_id, vec![ab, c]);
    fb.ret(vec![abc]);
    fb.build();
}

/// indirect_call(x,y) = (*fn_ptr(imul))(x,y) — function table + typed call.
fn build_indirect_call(mb: &mut ModuleBuilder) {
    let ft2 = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let imul_id = {
        let mut fb = mb.function("indirect_call_imul", ft2);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let r = fb.mul(Ty::I32, a, b);
        fb.ret(vec![r]);
        fb.build()
    };
    let mut fb = mb.function("indirect_call", ft2);
    let e = fb.create_block();
    let x = fb.add_block_param(e, Ty::I32);
    let y = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    let fp = fb.fn_addr(ft2, imul_id);
    let r = fb.call_indirect(fp, ft2, vec![x, y]);
    fb.ret(vec![r]);
    fb.build();
}

// ---------------------------------------------------------------------------
// P3 — the value domain: narrow types, sub-word and float memory, br_table
// switches, and static data.
//
// Every narrow value lives in an i32 carrier in a fixed canonical form
// (`src/wasm/lower.rs`, "Invariant N"): sign-extended for `I8`/`I16`,
// zero-extended for `U8`/`U16`. The shapes below exercise the producers that
// must re-establish it (wrapping arithmetic, casts, sub-word loads) and the
// consumers that read a particular view of it (signed vs unsigned divide,
// shift, compare).
// ---------------------------------------------------------------------------

/// Arithmetic at all four narrow widths, each result folded back into an i32 —
/// wrapping add/sub/mul, both shift directions, and the signed/unsigned divide
/// and compare families.
fn build_narrow_arith(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("narrow_arith", ft);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I32);
    let b = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);

    // u8: (a + b) * a, wrapping at 8 bits, then a nonzero unsigned divide.
    let au8 = fb.cast(CastOp::Trunc, Ty::I32, Ty::U8, a);
    let bu8 = fb.cast(CastOp::Trunc, Ty::I32, Ty::U8, b);
    let su8 = fb.binop(BinOp::Add, Ty::U8, au8, bu8);
    let mu8 = fb.binop(BinOp::Mul, Ty::U8, su8, au8);
    let one_u8 = fb.iconst(Ty::U8, 1);
    let nz_u8 = fb.binop(BinOp::Or, Ty::U8, bu8, one_u8);
    let du8 = fb.binop(BinOp::UDiv, Ty::U8, mu8, nz_u8);
    let ru8 = fb.binop(BinOp::URem, Ty::U8, mu8, nz_u8);
    let xu8 = fb.binop(BinOp::Xor, Ty::U8, du8, ru8);
    let three_u8 = fb.iconst(Ty::U8, 3);
    let shl_u8 = fb.binop(BinOp::Shl, Ty::U8, xu8, three_u8);
    let shr_u8 = fb.binop(BinOp::LShr, Ty::U8, shl_u8, three_u8);
    let w0 = fb.cast(CastOp::ZExt, Ty::U8, Ty::I32, shr_u8);

    // i8: negate, complement, popcount, arithmetic shift, signed divide.
    let ai8 = fb.cast(CastOp::Trunc, Ty::I32, Ty::I8, a);
    let bi8 = fb.cast(CastOp::Trunc, Ty::I32, Ty::I8, b);
    let ni8 = fb.unop(UnOp::Neg, Ty::I8, ai8);
    let ti8 = fb.unop(UnOp::Not, Ty::I8, ni8);
    let pi8 = fb.unop(UnOp::CtPop, Ty::I8, ti8);
    let mi8 = fb.binop(BinOp::Mul, Ty::I8, ti8, bi8);
    let two_i8 = fb.iconst(Ty::I8, 2);
    let ai8_shr = fb.binop(BinOp::AShr, Ty::I8, mi8, two_i8);
    let one_i8 = fb.iconst(Ty::I8, 1);
    let nz_i8 = fb.binop(BinOp::Or, Ty::I8, bi8, one_i8);
    let di8 = fb.binop(BinOp::SDiv, Ty::I8, ai8_shr, nz_i8);
    let si8 = fb.binop(BinOp::SRem, Ty::I8, ai8_shr, nz_i8);
    let sum_i8 = fb.binop(BinOp::Add, Ty::I8, di8, si8);
    let with_pop = fb.binop(BinOp::Add, Ty::I8, sum_i8, pi8);
    let w1 = fb.cast(CastOp::SExt, Ty::I8, Ty::I32, with_pop);

    // u16 / i16: the same shapes one width up, plus the compare families.
    let au16 = fb.cast(CastOp::Trunc, Ty::I32, Ty::U16, a);
    let bu16 = fb.cast(CastOp::Trunc, Ty::I32, Ty::U16, b);
    let su16 = fb.binop(BinOp::Sub, Ty::U16, au16, bu16);
    let w2 = fb.cast(CastOp::ZExt, Ty::U16, Ty::I32, su16);
    let ai16 = fb.cast(CastOp::Trunc, Ty::I32, Ty::I16, a);
    let bi16 = fb.cast(CastOp::Trunc, Ty::I32, Ty::I16, b);
    let mi16 = fb.binop(BinOp::Mul, Ty::I16, ai16, bi16);
    let w3 = fb.cast(CastOp::SExt, Ty::I16, Ty::I32, mi16);
    let lt_s = fb.icmp(ICmpOp::Slt, Ty::I8, ai8, bi8);
    let lt_u = fb.icmp(ICmpOp::Ult, Ty::U8, au8, bu8);
    let eq16 = fb.icmp(ICmpOp::Eq, Ty::U16, au16, bu16);
    let ge16 = fb.icmp(ICmpOp::Sge, Ty::I16, ai16, bi16);

    let c0 = fb.cast(CastOp::ZExt, Ty::Bool, Ty::I32, lt_s);
    let c1 = fb.cast(CastOp::ZExt, Ty::Bool, Ty::I32, lt_u);
    let c2 = fb.cast(CastOp::ZExt, Ty::Bool, Ty::I32, eq16);
    let c3 = fb.cast(CastOp::ZExt, Ty::Bool, Ty::I32, ge16);

    let s0 = fb.add(Ty::I32, w0, w1);
    let s1 = fb.add(Ty::I32, w2, w3);
    let s2 = fb.add(Ty::I32, c0, c1);
    let s3 = fb.add(Ty::I32, c2, c3);
    let s4 = fb.add(Ty::I32, s0, s1);
    let s5 = fb.add(Ty::I32, s2, s3);
    let out = fb.add(Ty::I32, s4, s5);
    fb.ret(vec![out]);
    fb.build();
}

/// Every narrow resize direction: truncate down, zero- and sign-extend back up,
/// and the same across the 64-bit carrier boundary.
fn build_narrow_casts(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("narrow_casts", ft);
    let e = fb.create_block();
    let x = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);

    let u8v = fb.cast(CastOp::Trunc, Ty::I32, Ty::U8, x);
    let i8v = fb.cast(CastOp::Bitcast, Ty::U8, Ty::I8, u8v);
    let zx = fb.cast(CastOp::ZExt, Ty::I8, Ty::I32, i8v);
    let sx = fb.cast(CastOp::SExt, Ty::U8, Ty::I32, u8v);
    let u16v = fb.cast(CastOp::Trunc, Ty::I32, Ty::U16, x);
    let i16v = fb.cast(CastOp::Bitcast, Ty::U16, Ty::I16, u16v);
    let wide = fb.cast(CastOp::SExt, Ty::I16, Ty::I64, i16v);
    let widened = fb.cast(CastOp::ZExt, Ty::U8, Ty::U64, u8v);
    let back0 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, wide);
    let back1 = fb.cast(CastOp::Trunc, Ty::U64, Ty::U16, widened);
    let b0 = fb.cast(CastOp::SExt, Ty::I8, Ty::I32, back0);
    let b1 = fb.cast(CastOp::ZExt, Ty::U16, Ty::I32, back1);

    let s0 = fb.add(Ty::I32, zx, sx);
    let s1 = fb.add(Ty::I32, b0, b1);
    let out = fb.add(Ty::I32, s0, s1);
    fb.ret(vec![out]);
    fb.build();
}

/// Sub-word memory: a byte written through `i32.store8` and read back both
/// sign- and zero-extending, plus the 16-bit pair.
fn build_subword_memory(mb: &mut ModuleBuilder) {
    let u8_ty = mb.add_type(Ty::U8);
    let u16_ty = mb.add_type(Ty::U16);
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("subword_memory", ft);
    let e = fb.create_block();
    let x = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    let bytes = fb.alloca(Ty::Array(u8_ty, 4));
    let halves = fb.alloca(Ty::Array(u16_ty, 2));
    let zero = fb.iconst(Ty::I32, 0);
    let one = fb.iconst(Ty::I32, 1);

    let b = fb.cast(CastOp::Trunc, Ty::I32, Ty::U8, x);
    let p0 = fb.gep(Ty::U8, bytes, vec![zero]);
    fb.store(Ty::U8, p0, b);
    let read_u = fb.load(Ty::U8, p0);
    let read_s = fb.load(Ty::I8, p0);
    let zu = fb.cast(CastOp::ZExt, Ty::U8, Ty::I32, read_u);
    let zs = fb.cast(CastOp::SExt, Ty::I8, Ty::I32, read_s);

    let h = fb.cast(CastOp::Trunc, Ty::I32, Ty::U16, x);
    let q0 = fb.gep(Ty::U16, halves, vec![one]);
    fb.store(Ty::U16, q0, h);
    let hread_u = fb.load(Ty::U16, q0);
    let hread_s = fb.load(Ty::I16, q0);
    let hu = fb.cast(CastOp::ZExt, Ty::U16, Ty::I32, hread_u);
    let hs = fb.cast(CastOp::SExt, Ty::I16, Ty::I32, hread_s);

    let s0 = fb.add(Ty::I32, zu, zs);
    let s1 = fb.add(Ty::I32, hu, hs);
    let out = fb.add(Ty::I32, s0, s1);
    fb.ret(vec![out]);
    fb.build();
}

/// `f32`/`f64` loads and stores: an i32 bit pattern round-tripped through a
/// float cell, and an i64 pattern through a double cell.
fn build_float_memory(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("float_memory", ft);
    let e = fb.create_block();
    let bits = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    let f32_cell = fb.alloca(Ty::F32);
    let f64_cell = fb.alloca(Ty::F64);

    let f = fb.cast(CastOp::Bitcast, Ty::I32, Ty::F32, bits);
    fb.store(Ty::F32, f32_cell, f);
    let g = fb.load(Ty::F32, f32_cell);
    let g_bits = fb.cast(CastOp::Bitcast, Ty::F32, Ty::I32, g);

    let wide = fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, bits);
    let d = fb.cast(CastOp::Bitcast, Ty::I64, Ty::F64, wide);
    fb.store(Ty::F64, f64_cell, d);
    let d2 = fb.load(Ty::F64, f64_cell);
    let d_bits = fb.cast(CastOp::Bitcast, Ty::F64, Ty::I64, d2);
    let d_low = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, d_bits);

    let out = fb.binop(BinOp::Xor, Ty::I32, g_bits, d_low);
    fb.ret(vec![out]);
    fb.build();
}

/// `pick(v, x)`: a switch whose case VALUES are given, each arm computing a
/// distinct join value, plus a default arm. When `default_is_a_case_target`,
/// the default edge reuses the FIRST case's block instead of its own — the
/// shape where a `br_table` default label and a case label must name the same
/// place without the block being emitted twice.
fn build_switch(
    mb: &mut ModuleBuilder,
    name: &'static str,
    values: &[i128],
    default_is_a_case_target: bool,
) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function(name, ft);
    let entry = fb.create_block();
    let join = fb.create_block();
    let r = fb.add_block_param(join, Ty::I32);
    let v = fb.add_block_param(entry, Ty::I32);
    let x = fb.add_block_param(entry, Ty::I32);
    let case_blocks: Vec<_> = values.iter().map(|_| fb.create_block()).collect();
    // The default arm's own block exists only when the default edge reaches
    // it: trust-ir refuses a block no edge reaches (`UnreachableBlock`), and
    // every ingestion entry refuses what the validator refuses (WS7.3).
    let own_default = (!default_is_a_case_target).then(|| fb.create_block());
    let default_block = own_default.unwrap_or(case_blocks[0]);
    fb.switch_to_block(entry);
    let cases: Vec<SwitchCase> = values
        .iter()
        .zip(&case_blocks)
        .map(|(value, &target)| SwitchCase {
            value: Constant::Int(*value),
            target,
            args: vec![],
        })
        .collect();
    fb.switch(v, cases, default_block, vec![]);
    for (k, &cb) in case_blocks.iter().enumerate() {
        fb.switch_to_block(cb);
        let kc = fb.iconst(Ty::I32, (k as i128) * 7 + 1);
        let val = fb.add(Ty::I32, x, kc);
        fb.br(join, vec![val]);
    }
    if let Some(own_default) = own_default {
        fb.switch_to_block(own_default);
        let sentinel = fb.iconst(Ty::I32, -1);
        let val = fb.add(Ty::I32, x, sentinel);
        fb.br(join, vec![val]);
    }
    fb.switch_to_block(join);
    fb.ret(vec![r]);
    fb.build();
}

/// A constant lookup table living in LINEAR MEMORY (a data segment) instead of
/// in code: `table[i & 7]`, read with a zero-extending byte load.
fn build_static_table(mb: &mut ModuleBuilder) {
    use trust_ir::Global;
    let u8_ty = mb.add_type(Ty::U8);
    let global_index = 0u32;
    mb.add_global(Global {
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
        name: "STATIC_TABLE".to_string(),
        ty: Ty::Array(u8_ty, 8),
        mutable: false,
        initializer: Some(Constant::Bytes {
            data: vec![3, 1, 4, 1, 5, 9, 2, 6],
            utf8: false,
        }),
        linkage: Default::default(),
        tls: None,
        align: None,
    });
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("static_table", ft);
    let e = fb.create_block();
    let i = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    let seven = fb.iconst(Ty::I32, 7);
    let idx = fb.binop(BinOp::And, Ty::I32, i, seven);
    let base = fb.global_addr(trust_ir::value::GlobalId::new(global_index));
    let p = fb.gep(Ty::U8, base, vec![idx]);
    let byte = fb.load(Ty::U8, p);
    let out = fb.cast(CastOp::ZExt, Ty::U8, Ty::I32, byte);
    fb.ret(vec![out]);
    fb.build();
}

// ---------------------------------------------------------------------------
// P2 — islands: imports, the index space, and the negotiated memory region.
//
// The finding-class this section exists to refute is a SILENT one: in wasm,
// imported functions occupy the LOW function index space and defined functions
// follow, so forgetting the shift makes a `call` land on a different function
// that happens to have the same type — a module that validates perfectly and
// computes the wrong answer. Every shape below is therefore checked three
// ways: the reference validator accepts it, the emitted immediates are read
// back and asserted against the index the shift demands, and (where node is
// installed) the module is EXECUTED and its answer checked.
// ---------------------------------------------------------------------------

/// Every import the module declares, as `"<kind> <module>.<name>"`, read back
/// out of the emitted bytes by the reference parser.
fn module_imports(bytes: &[u8]) -> Vec<String> {
    let mut out = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::ImportSection(reader) = payload.expect("parse") {
            for import in reader {
                let import = import.expect("import");
                let kind = match import.ty {
                    wasmparser::TypeRef::Func(_) => "func",
                    wasmparser::TypeRef::Table(_) => "table",
                    wasmparser::TypeRef::Memory(_) => "memory",
                    wasmparser::TypeRef::Global(_) => "global",
                    wasmparser::TypeRef::Tag(_) => "tag",
                };
                out.push(format!("{kind} {}.{}", import.module, import.name));
            }
        }
    }
    out
}

/// Every export, as `(name, kind, index)`.
fn module_exports(bytes: &[u8]) -> Vec<(String, wasmparser::ExternalKind, u32)> {
    let mut out = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::ExportSection(reader) = payload.expect("parse") {
            for export in reader {
                let export = export.expect("export");
                out.push((export.name.to_string(), export.kind, export.index));
            }
        }
    }
    out
}

/// True if the module DEFINES a linear memory (section 5).
fn defines_memory(bytes: &[u8]) -> bool {
    wasmparser::Parser::new(0)
        .parse_all(bytes)
        .any(|p| matches!(p.expect("parse"), wasmparser::Payload::MemorySection(_)))
}

/// The `call` immediates in each DEFINED function body, in body order.
fn call_immediates(bytes: &[u8]) -> Vec<Vec<u32>> {
    let mut out = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::CodeSectionEntry(body) = payload.expect("parse") {
            let mut calls = Vec::new();
            for op in body.get_operators_reader().expect("operators") {
                if let wasmparser::Operator::Call { function_index } = op.expect("operator") {
                    calls.push(function_index);
                }
            }
            out.push(calls);
        }
    }
    out
}

/// The global indices each DEFINED function body reads or writes, in body
/// order (deduplicated, ascending).
fn global_indices(bytes: &[u8]) -> Vec<Vec<u32>> {
    let mut out = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::CodeSectionEntry(body) = payload.expect("parse") {
            let mut seen: Vec<u32> = Vec::new();
            for op in body.get_operators_reader().expect("operators") {
                let idx = match op.expect("operator") {
                    wasmparser::Operator::GlobalGet { global_index }
                    | wasmparser::Operator::GlobalSet { global_index } => global_index,
                    _ => continue,
                };
                if !seen.contains(&idx) {
                    seen.push(idx);
                }
            }
            seen.sort_unstable();
            out.push(seen);
        }
    }
    out
}

fn unique_temp_dir(tag: &str) -> fresh_dir::ScratchDir {
    fresh_dir::create(&format!("trust_cg_wasm_island_{tag}_"))
}

/// EXECUTE `bytes` under node with `driver` (an ES module taking the `.wasm`
/// path as `argv[2]`). When node is not installed the lane says so out loud
/// and the hermetic validator + immediate assertions remain the gate — never a
/// silent pass.
fn run_under_node(tag: &str, bytes: &[u8], driver: &str) {
    if Command::new("node").arg("--version").output().is_err() {
        eprintln!("SKIP: wasm island EXECUTION gate `{tag}` — `node` is not on PATH");
        return;
    }
    let dir = unique_temp_dir(tag);
    let wasm_path = dir.join("island.wasm");
    let driver_path = dir.join("driver.mjs");
    std::fs::write(&wasm_path, bytes).expect("write wasm");
    std::fs::write(&driver_path, driver).expect("write driver");

    let out = Command::new("node")
        .arg(&driver_path)
        .arg(&wasm_path)
        .output()
        .expect("run node");
    let stdout = String::from_utf8_lossy(&out.stdout).trim().to_string();
    let stderr = String::from_utf8_lossy(&out.stderr).trim().to_string();
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        out.status.success() && stdout == "OK",
        "wasm island `{tag}` FAILED under node (status {:?})\nstdout: {stdout}\nstderr: {stderr}",
        out.status.code()
    );
}

/// Three host-function imports interleaved with two defined functions, where
/// one defined function calls the other. The imports share the callee's
/// signature ON PURPOSE: a forgotten import shift would emit `call 0`, which
/// still type-checks and still validates — only the index assertion and the
/// execution below can tell the difference.
fn build_import_shift_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("island_calls");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);

    // Declaration (no blocks) → a wasm function import.
    mb.function("host_a", ft).build();

    // callee(a, b) = a * 3 + b
    let callee = {
        let mut fb = mb.function("callee", ft);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let three = fb.iconst(Ty::I32, 3);
        let m = fb.mul(Ty::I32, a, three);
        let r = fb.add(Ty::I32, m, b);
        fb.ret(vec![r]);
        fb.build()
    };

    mb.function("host_b", ft).build();

    // caller(a, b) = callee(a, b) + 7
    {
        let mut fb = mb.function("caller", ft);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let c = fb.call(callee, vec![a, b]);
        let seven = fb.iconst(Ty::I32, 7);
        let r = fb.add(Ty::I32, c, seven);
        fb.ret(vec![r]);
        fb.build();
    }

    mb.function("host_c", ft).build();
    finish_wasm32(mb)
}

#[test]
fn k_func_imports_shift_every_defined_call_target() {
    let module = build_import_shift_module();
    let policy = WasmModulePolicy {
        func_imports: WasmFuncImportPolicy::FromModule(island_host_namespace("calls")),
        ..WasmModulePolicy::closed()
    };
    // The call must survive to be checked: without the mid-end, whose
    // inliner would splice `callee` into `caller`.
    let (bytes, evidence) = wasm::compile_module_with_evidence_policy_license_options(
        &module,
        &policy,
        &permit_unlicensed(),
        wasm::WasmOptOptions {
            level: trust_cg_codegen::pipeline::OptLevel::O2,
            mid_end: false,
        },
    )
    .unwrap_or_else(|e| panic!("wasm backend failed to compile `island_calls`: {e}"));
    validate("island_calls", &bytes);
    let contract = evidence.host_contract;

    assert_eq!(
        contract,
        vec![
            "func trust:island/calls@1.host_a",
            "func trust:island/calls@1.host_b",
            "func trust:island/calls@1.host_c",
        ],
        "the three body-less functions are the module's host contract"
    );
    assert_eq!(module_imports(&bytes), contract);

    // Imports own indices 0..2, so the two DEFINED functions are 3 and 4 —
    // and their export indices must say so.
    let exports = module_exports(&bytes);
    assert_eq!(
        exports,
        vec![
            ("callee".to_string(), wasmparser::ExternalKind::Func, 3),
            ("caller".to_string(), wasmparser::ExternalKind::Func, 4),
        ],
        "defined-function exports must be import-shifted"
    );

    // `caller` must call function 3 (`callee`), NOT function 0 (`host_a`).
    let calls = call_immediates(&bytes);
    assert_eq!(calls.len(), 2, "two defined bodies: {calls:?}");
    assert!(calls[0].is_empty(), "callee makes no calls: {calls:?}");
    assert_eq!(
        calls[1],
        vec![3],
        "caller must `call 3` (the defined callee); `call 0` would be the host import"
    );

    // And it really lands there: the imports throw if entered.
    let driver = r#"
import { readFileSync } from 'node:fs';
const bytes = readFileSync(process.argv[2]);
const trap = (name) => () => { throw new Error('island entered host import ' + name); };
const { instance } = await WebAssembly.instantiate(bytes, {
  'trust:island/calls@1': { host_a: trap('host_a'), host_b: trap('host_b'), host_c: trap('host_c') },
});
const callee = instance.exports.callee(5, 2);
if (callee !== 17) { console.error('callee(5,2) = ' + callee + ', expected 17'); process.exit(1); }
const caller = instance.exports.caller(5, 2);
if (caller !== 24) { console.error('caller(5,2) = ' + caller + ', expected 24'); process.exit(1); }
console.log('OK');
"#;
    run_under_node("call_shift", &bytes, driver);
}

/// An imports-only module: three declarations, no definitions. It validates,
/// declares its whole surface as imports, and defines nothing.
#[test]
fn an_imports_only_module_validates() {
    let mut mb = ModuleBuilder::new("imports_only");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    for name in ["host_a", "host_b", "host_c"] {
        mb.function(name, ft).build();
    }
    let module = finish_wasm32(mb);

    let policy = WasmModulePolicy {
        func_imports: WasmFuncImportPolicy::FromModule(island_host_namespace("calls")),
        ..WasmModulePolicy::closed()
    };
    let (bytes, contract) = compile_and_validate_with_policy("imports_only", &module, &policy);
    assert_eq!(
        contract,
        vec![
            "func trust:island/calls@1.host_a",
            "func trust:island/calls@1.host_b",
            "func trust:island/calls@1.host_c",
        ]
    );
    assert!(
        call_immediates(&bytes).is_empty(),
        "an imports-only module has no code section"
    );
    assert!(module_exports(&bytes).is_empty(), "it exports nothing");
    assert!(!defines_memory(&bytes));
}

/// Imports plus the funcref table: `fn_addr` lowers a function pointer to its
/// table index `closed_table_index(funcidx)` = funcidx + 1, and the element
/// segment must fill the table so that element `funcidx + 1` is function
/// `funcidx` — over the WHOLE index space, imports included (element 0 stays
/// the null funcref). The two host imports again share the target's
/// signature, so a forgotten shift would dispatch into the imported `host_a`
/// and still type-check.
#[test]
fn an_indirect_call_beside_imports_dispatches_through_the_shifted_table() {
    let mut mb = ModuleBuilder::new("island_table");
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    mb.function("host_a", ft).build();
    mb.function("host_b", ft).build();
    let imul = {
        let mut fb = mb.function("imul", ft);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let r = fb.mul(Ty::I32, a, b);
        fb.ret(vec![r]);
        fb.build()
    };
    {
        let mut fb = mb.function("dispatch", ft);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I32);
        let y = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let fp = fb.fn_addr(ft, imul);
        let r = fb.call_indirect(fp, ft, vec![x, y]);
        fb.ret(vec![r]);
        fb.build();
    }
    let module = finish_wasm32(mb);

    let policy = WasmModulePolicy {
        func_imports: WasmFuncImportPolicy::FromModule(island_host_namespace("calls")),
        ..WasmModulePolicy::closed()
    };
    let (bytes, contract) = compile_and_validate_with_policy("island_table", &module, &policy);
    assert_eq!(
        contract,
        vec![
            "func trust:island/calls@1.host_a",
            "func trust:island/calls@1.host_b",
        ]
    );

    // The table must be big enough for the null slot plus the whole index
    // space (2 imports + 2 definitions); a table sized to the definitions alone
    // would make element 3 out of bounds and the element segment invalid.
    let mut table_min = None;
    for payload in wasmparser::Parser::new(0).parse_all(&bytes) {
        if let wasmparser::Payload::TableSection(reader) = payload.expect("parse") {
            for table in reader {
                table_min = Some(table.expect("table").ty.initial);
            }
        }
    }
    assert_eq!(
        table_min,
        Some(5),
        "table must cover the null slot + imports + definitions"
    );

    // `dispatch` pushes `imul`'s table index as its pointer: funcidx 2 + 1,
    // not 1 (imported host_a).
    let mut fn_ptr_consts = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(&bytes) {
        if let wasmparser::Payload::CodeSectionEntry(body) = payload.expect("parse") {
            let mut consts = Vec::new();
            for op in body.get_operators_reader().expect("operators") {
                if let wasmparser::Operator::I32Const { value } = op.expect("operator") {
                    consts.push(value);
                }
            }
            fn_ptr_consts.push(consts);
        }
    }
    assert_eq!(
        fn_ptr_consts[1],
        vec![3],
        "the function pointer must be `imul`'s shifted table index 3, not 1 (imported host_a)"
    );

    let driver = r#"
import { readFileSync } from 'node:fs';
const bytes = readFileSync(process.argv[2]);
const trap = (name) => () => { throw new Error('island entered host import ' + name); };
const { instance } = await WebAssembly.instantiate(bytes, {
  'trust:island/calls@1': { host_a: trap('host_a'), host_b: trap('host_b') },
});
const r = instance.exports.dispatch(6, 7);
if (r !== 42) { console.error('dispatch(6,7) = ' + r + ', expected 42'); process.exit(1); }
console.log('OK');
"#;
    run_under_node("table_shift", &bytes, driver);
}

/// roundtrip(x) = { let c = alloca i32; *c = x; read_volatile(c) } — the
/// smallest shape that needs a shadow-stack frame, and therefore an address.
/// The read is volatile so that the trust-ir mid-end (on at the default
/// level) does not forward the store to it and remove the slot.
fn build_frame_module(name: &'static str) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new(name);
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("roundtrip", ft);
    let e = fb.create_block();
    let x = fb.add_block_param(e, Ty::I32);
    fb.switch_to_block(e);
    let cell = fb.alloca(Ty::I32);
    fb.store(Ty::I32, cell, x);
    let r = fb.load_volatile(Ty::I32, cell);
    fb.ret(vec![r]);
    fb.build();
    finish_wasm32(mb)
}

/// The island shape: the module lives in the HOST's linear memory and takes
/// its shadow-stack base from a region the host allocated and published
/// through an imported immutable global. It must define no memory, and its
/// frame code must address the IMPORT-SHIFTED stack-pointer global.
#[test]
fn an_island_shares_host_memory_with_a_host_negotiated_stack() {
    let module = build_frame_module("island_memory");
    let policy = WasmModulePolicy::island("memory_probe");
    let (bytes, contract) = compile_and_validate_with_policy("island_memory", &module, &policy);

    assert_eq!(
        contract,
        vec![
            format!("memory {ISLAND_ABI_NAMESPACE}.{ISLAND_MEMORY_IMPORT}"),
            format!("global {ISLAND_ABI_NAMESPACE}.{ISLAND_STACK_BASE_IMPORT}"),
        ],
    );
    assert_eq!(module_imports(&bytes), contract);
    assert!(
        !defines_memory(&bytes),
        "an island in the host's memory must not define one of its own"
    );

    // Global 0 is the imported base; the defined stack pointer is global 1.
    // Emitting `global.get 0` / `global.set 0` here would both address the
    // wrong global AND write an immutable import.
    assert_eq!(
        global_indices(&bytes),
        vec![vec![1]],
        "frame code must use the import-shifted stack-pointer global"
    );

    // The host hands the island a 2-page memory and a region at 4096. The
    // island's frame must land just under it — never at the private one-page
    // top (65536) the closed lane would have assumed, and never at the top of
    // the host memory it does not own (131072).
    let driver = r#"
import { readFileSync } from 'node:fs';
const bytes = readFileSync(process.argv[2]);
const memory = new WebAssembly.Memory({ initial: 2 });
const BASE = 4096;
const __island_stack_base = new WebAssembly.Global({ value: 'i32', mutable: false }, BASE);
const ns = 'trust:island/abi@1';
const { instance } = await WebAssembly.instantiate(bytes, { [ns]: { memory, __island_stack_base } });
const r = instance.exports.roundtrip(0x12345678);
if (r !== 0x12345678) { console.error('roundtrip = ' + r); process.exit(1); }
const view = new Int32Array(memory.buffer);
if (view[(BASE - 8) / 4] !== 0x12345678) {
  console.error('island frame did not land in the host-negotiated region at ' + (BASE - 8));
  process.exit(1);
}
for (const trespass of [65536, 131072]) {
  if (view[(trespass - 8) / 4] !== 0) {
    console.error('island wrote at ' + (trespass - 8) + ' — a region the host did not give it');
    process.exit(1);
  }
}
console.log('OK');
"#;
    run_under_node("host_memory", &bytes, driver);
}

/// An owned memory can be surfaced to a host by export, so the host can read
/// what the island computed without sharing its own address space.
#[test]
fn an_owned_memory_can_be_exported() {
    let module = build_frame_module("exported_memory");
    let policy = WasmModulePolicy {
        memory: WasmMemoryPolicy::Owned {
            pages: 1,
            export: Some("memory".to_string()),
        },
        ..WasmModulePolicy::closed()
    };
    let (bytes, contract) = compile_and_validate_with_policy("exported_memory", &module, &policy);

    assert!(
        contract.is_empty(),
        "an owned memory binds no host contract: {contract:?}"
    );
    assert!(defines_memory(&bytes));
    assert_eq!(
        module_exports(&bytes),
        vec![
            ("memory".to_string(), wasmparser::ExternalKind::Memory, 0),
            ("roundtrip".to_string(), wasmparser::ExternalKind::Func, 0),
        ],
    );

    let driver = r#"
import { readFileSync } from 'node:fs';
const bytes = readFileSync(process.argv[2]);
const { instance } = await WebAssembly.instantiate(bytes, {});
const r = instance.exports.roundtrip(0xabcdef);
if (r !== 0xabcdef) { console.error('roundtrip = ' + r); process.exit(1); }
const view = new Int32Array(instance.exports.memory.buffer);
if (view[(65536 - 8) / 4] !== 0xabcdef) {
  console.error('owned frame is not at the top of the owned page');
  process.exit(1);
}
console.log('OK');
"#;
    run_under_node("exported_memory", &bytes, driver);
}

/// A function that only LOADS through a pointer parameter needs no frame, but
/// it still needs a memory to load from. Before the memory policy existed, the
/// backend keyed memory off `Alloca` alone and emitted `i32.load` into a module
/// with no memory section at all — an invalid module.
#[test]
fn a_pointer_load_without_an_alloca_still_gets_a_memory() {
    let mut mb = ModuleBuilder::new("ptr_load");
    let ft = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I32]);
    let mut fb = mb.function("deref", ft);
    let e = fb.create_block();
    let p = fb.add_block_param(e, Ty::Ptr);
    fb.switch_to_block(e);
    let v = fb.load(Ty::I32, p);
    fb.ret(vec![v]);
    fb.build();
    let module = finish_wasm32(mb);

    let bytes = wasm::compile_module_with_policy_and_license(
        &module,
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .expect("a pointer load must compile");
    validate("ptr_load", &bytes);
    assert!(
        defines_memory(&bytes),
        "a module that loads from linear memory must have one"
    );
    assert!(
        global_indices(&bytes)[0].is_empty(),
        "a frameless function needs no stack-pointer global"
    );
}

// --- Fail-closed paths ------------------------------------------------------

/// A memory access under a policy that provides no memory is refused, naming
/// the function that needs it.
#[test]
fn a_memory_access_under_the_absent_policy_is_refused() {
    let module = build_frame_module("absent_memory");
    let policy = WasmModulePolicy {
        memory: WasmMemoryPolicy::Absent,
        ..WasmModulePolicy::closed()
    };
    let err = wasm::compile_module_with_policy_and_license(&module, &policy, &permit_unlicensed())
        .expect_err("a module needing memory must not compile under Absent");
    assert!(matches!(err, WasmLowerError::MemoryUnavailable(_)), "{err}");
    let msg = err.to_string();
    assert!(msg.contains("roundtrip"), "must name the function: {msg}");
    assert!(msg.contains("Absent"), "must name the policy: {msg}");
}

/// The collision this slice exists to prevent: a frame in the HOST's memory
/// with the stack still pinned at the module's private page top. 65536 is the
/// host's data there, so the request is refused rather than silently
/// corrupting it.
#[test]
fn a_frame_in_imported_memory_without_a_host_base_is_refused() {
    let module = build_frame_module("imported_memory_owned_stack");
    let policy = WasmModulePolicy {
        memory: WasmMemoryPolicy::Imported {
            module: ISLAND_ABI_NAMESPACE.to_string(),
            name: ISLAND_MEMORY_IMPORT.to_string(),
        },
        stack: WasmStackPolicy::OwnedTop,
        func_imports: WasmFuncImportPolicy::Forbidden,
        ..WasmModulePolicy::closed()
    };
    let err = wasm::compile_module_with_policy_and_license(&module, &policy, &permit_unlicensed())
        .expect_err("a private stack top inside a host's memory must be refused");
    assert!(
        matches!(err, WasmLowerError::StackBaseUnavailable(_)),
        "{err}"
    );
    let msg = err.to_string();
    assert!(msg.contains("roundtrip"), "must name the function: {msg}");
    assert!(msg.contains("HostBase"), "must name the fix: {msg}");
}

/// A body-less function has nothing to lower, so without an import policy it
/// is refused by name — not lowered as an empty function, and not silently
/// dropped.
#[test]
fn a_body_less_function_is_refused_without_an_import_policy() {
    let mut mb = ModuleBuilder::new("unbound_decl");
    let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    mb.function("host_only", ft).build();
    let module = finish_wasm32(mb);

    let err = wasm::compile_module_with_policy_and_license(
        &module,
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .expect_err("the closed lane must refuse a declaration it cannot define");
    assert!(
        matches!(err, WasmLowerError::UnboundDeclaration(_)),
        "{err}"
    );
    let msg = err.to_string();
    assert!(msg.contains("host_only"), "must name the function: {msg}");
    assert!(
        msg.contains("WasmFuncImportPolicy::FromModule"),
        "must name the fix: {msg}"
    );
}

// ---------------------------------------------------------------------------
// P3 — execution evidence: the value domain, run.
// ---------------------------------------------------------------------------

/// Compile ONE corpus shape into its own module, validate it, and return the
/// bytes.
fn compile_shape(name: &'static str, build: fn(&mut ModuleBuilder)) -> Vec<u8> {
    let mut mb = ModuleBuilder::new(name);
    build(&mut mb);
    let module = finish_wasm32(mb);
    let bytes = wasm::compile_module_with_policy_and_license(
        &module,
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .unwrap_or_else(|e| panic!("compiling `{name}`: {e}"));
    validate(name, &bytes);
    bytes
}

/// True if any defined body dispatches through `br_table`.
fn uses_br_table(bytes: &[u8]) -> bool {
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::CodeSectionEntry(body) = payload.expect("parse") {
            for op in body.get_operators_reader().expect("operators") {
                if matches!(op.expect("operator"), wasmparser::Operator::BrTable { .. }) {
                    return true;
                }
            }
        }
    }
    false
}

/// The `br_table` targets of the first table in the module, as
/// `(case labels…, default label)`.
fn br_table_targets(bytes: &[u8]) -> Option<(Vec<u32>, u32)> {
    for payload in wasmparser::Parser::new(0).parse_all(bytes) {
        if let wasmparser::Payload::CodeSectionEntry(body) = payload.expect("parse") {
            for op in body.get_operators_reader().expect("operators") {
                if let wasmparser::Operator::BrTable { targets } = op.expect("operator") {
                    let labels: Vec<u32> = targets.targets().map(|t| t.expect("target")).collect();
                    return Some((labels, targets.default()));
                }
            }
        }
    }
    None
}

/// A dense case range dispatches through ONE `br_table`, and every index —
/// in range, out of range, and negative — lands on the arm the trust-ir switch
/// names.
#[test]
fn a_dense_switch_dispatches_through_br_table() {
    let bytes = compile_shape("switch_dense", |mb| {
        build_switch(mb, "switch_dense", &[0, 1, 2, 3, 4, 5, 6, 7], false)
    });
    assert!(
        uses_br_table(&bytes),
        "8 contiguous cases must use br_table"
    );
    let (labels, default) = br_table_targets(&bytes).expect("a br_table");
    // Eight arms, at depths 0..=7, with the default one past them (at the
    // default level the emission pass's control cleanup unwraps the block no
    // branch names around the table).
    assert_eq!(labels, (0..=7).collect::<Vec<u32>>());
    assert_eq!(default, 8);

    let driver = r#"
import { readFileSync } from 'node:fs';
const { instance } = await WebAssembly.instantiate(readFileSync(process.argv[2]), {});
const f = instance.exports.switch_dense;
const X = 1000;
for (let v = 0; v < 8; v++) {
  const want = X + v * 7 + 1;
  if (f(v, X) !== want) { console.error(`switch_dense(${v}) = ${f(v, X)}, expected ${want}`); process.exit(1); }
}
for (const v of [-2147483648, -1000, -1, 8, 9, 100, 2147483647]) {
  if (f(v, X) !== X - 1) { console.error(`switch_dense(${v}) = ${f(v, X)}, expected the default ${X - 1}`); process.exit(1); }
}
console.log('OK');
"#;
    run_under_node("switch_dense", &bytes, driver);
}

/// Cases that do not start at zero are normalized by their minimum, holes in
/// the covered range take the DEFAULT edge, and negative case values work the
/// same way — the three classic `br_table` bug sites.
#[test]
fn br_table_normalizes_the_index_and_routes_holes_to_the_default() {
    let holes = compile_shape("switch_holes", |mb| {
        build_switch(mb, "switch_holes", &[10, 11, 13, 16], false)
    });
    assert!(uses_br_table(&holes));
    let (labels, default) = br_table_targets(&holes).expect("a br_table");
    // Span 10..=16 is seven entries; 12, 14 and 15 are holes → the default.
    assert_eq!(labels, vec![0, 1, default, 2, default, default, 3]);
    assert_eq!(default, 4);
    let driver = r#"
import { readFileSync } from 'node:fs';
const { instance } = await WebAssembly.instantiate(readFileSync(process.argv[2]), {});
const f = instance.exports.switch_holes;
const X = 100;
const want = { 10: X + 1, 11: X + 8, 13: X + 15, 16: X + 22 };
for (let v = -5; v <= 25; v++) {
  const expected = v in want ? want[v] : X - 1;
  if (f(v, X) !== expected) { console.error(`switch_holes(${v}) = ${f(v, X)}, expected ${expected}`); process.exit(1); }
}
console.log('OK');
"#;
    run_under_node("switch_holes", &holes, driver);

    let negative = compile_shape("switch_negative", |mb| {
        build_switch(mb, "switch_negative", &[-4, -3, -2, -1, 0, 1], false)
    });
    assert!(uses_br_table(&negative));
    let driver = r#"
import { readFileSync } from 'node:fs';
const { instance } = await WebAssembly.instantiate(readFileSync(process.argv[2]), {});
const f = instance.exports.switch_negative;
const X = 50;
for (let k = 0; k < 6; k++) {
  const v = -4 + k;
  const want = X + k * 7 + 1;
  if (f(v, X) !== want) { console.error(`switch_negative(${v}) = ${f(v, X)}, expected ${want}`); process.exit(1); }
}
for (const v of [-2147483648, -6, -5, 2, 3, 2147483647]) {
  if (f(v, X) !== X - 1) { console.error(`switch_negative(${v}) = ${f(v, X)}, expected the default`); process.exit(1); }
}
console.log('OK');
"#;
    run_under_node("switch_negative", &negative, driver);
}

/// A switch whose DEFAULT edge reuses one of its own case blocks: the default
/// label and that case's label must name the same arm, and the block must be
/// emitted exactly once.
#[test]
fn a_switch_whose_default_is_a_case_target_shares_one_arm() {
    let bytes = compile_shape("switch_default_is_a_case_target", |mb| {
        build_switch(
            mb,
            "switch_default_is_a_case_target",
            &[0, 1, 2, 3, 4],
            true,
        )
    });
    assert!(uses_br_table(&bytes));
    let driver = r#"
import { readFileSync } from 'node:fs';
const { instance } = await WebAssembly.instantiate(readFileSync(process.argv[2]), {});
const f = instance.exports.switch_default_is_a_case_target;
const X = 7;
for (let v = 0; v < 5; v++) {
  const want = X + v * 7 + 1;
  if (f(v, X) !== want) { console.error(`case ${v} = ${f(v, X)}, expected ${want}`); process.exit(1); }
}
// Everything else takes the default edge, which IS case 0's block.
for (const v of [-1, 5, 6, 1000]) {
  if (f(v, X) !== X + 1) { console.error(`default ${v} = ${f(v, X)}, expected ${X + 1}`); process.exit(1); }
}
console.log('OK');
"#;
    run_under_node("switch_default_case", &bytes, driver);
}

/// The widest table the density heuristic admits: 256 contiguous cases, which
/// is 256 nested `block`s around one `br_table`. The reference validator
/// accepts the nest and an engine dispatches through it — the scale check the
/// 8-case shapes cannot make.
#[test]
fn a_wide_dense_switch_nests_and_dispatches() {
    let values: Vec<i128> = (0..256).collect();
    let mut mb = ModuleBuilder::new("switch_wide");
    build_switch(&mut mb, "switch_wide", &values, false);
    let module = finish_wasm32(mb);
    let bytes = wasm::compile_module_with_policy_and_license(
        &module,
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .expect("a 256-case switch must compile");
    validate("switch_wide", &bytes);
    assert!(uses_br_table(&bytes));
    let (labels, default) = br_table_targets(&bytes).expect("a br_table");
    assert_eq!(labels.len(), 256, "one entry per covered value");
    assert_eq!(labels, (0..=255).collect::<Vec<u32>>());
    assert_eq!(default, 256);

    let driver = r#"
import { readFileSync } from 'node:fs';
const { instance } = await WebAssembly.instantiate(readFileSync(process.argv[2]), {});
const f = instance.exports.switch_wide;
const X = 11;
for (let v = 0; v < 256; v++) {
  const want = X + v * 7 + 1;
  if (f(v, X) !== want) { console.error(`switch_wide(${v}) = ${f(v, X)}, expected ${want}`); process.exit(1); }
}
for (const v of [-1, 256, 257, 1 << 20]) {
  if (f(v, X) !== X - 1) { console.error(`switch_wide(${v}) took an arm, not the default`); process.exit(1); }
}
console.log('OK');
"#;
    run_under_node("switch_wide", &bytes, driver);
}

/// Below the case-count floor, or too sparse for the density floor, the
/// compare-cascade stays — and still computes the same function.
#[test]
fn a_sparse_or_tiny_switch_keeps_the_compare_cascade() {
    let sparse = compile_shape("switch_sparse", |mb| {
        build_switch(mb, "switch_sparse", &[0, 500, 9000], false)
    });
    assert!(
        !uses_br_table(&sparse),
        "a 9001-wide span over 3 cases must not become a jump table"
    );
    let single = compile_shape("switch_single_case", |mb| {
        build_switch(mb, "switch_single_case", &[7], false)
    });
    assert!(!uses_br_table(&single), "one case is a single compare");

    let driver = r#"
import { readFileSync } from 'node:fs';
const { instance } = await WebAssembly.instantiate(readFileSync(process.argv[2]), {});
const f = instance.exports.switch_sparse;
const X = 3;
const want = { 0: X + 1, 500: X + 8, 9000: X + 15 };
for (const v of [0, 500, 9000, -1, 1, 499, 8999, 9001]) {
  const expected = v in want ? want[v] : X - 1;
  if (f(v, X) !== expected) { console.error(`switch_sparse(${v}) = ${f(v, X)}, expected ${expected}`); process.exit(1); }
}
console.log('OK');
"#;
    run_under_node("switch_sparse", &sparse, driver);
}

/// Sub-word memory: a byte stored through `i32.store8` and read back both ways
/// differs by exactly the sign extension, and the 16-bit pair does the same —
/// the property a 32-bit load could not express.
#[test]
fn sub_word_memory_round_trips_at_its_own_width() {
    let bytes = compile_shape("subword_memory", build_subword_memory);
    let driver = r#"
import { readFileSync } from 'node:fs';
const { instance } = await WebAssembly.instantiate(readFileSync(process.argv[2]), {});
const f = instance.exports.subword_memory;
for (const x of [0, 1, 127, 128, 255, 256, 0x7fff, 0x8000, 0xffff, 0x12345678, -1, -129]) {
  const b = x & 0xff, h = x & 0xffff;
  const want = (b + (b << 24 >> 24) + h + (h << 16 >> 16)) | 0;
  const got = f(x);
  if (got !== want) { console.error(`subword_memory(${x}) = ${got}, expected ${want}`); process.exit(1); }
}
console.log('OK');
"#;
    run_under_node("subword_memory", &bytes, driver);
}

/// A constant table lives in a DATA SEGMENT — bytes in linear memory — instead
/// of in a compare tree, and the module reads it back through a zero-extending
/// byte load.
#[test]
fn a_constant_table_lives_in_a_data_segment() {
    let bytes = compile_shape("static_table", build_static_table);
    let mut segments = Vec::new();
    for payload in wasmparser::Parser::new(0).parse_all(&bytes) {
        if let wasmparser::Payload::DataSection(reader) = payload.expect("parse") {
            for data in reader {
                let data = data.expect("data segment");
                segments.push(data.data.to_vec());
            }
        }
    }
    assert_eq!(
        segments,
        vec![vec![3u8, 1, 4, 1, 5, 9, 2, 6]],
        "the table's bytes must ship as a data segment"
    );

    let driver = r#"
import { readFileSync } from 'node:fs';
const { instance } = await WebAssembly.instantiate(readFileSync(process.argv[2]), {});
const f = instance.exports.static_table;
const table = [3, 1, 4, 1, 5, 9, 2, 6];
for (let i = -20; i < 40; i++) {
  const want = table[i & 7];
  if (f(i) !== want) { console.error(`static_table(${i}) = ${f(i)}, expected ${want}`); process.exit(1); }
}
console.log('OK');
"#;
    run_under_node("static_table", &bytes, driver);
}

/// `memory.size` / `memory.grow`, surfaced as exported shims: the module can
/// see and extend the memory it owns.
#[test]
fn the_memory_growth_shims_resize_an_owned_memory() {
    let module = build_frame_module("growable");
    let policy = WasmModulePolicy {
        memory: WasmMemoryPolicy::Owned {
            pages: 1,
            export: Some("memory".to_string()),
        },
        memory_growth: wasm::WasmMemoryGrowthPolicy::OwnedShims,
        ..WasmModulePolicy::closed()
    };
    let (bytes, contract) = compile_and_validate_with_policy("growable", &module, &policy);
    assert!(contract.is_empty(), "an owned memory binds no host");
    let exports: Vec<String> = module_exports(&bytes)
        .into_iter()
        .map(|(name, _, _)| name)
        .collect();
    assert!(
        exports.contains(&wasm::MEMORY_SIZE_EXPORT.to_string()),
        "{exports:?}"
    );
    assert!(
        exports.contains(&wasm::MEMORY_GROW_EXPORT.to_string()),
        "{exports:?}"
    );

    let driver = r#"
import { readFileSync } from 'node:fs';
const { instance } = await WebAssembly.instantiate(readFileSync(process.argv[2]), {});
const { __memory_size, __memory_grow, memory, roundtrip } = instance.exports;
if (__memory_size() !== 1) { console.error('initial size ' + __memory_size()); process.exit(1); }
const previous = __memory_grow(2);
if (previous !== 1) { console.error('grow returned ' + previous); process.exit(1); }
if (__memory_size() !== 3) { console.error('size after grow ' + __memory_size()); process.exit(1); }
if (memory.buffer.byteLength !== 3 * 65536) { console.error('buffer ' + memory.buffer.byteLength); process.exit(1); }
// The module still works across the resize.
if (roundtrip(0x2468ace) !== 0x2468ace) { console.error('roundtrip broke after grow'); process.exit(1); }
console.log('OK');
"#;
    run_under_node("memory_growth", &bytes, driver);
}

/// An island may put static data in the host's memory ONLY where the host
/// reserved a region, and may grow it only once the host has granted that too.
#[test]
fn an_island_writes_static_data_where_the_host_reserved_it() {
    let island_table = || {
        let mut mb = ModuleBuilder::new("island_table");
        build_static_table(&mut mb);
        finish_wasm32(mb)
    };

    // Fail closed first: the default island policy has no reserved region.
    let err = wasm::compile_module_with_policy_and_license(
        &island_table(),
        &WasmModulePolicy::island("tab"),
        &permit_unlicensed(),
    )
    .expect_err("static data in a host memory needs the host's grant");
    assert!(
        matches!(err, WasmLowerError::HostMemoryNotGranted(_)),
        "{err}"
    );
    assert!(err.to_string().contains("HostReservedAt"), "{err}");

    const RESERVED: u32 = 8192;
    let policy = WasmModulePolicy {
        static_data: wasm::WasmStaticDataPolicy::HostReservedAt { base: RESERVED },
        memory_growth: wasm::WasmMemoryGrowthPolicy::HostGrantedShims,
        ..WasmModulePolicy::island("tab")
    };
    let (bytes, contract) =
        compile_and_validate_with_policy("island_table", &island_table(), &policy);
    // The island needs no frame, so its only IMPORT is the memory itself — but
    // the two grants it took over that memory are terms of the same contract,
    // so the evidence names them beside it rather than understating the surface.
    assert_eq!(
        contract,
        vec![
            format!("memory {ISLAND_ABI_NAMESPACE}.{ISLAND_MEMORY_IMPORT}"),
            format!(
                "data {ISLAND_ABI_NAMESPACE}.{ISLAND_MEMORY_IMPORT}[{RESERVED}..{})",
                RESERVED + 8
            ),
            format!("grow {ISLAND_ABI_NAMESPACE}.{ISLAND_MEMORY_IMPORT}"),
        ],
        "the island binds the host memory, the region it writes, and growth"
    );
    assert!(!defines_memory(&bytes), "the island defines no memory");

    let driver = r#"
import { readFileSync } from 'node:fs';
const memory = new WebAssembly.Memory({ initial: 1 });
const ns = 'trust:island/abi@1';
const __island_stack_base = new WebAssembly.Global({ value: 'i32', mutable: false }, 4096);
const { instance } = await WebAssembly.instantiate(readFileSync(process.argv[2]), {
  [ns]: { memory, __island_stack_base },
});
const RESERVED = 8192;
const bytes = new Uint8Array(memory.buffer);
const table = [3, 1, 4, 1, 5, 9, 2, 6];
for (let i = 0; i < table.length; i++) {
  if (bytes[RESERVED + i] !== table[i]) {
    console.error(`byte ${i} landed as ${bytes[RESERVED + i]}, expected ${table[i]}`);
    process.exit(1);
  }
}
// Nothing was written outside the reserved region.
for (const probe of [0, 8, 4096 - 8, 4096, RESERVED - 1, RESERVED + table.length]) {
  if (bytes[probe] !== 0) { console.error('island wrote at ' + probe); process.exit(1); }
}
for (let i = -20; i < 40; i++) {
  if (instance.exports.static_table(i) !== table[i & 7]) {
    console.error('static_table(' + i + ') disagrees with the table in memory'); process.exit(1);
  }
}
// The host granted growth of ITS memory.
if (instance.exports.__memory_grow(1) !== 1) { console.error('grow'); process.exit(1); }
if (instance.exports.__memory_size() !== 2) { console.error('size'); process.exit(1); }
console.log('OK');
"#;
    run_under_node("island_static_data", &bytes, driver);
}

/// The default policy is the pre-P2 backend: for every corpus shape, the
/// policy-taking entry and the plain one emit the SAME BYTES. This is what
/// makes "islands are additive" a checked claim rather than an intention.
#[test]
fn the_closed_policy_reproduces_the_default_bytes() {
    let closed = WasmModulePolicy::closed();
    assert_eq!(closed, WasmModulePolicy::default());
    for shape in corpus() {
        let mut mb = ModuleBuilder::new(shape.name);
        (shape.build)(&mut mb);
        let module = finish_wasm32(mb);
        let default_bytes = wasm::compile_module_with_policy_and_license(
            &module,
            &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
            &permit_unlicensed(),
        )
        .expect("default compile");
        let policy_bytes =
            wasm::compile_module_with_policy_and_license(&module, &closed, &permit_unlicensed())
                .expect("closed-policy compile");
        assert_eq!(
            default_bytes, policy_bytes,
            "`{}` differs between compile_module and the closed policy",
            shape.name
        );
    }

    // The whole corpus as one module too.
    let mut mb = ModuleBuilder::new("combined");
    for shape in corpus() {
        (shape.build)(&mut mb);
    }
    let module = finish_wasm32(mb);
    assert_eq!(
        wasm::compile_module_with_policy_and_license(
            &module,
            &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
            &permit_unlicensed()
        )
        .expect("default compile"),
        wasm::compile_module_with_policy_and_license(&module, &closed, &permit_unlicensed())
            .expect("closed-policy compile"),
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
