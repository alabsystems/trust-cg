// trust-cg-verify/tests/wasm_cfg_structural_gate.rs — the P4 family-1 CFG gate
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// THE BUILD GATE for the WebAssembly CFG/structural invariant
// (`trust_cg_verify::wasm_cfg_proofs`). The module itself is byte-only — it
// takes a `.wasm` buffer and knows nothing about the compiler that produced it.
// That is what makes this file the load-bearing half: it RUNS THE REAL BACKEND
// over a control-flow-diverse corpus and checks the invariant against the bytes
// the backend actually emitted, then MUTATES those same real bytes and checks
// that the invariant fails.
//
// Three things are asserted here and each one matters on its own:
//
//   1. The invariant HOLDS on every emitted corpus module, and no module is
//      INCONCLUSIVE — an inconclusive verdict means the decoder met an opcode
//      it has no typing rule for, which is uncredited debt and fails the gate
//      loudly rather than passing quietly.
//   2. Every MUST-REFUTE mutation of a real emitted module is refuted. A
//      mutation that passes means the corresponding invariant is vacuous on
//      real output, whatever the synthetic mutants say.
//   3. Every KNOWN BLIND SPOT of a real emitted module is NOT refuted, and is
//      counted as such. This is the deliberate measurement of the family's gap:
//      the invariant is a NECESSARY CONDITION on structuring, not a
//      bisimulation, and these mutants are what that sentence means in bytes.
//
// The corpus's expected LOOP counts are stated here from the trust-ir CFGs
// built in this file — an independent source-side statement, not a quantity
// read back out of `lower.rs` — and compared against the `loop` openers decoded
// from the emitted bytes.

use trust_cg_codegen::wasm;
use trust_cg_verify::coverage_gate::{CoverageFinding, CoverageGate, GateArch, OpcodeClass};
use trust_cg_verify::wasm_cfg_proofs as cfg;
use trust_ir::{CastOp, Constant, FuncId, ICmpOp, SwitchCase, Ty};
use trust_ir_build::ModuleBuilder;

// ===========================================================================
// The corpus
// ===========================================================================

/// One corpus shape: a name, a builder, and the number of LOOP HEADERS its
/// trust-ir CFG has (i.e. the number of distinct back-edge targets), stated
/// from the CFG this file constructs.
struct Shape {
    name: &'static str,
    build: fn(&mut ModuleBuilder),
    expected_loops: usize,
}

fn corpus() -> Vec<Shape> {
    vec![
        Shape {
            name: "if_else_diamond",
            build: build_if_else_diamond,
            expected_loops: 0,
        },
        Shape {
            name: "counted_loop",
            build: build_counted_loop,
            expected_loops: 1,
        },
        Shape {
            name: "gcd_mod_loop",
            build: build_gcd,
            expected_loops: 1,
        },
        Shape {
            name: "nested_loop",
            build: build_nested_loop,
            expected_loops: 2,
        },
        Shape {
            name: "clamp_nested_ifs",
            build: build_clamp,
            expected_loops: 0,
        },
        Shape {
            name: "switch_dense_br_table",
            build: |mb| {
                build_switch(
                    mb,
                    "switch_dense_br_table",
                    &[0, 1, 2, 3, 4, 5, 6, 7],
                    false,
                )
            },
            expected_loops: 0,
        },
        Shape {
            name: "switch_sparse_cascade",
            build: |mb| build_switch(mb, "switch_sparse_cascade", &[0, 500, 9000], false),
            expected_loops: 0,
        },
        Shape {
            // THE two-merge-children shape: the default edge reuses case 0's
            // block, so that block gains a second predecessor and becomes a
            // merge child beside the join. This is the shape the P3
            // `split_first`/`split_last` defect failed on.
            name: "switch_default_is_a_case_target",
            build: |mb| {
                build_switch(
                    mb,
                    "switch_default_is_a_case_target",
                    &[0, 1, 2, 3, 4],
                    true,
                )
            },
            expected_loops: 0,
        },
        Shape {
            name: "loop_with_switch_inside",
            build: build_loop_with_switch,
            expected_loops: 1,
        },
        Shape {
            name: "direct_call_chain",
            build: build_call_chain,
            expected_loops: 0,
        },
        Shape {
            name: "subword_memory",
            build: build_subword_memory,
            expected_loops: 0,
        },
        Shape {
            name: "float_round_trip",
            build: build_float_round_trip,
            expected_loops: 0,
        },
    ]
}

/// `max(a, b)` — one if/else diamond with a parameterized join.
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

/// `xor_to(n)` — one back edge (a counted loop with an accumulator). The
/// accumulator is an `xor`, not a sum: the optimizing lane's closed-form
/// induction replaces an affine sum by its value, and this shape pins the
/// relooper's `loop` scope, so the loop must reach it.
fn build_counted_loop(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("counted_loop", ft);
    let entry = fb.create_block();
    let header = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    let n = fb.add_block_param(entry, Ty::I32);
    let _unused = fb.add_block_param(entry, Ty::I32);
    let i = fb.add_block_param(header, Ty::I32);
    let acc = fb.add_block_param(header, Ty::I32);
    let out = fb.add_block_param(exit, Ty::I32);
    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I32, 0);
    fb.br(header, vec![zero, zero]);
    fb.switch_to_block(header);
    let done = fb.icmp(ICmpOp::Sge, Ty::I32, i, n);
    fb.condbr(done, exit, vec![acc], body, vec![]);
    fb.switch_to_block(body);
    let one = fb.iconst(Ty::I32, 1);
    let next_i = fb.add(Ty::I32, i, one);
    let next_acc = fb.binop(trust_ir::BinOp::Xor, Ty::I32, acc, i);
    fb.br(header, vec![next_i, next_acc]);
    fb.switch_to_block(exit);
    fb.ret(vec![out]);
    fb.build();
}

/// `gcd(a, b)` by repeated remainder — one back edge with an if inside it.
fn build_gcd(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("gcd_mod_loop", ft);
    let entry = fb.create_block();
    let header = fb.create_block();
    let body = fb.create_block();
    let exit = fb.create_block();
    let a0 = fb.add_block_param(entry, Ty::I32);
    let b0 = fb.add_block_param(entry, Ty::I32);
    let a = fb.add_block_param(header, Ty::I32);
    let b = fb.add_block_param(header, Ty::I32);
    let out = fb.add_block_param(exit, Ty::I32);
    fb.switch_to_block(entry);
    fb.br(header, vec![a0, b0]);
    fb.switch_to_block(header);
    let zero = fb.iconst(Ty::I32, 0);
    let done = fb.icmp(ICmpOp::Eq, Ty::I32, b, zero);
    fb.condbr(done, exit, vec![a], body, vec![]);
    fb.switch_to_block(body);
    // `b` is nonzero on this edge; the remainder is well defined.
    let r = fb.binop(trust_ir::BinOp::SRem, Ty::I32, a, b);
    fb.br(header, vec![b, r]);
    fb.switch_to_block(exit);
    fb.ret(vec![out]);
    fb.build();
}

/// Two nested counted loops — two loop headers, so two `loop` scopes. The
/// inner accumulator is an `xor` for the reason `build_counted_loop` states.
fn build_nested_loop(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("nested_loop", ft);
    let entry = fb.create_block();
    let outer = fb.create_block();
    let inner_pre = fb.create_block();
    let inner = fb.create_block();
    let inner_body = fb.create_block();
    let outer_latch = fb.create_block();
    let exit = fb.create_block();
    let n = fb.add_block_param(entry, Ty::I32);
    let m = fb.add_block_param(entry, Ty::I32);
    let i = fb.add_block_param(outer, Ty::I32);
    let acc = fb.add_block_param(outer, Ty::I32);
    let j = fb.add_block_param(inner, Ty::I32);
    let iacc = fb.add_block_param(inner, Ty::I32);
    let done_acc = fb.add_block_param(outer_latch, Ty::I32);
    let out = fb.add_block_param(exit, Ty::I32);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I32, 0);
    fb.br(outer, vec![zero, zero]);

    fb.switch_to_block(outer);
    let outer_done = fb.icmp(ICmpOp::Sge, Ty::I32, i, n);
    fb.condbr(outer_done, exit, vec![acc], inner_pre, vec![]);

    fb.switch_to_block(inner_pre);
    let z2 = fb.iconst(Ty::I32, 0);
    fb.br(inner, vec![z2, acc]);

    fb.switch_to_block(inner);
    let inner_done = fb.icmp(ICmpOp::Sge, Ty::I32, j, m);
    fb.condbr(inner_done, outer_latch, vec![iacc], inner_body, vec![]);

    fb.switch_to_block(inner_body);
    let one = fb.iconst(Ty::I32, 1);
    let next_j = fb.add(Ty::I32, j, one);
    let next_iacc = fb.binop(trust_ir::BinOp::Xor, Ty::I32, iacc, j);
    fb.br(inner, vec![next_j, next_iacc]);

    fb.switch_to_block(outer_latch);
    let one2 = fb.iconst(Ty::I32, 1);
    let next_i = fb.add(Ty::I32, i, one2);
    fb.br(outer, vec![next_i, done_acc]);

    fb.switch_to_block(exit);
    fb.ret(vec![out]);
    fb.build();
}

/// `clamp(v, hi)` — two chained if/else diamonds sharing a join.
fn build_clamp(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("clamp_nested_ifs", ft);
    let entry = fb.create_block();
    let lo_arm = fb.create_block();
    let mid = fb.create_block();
    let hi_arm = fb.create_block();
    let pass = fb.create_block();
    let join = fb.create_block();
    let v = fb.add_block_param(entry, Ty::I32);
    let hi = fb.add_block_param(entry, Ty::I32);
    let r = fb.add_block_param(join, Ty::I32);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I32, 0);
    let below = fb.icmp(ICmpOp::Slt, Ty::I32, v, zero);
    fb.condbr(below, lo_arm, vec![], mid, vec![]);

    fb.switch_to_block(lo_arm);
    let z2 = fb.iconst(Ty::I32, 0);
    fb.br(join, vec![z2]);

    fb.switch_to_block(mid);
    let above = fb.icmp(ICmpOp::Sgt, Ty::I32, v, hi);
    fb.condbr(above, hi_arm, vec![], pass, vec![]);

    fb.switch_to_block(hi_arm);
    fb.br(join, vec![hi]);

    fb.switch_to_block(pass);
    fb.br(join, vec![v]);

    fb.switch_to_block(join);
    fb.ret(vec![r]);
    fb.build();
}

/// A `Switch` over `values`. When `default_is_a_case_target`, the default edge
/// REUSES case 0's block, which gives that block a second predecessor: the
/// enclosing node then has TWO merge children, which is exactly the nesting the
/// relooper must order latest-RPO-outermost.
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
    // every trust-cg ingestion entry refuses what the validator refuses
    // (WS7.3).
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

/// A `Switch` INSIDE a loop body — a br_table nest under a `loop` label, so the
/// table's depths are measured through a scope the table did not open.
fn build_loop_with_switch(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("loop_with_switch_inside", ft);
    let entry = fb.create_block();
    let header = fb.create_block();
    let body = fb.create_block();
    let arms: Vec<_> = (0..4).map(|_| fb.create_block()).collect();
    let latch = fb.create_block();
    let exit = fb.create_block();
    let n = fb.add_block_param(entry, Ty::I32);
    let _x = fb.add_block_param(entry, Ty::I32);
    let i = fb.add_block_param(header, Ty::I32);
    let acc = fb.add_block_param(header, Ty::I32);
    let delta = fb.add_block_param(latch, Ty::I32);
    let out = fb.add_block_param(exit, Ty::I32);

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::I32, 0);
    fb.br(header, vec![zero, zero]);

    fb.switch_to_block(header);
    let done = fb.icmp(ICmpOp::Sge, Ty::I32, i, n);
    fb.condbr(done, exit, vec![acc], body, vec![]);

    fb.switch_to_block(body);
    let three = fb.iconst(Ty::I32, 3);
    let sel = fb.binop(trust_ir::BinOp::And, Ty::I32, i, three);
    let cases: Vec<SwitchCase> = arms
        .iter()
        .enumerate()
        .map(|(k, &target)| SwitchCase {
            value: Constant::Int(k as i128),
            target,
            args: vec![],
        })
        .collect();
    fb.switch(sel, cases, arms[0], vec![]);
    for (k, &arm) in arms.iter().enumerate() {
        fb.switch_to_block(arm);
        let c = fb.iconst(Ty::I32, (k as i128) + 1);
        fb.br(latch, vec![c]);
    }

    fb.switch_to_block(latch);
    let one = fb.iconst(Ty::I32, 1);
    let next_i = fb.add(Ty::I32, i, one);
    let next_acc = fb.add(Ty::I32, acc, delta);
    fb.br(header, vec![next_i, next_acc]);

    fb.switch_to_block(exit);
    fb.ret(vec![out]);
    fb.build();
}

/// Two functions, the second calling the first — exercises the `call` typing
/// rule (params popped in order, results pushed).
fn build_call_chain(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let callee: FuncId = {
        let mut fb = mb.function("call_chain_leaf", ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I32);
        let b = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let s = fb.add(Ty::I32, a, b);
        fb.ret(vec![s]);
        fb.build()
    };
    let mut fb = mb.function("direct_call_chain", ft);
    let entry = fb.create_block();
    let tb = fb.create_block();
    let eb = fb.create_block();
    let join = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    let r = fb.add_block_param(join, Ty::I32);
    fb.switch_to_block(entry);
    let c = fb.icmp(ICmpOp::Slt, Ty::I32, a, b);
    fb.condbr(c, tb, vec![], eb, vec![]);
    fb.switch_to_block(tb);
    let s1 = fb.call(callee, vec![a, b]);
    fb.br(join, vec![s1]);
    fb.switch_to_block(eb);
    let s2 = fb.call(callee, vec![b, a]);
    fb.br(join, vec![s2]);
    fb.switch_to_block(join);
    fb.ret(vec![r]);
    fb.build();
}

/// A narrow value written to and read back from the shadow stack — sub-word
/// stores/loads plus the narrow-carrier canonicalization, under an if/else.
fn build_subword_memory(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("subword_memory", ft);
    let entry = fb.create_block();
    let tb = fb.create_block();
    let eb = fb.create_block();
    let join = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    let r = fb.add_block_param(join, Ty::I32);

    fb.switch_to_block(entry);
    let slot = fb.alloca(Ty::U8);
    let c = fb.icmp(ICmpOp::Slt, Ty::I32, a, b);
    fb.condbr(c, tb, vec![], eb, vec![]);

    fb.switch_to_block(tb);
    let na = fb.cast(CastOp::Trunc, Ty::I32, Ty::U8, a);
    fb.store(Ty::U8, slot, na);
    let back_a = fb.load(Ty::U8, slot);
    let wide_a = fb.cast(CastOp::ZExt, Ty::U8, Ty::I32, back_a);
    fb.br(join, vec![wide_a]);

    fb.switch_to_block(eb);
    let nb = fb.cast(CastOp::Trunc, Ty::I32, Ty::U8, b);
    fb.store(Ty::U8, slot, nb);
    let back_b = fb.load(Ty::U8, slot);
    let wide_b = fb.cast(CastOp::ZExt, Ty::U8, Ty::I32, back_b);
    fb.br(join, vec![wide_b]);

    fb.switch_to_block(join);
    fb.ret(vec![r]);
    fb.build();
}

/// An f64 round trip through a compare — exercises the f64 typing rules and the
/// int<->float conversions in the same body.
fn build_float_round_trip(mb: &mut ModuleBuilder) {
    let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let mut fb = mb.function("float_round_trip", ft);
    let entry = fb.create_block();
    let tb = fb.create_block();
    let eb = fb.create_block();
    let join = fb.create_block();
    let a = fb.add_block_param(entry, Ty::I32);
    let b = fb.add_block_param(entry, Ty::I32);
    let r = fb.add_block_param(join, Ty::I32);

    fb.switch_to_block(entry);
    let fa = fb.cast(CastOp::SIToFP, Ty::I32, Ty::F64, a);
    let fb2 = fb.cast(CastOp::SIToFP, Ty::I32, Ty::F64, b);
    let sum = fb.fadd(Ty::F64, fa, fb2);
    let prod = fb.fmul(Ty::F64, fa, fb2);
    let c = fb.fcmp(trust_ir::FCmpOp::OLt, Ty::F64, sum, prod);
    fb.condbr(c, tb, vec![], eb, vec![]);

    fb.switch_to_block(tb);
    let back1 = fb.cast(CastOp::FPToSISat, Ty::F64, Ty::I32, sum);
    fb.br(join, vec![back1]);

    fb.switch_to_block(eb);
    let back2 = fb.cast(CastOp::FPToSISat, Ty::F64, Ty::I32, prod);
    fb.br(join, vec![back2]);

    fb.switch_to_block(join);
    fb.ret(vec![r]);
    fb.build();
}

/// Compile one shape into a wasm32 module, or fail naming the shape.
fn compile(shape: &Shape) -> Vec<u8> {
    let mut mb = ModuleBuilder::new(shape.name);
    (shape.build)(&mut mb);
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    module.target_info = Some(wasm::target::wasm32_target_info());
    wasm::compile_module_with_policy_and_license(
        &module,
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .unwrap_or_else(|e| panic!("wasm backend failed to compile `{}`: {e}", shape.name))
}

/// Every corpus shape, compiled once.
fn compiled_corpus() -> Vec<(&'static str, usize, Vec<u8>)> {
    corpus()
        .iter()
        .map(|s| (s.name, s.expected_loops, compile(s)))
        .collect()
}

// ===========================================================================
// 1. The invariant on real emitted bytes
// ===========================================================================

/// THE GATE. The structural invariant holds on every emitted corpus module, and
/// no module is INCONCLUSIVE — an opcode without a typing rule fails here
/// loudly instead of being waved past.
///
/// Prints the REAL per-shape evidence counts so the numbers in any report can
/// be traced back to a run.
#[test]
fn every_corpus_module_satisfies_the_structural_invariant() {
    let mut functions = 0usize;
    let mut instructions = 0usize;
    let mut branches = 0usize;
    let mut joins = 0usize;
    let mut scopes = 0usize;

    for (name, _, bytes) in compiled_corpus() {
        let verdict = cfg::check_module_structure(&bytes);
        assert!(
            !verdict.is_inconclusive(),
            "`{name}`: the checker DECLINED ({verdict}) — an opcode with no typing rule is \
             uncredited debt, not a pass"
        );
        assert!(verdict.holds(), "`{name}`: {verdict}");
        let report = verdict.report().expect("holds");
        let t = report.totals();
        eprintln!(
            "  {name:<34} {} bytes | {} fn | {} inst | {} branch labels | {} joins | {} scopes",
            bytes.len(),
            t.functions,
            t.instructions,
            t.branch_labels_resolved,
            t.joins_checked,
            t.scopes_matched
        );
        functions += t.functions;
        instructions += t.instructions;
        branches += t.branch_labels_resolved;
        joins += t.joins_checked;
        scopes += t.scopes_matched;
    }

    eprintln!(
        "wasm CFG structural invariant: {functions} functions, {instructions} instructions, \
         {branches} branch label references resolved, {joins} joins checked, {scopes} scopes \
         matched — all over REAL emitted bytes"
    );
    assert!(functions >= 12, "corpus shrank: only {functions} functions");
    assert!(branches > 0 && joins > 0 && scopes > 0);
}

/// The `loop` scopes decoded from the bytes match the loop-header count of the
/// trust-ir CFG this file built — the one structural quantity whose expected
/// value is stated INDEPENDENTLY of the backend (from the CFG, in `corpus()`).
///
/// This is not a bisimulation and does not pretend to be: it pins one count,
/// which a relooper that dropped or invented a loop scope would break.
#[test]
fn emitted_loop_scopes_match_the_source_cfg_back_edges() {
    for (name, expected_loops, bytes) in compiled_corpus() {
        let verdict = cfg::check_module_structure(&bytes);
        let report = verdict
            .report()
            .unwrap_or_else(|| panic!("`{name}`: {verdict}"));
        // The corpus function is the LAST defined one (helper functions the
        // backend synthesizes for memory access come first when present, and a
        // called leaf is defined before its caller).
        let loops: usize = report.functions.iter().map(|f| f.loops).sum();
        assert_eq!(
            loops, expected_loops,
            "`{name}`: {loops} `loop` scope(s) in the emitted bytes, but the trust-ir CFG this \
             test built has {expected_loops} loop header(s)"
        );
    }
}

/// REPORTS WHICH PART OF THE DECODER REAL BYTES ACTUALLY EXERCISE.
///
/// A checker that has typing rules for the whole spec but is only ever run over
/// `i32` straight-line code has been tested for far less than its rule table
/// suggests. This prints the distinct opcodes the corpus really produced, so a
/// reader can see exactly which rules are backed by emitted bytes and which are
/// backed only by the module's own unit tests. It is a REPORT with a floor, not
/// a completeness claim.
#[test]
fn corpus_opcode_coverage_is_reported() {
    let mut seen: std::collections::BTreeSet<String> = std::collections::BTreeSet::new();
    for (name, _, bytes) in compiled_corpus() {
        let bodies = cfg::decode_function_bodies(&bytes)
            .unwrap_or_else(|e| panic!("`{name}`: the decoder declined: {e}"));
        for (_, insts) in bodies {
            for inst in insts {
                match inst.sub {
                    Some(s) => seen.insert(format!("0xfc/{s}")),
                    None => seen.insert(format!("0x{:02x}", inst.opcode)),
                };
            }
        }
    }
    eprintln!(
        "corpus opcode coverage: {} distinct opcodes decoded from real emitted bytes: {}",
        seen.len(),
        seen.iter().cloned().collect::<Vec<_>>().join(" ")
    );
    // The control-flow surface this family is about must all be present.
    for required in [
        "0x02", "0x03", "0x04", "0x05", "0x0b", "0x0c", "0x0e", "0x0f",
    ] {
        assert!(
            seen.contains(required),
            "the corpus never emitted {required} — that control opcode's rule is exercised only by \
             the module's own unit tests"
        );
    }
    assert!(
        seen.len() >= 20,
        "opcode diversity collapsed to {} — the corpus stopped exercising the decoder",
        seen.len()
    );
}

/// The br_table shapes really do emit a `br_table`, and every one of its label
/// references — arms and default — resolved to a live label of uniform arity.
/// Without this the B3 row could be silently untested by the corpus.
#[test]
fn br_table_nests_resolve_every_arm_and_the_default() {
    let mut tables = 0usize;
    let mut table_labels = 0usize;
    for (name, _, bytes) in compiled_corpus() {
        let verdict = cfg::check_module_structure(&bytes);
        let report = verdict
            .report()
            .unwrap_or_else(|| panic!("`{name}`: {verdict}"));
        for f in &report.functions {
            let entries: Vec<_> = f.branches.iter().filter(|b| b.opcode == 0x0e).collect();
            if entries.is_empty() {
                continue;
            }
            // One `br_table` instruction contributes one resolution per arm plus
            // one for its default; they all share the instruction's offset.
            let offsets: std::collections::BTreeSet<_> = entries.iter().map(|b| b.offset).collect();
            tables += offsets.len();
            table_labels += entries.len();
            for b in entries {
                assert_eq!(
                    b.label_arity, 0,
                    "`{name}`: br_table label at 0x{:x} has arity {}",
                    b.offset, b.label_arity
                );
            }
        }
    }
    assert!(
        tables >= 2,
        "the corpus must exercise br_table; found {tables}"
    );
    eprintln!(
        "br_table coverage: {tables} table(s), {table_labels} label reference(s) resolved and \
         arity-checked"
    );
}

// ===========================================================================
// 2. Anti-tautology over REAL emitted bytes
// ===========================================================================

type Mutator = fn(&[u8]) -> Option<Vec<u8>>;

fn must_refute_mutators() -> Vec<(&'static str, Mutator)> {
    vec![
        ("br depth 127 (no such label)", |m| {
            cfg::mutate_branch_depth(m, 0x7f)
        }),
        ("dropped block `end`", |m| cfg::mutate_erase_end(m, 0)),
        ("second dropped block `end`", |m| {
            cfg::mutate_erase_end(m, 1)
        }),
        ("i32.add lowered as i64.add", cfg::mutate_i32_add_to_i64_add),
    ]
}

fn blind_spot_mutators() -> Vec<(&'static str, Mutator)> {
    vec![
        (
            "br retargeted to another live same-arity label",
            cfg::mutate_branch_to_wrong_live_label,
        ),
        (
            "`block` opener rewritten as `loop`",
            cfg::mutate_block_opener_to_loop,
        ),
    ]
}

/// THE TEETH. Every must-refute mutation of a REAL emitted module is refuted.
///
/// A mutation that is not applicable to a shape (no `i32.add`, no second `end`)
/// is counted as NOT APPLICABLE and reported — never silently treated as a
/// pass. The test fails if any applicable mutation survives, and it also fails
/// if a mutator turns out to be applicable nowhere, which would mean the
/// battery is testing nothing.
#[test]
fn real_module_mutations_are_refuted() {
    let corpus = compiled_corpus();
    let mut applied = 0usize;
    let mut refuted = 0usize;
    let mut not_applicable = 0usize;
    let mut inconclusive = 0usize;
    let mut per_mutator: Vec<(&'static str, usize, usize)> = Vec::new();

    for (mname, mutate) in must_refute_mutators() {
        let mut hits = 0usize;
        let mut kills = 0usize;
        for (name, _, bytes) in &corpus {
            let Some(mutant) = mutate(bytes) else {
                not_applicable += 1;
                continue;
            };
            assert_ne!(&mutant, bytes, "`{name}` / {mname}: mutation was a no-op");
            hits += 1;
            applied += 1;
            let verdict = cfg::check_module_structure(&mutant);
            if verdict.is_inconclusive() {
                // A mutation that makes the module undecodable is honest but is
                // NOT a refutation by the invariant; count it apart.
                inconclusive += 1;
                continue;
            }
            assert!(
                verdict.is_refuted(),
                "`{name}` / {mname}: the mutated module was NOT refuted ({verdict}) — the \
                 corresponding invariant is vacuous on real output"
            );
            kills += 1;
            refuted += 1;
        }
        assert!(
            hits > 0,
            "mutator `{mname}` applied to NO corpus module — the battery would be testing nothing"
        );
        per_mutator.push((mname, hits, kills));
    }

    for (mname, hits, kills) in &per_mutator {
        eprintln!("  must-refute {mname:<38} applied {hits:>2}, refuted {kills:>2}");
    }
    eprintln!(
        "anti-tautology over REAL emitted bytes: {applied} mutations applied, {refuted} refuted, \
         {inconclusive} made the module undecodable (counted apart, not as refutations), \
         {not_applicable} not applicable to that shape"
    );
    assert_eq!(
        refuted + inconclusive,
        applied,
        "every applied mutation must be refuted or (honestly) undecodable"
    );
}

/// THE OFF-BY-ONE SURVEY — the realistic depth-arithmetic slip, applied to
/// EVERY single-byte branch depth in every corpus module, one at a time.
///
/// A `br depth 127` is an easy kill and proves little on its own. This survey
/// bumps each real branch depth by exactly one — what `open_labels - depth`
/// computed against a stale frame produces — and reports how many of those
/// mutants the liveness invariant refutes and how many land on ANOTHER LIVE
/// LABEL and survive. The two numbers together are the honest measure of what
/// B1 discriminates: the survivors are precisely the wrong-successor class the
/// `branch-target INTENT binding` deferral owes, quantified rather than
/// asserted.
#[test]
fn off_by_one_branch_depth_survey() {
    let corpus = compiled_corpus();
    let mut sites = 0usize;
    let mut refuted = 0usize;
    let mut survived = 0usize;
    let mut inconclusive = 0usize;

    for (name, _, bytes) in &corpus {
        let mut nth = 0usize;
        let mut per_shape_refuted = 0usize;
        while let Some(mutant) = cfg::mutate_bump_nth_branch_depth(bytes, nth) {
            nth += 1;
            sites += 1;
            let verdict = cfg::check_module_structure(&mutant);
            if verdict.is_refuted() {
                refuted += 1;
                per_shape_refuted += 1;
            } else if verdict.holds() {
                survived += 1;
            } else {
                inconclusive += 1;
            }
        }
        eprintln!(
            "  {name:<34} {nth:>2} branch depth site(s), {per_shape_refuted:>2} off-by-one \
             mutant(s) refuted"
        );
    }

    eprintln!(
        "off-by-one depth survey: {sites} branch sites mutated one at a time — {refuted} REFUTED \
         (the depth left the label stack), {survived} survived on another live label (the \
         wrong-successor class the bisimulation deferral owes), {inconclusive} undecodable"
    );
    assert!(
        sites >= 20,
        "the survey needs real branch sites, got {sites}"
    );
    assert!(
        refuted > 0,
        "no off-by-one depth mutation was refuted — B1 would be catching only absurd depths"
    );
    assert_eq!(inconclusive, 0, "a depth bump must never break the decoder");
}

/// The stack-discipline mutation (`local.set` lowered as `local.get`, turning a
/// pop into a push) is refuted WHERE THE SPEC CAN SEE IT — and where it cannot,
/// this test says so with a number instead of leaving the impression of
/// universal coverage.
///
/// The spec's own rule is what limits it: an unconditional `br` / `br_table` /
/// `return` makes the rest of its block unreachable AND truncates the operand
/// stack to the block's entry height, so a stray operand pushed just before one
/// is legal wasm — no validator, this one or the reference implementation, can
/// refute it. The mutation is therefore refutable exactly when the extra value
/// reaches a REACHABLE join. Like the off-by-one survey, it is applied to EVERY
/// `local.set` of every corpus module, one at a time, rather than to a
/// convenient first site: which sites the optimizing passes leave in front of
/// a branch is the passes' choice, not the invariant's. Both counts are
/// reported; the survivals are the `unreachable-code coverage` deferral
/// showing up on real bytes.
#[test]
fn stack_discipline_mutation_is_refuted_where_the_spec_can_see_it() {
    let corpus = compiled_corpus();
    let mut applied = 0usize;
    let mut refuted = 0usize;
    let mut absorbed = 0usize;
    let mut modules_refuted = Vec::new();
    let mut modules_absorbed = Vec::new();

    for (name, _, bytes) in &corpus {
        let mut nth = 0usize;
        let mut any_refuted = false;
        while let Some(mutant) = cfg::mutate_nth_local_set_to_get(bytes, nth) {
            nth += 1;
            applied += 1;
            let verdict = cfg::check_module_structure(&mutant);
            if verdict.is_refuted() {
                refuted += 1;
                any_refuted = true;
            } else {
                assert!(
                    verdict.holds(),
                    "`{name}` site {}: the stack-discipline mutant must either be refuted or \
                     remain a legal module, got {verdict}",
                    nth - 1
                );
                absorbed += 1;
            }
        }
        if nth == 0 {
            continue;
        }
        if any_refuted {
            modules_refuted.push(*name);
        } else {
            modules_absorbed.push(*name);
        }
    }

    eprintln!(
        "stack-discipline mutation (local.set -> local.get): applied at {applied} sites of {} \
         real modules, {refuted} REFUTED at a reachable join, {absorbed} absorbed by the \
         spec's post-branch stack polymorphism; modules with a refuted site {:?}, modules \
         with every site absorbed {:?} — the absorbed count is the `unreachable-code \
         coverage` deferral, measured",
        modules_refuted.len() + modules_absorbed.len(),
        modules_refuted,
        modules_absorbed
    );
    assert!(applied > 0, "the mutation applied nowhere");
    assert!(
        refuted > 0,
        "the join-height invariant refuted NO real stack-discipline mutation — it would be \
         vacuous on real output"
    );
}

/// THE MEASURED GAP. The known blind spots are NOT caught on real emitted
/// bytes either — asserted, so the family cannot quietly start claiming them.
///
/// Both mutants are real miscompiles: a branch retargeted to a different live
/// label of the same arity goes to the wrong successor, and a `block` rewritten
/// as a `loop` turns a forward exit into a backward jump. The invariant is a
/// necessary condition on structuring and sees neither. That is what the
/// `branch-target INTENT binding` deferral says, in bytes.
#[test]
fn known_blind_spots_are_not_caught_and_are_counted() {
    let corpus = compiled_corpus();
    let mut applied = 0usize;
    let mut survived = 0usize;
    let mut caught_incidentally = 0usize;

    for (mname, mutate) in blind_spot_mutators() {
        let mut hits = 0usize;
        let mut lived = 0usize;
        for (_, _, bytes) in &corpus {
            let Some(mutant) = mutate(bytes) else {
                continue;
            };
            hits += 1;
            applied += 1;
            let verdict = cfg::check_module_structure(&mutant);
            if verdict.holds() {
                survived += 1;
                lived += 1;
            } else {
                // Sometimes a retarget happens to break arity or height too;
                // that is a bonus, not a claim. Counted separately.
                caught_incidentally += 1;
            }
        }
        assert!(hits > 0, "blind-spot mutator `{mname}` applied nowhere");
        assert!(
            lived > 0,
            "blind-spot mutator `{mname}` was caught EVERYWHERE — if that is real, the deferral's \
             wording must be revised rather than left overstated"
        );
        eprintln!("  blind spot {mname:<44} applied {hits:>2}, survived {lived:>2}");
    }

    eprintln!(
        "measured gap: {applied} wrong-successor / wrong-label-kind mutations applied to real \
         emitted modules, {survived} SURVIVED the structural invariant unrefuted, \
         {caught_incidentally} were caught incidentally (arity or height also broke). The \
         surviving ones are exactly what the bisimulation deferral owes"
    );
    assert!(survived > 0);
}

// ===========================================================================
// 3. Inventory pins
// ===========================================================================

/// The synthetic battery inside the module agrees with itself, and the
/// bisimulation stays a NAMED RED deferral. This is the row that would have to
/// be deleted for the family to over-claim, so it is pinned in the gate.
#[test]
fn family_inventory_is_pinned_and_the_bisimulation_stays_red() {
    let summary = cfg::cfg_family_summary();
    eprintln!(
        "family: {} checked invariants, {} named deferrals (all RED), {} must-refute mutants, \
         {} known blind spots, {} behaving as declared",
        summary.invariants,
        summary.deferrals,
        summary.mutants_must_refute,
        summary.mutants_blind_spots,
        summary.mutants_as_expected
    );
    assert_eq!(summary.invariants, cfg::WASM_CFG_INVARIANTS.len());
    assert_eq!(summary.deferrals, cfg::WASM_CFG_DEFERRALS.len());
    assert_eq!(
        summary.mutants_as_expected,
        summary.mutants_must_refute + summary.mutants_blind_spots
    );
    assert!(
        cfg::WASM_CFG_DEFERRALS
            .iter()
            .any(|d| d.name.contains("BISIMULATION")),
        "the relooper bisimulation must remain a named RED deferral of this family"
    );
    for d in cfg::WASM_CFG_DEFERRALS {
        eprintln!("  RED deferral: {} -> {}", d.name, d.family);
    }
}

/// A module the backend did NOT produce — one carrying an opcode outside the
/// modeled surface — must come back INCONCLUSIVE, never `holds`. Fail-closed is
/// the property that makes the green rows above mean anything.
#[test]
fn an_unmodeled_opcode_declines_rather_than_passing() {
    let (_, _, bytes) = compiled_corpus()
        .into_iter()
        .find(|(n, _, _)| *n == "if_else_diamond")
        .expect("shape present");
    // Overwrite the first `local.get` opcode with 0xd0 (`ref.null`), which this
    // checker has no typing rule for.
    let bodies = cfg::decode_function_bodies(&bytes).expect("decodes");
    let (base, insts) = bodies.into_iter().next().expect("one function");
    let target = insts
        .iter()
        .find(|i| i.opcode == 0x20)
        .expect("a local.get is emitted");
    let mut mutant = bytes.clone();
    mutant[base + target.offset] = 0xd0;
    let verdict = cfg::check_module_structure(&mutant);
    assert!(
        verdict.is_inconclusive(),
        "an unmodeled opcode must DECLINE, got {verdict}"
    );
    assert!(!cfg::structural_invariant_holds(&mutant));
}

// ===========================================================================
// The family is COUNTED by the coverage gate, not merely present
// ===========================================================================

/// Run `f` on a large stack so `ProofDatabase::new()` does not overflow the
/// default test-thread stack (proof_database.rs #205).
fn on_large_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .name("wasm-cfg-gate".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn large-stack gate thread")
        .join()
        .expect("gate thread panicked")
}

/// PINS the family's rows in `GateArch::WasmCfgStructural`: 20 rows, of which 13
/// are in the denominator (6 covered, 7 RED) and 7 are the invariant STATEMENTS,
/// excluded because their evidence is the mutant rows in the same audit.
///
/// The 6 covered rows are the reference module the checker must ACCEPT plus the
/// 5 mutants it must REFUTE. The 7 RED rows are the 2 measured blind spots and
/// the 5 named deferrals — the relooper BISIMULATION first among them, kept RED
/// on purpose so nothing in this audit can be read as proving the relooper
/// correct.
///
/// The credit unit is deliberately the MUTANT rather than the invariant: the
/// family's no-argument battery does not exercise every statement (its
/// hand-encoded reference module has no `br_table`, so B3 has no mutant here),
/// and crediting all seven off one battery would hand a statement its
/// neighbours' teeth.
#[test]
fn the_family_is_counted_in_the_coverage_gate() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::WasmCfgStructural));
    eprintln!("{}", report.audit_log());

    assert_eq!(
        report.total(),
        20,
        "wasm-cfg gate row count changed — 1 reference module + 7 mutants + 5 deferrals + 7 \
         invariant statements.\n{}",
        report.audit_log()
    );
    assert_eq!(
        report.emittable_count(),
        13,
        "the wasm-cfg denominator is the reference module + the 7 mutants + the 5 deferrals"
    );
    assert_eq!(
        report.allowlisted_count(),
        cfg::WASM_CFG_INVARIANTS.len(),
        "the excluded rows are exactly the invariant STATEMENTS, whose teeth are counted as the \
         mutant rows"
    );
    assert_eq!(
        report.covered_count(),
        6,
        "wasm-cfg covered count changed — 1 accepted reference module + 5 refuted mutants. Do NOT \
         inflate by crediting a blind spot, a deferral, or an invariant statement.\n{}",
        report.audit_log()
    );
    assert_eq!(
        report.failures().len(),
        7,
        "exactly the 2 measured blind spots and the 5 named deferrals are RED:\n{}",
        report.failure_summary()
    );
}

/// LOCKS IN that every RED wasm-cfg row is a NAMED deferral (never a vacuous
/// mutant reported as debt), that the family's headline claim is among them, and
/// that credited and deferred rows are DISJOINT.
#[test]
fn gate_red_rows_are_named_deferrals_and_disjoint_from_credit() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::WasmCfgStructural));
    for row in report.failures() {
        assert!(
            matches!(
                row.finding,
                Some(CoverageFinding::DeferredUnfaithfulModel { .. })
            ),
            "wasm-cfg RED row {} is a VACUOUS invariant or a wiring gap, not an honest \
             deferral:\n{}",
            row.opcode_display,
            report.failure_summary()
        );
    }
    let red: std::collections::HashSet<&str> = report
        .failures()
        .iter()
        .map(|r| r.opcode_display.as_str())
        .collect();
    let credited: std::collections::HashSet<&str> = report
        .rows
        .iter()
        .filter(|r| r.class == OpcodeClass::EmittableNeedsProof && r.finding.is_none())
        .map(|r| r.opcode_display.as_str())
        .collect();
    assert!(
        red.is_disjoint(&credited),
        "a wasm-cfg row is BOTH credited and deferred: {:?}",
        red.intersection(&credited).collect::<Vec<_>>()
    );
    for d in cfg::WASM_CFG_DEFERRALS {
        assert!(
            red.contains(format!("wasm-cfg::{}", d.name).as_str()),
            "deferral `{}` is not a RED row in the gate — a deferral that does not reach the \
             inventory is invisible debt",
            d.name
        );
    }
    assert!(
        red.iter().any(|n| n.contains("BISIMULATION")),
        "the relooper bisimulation must be RED IN the gate's denominator, not merely RED in a \
         table the gate never reads"
    );
}

/// LOCKS IN that each invariant statement reaches the audit carrying its own
/// `does_not_cover` clause.
///
/// The clause is the load-bearing half of the row: an invariant printed without
/// it reads as a proof of the property it is only a necessary condition for.
#[test]
fn gate_invariant_rows_carry_their_does_not_cover_clause() {
    let report = on_large_stack(|| CoverageGate::new().audit(GateArch::WasmCfgStructural));
    for inv in cfg::WASM_CFG_INVARIANTS {
        let row = report
            .rows
            .iter()
            .find(|r| r.opcode_display == format!("wasm-cfg::{}", inv.id))
            .unwrap_or_else(|| panic!("invariant `{}` is missing from the audit", inv.id));
        assert!(
            matches!(row.class, OpcodeClass::FailClosedAllowlisted { .. }),
            "invariant `{}` must be an excluded STATEMENT row, not its own credit",
            inv.id
        );
        assert!(
            row.note.contains(inv.does_not_cover),
            "invariant `{}` reaches the audit without its DOES NOT COVER clause: {}",
            inv.id,
            row.note
        );
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
