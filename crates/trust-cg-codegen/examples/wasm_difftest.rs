// trust-cg-codegen/examples/wasm_difftest.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Differential translation-validation harness for the wasm backend.
//!
//! The per-instruction SMT proofs (trust-cg-verify) validate each op's value
//! semantics, but say nothing about whether the **relooper** faithfully
//! structures the trust-ir CFG into wasm `block`/`loop`/`if`. This harness
//! closes that: for a control-flow-diverse corpus, it runs the trust-ir
//! **interpreter** (the operational semantics, also formalized in Lean) and the
//! **compiled wasm** on the same seeded-random inputs, and checks they agree
//! bit-for-bit. A divergence is a real miscompile (this is how the gcd
//! back-edge bug surfaced earlier).
//!
//! Emits `<out>.wasm` + `<out>.json` (interpreter-computed expectations); the
//! companion `wasm_difftest.mjs` runs the wasm and validates.

use std::io::Write;

use trust_cg_codegen::wasm;
use trust_ir::{
    BinOp, CastOp, Constant, FuncId, Global, ICmpOp, InterpretOptions, InterpretValue, Interpreter,
    SwitchCase, Ty, UnOp,
};
use trust_ir_build::ModuleBuilder;

/// Deterministic LCG — reproducible random inputs (no wall-clock seed).
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u32 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) as u32
    }
    /// Uniform i32 in `[lo, hi]`.
    fn range(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next() as u64 % span) as i32
    }
}

/// One corpus function: its name, id, and a generator of valid input vectors
/// (respecting per-function constraints, e.g. terminating loops, nonzero
/// divisors, no INT_MIN/-1 signed-div overflow).
struct Case {
    name: &'static str,
    fid: FuncId,
    make_args: fn(&mut Lcg) -> Vec<i32>,
}

fn build_corpus(mb: &mut ModuleBuilder) -> Vec<Case> {
    let mut cases = Vec::new();
    let i32_2 = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
    let i32_3 = mb.add_func_type(vec![Ty::I32, Ty::I32, Ty::I32], vec![Ty::I32]);
    let i32_4 = mb.add_func_type(vec![Ty::I32; 4], vec![Ty::I32]);
    let i32_6 = mb.add_func_type(vec![Ty::I32; 6], vec![Ty::I32]);

    // --- if/else diamond: max(a,b) ---
    {
        let mut fb = mb.function("max", i32_2);
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
        let fid = fb.build();
        cases.push(Case {
            name: "max",
            fid,
            make_args: |r| vec![r.range(-1000, 1000), r.range(-1000, 1000)],
        });
    }

    // --- single counting loop: sum_to(n, acc0, i0, step) ---
    {
        let mut fb = mb.function("sum_to", i32_4);
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
        let fid = fb.build();
        cases.push(Case {
            name: "sum_to",
            fid,
            make_args: |r| vec![r.range(0, 40), r.range(0, 5), r.range(1, 3), r.range(1, 3)],
        });
    }

    // --- gcd(a,b): loop with if/else inside, two back-edges ---
    {
        let mut fb = mb.function("gcd", i32_2);
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
        fb.br(header, vec![na, xb]);
        fb.switch_to_block(dec_b);
        let nb = fb.sub(Ty::I32, yb, ya);
        fb.br(header, vec![ya, nb]);
        fb.switch_to_block(exit);
        fb.ret(vec![ra]);
        let fid = fb.build();
        cases.push(Case {
            name: "gcd",
            fid,
            make_args: |r| vec![r.range(1, 600), r.range(1, 600)],
        });
    }

    // --- mul_loop(a,b,...): NESTED loops ---
    {
        let mut fb = mb.function("mul_loop", i32_6);
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
        fb.br(ih, vec![nacc, boi, nii]);
        fb.switch_to_block(odone);
        let noi = fb.add(Ty::I32, doi, step);
        fb.br(oh, vec![dacc, noi]);
        fb.switch_to_block(exit);
        fb.ret(vec![facc]);
        let fid = fb.build();
        cases.push(Case {
            name: "mul_loop",
            fid,
            make_args: |r| vec![r.range(0, 25), r.range(0, 25), 0, 0, 0, 1],
        });
    }

    // --- do_while_sum: bottom-test self-loop (body runs once even if n<1) ---
    {
        let mut fb = mb.function("do_while_sum", i32_4);
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
        let fid = fb.build();
        cases.push(Case {
            name: "do_while_sum",
            fid,
            make_args: |r| vec![r.range(-5, 40), 0, 1, r.range(1, 3)],
        });
    }

    // --- clamp(x,lo,hi): nested if/else ---
    {
        let mut fb = mb.function("clamp", i32_3);
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
        let fid = fb.build();
        cases.push(Case {
            name: "clamp",
            fid,
            make_args: |r| {
                let lo = r.range(-50, 50);
                vec![r.range(-100, 100), lo, lo + r.range(0, 50)]
            },
        });
    }

    // --- pick(v,a,b,c): switch ---
    {
        let mut fb = mb.function("pick", i32_4);
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
        let fid = fb.build();
        cases.push(Case {
            name: "pick",
            fid,
            make_args: |r| {
                vec![
                    r.range(0, 4),
                    r.range(-99, 99),
                    r.range(-99, 99),
                    r.range(-99, 99),
                ]
            },
        });
    }

    // --- idiv_s(a,b): signed division (b != 0, no INT_MIN/-1) ---
    {
        let mut fb = mb.function("idiv_s", i32_2);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let r = fb.binop(BinOp::SDiv, Ty::I32, a, b);
        fb.ret(vec![r]);
        let fid = fb.build();
        cases.push(Case {
            name: "idiv_s",
            fid,
            make_args: |r| {
                let mut b = r.range(-500, 500);
                if b == 0 {
                    b = 1;
                }
                vec![r.range(-100000, 100000), b]
            },
        });
    }

    // --- irem_s(a,b): signed remainder (b != 0) ---
    {
        let mut fb = mb.function("irem_s", i32_2);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let r = fb.binop(BinOp::SRem, Ty::I32, a, b);
        fb.ret(vec![r]);
        let fid = fb.build();
        cases.push(Case {
            name: "irem_s",
            fid,
            make_args: |r| {
                let mut b = r.range(-500, 500);
                if b == 0 {
                    b = 1;
                }
                vec![r.range(-100000, 100000), b]
            },
        });
    }

    // --- ishl(a,b): shift (wasm masks b mod 32) ---
    {
        let mut fb = mb.function("ishl", i32_2);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let r = fb.binop(BinOp::Shl, Ty::I32, a, b);
        fb.ret(vec![r]);
        let fid = fb.build();
        // Keep shift amount < 32 so the trust-ir (unmasked) and wasm (masked)
        // semantics coincide — the proof's precondition domain.
        cases.push(Case {
            name: "ishl",
            fid,
            make_args: |r| vec![r.range(-100000, 100000), r.range(0, 31)],
        });
    }

    // --- integer unary ops (i32): Neg, Not, CtPop ---
    for (name, op) in [
        ("ineg", UnOp::Neg),
        ("inot", UnOp::Not),
        ("ictpop", UnOp::CtPop),
    ] {
        let mut fb = mb.function(name, i32_2);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let _b = fb.add_block_param(e, Ty::I32); // unused 2nd param (uniform sig)
        fb.switch_to_block(e);
        let r = fb.unop(op, Ty::I32, a);
        fb.ret(vec![r]);
        let fid = fb.build();
        cases.push(Case {
            name,
            fid,
            make_args: |r| vec![r.range(-100000, 100000), 0],
        });
    }

    build_p3_corpus(mb, i32_2, &mut cases);
    cases
}

/// P3 — the value domain, as EXECUTION evidence.
///
/// wasm has no sub-32-bit value type, so every `I8`/`U8`/`I16`/`U16` value
/// rides an `i32` carrier in a canonical form (`src/wasm/lower.rs`,
/// "Invariant N"). These cases run the places that form can leak: arithmetic
/// that must wrap at the narrow width, a signed and an unsigned read of the
/// SAME bits, shifts that must not see the extension, sub-word memory whose
/// load carries the extension, `f32`/`f64` memory, `br_table` dispatch (dense,
/// holed, negative, shared-default) beside the compare-cascade it replaces, and
/// a constant table that lives in a data segment.
///
/// Every input generator stays inside the trust-ir DEFINED domain — a shift
/// amount below the operand width, a nonzero and non-overflowing divisor — so
/// a divergence is a miscompile, never a disagreement about undefined
/// behaviour.
fn build_p3_corpus(mb: &mut ModuleBuilder, i32_2: trust_ir::FuncTyId, cases: &mut Vec<Case>) {
    let i32_1 = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
    let u8_ty = mb.add_type(Ty::U8);
    let u16_ty = mb.add_type(Ty::U16);

    // --- wrapping narrow arithmetic: the high bits must never be observed ---
    for (name, narrow, ext) in [
        ("u8_wrap", Ty::U8, CastOp::ZExt),
        ("i8_wrap", Ty::I8, CastOp::SExt),
        ("u16_wrap", Ty::U16, CastOp::ZExt),
        ("i16_wrap", Ty::I16, CastOp::SExt),
    ] {
        let mut fb = mb.function(name, i32_2);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let an = fb.cast(CastOp::Trunc, Ty::I32, narrow.clone(), a);
        let bn = fb.cast(CastOp::Trunc, Ty::I32, narrow.clone(), b);
        let s = fb.binop(BinOp::Add, narrow.clone(), an, bn);
        let m = fb.binop(BinOp::Mul, narrow.clone(), s, an);
        let d = fb.binop(BinOp::Sub, narrow.clone(), m, bn);
        let x = fb.binop(BinOp::Xor, narrow.clone(), d, bn);
        let n = fb.unop(UnOp::Neg, narrow.clone(), x);
        let t = fb.unop(UnOp::Not, narrow.clone(), n);
        let out = fb.cast(ext, narrow, Ty::I32, t);
        fb.ret(vec![out]);
        let fid = fb.build();
        cases.push(Case {
            name,
            fid,
            make_args: |r| vec![r.range(-70000, 70000), r.range(-70000, 70000)],
        });
    }

    // --- the same 8 bits divided both ways, plus popcount over the value ---
    {
        let mut fb = mb.function("narrow_div_rem", i32_2);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let au = fb.cast(CastOp::Trunc, Ty::I32, Ty::U8, a);
        let as_ = fb.cast(CastOp::Trunc, Ty::I32, Ty::I8, a);
        // Divisor in 1..=63: nonzero, and positive so `I8::MIN / -1` (the one
        // overflowing signed division) is unreachable.
        let bu = fb.cast(CastOp::Trunc, Ty::I32, Ty::U8, b);
        let mask_u = fb.iconst(Ty::U8, 0x3f);
        let one_u = fb.iconst(Ty::U8, 1);
        let du = fb.binop(BinOp::And, Ty::U8, bu, mask_u);
        let du = fb.binop(BinOp::Or, Ty::U8, du, one_u);
        let bs = fb.cast(CastOp::Trunc, Ty::I32, Ty::I8, b);
        let mask_s = fb.iconst(Ty::I8, 0x3f);
        let one_s = fb.iconst(Ty::I8, 1);
        let ds = fb.binop(BinOp::And, Ty::I8, bs, mask_s);
        let ds = fb.binop(BinOp::Or, Ty::I8, ds, one_s);

        let q = fb.binop(BinOp::UDiv, Ty::U8, au, du);
        let r = fb.binop(BinOp::URem, Ty::U8, au, du);
        let sq = fb.binop(BinOp::SDiv, Ty::I8, as_, ds);
        let sr = fb.binop(BinOp::SRem, Ty::I8, as_, ds);
        let pu = fb.unop(UnOp::CtPop, Ty::U8, au);
        let ps = fb.unop(UnOp::CtPop, Ty::I8, as_);

        let zq = fb.cast(CastOp::ZExt, Ty::U8, Ty::I32, q);
        let zr = fb.cast(CastOp::ZExt, Ty::U8, Ty::I32, r);
        let ssq = fb.cast(CastOp::SExt, Ty::I8, Ty::I32, sq);
        let ssr = fb.cast(CastOp::SExt, Ty::I8, Ty::I32, sr);
        let zpu = fb.cast(CastOp::ZExt, Ty::U8, Ty::I32, pu);
        let zps = fb.cast(CastOp::SExt, Ty::I8, Ty::I32, ps);
        let s0 = fb.add(Ty::I32, zq, zr);
        let s1 = fb.add(Ty::I32, ssq, ssr);
        let s2 = fb.add(Ty::I32, zpu, zps);
        let s3 = fb.add(Ty::I32, s0, s1);
        let out = fb.add(Ty::I32, s3, s2);
        fb.ret(vec![out]);
        let fid = fb.build();
        cases.push(Case {
            name: "narrow_div_rem",
            fid,
            make_args: |r| vec![r.range(-70000, 70000), r.range(-70000, 70000)],
        });
    }

    // --- shifts: all four (signedness x direction) combinations at 8 bits ---
    {
        let mut fb = mb.function("narrow_shifts", i32_2);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let au = fb.cast(CastOp::Trunc, Ty::I32, Ty::U8, a);
        let as_ = fb.cast(CastOp::Trunc, Ty::I32, Ty::I8, a);
        // Shift amounts stay below the OPERAND width: trust-ir leaves a wider
        // amount undefined, and wasm would mask it mod 32 instead.
        let seven_u = fb.iconst(Ty::U8, 7);
        let ku = fb.cast(CastOp::Trunc, Ty::I32, Ty::U8, b);
        let ku = fb.binop(BinOp::And, Ty::U8, ku, seven_u);
        let seven_s = fb.iconst(Ty::I8, 7);
        let ks = fb.cast(CastOp::Trunc, Ty::I32, Ty::I8, b);
        let ks = fb.binop(BinOp::And, Ty::I8, ks, seven_s);

        let shl_u = fb.binop(BinOp::Shl, Ty::U8, au, ku);
        let shl_s = fb.binop(BinOp::Shl, Ty::I8, as_, ks);
        // The cross cases are the ones the carrier form can break: a LOGICAL
        // right shift of a SIGNED narrow value must not pull the sign
        // extension down, and an ARITHMETIC right shift of an UNSIGNED one
        // must sign-extend from bit 7 rather than from bit 31.
        let lshr_u = fb.binop(BinOp::LShr, Ty::U8, au, ku);
        let lshr_s = fb.binop(BinOp::LShr, Ty::I8, as_, ks);
        let ashr_u = fb.binop(BinOp::AShr, Ty::U8, au, ku);
        let ashr_s = fb.binop(BinOp::AShr, Ty::I8, as_, ks);

        let w0 = fb.cast(CastOp::ZExt, Ty::U8, Ty::I32, shl_u);
        let w1 = fb.cast(CastOp::SExt, Ty::I8, Ty::I32, shl_s);
        let w2 = fb.cast(CastOp::ZExt, Ty::U8, Ty::I32, lshr_u);
        let w3 = fb.cast(CastOp::SExt, Ty::I8, Ty::I32, lshr_s);
        let w4 = fb.cast(CastOp::ZExt, Ty::U8, Ty::I32, ashr_u);
        let w5 = fb.cast(CastOp::SExt, Ty::I8, Ty::I32, ashr_s);
        let s0 = fb.add(Ty::I32, w0, w1);
        let s1 = fb.add(Ty::I32, w2, w3);
        let s2 = fb.add(Ty::I32, w4, w5);
        let s3 = fb.add(Ty::I32, s0, s1);
        let out = fb.add(Ty::I32, s3, s2);
        fb.ret(vec![out]);
        let fid = fb.build();
        cases.push(Case {
            name: "narrow_shifts",
            fid,
            make_args: |r| vec![r.range(-70000, 70000), r.range(0, 255)],
        });
    }

    // --- comparisons: signed vs unsigned readings of the same narrow bits ---
    {
        let mut fb = mb.function("narrow_cmp", i32_2);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let au = fb.cast(CastOp::Trunc, Ty::I32, Ty::U8, a);
        let bu = fb.cast(CastOp::Trunc, Ty::I32, Ty::U8, b);
        let as_ = fb.cast(CastOp::Trunc, Ty::I32, Ty::I8, a);
        let bs = fb.cast(CastOp::Trunc, Ty::I32, Ty::I8, b);
        let a16 = fb.cast(CastOp::Trunc, Ty::I32, Ty::U16, a);
        let b16 = fb.cast(CastOp::Trunc, Ty::I32, Ty::U16, b);
        let a16s = fb.cast(CastOp::Trunc, Ty::I32, Ty::I16, a);
        let b16s = fb.cast(CastOp::Trunc, Ty::I32, Ty::I16, b);
        let preds = [
            fb.icmp(ICmpOp::Slt, Ty::I8, as_, bs),
            fb.icmp(ICmpOp::Ult, Ty::U8, au, bu),
            fb.icmp(ICmpOp::Sge, Ty::I8, as_, bs),
            fb.icmp(ICmpOp::Uge, Ty::U8, au, bu),
            fb.icmp(ICmpOp::Eq, Ty::U8, au, bu),
            fb.icmp(ICmpOp::Ne, Ty::I16, a16s, b16s),
            fb.icmp(ICmpOp::Sle, Ty::I16, a16s, b16s),
            fb.icmp(ICmpOp::Ugt, Ty::U16, a16, b16),
        ];
        let mut acc = fb.iconst(Ty::I32, 0);
        for (bit, pred) in preds.into_iter().enumerate() {
            let z = fb.cast(CastOp::ZExt, Ty::Bool, Ty::I32, pred);
            let weight = fb.iconst(Ty::I32, 1i128 << bit);
            let term = fb.mul(Ty::I32, z, weight);
            acc = fb.add(Ty::I32, acc, term);
        }
        fb.ret(vec![acc]);
        let fid = fb.build();
        cases.push(Case {
            name: "narrow_cmp",
            fid,
            make_args: |r| vec![r.range(-70000, 70000), r.range(-70000, 70000)],
        });
    }

    // --- resize chains through and across the carrier boundary ---
    {
        let mut fb = mb.function("narrow_casts", i32_1);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let u8v = fb.cast(CastOp::Trunc, Ty::I32, Ty::U8, x);
        let i8v = fb.cast(CastOp::Trunc, Ty::I32, Ty::I8, x);
        let zx = fb.cast(CastOp::ZExt, Ty::I8, Ty::I32, i8v);
        let sx = fb.cast(CastOp::SExt, Ty::U8, Ty::I32, u8v);
        let wide_s = fb.cast(CastOp::SExt, Ty::I8, Ty::I64, i8v);
        let wide_u = fb.cast(CastOp::ZExt, Ty::U8, Ty::U64, u8v);
        let back_s = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, wide_s);
        let back_u = fb.cast(CastOp::Trunc, Ty::U64, Ty::U16, wide_u);
        let b0 = fb.cast(CastOp::SExt, Ty::I16, Ty::I32, back_s);
        let b1 = fb.cast(CastOp::ZExt, Ty::U16, Ty::I32, back_u);
        let s0 = fb.add(Ty::I32, zx, sx);
        let s1 = fb.add(Ty::I32, b0, b1);
        let out = fb.add(Ty::I32, s0, s1);
        fb.ret(vec![out]);
        let fid = fb.build();
        cases.push(Case {
            name: "narrow_casts",
            fid,
            make_args: |r| vec![r.range(-2_000_000, 2_000_000)],
        });
    }

    // --- sub-word memory: the store writes 1 (or 2) bytes, and the two loads
    // of the SAME address differ by exactly the extension ---
    for (name, elem_ty, narrow_u, narrow_s, lanes, mask) in [
        ("subword8_mem", u8_ty, Ty::U8, Ty::I8, 8u64, 7i128),
        ("subword16_mem", u16_ty, Ty::U16, Ty::I16, 4, 3),
    ] {
        let mut fb = mb.function(name, i32_2);
        let e = fb.create_block();
        let i = fb.add_block_param(e, Ty::I32);
        let x = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let buf = fb.alloca(Ty::Array(elem_ty, lanes));
        let m = fb.iconst(Ty::I32, mask);
        let idx = fb.binop(BinOp::And, Ty::I32, i, m);
        let p = fb.gep(narrow_u.clone(), buf, vec![idx]);
        let v = fb.cast(CastOp::Trunc, Ty::I32, narrow_u.clone(), x);
        fb.store(narrow_u.clone(), p, v);
        let q = fb.gep(narrow_u.clone(), buf, vec![idx]);
        let ru = fb.load(narrow_u.clone(), q);
        let rs = fb.load(narrow_s.clone(), q);
        let zu = fb.cast(CastOp::ZExt, narrow_u, Ty::I32, ru);
        let zs = fb.cast(CastOp::SExt, narrow_s, Ty::I32, rs);
        let out = fb.add(Ty::I32, zu, zs);
        fb.ret(vec![out]);
        let fid = fb.build();
        cases.push(Case {
            name,
            fid,
            make_args: |r| vec![r.range(0, 31), r.range(-2_000_000, 2_000_000)],
        });
    }

    // --- f32 / f64 memory round-trips (bit-exact: load/store move bits) ---
    {
        let mut fb = mb.function("f32_mem", i32_1);
        let e = fb.create_block();
        let bits = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let cell = fb.alloca(Ty::F32);
        let f = fb.cast(CastOp::Bitcast, Ty::I32, Ty::F32, bits);
        fb.store(Ty::F32, cell, f);
        let g = fb.load(Ty::F32, cell);
        let out = fb.cast(CastOp::Bitcast, Ty::F32, Ty::I32, g);
        fb.ret(vec![out]);
        let fid = fb.build();
        cases.push(Case {
            name: "f32_mem",
            fid,
            // Ordinary finite f32 patterns: exponent kept out of the all-ones
            // (NaN/inf) range so no engine may canonicalize a payload.
            make_args: |r| vec![r.range(0, 0x7f00_0000)],
        });
    }
    {
        let mut fb = mb.function("f64_mem", i32_2);
        let e = fb.create_block();
        let hi = fb.add_block_param(e, Ty::I32);
        let lo = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let cell = fb.alloca(Ty::F64);
        let h = fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, hi);
        let thirty_two = fb.iconst(Ty::I64, 32);
        let sh = fb.binop(BinOp::Shl, Ty::I64, h, thirty_two);
        let l = fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, lo);
        let w = fb.binop(BinOp::Or, Ty::I64, sh, l);
        let d = fb.cast(CastOp::Bitcast, Ty::I64, Ty::F64, w);
        fb.store(Ty::F64, cell, d);
        let d2 = fb.load(Ty::F64, cell);
        let w2 = fb.cast(CastOp::Bitcast, Ty::F64, Ty::I64, d2);
        let lo2 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, w2);
        let hi_shift = fb.binop(BinOp::LShr, Ty::I64, w2, thirty_two);
        let hi2 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, hi_shift);
        let out = fb.binop(BinOp::Xor, Ty::I32, lo2, hi2);
        fb.ret(vec![out]);
        let fid = fb.build();
        cases.push(Case {
            name: "f64_mem",
            fid,
            make_args: |r| {
                vec![
                    r.range(0, 0x7fe0_0000),
                    r.range(-2_000_000_000, 2_000_000_000),
                ]
            },
        });
    }

    // --- switches: every density class, and both lowerings ---
    for (name, values, shared_default) in [
        // Dense and contiguous → br_table with no holes.
        ("switch_dense8", vec![0, 1, 2, 3, 4, 5, 6, 7], false),
        // Holes inside the covered range must take the DEFAULT edge.
        ("switch_holes", vec![10, 11, 13, 16], false),
        // A range that does not start at zero AND is negative.
        ("switch_negative", vec![-4, -3, -2, -1, 0, 1], false),
        // Too sparse for the density floor → compare-cascade.
        ("switch_sparse", vec![0, 500, 9000], false),
        // One case → compare-cascade.
        ("switch_single", vec![7], false),
        // The default edge REUSES a case block.
        ("switch_shared_default", vec![0, 1, 2, 3, 4], true),
    ] {
        let fid = build_switch_case(mb, i32_2, name, &values, shared_default);
        // The generator is chosen per shape below; a fn pointer cannot capture,
        // so each shape names its own.
        let make_args: fn(&mut Lcg) -> Vec<i32> = match name {
            "switch_dense8" => |r| vec![r.range(-4, 12), r.range(-999, 999)],
            "switch_holes" => |r| vec![r.range(5, 22), r.range(-999, 999)],
            "switch_negative" => |r| vec![r.range(-9, 6), r.range(-999, 999)],
            "switch_sparse" => |r| {
                // Hit the three case values often, not only the wide gaps.
                let v = match r.range(0, 3) {
                    0 => 0,
                    1 => 500,
                    2 => 9000,
                    _ => r.range(-20, 9020),
                };
                vec![v, r.range(-999, 999)]
            },
            "switch_single" => |r| vec![r.range(0, 15), r.range(-999, 999)],
            _ => |r| vec![r.range(-6, 11), r.range(-999, 999)],
        };
        cases.push(Case {
            name,
            fid,
            make_args,
        });
    }

    // --- a constant table in a DATA SEGMENT rather than in a compare tree ---
    {
        let table: Vec<u8> = (0..32u16).map(|k| (k * 7 + 3) as u8).collect();
        // The corpus module declares exactly this one global, so it is index 0.
        let global_index = 0u32;
        mb.add_global(Global {
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
            name: "DIFFTEST_TABLE".to_string(),
            ty: Ty::Array(u8_ty, table.len() as u64),
            mutable: false,
            initializer: Some(Constant::Bytes {
                data: table,
                utf8: false,
            }),
            linkage: Default::default(),
            tls: None,
            align: None,
        });
        let mut fb = mb.function("static_table", i32_1);
        let e = fb.create_block();
        let i = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let mask = fb.iconst(Ty::I32, 31);
        let idx = fb.binop(BinOp::And, Ty::I32, i, mask);
        let base = fb.global_addr(trust_ir::value::GlobalId::new(global_index));
        let p = fb.gep(Ty::U8, base, vec![idx]);
        let byte = fb.load(Ty::U8, p);
        let out = fb.cast(CastOp::ZExt, Ty::U8, Ty::I32, byte);
        fb.ret(vec![out]);
        let fid = fb.build();
        cases.push(Case {
            name: "static_table",
            fid,
            make_args: |r| vec![r.range(-1000, 1000)],
        });
    }
}

/// `switch_<name>(v, x)`: `x + 7k + 1` for the k-th case value, `x - 1`
/// otherwise. With `shared_default` the default edge reuses case 0's block
/// instead of its own — the shape where a `br_table` default label and a case
/// label name the same arm.
fn build_switch_case(
    mb: &mut ModuleBuilder,
    sig: trust_ir::FuncTyId,
    name: &'static str,
    values: &[i128],
    shared_default: bool,
) -> FuncId {
    let mut fb = mb.function(name, sig);
    let entry = fb.create_block();
    let join = fb.create_block();
    let r = fb.add_block_param(join, Ty::I32);
    let v = fb.add_block_param(entry, Ty::I32);
    let x = fb.add_block_param(entry, Ty::I32);
    let case_blocks: Vec<_> = values.iter().map(|_| fb.create_block()).collect();
    // The own-default block is CREATED ONLY WHEN IT IS THE DEFAULT EDGE. It
    // used to be created unconditionally, so the `shared_default` shape — the
    // one whose point is that the default label and a case label name the same
    // arm — also carried a block nothing branched to, and the whole corpus was
    // refused `InvalidTrustIr { stage: Received, errors: [UnreachableBlock(7)] }`
    // once trust-ir's validator reached unreachable blocks. The fixture was
    // wrong, not the validator: an unreachable block is not part of the shape
    // being measured, and `switch_shared_default`'s claim is about the EDGE.
    // The non-shared shapes allocate the same ids as before.
    let own_default = (!shared_default).then(|| fb.create_block());
    let default_block = own_default.unwrap_or(case_blocks[0]);
    fb.switch_to_block(entry);
    let switch_cases: Vec<SwitchCase> = values
        .iter()
        .zip(&case_blocks)
        .map(|(value, &target)| SwitchCase {
            value: Constant::Int(*value),
            target,
            args: vec![],
        })
        .collect();
    fb.switch(v, switch_cases, default_block, vec![]);
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
    fb.build()
}

fn main() {
    let out = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/tmp/difftest".to_string());
    const PER_FN: usize = 300;

    let mut mb = ModuleBuilder::new("difftest");
    let cases = build_corpus(&mut mb);
    let mut module = mb
        .build()
        .expect("ModuleBuilder::build: the example module");

    let interp = Interpreter::with_module(&module).with_options(InterpretOptions {
        fuel: 50_000_000,
        max_call_depth: 256,
        panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
    });

    let mut rng = Lcg(0x9E3779B97F4A7C15);
    let mut json = String::from("{\"cases\":[");
    for (ci, case) in cases.iter().enumerate() {
        if ci > 0 {
            json.push(',');
        }
        json.push_str(&format!("{{\"name\":\"{}\",\"inputs\":[", case.name));
        let mut expected = String::from("],\"expected\":[");
        for k in 0..PER_FN {
            let args = (case.make_args)(&mut rng);
            let ivals: Vec<InterpretValue> = args
                .iter()
                .map(|&v| InterpretValue::int(Ty::I32, v as i128).unwrap())
                .collect();
            let outcome = interp
                .execute_func(case.fid, ivals)
                .unwrap_or_else(|e| panic!("interp {} {:?} failed: {e}", case.name, args));
            let res = outcome.returns[0]
                .as_int()
                .expect("i32 result")
                .as_unsigned() as u32;
            if k > 0 {
                json.push(',');
                expected.push(',');
            }
            json.push('[');
            for (j, a) in args.iter().enumerate() {
                if j > 0 {
                    json.push(',');
                }
                json.push_str(&a.to_string());
            }
            json.push(']');
            expected.push_str(&res.to_string());
        }
        json.push_str(&expected);
        json.push(']');
        json.push('}');
    }
    json.push_str("]}");

    // compile_module fail-closes on target-free modules; the interpreter above
    // fail-closes the other way (reference execution wants the canonical
    // 64-bit layout), so the wasm32 pin is stamped after interpretation.
    module.target_info = Some(wasm::wasm32_target_info());
    let bytes = wasm::compile_module_with_policy_and_license(
        &module,
        &trust_cg_codegen::wasm::WasmModulePolicy::closed(),
        &permit_unlicensed(),
    )
    .expect("compile_module");
    std::fs::File::create(format!("{out}.wasm"))
        .unwrap()
        .write_all(&bytes)
        .unwrap();
    std::fs::File::create(format!("{out}.json"))
        .unwrap()
        .write_all(json.as_bytes())
        .unwrap();
    eprintln!(
        "wrote {out}.wasm ({} bytes) + {out}.json ({} fns x {PER_FN} interpreter-checked cases)",
        bytes.len(),
        cases.len()
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
