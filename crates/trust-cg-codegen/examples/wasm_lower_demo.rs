// trust-cg-codegen/examples/wasm_lower_demo.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! End-to-end demo: build a trust-ir module, lower it to a binary `.wasm`
//! module via trust-cg, and write the bytes to the path given as the first CLI
//! argument. Exercises Slices 0/1/1b.
//!
//! Pair with a wasm runtime (e.g. node) to validate + run the emitted module:
//!
//! ```text
//! cargo run -p trust-cg-codegen --example wasm_lower_demo -- /tmp/demo.wasm
//! node -e 'const b=require("fs").readFileSync("/tmp/demo.wasm"); \
//!   WebAssembly.instantiate(b).then(({instance})=>{ \
//!     console.log(instance.exports.sum_to(5,0,1,1)); })'  // -> 15
//! ```
//!
//! Exports: straight-line `add`/`sub`/`mul` (i32), `addw` (i64), `poly`;
//! if/else `max`/`min`/`clamp`; and reducible loops `sum_to`, `factorial`,
//! `gcd` (if/else in a loop), `mul_loop` (nested loops), `do_while_sum`
//! (bottom test), `countdown_sum` (decreasing counter).

use std::io::Write;

use trust_cg_codegen::wasm;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

fn main() {
    let mut mb = ModuleBuilder::new("wasm_lower_demo");

    // Three i32 binops: add, sub, mul.
    for (name, op) in [
        ("add", BinOp::Add),
        ("sub", BinOp::Sub),
        ("mul", BinOp::Mul),
    ] {
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function(name, ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I32);
        let b = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let r = fb.binop(op, Ty::I32, a, b);
        fb.ret(vec![r]);
        fb.build();
    }

    // An i64 add, to exercise the 64-bit value type.
    {
        let ft = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
        let mut fb = mb.function("addw", ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let b = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let r = fb.add(Ty::I64, a, b);
        fb.ret(vec![r]);
        fb.build();
    }

    // A multi-op function: poly(a, b) = (a + b) * a - b (chained results + locals).
    {
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("poly", ft);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I32);
        let b = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let s = fb.add(Ty::I32, a, b);
        let p = fb.mul(Ty::I32, s, a);
        let d = fb.sub(Ty::I32, p, b);
        fb.ret(vec![d]);
        fb.build();
    }

    // Slice 1: if/else diamond. max(a, b) = if a >= b { a } else { b }.
    for (name, cmp) in [("max", ICmpOp::Sge), ("min", ICmpOp::Sle)] {
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function(name, ft);
        let entry = fb.create_block();
        let then_b = fb.create_block();
        let else_b = fb.create_block();
        let join = fb.create_block();
        let r = fb.add_block_param(join, Ty::I32);
        let a = fb.add_block_param(entry, Ty::I32);
        let b = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let cond = fb.icmp(cmp, Ty::I32, a, b);
        fb.condbr(cond, then_b, vec![], else_b, vec![]);
        fb.switch_to_block(then_b);
        fb.br(join, vec![a]);
        fb.switch_to_block(else_b);
        fb.br(join, vec![b]);
        fb.switch_to_block(join);
        fb.ret(vec![r]);
        fb.build();
    }

    // Slice 1: nested if/else. clamp(x, lo, hi) = lo if x<lo, hi if x>hi, else x.
    {
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("clamp", ft);
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

    // ---- Slice 1b: reducible loops (the relooper) --------------------------

    // sum_to(n, acc0=0, i0=1, step=1): while i<=n { acc+=i; i+=step }  -> 1+..+n
    {
        let ft = mb.add_func_type(vec![Ty::I32; 4], vec![Ty::I32]);
        let mut fb = mb.function("sum_to", ft);
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

    // factorial(n, prod0=1, i0=2, step=1): while i<=n { prod*=i; i+=step }
    {
        let ft = mb.add_func_type(vec![Ty::I32; 4], vec![Ty::I32]);
        let mut fb = mb.function("factorial", ft);
        let entry = fb.create_block();
        let header = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();
        let prod = fb.add_block_param(header, Ty::I32);
        let i = fb.add_block_param(header, Ty::I32);
        let bp = fb.add_block_param(body, Ty::I32);
        let bi = fb.add_block_param(body, Ty::I32);
        let rp = fb.add_block_param(exit, Ty::I32);
        let n = fb.add_block_param(entry, Ty::I32);
        let prod0 = fb.add_block_param(entry, Ty::I32);
        let i0 = fb.add_block_param(entry, Ty::I32);
        let step = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.br(header, vec![prod0, i0]);
        fb.switch_to_block(header);
        let c = fb.icmp(ICmpOp::Sle, Ty::I32, i, n);
        fb.condbr(c, body, vec![prod, i], exit, vec![prod]);
        fb.switch_to_block(body);
        let np = fb.mul(Ty::I32, bp, bi);
        let ni = fb.add(Ty::I32, bi, step);
        fb.br(header, vec![np, ni]);
        fb.switch_to_block(exit);
        fb.ret(vec![rp]);
        fb.build();
    }

    // gcd(a, b): while a!=b { if a>b {a-=b} else {b-=a} }  — if/else INSIDE a loop,
    // both arms back-edge to the header. The hard branch-depth case.
    {
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("gcd", ft);
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
        let nb = fb.sub(Ty::I32, yb, ya); // else arm: a < b, so b -= a
        fb.br(header, vec![ya, nb]);
        fb.switch_to_block(exit);
        fb.ret(vec![ra]);
        fb.build();
    }

    // mul(a, b, acc0=0, oi0=0, ii0=0, step=1): nested loops, a*b via repeated add.
    {
        let ft = mb.add_func_type(vec![Ty::I32; 6], vec![Ty::I32]);
        let mut fb = mb.function("mul_loop", ft);
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
        fb.build();
    }

    // do_while_sum(n, acc0=0, i0=1, step=1): test at the BOTTOM (body runs once).
    {
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
        fb.condbr(c, body, vec![nacc, ni], exit, vec![nacc]); // self back-edge
        fb.switch_to_block(exit);
        fb.ret(vec![racc]);
        fb.build();
    }

    // countdown_sum(n, acc0=0, step=1, zero=0): i=n; while i>0 { acc+=i; i-=step }.
    {
        let ft = mb.add_func_type(vec![Ty::I32; 4], vec![Ty::I32]);
        let mut fb = mb.function("countdown_sum", ft);
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
        let step = fb.add_block_param(entry, Ty::I32);
        let zero = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        fb.br(header, vec![acc0, n]);
        fb.switch_to_block(header);
        let c = fb.icmp(ICmpOp::Sgt, Ty::I32, i, zero);
        fb.condbr(c, body, vec![acc, i], exit, vec![acc]);
        fb.switch_to_block(body);
        let nacc = fb.add(Ty::I32, bacc, bi);
        let ni = fb.sub(Ty::I32, bi, step);
        fb.br(header, vec![nacc, ni]);
        fb.switch_to_block(exit);
        fb.ret(vec![racc]);
        fb.build();
    }

    // Slice 1c: Switch. pick(v, a, b, c) = switch v { 0=>a, 1=>b, _=>c }.
    {
        use trust_ir::{Constant, SwitchCase};
        let ft = mb.add_func_type(vec![Ty::I32; 4], vec![Ty::I32]);
        let mut fb = mb.function("pick", ft);
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

    // Slice 2a: linear memory. roundtrip(x) = { let c = alloca i32; *c = x; *c }.
    {
        let ft = mb.add_func_type(vec![Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("roundtrip", ft);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let cell = fb.alloca(Ty::I32);
        fb.store(Ty::I32, cell, x);
        let r = fb.load(Ty::I32, cell);
        fb.ret(vec![r]);
        fb.build();
    }

    // Slice 2a: alloca + load/store INSIDE a loop (frame reused each iteration).
    // mem_sum(n, i0, step, zero): c = alloca; *c = zero; while i<=n { *c += i; i+=step } ; *c
    {
        let ft = mb.add_func_type(vec![Ty::I32; 4], vec![Ty::I32]);
        let mut fb = mb.function("mem_sum", ft);
        let entry = fb.create_block();
        let header = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();
        let i = fb.add_block_param(header, Ty::I32);
        let bi = fb.add_block_param(body, Ty::I32);
        let n = fb.add_block_param(entry, Ty::I32);
        let i0 = fb.add_block_param(entry, Ty::I32);
        let step = fb.add_block_param(entry, Ty::I32);
        let zero = fb.add_block_param(entry, Ty::I32);
        fb.switch_to_block(entry);
        let cell = fb.alloca(Ty::I32);
        fb.store(Ty::I32, cell, zero);
        fb.br(header, vec![i0]);
        fb.switch_to_block(header);
        let c = fb.icmp(ICmpOp::Sle, Ty::I32, i, n);
        fb.condbr(c, body, vec![i], exit, vec![]);
        fb.switch_to_block(body);
        let acc = fb.load(Ty::I32, cell);
        let nacc = fb.add(Ty::I32, acc, bi);
        fb.store(Ty::I32, cell, nacc);
        let ni = fb.add(Ty::I32, bi, step);
        fb.br(header, vec![ni]);
        fb.switch_to_block(exit);
        let r = fb.load(Ty::I32, cell);
        fb.ret(vec![r]);
        fb.build();
    }

    // Slice 3: direct calls. add3(a,b,c) = addtwo(addtwo(a,b), c).
    {
        let ft2 = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let addtwo_id = {
            let mut fb = mb.function("addtwo", ft2);
            let e = fb.create_block();
            let a = fb.add_block_param(e, Ty::I32);
            let b = fb.add_block_param(e, Ty::I32);
            fb.switch_to_block(e);
            let r = fb.add(Ty::I32, a, b);
            fb.ret(vec![r]);
            fb.build()
        };
        let ft3 = mb.add_func_type(vec![Ty::I32, Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("add3", ft3);
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

    // Slice 2b: array alloca + GEP. array_sum3(a,b,c): buf=[i32;3];
    // buf[0]=a; buf[1]=b; buf[2]=c; return buf[0]+buf[1]+buf[2].
    {
        let elem = mb.add_type(Ty::I32);
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("array_sum3", ft);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        let c = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let buf = fb.alloca(Ty::Array(elem, 3));
        let i0 = fb.iconst(Ty::I32, 0);
        let i1 = fb.iconst(Ty::I32, 1);
        let i2 = fb.iconst(Ty::I32, 2);
        let p0 = fb.gep(Ty::I32, buf, vec![i0]);
        fb.store(Ty::I32, p0, a);
        let p1 = fb.gep(Ty::I32, buf, vec![i1]);
        fb.store(Ty::I32, p1, b);
        let p2 = fb.gep(Ty::I32, buf, vec![i2]);
        fb.store(Ty::I32, p2, c);
        let q0 = fb.gep(Ty::I32, buf, vec![i0]);
        let x0 = fb.load(Ty::I32, q0);
        let q1 = fb.gep(Ty::I32, buf, vec![i1]);
        let x1 = fb.load(Ty::I32, q1);
        let q2 = fb.gep(Ty::I32, buf, vec![i2]);
        let x2 = fb.load(Ty::I32, q2);
        let s = fb.add(Ty::I32, x0, x1);
        let s2 = fb.add(Ty::I32, s, x2);
        fb.ret(vec![s2]);
        fb.build();
    }

    // Slice 2c: struct-field GEP. pair_sum(x,y): Pair{a:i32@0,b:i32@4};
    // p=alloca Pair; p.a=x; p.b=y; return p.a + p.b.
    {
        use trust_ir::StructId;
        use trust_ir::ty::{FieldDef, StructDef};
        let sid = mb.add_struct(StructDef {
            id: StructId::new(0),
            name: "Pair".to_string(),
            fields: vec![
                FieldDef {
                    name: "a".to_string(),
                    ty: Ty::I32,
                    offset: Some(0),
                },
                FieldDef {
                    name: "b".to_string(),
                    ty: Ty::I32,
                    offset: Some(4),
                },
            ],
            size: Some(8),
            align: Some(4),
            repr: Default::default(),
        });
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function("pair_sum", ft);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I32);
        let y = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let buf = fb.alloca(Ty::Struct(sid));
        let zero = fb.iconst(Ty::I32, 0);
        let f0 = fb.iconst(Ty::I32, 0);
        let f1 = fb.iconst(Ty::I32, 1);
        let pa = fb.gep(Ty::Struct(sid), buf, vec![zero, f0]);
        fb.store(Ty::I32, pa, x);
        let pb = fb.gep(Ty::Struct(sid), buf, vec![zero, f1]);
        fb.store(Ty::I32, pb, y);
        let qa = fb.gep(Ty::Struct(sid), buf, vec![zero, f0]);
        let va = fb.load(Ty::I32, qa);
        let qb = fb.gep(Ty::Struct(sid), buf, vec![zero, f1]);
        let vb = fb.load(Ty::I32, qb);
        let s = fb.add(Ty::I32, va, vb);
        fb.ret(vec![s]);
        fb.build();
    }

    // Slice 3b: indirect call. dispatch(x,y) = (*fn_ptr(imul))(x,y).
    {
        let ft2 = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let imul_id = {
            let mut fb = mb.function("imul", ft2);
            let e = fb.create_block();
            let a = fb.add_block_param(e, Ty::I32);
            let b = fb.add_block_param(e, Ty::I32);
            fb.switch_to_block(e);
            let r = fb.mul(Ty::I32, a, b);
            fb.ret(vec![r]);
            fb.build()
        };
        let mut fb = mb.function("dispatch", ft2);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I32);
        let y = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let fp = fb.fn_addr(ft2, imul_id);
        let r = fb.call_indirect(fp, ft2, vec![x, y]);
        fb.ret(vec![r]);
        fb.build();
    }

    // Slice 6: integer division/remainder. div_s/rem_s/div_u/rem_u (i32).
    for (name, op) in [
        ("idiv_s", BinOp::SDiv),
        ("irem_s", BinOp::SRem),
        ("idiv_u", BinOp::UDiv),
        ("irem_u", BinOp::URem),
    ] {
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function(name, ft);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let r = fb.binop(op, Ty::I32, a, b);
        fb.ret(vec![r]);
        fb.build();
    }

    // Slice 7: bitwise + shifts (i32). wasm masks the shift amount mod 32.
    for (name, op) in [
        ("iand", BinOp::And),
        ("ior", BinOp::Or),
        ("ixor", BinOp::Xor),
        ("ishl", BinOp::Shl),
        ("ishr_s", BinOp::AShr),
        ("ishr_u", BinOp::LShr),
    ] {
        let ft = mb.add_func_type(vec![Ty::I32, Ty::I32], vec![Ty::I32]);
        let mut fb = mb.function(name, ft);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I32);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let r = fb.binop(op, Ty::I32, a, b);
        fb.ret(vec![r]);
        fb.build();
    }

    // Slice 8: IEEE-754 float arithmetic (f64 add/sub/mul/div).
    for (name, op) in [
        ("fadd", BinOp::FAdd),
        ("fsub", BinOp::FSub),
        ("fmul", BinOp::FMul),
        ("fdiv", BinOp::FDiv),
    ] {
        let ft = mb.add_func_type(vec![Ty::F64, Ty::F64], vec![Ty::F64]);
        let mut fb = mb.function(name, ft);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::F64);
        let b = fb.add_block_param(e, Ty::F64);
        fb.switch_to_block(e);
        let r = fb.binop(op, Ty::F64, a, b);
        fb.ret(vec![r]);
        fb.build();
    }

    // Coverage: float unary ops (f64).
    for (name, op) in [
        ("fneg", trust_ir::UnOp::FNeg),
        ("fabs", trust_ir::UnOp::FAbs),
        ("fsqrt", trust_ir::UnOp::FSqrt),
        ("fceil", trust_ir::UnOp::FCeil),
        ("ffloor", trust_ir::UnOp::FFloor),
        ("ftrunc", trust_ir::UnOp::FTrunc),
    ] {
        let ft = mb.add_func_type(vec![Ty::F64], vec![Ty::F64]);
        let mut fb = mb.function(name, ft);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::F64);
        fb.switch_to_block(e);
        let r = fb.unop(op, Ty::F64, a);
        fb.ret(vec![r]);
        fb.build();
    }

    // Coverage: float comparisons (f64) — ordered + unordered, exercised with
    // NaN in the demo's JS checks.
    for (name, op) in [
        ("foeq", trust_ir::FCmpOp::OEq),
        ("folt", trust_ir::FCmpOp::OLt),
        ("fone", trust_ir::FCmpOp::ONe),
        ("fune", trust_ir::FCmpOp::UNe),
        ("fueq", trust_ir::FCmpOp::UEq),
        ("fult", trust_ir::FCmpOp::ULt),
    ] {
        let ft = mb.add_func_type(vec![Ty::F64, Ty::F64], vec![Ty::I32]);
        let mut fb = mb.function(name, ft);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::F64);
        let b = fb.add_block_param(e, Ty::F64);
        fb.switch_to_block(e);
        let r = fb.fcmp(op, Ty::F64, a, b);
        fb.ret(vec![r]);
        fb.build();
    }

    // Coverage: casts. (src_ty, dst_ty, CastOp, name)
    {
        use trust_ir::CastOp;
        let specs: &[(Ty, Ty, CastOp, &str)] = &[
            (Ty::I64, Ty::I32, CastOp::Trunc, "trunc64"),
            (Ty::I32, Ty::I64, CastOp::SExt, "sext32"),
            (Ty::I32, Ty::I64, CastOp::ZExt, "zext32"),
            (Ty::F64, Ty::I32, CastOp::FPToSI, "f2i_s"),
            (Ty::F64, Ty::I32, CastOp::FPToUI, "f2i_u"),
            (Ty::I32, Ty::F64, CastOp::SIToFP, "i2f_s"),
            (Ty::F64, Ty::F32, CastOp::FPTrunc, "fdemote"),
            (Ty::F32, Ty::F64, CastOp::FPExt, "fpromote"),
            (Ty::F32, Ty::I32, CastOp::Bitcast, "bitcast_f2i"),
        ];
        for (src, dst, op, name) in specs {
            let ft = mb.add_func_type(vec![src.clone()], vec![dst.clone()]);
            let mut fb = mb.function(*name, ft);
            let e = fb.create_block();
            let a = fb.add_block_param(e, src.clone());
            fb.switch_to_block(e);
            let r = fb.cast(*op, src.clone(), dst.clone(), a);
            fb.ret(vec![r]);
            fb.build();
        }
    }

    let module = mb.build();
    let bytes = wasm::compile_module(&module).expect("Slice 0 lowering failed");

    let path = std::env::args()
        .nth(1)
        .expect("usage: wasm_lower_demo <out.wasm>");
    let mut f = std::fs::File::create(&path).expect("create output file");
    f.write_all(&bytes).expect("write wasm bytes");
    eprintln!("wrote {} bytes to {path}", bytes.len());
}
