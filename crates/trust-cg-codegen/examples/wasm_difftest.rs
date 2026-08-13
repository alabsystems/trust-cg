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
    BinOp, Constant, FuncId, ICmpOp, InterpretOptions, InterpretValue, Interpreter, SwitchCase, Ty,
    UnOp,
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

    cases
}

fn main() {
    let out = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/tmp/difftest".to_string());
    const PER_FN: usize = 300;

    let mut mb = ModuleBuilder::new("difftest");
    let cases = build_corpus(&mut mb);
    let module = mb.build();

    let interp = Interpreter::with_module(&module).with_options(InterpretOptions {
        fuel: 50_000_000,
        max_call_depth: 256,
        mem_budget: 256 * 1024 * 1024,
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

    let bytes = wasm::compile_module(&module).expect("compile_module");
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
