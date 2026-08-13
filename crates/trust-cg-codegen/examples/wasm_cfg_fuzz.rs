// trust-cg-codegen/examples/wasm_cfg_fuzz.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Reducible-CFG **fuzzer** for the trust-cg wasm relooper, with the trust-ir
//! interpreter as a formal oracle. It generates random *structured* trust-ir
//! CFGs — nested if/else, bounded loops, switches — which are reducible by
//! construction, compiles each to wasm, and (via the companion
//! `wasm_difftest.mjs`) checks the compiled wasm agrees bit-for-bit with the
//! interpreter on random inputs. Any mismatch, or any `WasmLowerError` from
//! `compile_module`, is a relooper miscompile — the bug class this exists to
//! find (it is how the gcd back-edge bug was caught).
//!
//! Generation invariant (guarantees valid block-param SSA): `emit_region` is
//! called with `cur` already switched-to and a `live` vector of exactly `K`
//! i32 SSA values valid in `cur`; it emits a structured region and returns
//! `(exit_block, exit_live)` with `exit_live` of length `K` valid as edge args
//! out of `exit_block`. Loops carry `K+1` (live + a data-independent trip
//! counter) so termination is guaranteed regardless of the random body.
//!
//!   cargo run -p trust-cg-codegen --example wasm_cfg_fuzz -- /tmp/fuzz [N] [seed]
//!   node crates/trust-cg-codegen/examples/wasm_difftest.mjs /tmp/fuzz.wasm /tmp/fuzz.json

use std::io::Write;

use trust_cg_codegen::wasm;
use trust_ir::{
    BinOp, Constant, ICmpOp, InterpretOptions, InterpretValue, Interpreter, SwitchCase, Ty, ValueId,
};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

const K: usize = 4; // live-set width

/// Deterministic LCG (reproducible — never seeded from wall-clock).
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u32 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 33) as u32
    }
    fn range(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next() as u64 % span) as i32
    }
    fn pick(&mut self, n: u32) -> u32 {
        self.next() % n
    }
}

struct Gen<'a, 'b> {
    fb: &'a mut FunctionBuilder<'b>,
    rng: Lcg,
    budget: i32, // region-depth fuel; generation terminates at 0
}

impl<'a, 'b> Gen<'a, 'b> {
    /// A non-trapping i32 binop over two live values (+ a small constant), with
    /// the result optionally overwriting a live slot. Always returns length-K.
    fn leaf(&mut self, mut live: Vec<ValueId>) -> Vec<ValueId> {
        let rounds = self.rng.pick(3);
        for _ in 0..rounds {
            let i = self.rng.pick(K as u32) as usize;
            let j = self.rng.pick(K as u32) as usize;
            let op = match self.rng.pick(5) {
                0 => BinOp::Add,
                1 => BinOp::Sub,
                2 => BinOp::Mul,
                3 => BinOp::And,
                _ => BinOp::Xor,
            };
            let r = self.fb.binop(op, Ty::I32, live[i], live[j]);
            let dst = self.rng.pick(K as u32) as usize;
            live[dst] = r;
        }
        live
    }

    fn cond(&mut self, live: &[ValueId]) -> ValueId {
        let i = self.rng.pick(K as u32) as usize;
        let j = self.rng.pick(K as u32) as usize;
        let op = match self.rng.pick(6) {
            0 => ICmpOp::Eq,
            1 => ICmpOp::Ne,
            2 => ICmpOp::Slt,
            3 => ICmpOp::Sle,
            4 => ICmpOp::Sgt,
            _ => ICmpOp::Sge,
        };
        self.fb.icmp(op, Ty::I32, live[i], live[j])
    }

    /// Emit a structured region. Contract: `cur` is switched-to and `live` has
    /// length K valid in `cur`; returns `(exit_block, exit_live)` (length K).
    fn region(&mut self, live: Vec<ValueId>) -> Vec<ValueId> {
        self.budget -= 1;
        if self.budget <= 0 {
            return self.leaf(live);
        }
        match self.rng.pick(5) {
            0 | 1 => {
                // Leaf, then maybe another region (sequence).
                let live = self.leaf(live);
                if self.rng.pick(2) == 0 {
                    self.region(live)
                } else {
                    live
                }
            }
            2 => self.if_else(live),
            3 => self.loop_region(live),
            _ => self.switch_region(live),
        }
    }

    /// if/else with a K-param join. Both arms recurse; their length-K exit live
    /// sets become the join's edge args.
    fn if_else(&mut self, live: Vec<ValueId>) -> Vec<ValueId> {
        let then_b = self.fb.create_block();
        let else_b = self.fb.create_block();
        let join = self.fb.create_block();
        let join_params: Vec<ValueId> = (0..K)
            .map(|_| self.fb.add_block_param(join, Ty::I32))
            .collect();

        let c = self.cond(&live);
        // then/else take no params; they read `live` by dominance.
        self.fb.condbr(c, then_b, vec![], else_b, vec![]);

        self.fb.switch_to_block(then_b);
        let tl = self.region(live.clone());
        self.fb.br(join, tl);

        self.fb.switch_to_block(else_b);
        let el = self.region(live);
        self.fb.br(join, el);

        self.fb.switch_to_block(join);
        join_params
    }

    /// Bounded loop: header carries K live + a trip counter; body runs exactly
    /// N (data-independent) times, so it always terminates. Back-edge body→header
    /// is reducible (header dominates body).
    fn loop_region(&mut self, live: Vec<ValueId>) -> Vec<ValueId> {
        let header = self.fb.create_block();
        let body = self.fb.create_block();
        let exit = self.fb.create_block();

        // header params: K live + counter.
        let h_live: Vec<ValueId> = (0..K)
            .map(|_| self.fb.add_block_param(header, Ty::I32))
            .collect();
        let h_counter = self.fb.add_block_param(header, Ty::I32);
        // exit params: K live (counter dropped).
        let e_live: Vec<ValueId> = (0..K)
            .map(|_| self.fb.add_block_param(exit, Ty::I32))
            .collect();

        let n = self.rng.range(0, 6);
        // enter: br header with live ++ [0]
        let zero = self.fb.iconst(Ty::I32, 0);
        let mut enter_args = live;
        enter_args.push(zero);
        self.fb.br(header, enter_args);

        // header: if counter < N goto body(live++counter) else exit(live)
        self.fb.switch_to_block(header);
        let bound = self.fb.iconst(Ty::I32, n as i128);
        let c = self.fb.icmp(ICmpOp::Slt, Ty::I32, h_counter, bound);
        let mut body_args = h_live.clone();
        body_args.push(h_counter);
        self.fb.condbr(c, body, body_args, exit, h_live);

        // body params: K live + counter; run a sub-region on the K live, then
        // br header with (region-live ++ counter+1).
        self.fb.switch_to_block(body);
        let b_live: Vec<ValueId> = (0..K)
            .map(|_| self.fb.add_block_param(body, Ty::I32))
            .collect();
        let b_counter = self.fb.add_block_param(body, Ty::I32);
        let rl = self.region(b_live);
        let one = self.fb.iconst(Ty::I32, 1);
        let next = self.fb.add(Ty::I32, b_counter, one);
        let mut back_args = rl;
        back_args.push(next);
        self.fb.br(header, back_args); // back-edge

        self.fb.switch_to_block(exit);
        e_live
    }

    /// switch on a clamped live value (so default is also exercised), M cases.
    fn switch_region(&mut self, live: Vec<ValueId>) -> Vec<ValueId> {
        let m: usize = 3;
        let join = self.fb.create_block();
        let join_params: Vec<ValueId> = (0..K)
            .map(|_| self.fb.add_block_param(join, Ty::I32))
            .collect();

        // clamp live[0] into 0..=m via and-with-(next-pow2-1) is overkill; use a
        // small modulo-ish: and with 3 then it's 0..3, default hits 3.
        let mask = self.fb.iconst(Ty::I32, m as i128); // 3 → sel in 0..=3, default hits 3
        let sel = self.fb.binop(BinOp::And, Ty::I32, live[0], mask);

        // Case/default blocks take no params — they read `live` by dominance
        // (the switch block dominates them), so all edge args are empty.
        let case_blocks: Vec<_> = (0..m).map(|_| self.fb.create_block()).collect();
        let default_b = self.fb.create_block();
        let cases: Vec<SwitchCase> = (0..m)
            .map(|k| SwitchCase {
                value: Constant::Int(k as i128),
                target: case_blocks[k],
                args: vec![],
            })
            .collect();
        self.fb.switch(sel, cases, default_b, vec![]);

        for &cb in &case_blocks {
            self.fb.switch_to_block(cb);
            let cl = self.leaf(live.clone());
            self.fb.br(join, cl);
        }
        self.fb.switch_to_block(default_b);
        let dl = self.leaf(live.clone());
        self.fb.br(join, dl);

        self.fb.switch_to_block(join);
        join_params
    }
}

/// Build a module of `n` random reducible CFGs for `seed` (shared by `main` and
/// the regression test).
fn build_fuzz_module(seed: u64, n: usize) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("cfg_fuzz");
    let ft = mb.add_func_type(vec![Ty::I32; K], vec![Ty::I32]);
    for idx in 0..n {
        let name = format!("f{idx}");
        let mut fb = mb.function(&name, ft);
        let entry = fb.create_block();
        let live: Vec<ValueId> = (0..K).map(|_| fb.add_block_param(entry, Ty::I32)).collect();
        fb.switch_to_block(entry);
        let fseed = seed ^ (idx as u64).wrapping_mul(0x9E3779B97F4A7C15);
        let mut g = Gen {
            fb: &mut fb,
            rng: Lcg(fseed),
            budget: 6,
        };
        let exit_live = g.region(live);
        fb.ret(vec![exit_live[0]]);
        fb.build();
    }
    mb.build()
}

#[cfg(test)]
mod tests {
    use super::*;
    /// The relooper must compile every CFG the generator produces (the generator
    /// only emits reducible structured regions). A failure here is either a
    /// relooper bug or a generator bug — both worth catching. CI-runnable via
    /// `cargo test --example wasm_cfg_fuzz`.
    #[test]
    fn relooper_compiles_random_reducible_cfgs() {
        for seed in 0..64u64 {
            let module = build_fuzz_module(seed.wrapping_mul(0x100000001B3) ^ 0xABCD, 20);
            wasm::compile_module(&module)
                .unwrap_or_else(|e| panic!("seed {seed}: compile_module failed: {e}"));
        }
    }
}

fn main() {
    let out = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "/tmp/fuzz".to_string());
    let n_funcs: usize = std::env::args()
        .nth(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or(200);
    let base_seed: u64 = std::env::args()
        .nth(3)
        .and_then(|s| s.parse().ok())
        .unwrap_or(0xD1CE_5EED_1234_5678);
    const PER_FN: usize = 200;

    let module = build_fuzz_module(base_seed, n_funcs);
    let names: Vec<String> = (0..n_funcs).map(|i| format!("f{i}")).collect();

    let interp = Interpreter::with_module(&module).with_options(InterpretOptions {
        fuel: 50_000_000,
        max_call_depth: 256,
        mem_budget: 256 * 1024 * 1024,
    });

    // Inputs are derived from the same base seed, independent of generation.
    let mut rng = Lcg(base_seed ^ 0xABCD_1234);
    let mut json = String::from("{\"cases\":[");
    for (ci, (name, fid)) in names.iter().zip(0u32..).enumerate() {
        if ci > 0 {
            json.push(',');
        }
        json.push_str(&format!("{{\"name\":\"{name}\",\"inputs\":["));
        let mut exp = String::from("],\"expected\":[");
        for k in 0..PER_FN {
            let args: Vec<i32> = (0..K).map(|_| rng.range(-1000, 1000)).collect();
            let ivals: Vec<InterpretValue> = args
                .iter()
                .map(|&v| InterpretValue::int(Ty::I32, v as i128).unwrap())
                .collect();
            let outcome = interp
                .execute_func(trust_ir::FuncId::new(fid), ivals)
                .unwrap_or_else(|e| panic!("interp {name} {args:?}: {e}"));
            let res = outcome.returns[0].as_int().expect("i32").as_unsigned() as u32;
            if k > 0 {
                json.push(',');
                exp.push(',');
            }
            json.push('[');
            for (j, a) in args.iter().enumerate() {
                if j > 0 {
                    json.push(',');
                }
                json.push_str(&a.to_string());
            }
            json.push(']');
            exp.push_str(&res.to_string());
        }
        json.push_str(&exp);
        json.push(']');
        json.push('}');
    }
    json.push_str("]}");

    let bytes = wasm::compile_module(&module)
        .unwrap_or_else(|e| panic!("compile_module failed (relooper bug?): {e}"));
    std::fs::File::create(format!("{out}.wasm"))
        .unwrap()
        .write_all(&bytes)
        .unwrap();
    std::fs::File::create(format!("{out}.json"))
        .unwrap()
        .write_all(json.as_bytes())
        .unwrap();
    eprintln!(
        "wrote {out}.wasm ({} bytes) + {out}.json ({n_funcs} random reducible CFGs x {PER_FN} \
         interpreter-checked inputs, seed {base_seed:#x})",
        bytes.len()
    );
}
