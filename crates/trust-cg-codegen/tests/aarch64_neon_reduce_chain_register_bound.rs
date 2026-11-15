// trust-cg-codegen - bitwise-chain body guards against a multi-def register bound
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `neon-reduce`'s forward-chain path (`BitChainRecognized`) admits a body
//! guard `i <u r` as covered by the header's constant bound `N` when the
//! register `r` holds `N`. These tests JIT-run, at O2 and O3, a chain loop
//! whose body guard compares against the register an early-exit search left,
//! and compare with a plain Rust model of the same loops.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, ICmpOp, Ty};
use trust_ir_build::ModuleBuilder;

/// Added to the early exit's result so it differs from the loop exit's.
const EARLY: u64 = 1000;
/// Scales the induction folded into the early exit's result.
const IV_SCALE: u64 = 1_000_003;

fn mask_of(elem: &Ty) -> u64 {
    match elem {
        Ty::U32 => u64::from(u32::MAX),
        Ty::U64 => u64::MAX,
        other => panic!("unsupported element type {other:?}"),
    }
}

/// `fn(p: *const T, sel: u64, _: u64, _: u64) -> u64`:
///
/// ```text
/// j = 0; loop { j += 1; if j == limit || j == sel { break } }   // r = j
/// i = 0; acc = 0
/// while i <u limit {
///     if !(i <u r) { return early(i, acc) }   // or `return acc` (shared exit)
///     acc ^= a[i]; i += 1
/// }
/// return acc
/// ```
///
/// A small constant `limit` lets O2/O3 fully unroll the search, which
/// rewrites `j` into one `Movz r, #k` per unrolled exit edge, the layout-last
/// being `#limit`, so `r` equals the header's bound only on the path that
/// stops at `limit`.
fn build_module(name: &str, elem: &Ty, limit: u64, shared_exit: bool) -> trust_ir::Module {
    let mut mb = ModuleBuilder::new(name);
    let fty = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(name, fty);
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, Ty::Ptr);
    let sel = fb.add_block_param(entry, Ty::U64);
    let _unused_a = fb.add_block_param(entry, Ty::U64);
    let _unused_b = fb.add_block_param(entry, Ty::U64);
    let search = fb.create_block();
    let j = fb.add_block_param(search, Ty::U64);
    let search_test = fb.create_block();
    let pre = fb.create_block();
    let r = fb.add_block_param(pre, Ty::U64);
    let header = fb.create_block();
    let iv = fb.add_block_param(header, Ty::U64);
    let acc = fb.add_block_param(header, elem.clone());
    let body = fb.create_block();
    let exit = fb.create_block();
    let exit_acc = fb.add_block_param(exit, elem.clone());
    let early = fb.create_block();
    let early_iv = fb.add_block_param(early, Ty::U64);
    let early_acc = fb.add_block_param(early, elem.clone());
    let latch = fb.create_block();
    let wide = |fb: &mut trust_ir_build::FunctionBuilder<'_>, v| {
        if *elem == Ty::U64 {
            v
        } else {
            fb.zext(elem.clone(), Ty::U64, v)
        }
    };

    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    fb.br(search, vec![zero]);

    fb.switch_to_block(search);
    let one = fb.iconst(Ty::U64, 1);
    let next = fb.add(Ty::U64, j, one);
    fb.br(search_test, vec![]);

    fb.switch_to_block(search_test);
    let lim = fb.iconst(Ty::U64, i128::from(limit));
    let trip = fb.icmp(ICmpOp::Ne, Ty::U64, next, lim);
    let not_found = fb.icmp(ICmpOp::Ne, Ty::U64, next, sel);
    let more = fb.binop(BinOp::And, Ty::Bool, trip, not_found);
    fb.condbr(more, search, vec![next], pre, vec![next]);

    fb.switch_to_block(pre);
    let i0 = fb.iconst(Ty::U64, 0);
    let seed = fb.iconst(elem.clone(), 0);
    fb.br(header, vec![i0, seed]);

    fb.switch_to_block(header);
    let n = fb.iconst(Ty::U64, i128::from(limit));
    let go = fb.icmp(ICmpOp::Ult, Ty::U64, iv, n);
    fb.condbr(go, body, vec![], exit, vec![acc]);

    fb.switch_to_block(body);
    let in_range = fb.icmp(ICmpOp::Ult, Ty::U64, iv, r);
    if shared_exit {
        fb.condbr(in_range, latch, vec![], exit, vec![acc]);
    } else {
        fb.condbr(in_range, latch, vec![], early, vec![iv, acc]);
    }

    fb.switch_to_block(latch);
    let addr = fb.gep(elem.clone(), p, vec![iv]);
    let v = fb.load(elem.clone(), addr);
    let acc_next = fb.binop(BinOp::Xor, elem.clone(), acc, v);
    let step = fb.iconst(Ty::U64, 1);
    let iv_next = fb.add(Ty::U64, iv, step);
    fb.br(header, vec![iv_next, acc_next]);

    fb.switch_to_block(exit);
    let result = wide(&mut fb, exit_acc);
    fb.ret(vec![result]);

    fb.switch_to_block(early);
    let acc_wide = wide(&mut fb, early_acc);
    let k = fb.iconst(Ty::U64, i128::from(IV_SCALE));
    let scaled = fb.mul(Ty::U64, early_iv, k);
    let mixed = fb.binop(BinOp::Xor, Ty::U64, acc_wide, scaled);
    let bias = fb.iconst(Ty::U64, i128::from(EARLY));
    let result = fb.add(Ty::U64, mixed, bias);
    fb.ret(vec![result]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// Plain-Rust model of the same loops over `data` (elements as u64, masked
/// to the element width).
fn model(data: &[u64], mask: u64, limit: u64, shared_exit: bool, sel: u64) -> u64 {
    let mut r = 0u64;
    loop {
        r += 1;
        if r == limit || r == sel {
            break;
        }
    }
    let mut acc = 0u64;
    for i in 0..limit {
        if i >= r {
            return if shared_exit {
                acc
            } else {
                (acc ^ i.wrapping_mul(IV_SCALE)).wrapping_add(EARLY)
            };
        }
        acc ^= data[i as usize] & mask;
    }
    acc
}

/// Deterministic element data with every byte varied.
fn data_for(len: usize) -> Vec<u64> {
    let mut x = 0x0F1E_2D3C_4B5A_6978_u64;
    (0..len)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        })
        .collect()
}

/// Every `sel` in `0..=limit + 1` at O2 and O3. Returns the failures as text.
fn probe(name: &str, elem: &Ty, limit: u64, shared_exit: bool) -> Vec<String> {
    let module = build_module(name, elem, limit, shared_exit);
    let mask = mask_of(elem);
    let data64 = data_for(limit as usize + 64);
    let data32: Vec<u32> = data64.iter().map(|x| *x as u32).collect();
    let mut failures = Vec::new();
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt_level;
        let result = match Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
        {
            Ok(result) => result,
            Err(error) => {
                failures.push(format!("{name} {opt_level:?}: compile refused: {error}"));
                continue;
            }
        };
        // SAFETY: the entry's trust-ir signature is (ptr, u64, u64, u64) ->
        // u64, and `result` outlives every call through `entry`.
        let entry = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*const u8, u64, u64, u64) -> u64>(name)
        }
        .expect("entry symbol");
        for sel in 0..=limit + 1 {
            let expected = model(&data64, mask, limit, shared_exit, sel);
            let ptr: *const u8 = if *elem == Ty::U64 {
                data64.as_ptr().cast()
            } else {
                data32.as_ptr().cast()
            };
            let got = entry.as_ref()(ptr, sel, 0, 0);
            if got != expected {
                failures.push(format!(
                    "{name} {opt_level:?} sel={sel}: got {got:#x}, expected {expected:#x}"
                ));
            }
        }
    }
    failures
}

/// The body guard `i <u r` compares against the register a fully unrolled
/// search left, which holds `sel` on every early-exit path and `limit` only
/// on the path that runs the search out. Its layout-last def is
/// `Movz r, #limit`, equal to the header's bound, so a bound check that
/// resolves `r` through the last-wins def map treats the guard as implied by
/// the header and drops the early exit. The guard must instead be kept: the
/// chain loop exits at `i == sel` on every early-exit path.
#[test]
fn chain_guard_against_a_multi_def_register_bound_is_kept() {
    let mut failures = Vec::new();
    for (name, elem, limit, shared_exit) in [
        ("rbound_x64_l8", Ty::U64, 8u64, false),
        ("rbound_x64_l8_shared", Ty::U64, 8, true),
        ("rbound_x64_l16", Ty::U64, 16, false),
        ("rbound_x32_l16", Ty::U32, 16, false),
        ("rbound_x32_l16_shared", Ty::U32, 16, true),
        // A search too long to unroll fully keeps `r` a loop-carried register.
        ("rbound_x32_l64", Ty::U32, 64, false),
    ] {
        failures.extend(probe(name, &elem, limit, shared_exit));
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
