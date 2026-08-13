// trust-cg-fuzz/tests/sweep3_mem_aliasing.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Sweep3 surface: MEMORY ALIASING.
//
// This sweep stresses stack memory and pointer arithmetic where the *aliasing*
// relationship between accesses is what determines the answer:
//   * overlapping / adjacent alloca slots (do distinct allocas get distinct
//     storage? do byte-offset GEPs into one slot alias a neighbour?);
//   * store-then-load through different-typed pointers (store i64, reload the
//     low i32; store via a byte GEP, reload the i64);
//   * GEP chains with computed (runtime) indices;
//   * load-after-store across calls and across basic blocks;
//   * SROA / mem2reg stress: O1+ must agree with O0, because the higher opt
//     levels are exactly where a scalar-replacement / store-forwarding pass can
//     drop or reorder an aliasing access.
//
// ORACLE CHOICE. The trust_cg interpreter *rejects* Alloca (see the sweep task
// contract and trust_ir_gen). It is therefore unusable as an oracle for any of
// these modules. So, exactly like sweep2_i128, this sweep uses two oracles,
// NEITHER of which is the interpreter:
//   * a Rust ground truth that models the intended little-endian byte-level
//     semantics of each module directly; and
//   * cross-config JIT agreement — every opt level (O0..O3) crossed with both
//     the fast-regalloc and precise-regalloc profiles must agree.
// A DEFECT is any JIT value disagreeing with the Rust ground truth, any JIT
// configuration disagreeing with another, or any compile error / panic on a
// module that is otherwise well-formed.
//
// ANTI-FALSE-POSITIVE. Every module is deterministic and free of UB by
// construction: all alloca storage is fully initialised before it is read; all
// indices are masked into bounds; no access ever leaves the allocated slot;
// arithmetic is wrapping; this host is little-endian (asserted at runtime).
//
// The entry signature is the fixed `(i64,i64,i64,i64) -> i64`.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::value::FuncId;
use trust_ir::{BinOp, CastOp, ICmpOp, Ty};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// Compile `module` under one (opt, regalloc) config and JIT-run `fuzz_fn`.
fn jit(module: &trust_ir::Module, opt: OptLevel, fast: bool, row: [i64; 4]) -> Result<i64, String> {
    let externs: HashMap<String, *const u8> = HashMap::new();
    let mut cfg = if fast {
        CompilerConfig::jit_fast(Target::host())
    } else {
        let mut c = CompilerConfig::for_host_jit();
        c.enable_jit_fast_regalloc = false;
        c
    };
    cfg.opt_level = opt;
    let buf = Compiler::new(cfg)
        .compile_module_to_jit(module, &externs)
        .map_err(|e| format!("compile_err: {e:?}"))?
        .buffer;
    let f = unsafe { buf.get_fn_bound::<extern "C" fn(i64, i64, i64, i64) -> i64>("fuzz_fn") }
        .ok_or_else(|| "symbol_not_found".to_string())?
        .into_inner();
    let v = f(row[0], row[1], row[2], row[3]);
    drop(buf);
    Ok(v)
}

/// Run one module across all opt x regalloc JIT configs, asserting every result
/// equals `truth(row)` and that all configs agree with each other.
fn check<F>(label: &str, module: &trust_ir::Module, rows: &[[i64; 4]], truth: F)
where
    F: Fn([i64; 4]) -> i64,
{
    const {
        assert!(
            cfg!(target_endian = "little"),
            "ground truth assumes LE host"
        );
    }
    for &row in rows {
        let want = truth(row);
        let mut jit_vals: Vec<(OptLevel, bool, i64)> = Vec::new();
        for fast in [true, false] {
            for opt in OPTS {
                match jit(module, opt, fast, row) {
                    Ok(v) => jit_vals.push((opt, fast, v)),
                    Err(e) => panic!("{label}: row={row:?} opt={opt:?} fast={fast}: {e}"),
                }
            }
        }
        for (opt, fast, got) in &jit_vals {
            assert_eq!(
                *got, want,
                "{label}: TRUTH MISMATCH row={row:?} opt={opt:?} fast={fast} got={got} want={want}"
            );
        }
        if let Some((opt0, fast0, v0)) = jit_vals.first().copied() {
            for (opt, fast, got) in &jit_vals[1..] {
                assert_eq!(
                    *got, v0,
                    "{label}: JIT DIVERGENCE row={row:?} \
                     ({opt0:?},fast={fast0})={v0} vs ({opt:?},fast={fast})={got}"
                );
            }
        }
    }
}

/// Standard 4xI64 -> I64 entry shell. `body` builds the function body in the
/// already-active entry block and must call `fb.ret(..)`.
fn build_module<F>(name: &str, body: F) -> trust_ir::Module
where
    F: FnOnce(&mut FunctionBuilder, [trust_ir::ValueId; 4]),
{
    let mut mb = ModuleBuilder::new(name);
    let ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    body(&mut fb, [a, b, c, d]);
    fb.build();
    mb.build()
}

/// Like `build_module`, but pre-interns an `[elem; len]` array type and passes
/// the resulting `Ty` (an `Array`) to the body so it can `alloca` a contiguous
/// multi-element region without needing module access inside the closure.
fn build_module_arr<F>(name: &str, elem: Ty, len: u64, body: F) -> trust_ir::Module
where
    F: FnOnce(&mut FunctionBuilder, [trust_ir::ValueId; 4], Ty),
{
    let mut mb = ModuleBuilder::new(name);
    let elem_id = mb.add_type(elem);
    let arr_ty = Ty::Array(elem_id, len);
    let ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    body(&mut fb, [a, b, c, d], arr_ty);
    fb.build();
    mb.build()
}

const ROWS: &[[i64; 4]] = &[
    [0, 0, 0, 0],
    [1, 2, 3, 4],
    [-1, -2, -3, -4],
    [i64::MAX, i64::MIN, 1, -1],
    [i64::MIN, i64::MAX, -1, 1],
    [
        0x1122_3344_5566_7788,
        0x99aa_bbcc_ddee_ff00u64 as i64,
        7,
        13,
    ],
    [123456789, -987654321, 0x7fff_ffff, -0x8000_0000],
    [0xdead_beef, 0x1234_5678, 64, 65],
    [42, 99, 5, 6],
    [-7, 11, 3, 200],
    // Index-coverage rows: exercise every (c&3, d&3) selector pair 0..3 used by
    // the computed-index / pointer-select tests, plus low-byte/half patterns for
    // the narrow-width reload tests.
    [
        0xffff_ffff_0000_0000u64 as i64,
        0x0000_0000_ffff_ffffu64 as i64,
        2,
        2,
    ],
    [
        0x8000_0000_8000_0001u64 as i64,
        0x7fff_ffff_7fff_ffffu64 as i64,
        0,
        3,
    ],
    [
        0x00ff_00ff_00ff_00ffu64 as i64,
        0xff00_ff00_ff00_ff00u64 as i64,
        2,
        1,
    ],
    [
        0xabcd_ef01_2345_6789u64 as i64,
        0x0fed_cba9_8765_4321u64 as i64,
        6,
        11,
    ],
];

// ===========================================================================
// PROBE: smallest possible alloca+store+load through the JIT path.
// ===========================================================================

#[test]
fn probe_single_slot_roundtrip() {
    // store i64 a; load i64 -> a.
    let m = build_module("probe_rt", |fb, [a, _b, _c, _d]| {
        let p = fb.alloca(Ty::I64);
        fb.store(Ty::I64, p, a);
        let v = fb.load(Ty::I64, p);
        fb.ret(vec![v]);
    });
    check("probe_single_slot_roundtrip", &m, ROWS, |row| row[0]);
}

#[test]
fn probe_two_slots_distinct() {
    // Two allocas must NOT alias: store a into p, b into q, return load(p)-load(q).
    let m = build_module("probe_two", |fb, [a, b, _c, _d]| {
        let p = fb.alloca(Ty::I64);
        let q = fb.alloca(Ty::I64);
        fb.store(Ty::I64, p, a);
        fb.store(Ty::I64, q, b);
        let va = fb.load(Ty::I64, p);
        let vb = fb.load(Ty::I64, q);
        let r = fb.binop(BinOp::Sub, Ty::I64, va, vb);
        fb.ret(vec![r]);
    });
    check("probe_two_slots_distinct", &m, ROWS, |row| {
        row[0].wrapping_sub(row[1])
    });
}

#[test]
fn probe_overwrite_order() {
    // store a; store b to same slot; load must see b.
    let m = build_module("probe_ow", |fb, [a, b, _c, _d]| {
        let p = fb.alloca(Ty::I64);
        fb.store(Ty::I64, p, a);
        fb.store(Ty::I64, p, b);
        let v = fb.load(Ty::I64, p);
        fb.ret(vec![v]);
    });
    check("probe_overwrite_order", &m, ROWS, |row| row[1]);
}

// Helpers for byte/element pointer arithmetic.

/// `gep_i8(base, n)` = base + n bytes, modelled with pointee i8 (stride 1).
fn gep_i8(fb: &mut FunctionBuilder, base: trust_ir::ValueId, n: i64) -> trust_ir::ValueId {
    let idx = fb.iconst(Ty::I64, n as i128);
    fb.gep(Ty::I8, base, vec![idx])
}

/// `gep_elem(ty, base, idx_val)` = base + idx_val * sizeof(ty), runtime index.
fn gep_elem(
    fb: &mut FunctionBuilder,
    ty: Ty,
    base: trust_ir::ValueId,
    idx_val: trust_ir::ValueId,
) -> trust_ir::ValueId {
    fb.gep(ty, base, vec![idx_val])
}

/// Truncate an i64 to `narrow`, then zero-extend back to i64. Used to model the
/// low-`width` bits of a stored value when it is reloaded through a narrower
/// pointer type.
fn lo_bits(v: i64, narrow: Ty) -> i64 {
    match narrow {
        Ty::I8 | Ty::U8 => (v as u8) as i64,
        Ty::I16 | Ty::U16 => (v as u16) as i64,
        Ty::I32 | Ty::U32 => (v as u32) as i64,
        _ => v,
    }
}

// ===========================================================================
// OVERLAPPING / ADJACENT SLOTS.
//
// Allocate an array of 4 x i64 in one slot and access it through byte GEPs and
// element GEPs. A miscompile that computes a wrong stride, or that lets a
// store-forwarding pass forward a stale value across an aliasing store, shows
// up here.
// ===========================================================================

/// Alloca [i64; 4]; store a,b,c,d into elements 0..3 via element GEPs; reload
/// elements in a *different* order and xor-fold. Verifies adjacent element slots
/// are distinct and that GEP element stride is sizeof(i64)=8.
#[test]
fn array4_elem_gep_roundtrip() {
    let m = build_module_arr("arr4_elem", Ty::I64, 4, |fb, [a, b, c, d], arr_ty| {
        let base = fb.alloca(arr_ty);
        for (i, &v) in [a, b, c, d].iter().enumerate() {
            let idx = fb.iconst(Ty::I64, i as i128);
            let p = gep_elem(fb, Ty::I64, base, idx);
            fb.store(Ty::I64, p, v);
        }
        let mut acc = fb.iconst(Ty::I64, 0);
        for &i in &[3i64, 1, 2, 0] {
            let idx = fb.iconst(Ty::I64, i as i128);
            let p = gep_elem(fb, Ty::I64, base, idx);
            let v = fb.load(Ty::I64, p);
            acc = fb.binop(BinOp::Xor, Ty::I64, acc, v);
        }
        fb.ret(vec![acc]);
    });
    check("array4_elem_gep_roundtrip", &m, ROWS, |row| {
        row[0] ^ row[1] ^ row[2] ^ row[3]
    });
}

/// Computed-index GEP into [i64; 4]. Write arg i into slot (i ^ mask) where mask
/// is derived from a runtime arg (masked to 0..3); then read slot (row index
/// permuted the same way) so the answer depends on a *runtime* GEP index, not a
/// constant one. This is the canonical "gep chains with computed indices" case.
#[test]
fn array4_computed_index() {
    let m = build_module_arr("arr4_computed", Ty::I64, 4, |fb, [a, b, c, d], arr_ty| {
        let base = fb.alloca(arr_ty);
        // mask = c & 3 (runtime). Write each arg into element (i ^ mask).
        let three = fb.iconst(Ty::I64, 3);
        let mask = fb.binop(BinOp::And, Ty::I64, c, three);
        for (i, &v) in [a, b, c, d].iter().enumerate() {
            let ic = fb.iconst(Ty::I64, i as i128);
            let dst = fb.binop(BinOp::Xor, Ty::I64, ic, mask);
            let p = gep_elem(fb, Ty::I64, base, dst);
            fb.store(Ty::I64, p, v);
        }
        // Read element (d & 3).
        let ridx = fb.binop(BinOp::And, Ty::I64, d, three);
        let p = gep_elem(fb, Ty::I64, base, ridx);
        let v = fb.load(Ty::I64, p);
        fb.ret(vec![v]);
    });
    check("array4_computed_index", &m, ROWS, |row| {
        let mask = (row[2] & 3) as usize;
        let mut slot = [0i64; 4];
        for (i, &v) in row.iter().enumerate() {
            slot[i ^ mask] = v;
        }
        slot[(row[3] & 3) as usize]
    });
}

/// Byte-level aliasing: alloca [i64; 2]; store the i64 `a` to element 0, then
/// overwrite byte 0 (lowest) of that element via an i8 store of `b`, then reload
/// the full i64. The reloaded value must have its low byte replaced. Exercises
/// store-then-load through different-typed pointers into the SAME bytes.
#[test]
fn byte_store_into_i64_low() {
    let m = build_module_arr("byte_lo", Ty::I64, 2, |fb, [a, b, _c, _d], arr_ty| {
        let base = fb.alloca(arr_ty);
        // base points at element 0.
        fb.store(Ty::I64, base, a);
        // overwrite byte 0 with low 8 bits of b.
        let b8 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, b);
        let bp = gep_i8(fb, base, 0);
        fb.store(Ty::I8, bp, b8);
        let v = fb.load(Ty::I64, base);
        fb.ret(vec![v]);
    });
    check("byte_store_into_i64_low", &m, ROWS, |row| {
        let a = row[0] as u64;
        let lo = (row[1] as u64) & 0xff;
        ((a & !0xffu64) | lo) as i64
    });
}

/// store i64, reload low i32 through a narrower pointer (different-typed load).
#[test]
fn store_i64_load_low_i32() {
    let m = build_module_arr("i64_lo32", Ty::I64, 1, |fb, [a, _b, _c, _d], arr_ty| {
        let base = fb.alloca(arr_ty);
        fb.store(Ty::I64, base, a);
        let lo = fb.load(Ty::I32, base); // low 4 bytes (LE)
        let z = fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, lo);
        fb.ret(vec![z]);
    });
    check("store_i64_load_low_i32", &m, ROWS, |row| {
        lo_bits(row[0], Ty::U32)
    });
}

/// store i64, reload the HIGH i32 via a +4 byte GEP (different-typed, offset).
#[test]
fn store_i64_load_high_i32() {
    let m = build_module_arr("i64_hi32", Ty::I64, 1, |fb, [a, _b, _c, _d], arr_ty| {
        let base = fb.alloca(arr_ty);
        fb.store(Ty::I64, base, a);
        let hp = gep_i8(fb, base, 4); // byte offset 4
        let hi = fb.load(Ty::I32, hp);
        let z = fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, hi);
        fb.ret(vec![z]);
    });
    check("store_i64_load_high_i32", &m, ROWS, |row| {
        ((row[0] as u64) >> 32) as u32 as i64
    });
}

/// Two i32 stores assembling an i64: store low i32 of a, high i32 of b, reload
/// the full i64. Classic "small writes, wide read" aliasing that store-to-load
/// forwarding at O1+ must get right.
#[test]
fn two_i32_stores_one_i64_load() {
    let m = build_module_arr("two32", Ty::I64, 1, |fb, [a, b, _c, _d], arr_ty| {
        let base = fb.alloca(arr_ty);
        let a32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, a);
        let b32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, b);
        fb.store(Ty::I32, base, a32); // bytes 0..4
        let hp = gep_i8(fb, base, 4);
        fb.store(Ty::I32, hp, b32); // bytes 4..8
        let v = fb.load(Ty::I64, base);
        fb.ret(vec![v]);
    });
    check("two_i32_stores_one_i64_load", &m, ROWS, |row| {
        let lo = (row[0] as u64) & 0xffff_ffff;
        let hi = (row[1] as u64) & 0xffff_ffff;
        ((hi << 32) | lo) as i64
    });
}

// ===========================================================================
// ADJACENT DISTINCT ALLOCAS.
//
// Several separate i64 allocas must each get their own storage. Write a unique
// value into each, then read them all back. The legacy non-JIT pipeline once
// mapped every Alloca to "slot 0" (see e2e_stack_alloc.rs header); if the JIT
// frame lowering ever regressed that way, two slots would alias and this fails.
// ===========================================================================

#[test]
fn four_distinct_slots() {
    let m = build_module("four_slots", |fb, [a, b, c, d]| {
        let p0 = fb.alloca(Ty::I64);
        let p1 = fb.alloca(Ty::I64);
        let p2 = fb.alloca(Ty::I64);
        let p3 = fb.alloca(Ty::I64);
        // Store in one order...
        fb.store(Ty::I64, p0, a);
        fb.store(Ty::I64, p1, b);
        fb.store(Ty::I64, p2, c);
        fb.store(Ty::I64, p3, d);
        // ...read back interleaved and combine so a slot-collision corrupts it.
        let v0 = fb.load(Ty::I64, p0);
        let v2 = fb.load(Ty::I64, p2);
        let v1 = fb.load(Ty::I64, p1);
        let v3 = fb.load(Ty::I64, p3);
        let s01 = fb.binop(BinOp::Sub, Ty::I64, v0, v1);
        let s23 = fb.binop(BinOp::Sub, Ty::I64, v2, v3);
        let r = fb.binop(BinOp::Add, Ty::I64, s01, s23);
        fb.ret(vec![r]);
    });
    check("four_distinct_slots", &m, ROWS, |row| {
        row[0]
            .wrapping_sub(row[1])
            .wrapping_add(row[2].wrapping_sub(row[3]))
    });
}

/// Write to slot p, then write a DIFFERENT value to a separate slot q, then read
/// p. If q aliases p, the read of p sees q's value. (no-alias check)
#[test]
fn no_alias_between_slots() {
    let m = build_module("no_alias", |fb, [a, b, _c, _d]| {
        let p = fb.alloca(Ty::I64);
        let q = fb.alloca(Ty::I64);
        fb.store(Ty::I64, p, a);
        fb.store(Ty::I64, q, b);
        // also overwrite q again to make q's last value distinct from a
        let bb = fb.binop(BinOp::Add, Ty::I64, b, b);
        fb.store(Ty::I64, q, bb);
        let v = fb.load(Ty::I64, p); // must still be a
        fb.ret(vec![v]);
    });
    check("no_alias_between_slots", &m, ROWS, |row| row[0]);
}

// ===========================================================================
// LOAD-AFTER-STORE ACROSS BASIC BLOCKS.
//
// The store and the load live in different blocks, with a data-dependent branch
// between them. A mem2reg / store-forwarding pass that ignores the CFG, or a
// register allocator that drops the slot across the edge, fails here.
// ===========================================================================

#[test]
fn store_then_load_across_block() {
    let m = build_module("xblock", |fb, [a, b, c, _d]| {
        let p = fb.alloca(Ty::I64);
        fb.store(Ty::I64, p, a);
        // branch on (c & 1)
        let one = fb.iconst(Ty::I64, 1);
        let lobit = fb.binop(BinOp::And, Ty::I64, c, one);
        let zero = fb.iconst(Ty::I64, 0);
        let cond = fb.icmp(ICmpOp::Ne, Ty::I64, lobit, zero);

        let then_b = fb.create_block();
        let else_b = fb.create_block();
        let join = fb.create_block();
        fb.condbr(cond, then_b, vec![], else_b, vec![]);

        // then: overwrite p with b
        fb.switch_to_block(then_b);
        fb.store(Ty::I64, p, b);
        fb.br(join, vec![]);

        // else: leave p as a
        fb.switch_to_block(else_b);
        fb.br(join, vec![]);

        // join: load p — value depends on which path stored
        fb.switch_to_block(join);
        let v = fb.load(Ty::I64, p);
        fb.ret(vec![v]);
    });
    check("store_then_load_across_block", &m, ROWS, |row| {
        if row[2] & 1 != 0 { row[1] } else { row[0] }
    });
}

/// Store in a loop body, load after the loop. The slot accumulates across
/// iterations; an aliasing/forwarding bug that hoists the load out of the loop
/// or forwards a stale store diverges.
#[test]
fn store_in_loop_load_after() {
    // for i in 0..n { *p = *p + step }  ; return *p     (n masked to 0..8)
    let m = build_module("loop_acc", |fb, [a, b, c, _d]| {
        let p = fb.alloca(Ty::I64);
        fb.store(Ty::I64, p, a); // init accumulator = a

        let header = fb.create_block();
        let body = fb.create_block();
        let exit = fb.create_block();

        // n = c & 7
        let seven = fb.iconst(Ty::I64, 7);
        let n = fb.binop(BinOp::And, Ty::I64, c, seven);
        let zero = fb.iconst(Ty::I64, 0);
        // loop counter carried as a block param
        fb.br(header, vec![zero]);

        fb.switch_to_block(header);
        let i = fb.add_block_param(header, Ty::I64);
        let cont = fb.icmp(ICmpOp::Slt, Ty::I64, i, n);
        fb.condbr(cont, body, vec![], exit, vec![]);

        fb.switch_to_block(body);
        let cur = fb.load(Ty::I64, p);
        let nxt = fb.binop(BinOp::Add, Ty::I64, cur, b); // += b
        fb.store(Ty::I64, p, nxt);
        let one = fb.iconst(Ty::I64, 1);
        let i1 = fb.binop(BinOp::Add, Ty::I64, i, one);
        fb.br(header, vec![i1]);

        fb.switch_to_block(exit);
        let v = fb.load(Ty::I64, p);
        fb.ret(vec![v]);
    });
    check("store_in_loop_load_after", &m, ROWS, |row| {
        let n = (row[2] & 7) as u64;
        let mut acc = row[0];
        for _ in 0..n {
            acc = acc.wrapping_add(row[1]);
        }
        acc
    });
}

// ===========================================================================
// LOAD-AFTER-STORE ACROSS CALLS.
//
// Store into a stack slot, call a helper (which clobbers caller-saved regs and
// has its own frame), then load the slot back. The slot's address and value
// must survive the call. We define a pure helper `fuzz_fn` is FuncId(0); the
// helper is FuncId(1).
// ===========================================================================

/// Build a module with the entry `fuzz_fn` plus a helper `h(x)->x*3+1`.
fn build_with_helper<F>(name: &str, body: F) -> trust_ir::Module
where
    F: FnOnce(&mut FunctionBuilder, [trust_ir::ValueId; 4], FuncId),
{
    let mut mb = ModuleBuilder::new(name);
    let entry_ty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let helper_ty = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);

    // Entry (FuncId 0).
    let mut fb = mb.function("fuzz_fn", entry_ty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let helper_id = FuncId::new(1);
    body(&mut fb, [a, b, c, d], helper_id);
    fb.build();

    // Helper (FuncId 1): h(x) = x*3 + 1 (wrapping).
    let mut hb = mb.function("helper_h", helper_ty);
    let he = hb.create_block();
    let x = hb.add_block_param(he, Ty::I64);
    hb.switch_to_block(he);
    let three = hb.iconst(Ty::I64, 3);
    let m3 = hb.binop(BinOp::Mul, Ty::I64, x, three);
    let one = hb.iconst(Ty::I64, 1);
    let r = hb.binop(BinOp::Add, Ty::I64, m3, one);
    hb.ret(vec![r]);
    hb.build();

    mb.build()
}

fn helper_h(x: i64) -> i64 {
    x.wrapping_mul(3).wrapping_add(1)
}

#[test]
fn store_call_load() {
    // *p = a; t = h(b); *q = c; reload *p and *q; combine with t.
    let m = build_with_helper("store_call_load", |fb, [a, b, c, _d], h| {
        let p = fb.alloca(Ty::I64);
        let q = fb.alloca(Ty::I64);
        fb.store(Ty::I64, p, a);
        fb.store(Ty::I64, q, c);
        let t = fb.call(h, vec![b]); // clobbers caller-saved regs
        let vp = fb.load(Ty::I64, p); // must still be a
        let vq = fb.load(Ty::I64, q); // must still be c
        let s = fb.binop(BinOp::Add, Ty::I64, vp, vq);
        let r = fb.binop(BinOp::Add, Ty::I64, s, t);
        fb.ret(vec![r]);
    });
    check("store_call_load", &m, ROWS, |row| {
        row[0].wrapping_add(row[2]).wrapping_add(helper_h(row[1]))
    });
}

/// Pass the address of a stack slot's *value* round-trip: store, call helper on
/// a loaded value, then store the helper result back and reload. Forces the slot
/// live across the call AND a store-after-call.
#[test]
fn store_call_modify_reload() {
    let m = build_with_helper("store_call_modify", |fb, [a, _b, _c, _d], h| {
        let p = fb.alloca(Ty::I64);
        fb.store(Ty::I64, p, a);
        let cur = fb.load(Ty::I64, p);
        let t = fb.call(h, vec![cur]);
        fb.store(Ty::I64, p, t);
        let v = fb.load(Ty::I64, p);
        fb.ret(vec![v]);
    });
    check("store_call_modify_reload", &m, ROWS, |row| helper_h(row[0]));
}

// ===========================================================================
// SROA / mem2reg STRESS (O1+ vs O0).
//
// These are shaped so a scalar-replacement-of-aggregates or store-to-load
// forwarding pass has the maximum opportunity to misbehave: many small fields
// of one alloca, partial overwrites, and a final wide read whose value depends
// on the exact byte-level aliasing. O0 (which keeps real memory traffic) is the
// independent cross-check against O1..O3 (which may scalarise).
// ===========================================================================

/// [i64; 4] used as a scratch struct: store all four args, then partially
/// overwrite element 1's low i32 with element 3's high i32, then sum all four
/// elements as i64. SROA must track the partial (i32) overwrite of an i64 field.
#[test]
fn sroa_partial_overwrite_sum() {
    let m = build_module_arr("sroa_partial", Ty::I64, 4, |fb, [a, b, c, d], arr_ty| {
        let base = fb.alloca(arr_ty);
        for (i, &v) in [a, b, c, d].iter().enumerate() {
            let idx = fb.iconst(Ty::I64, i as i128);
            let p = gep_elem(fb, Ty::I64, base, idx);
            fb.store(Ty::I64, p, v);
        }
        // Overwrite low i32 of element 1 with low i32 of d.
        let e1 = {
            let idx = fb.iconst(Ty::I64, 1);
            gep_elem(fb, Ty::I64, base, idx)
        };
        let d32 = fb.cast(CastOp::Trunc, Ty::I64, Ty::I32, d);
        fb.store(Ty::I32, e1, d32); // low 4 bytes of element 1
        // Sum all four i64 elements.
        let mut acc = fb.iconst(Ty::I64, 0);
        for i in 0..4i64 {
            let idx = fb.iconst(Ty::I64, i as i128);
            let p = gep_elem(fb, Ty::I64, base, idx);
            let v = fb.load(Ty::I64, p);
            acc = fb.binop(BinOp::Add, Ty::I64, acc, v);
        }
        fb.ret(vec![acc]);
    });
    check("sroa_partial_overwrite_sum", &m, ROWS, |row| {
        let mut e = [row[0] as u64, row[1] as u64, row[2] as u64, row[3] as u64];
        // overwrite low 32 bits of e[1] with low 32 bits of d (row[3]).
        let lo = (row[3] as u64) & 0xffff_ffff;
        e[1] = (e[1] & !0xffff_ffffu64) | lo;
        e.iter().fold(0u64, |s, &x| s.wrapping_add(x)) as i64
    });
}

/// Aggregate copy via element loads/stores between two allocas, with a runtime
/// index selecting which element of the destination is then returned. Exercises
/// SROA across two distinct aggregates plus a computed-index read.
#[test]
fn sroa_copy_between_aggregates() {
    let m = build_module_arr("sroa_copy", Ty::I64, 4, |fb, [a, b, c, d], arr_ty| {
        let src = fb.alloca(arr_ty.clone());
        let dst = fb.alloca(arr_ty);
        for (i, &v) in [a, b, c, d].iter().enumerate() {
            let idx = fb.iconst(Ty::I64, i as i128);
            let p = gep_elem(fb, Ty::I64, src, idx);
            fb.store(Ty::I64, p, v);
        }
        // copy src -> dst element-wise, reversed (dst[i] = src[3-i]).
        for i in 0..4i64 {
            let si = fb.iconst(Ty::I64, (3 - i) as i128);
            let sp = gep_elem(fb, Ty::I64, src, si);
            let val = fb.load(Ty::I64, sp);
            let di = fb.iconst(Ty::I64, i as i128);
            let dp = gep_elem(fb, Ty::I64, dst, di);
            fb.store(Ty::I64, dp, val);
        }
        // return dst[c & 3]
        let three = fb.iconst(Ty::I64, 3);
        let ridx = fb.binop(BinOp::And, Ty::I64, c, three);
        let rp = gep_elem(fb, Ty::I64, dst, ridx);
        let v = fb.load(Ty::I64, rp);
        fb.ret(vec![v]);
    });
    check("sroa_copy_between_aggregates", &m, ROWS, |row| {
        let src = [row[0], row[1], row[2], row[3]];
        let mut dst = [0i64; 4];
        for i in 0..4usize {
            dst[i] = src[3 - i];
        }
        dst[(row[2] & 3) as usize]
    });
}

/// Conditionally choose WHICH of two slots to store into, via a select on the
/// pointer, then read both. A select-of-pointers that SROA mishandles (treating
/// both targets as written) diverges from O0.
#[test]
fn select_pointer_store() {
    let m = build_module("sel_ptr", |fb, [a, b, c, _d]| {
        let p = fb.alloca(Ty::I64);
        let q = fb.alloca(Ty::I64);
        // init both to a known sentinel derived from a.
        fb.store(Ty::I64, p, a);
        fb.store(Ty::I64, q, a);
        // chosen = (c & 1) ? q : p ; store b into chosen.
        let one = fb.iconst(Ty::I64, 1);
        let lobit = fb.binop(BinOp::And, Ty::I64, c, one);
        let zero = fb.iconst(Ty::I64, 0);
        let cond = fb.icmp(ICmpOp::Ne, Ty::I64, lobit, zero);
        let chosen = fb.select(Ty::Ptr, cond, q, p);
        fb.store(Ty::I64, chosen, b);
        let vp = fb.load(Ty::I64, p);
        let vq = fb.load(Ty::I64, q);
        // combine so each slot's identity matters.
        let r = fb.binop(BinOp::Sub, Ty::I64, vp, vq);
        fb.ret(vec![r]);
    });
    check("select_pointer_store", &m, ROWS, |row| {
        let (a, b) = (row[0], row[1]);
        let (mut p, mut q) = (a, a);
        if row[2] & 1 != 0 {
            q = b;
        } else {
            p = b;
        }
        p.wrapping_sub(q)
    });
}

// ===========================================================================
// ESCALATION 1 — SUB-WORD ELEMENT STRIDES.
//
// [i16; 4] and [i8; 8] regions: GEP element stride is sizeof(elem) (2 / 1), and
// loads/stores are narrow. An incorrect stride or a narrow store that bleeds
// into a neighbouring element shows up as a corrupted reload of the neighbour.
// ===========================================================================

#[test]
fn array_i16_neighbour_integrity() {
    // store a..d truncated to i16 into elements 0..3, reload as zero-extended
    // i64 and pack into one i64: e0 | e1<<16 | e2<<32 | e3<<48.
    let m = build_module_arr("arr_i16", Ty::I16, 4, |fb, [a, b, c, d], arr_ty| {
        let base = fb.alloca(arr_ty);
        for (i, &v) in [a, b, c, d].iter().enumerate() {
            let idx = fb.iconst(Ty::I64, i as i128);
            let p = fb.gep(Ty::I16, base, vec![idx]);
            let t = fb.cast(CastOp::Trunc, Ty::I64, Ty::I16, v);
            fb.store(Ty::I16, p, t);
        }
        let mut acc = fb.iconst(Ty::I64, 0);
        for i in 0..4i64 {
            let idx = fb.iconst(Ty::I64, i as i128);
            let p = fb.gep(Ty::I16, base, vec![idx]);
            let e = fb.load(Ty::I16, p);
            let z = fb.cast(CastOp::ZExt, Ty::I16, Ty::I64, e);
            let sh = fb.iconst(Ty::I64, (i * 16) as i128);
            let shifted = fb.binop(BinOp::Shl, Ty::I64, z, sh);
            acc = fb.binop(BinOp::Or, Ty::I64, acc, shifted);
        }
        fb.ret(vec![acc]);
    });
    check("array_i16_neighbour_integrity", &m, ROWS, |row| {
        let mut out = 0u64;
        for (i, &v) in row.iter().enumerate() {
            let e = (v as u64) & 0xffff;
            out |= e << (i * 16);
        }
        out as i64
    });
}

#[test]
fn array_i8_eight_lanes() {
    // [i8; 8]: store low byte of each of (a,b,c,d,a^b,b^c,c^d,d^a), reload and
    // assemble into one i64 little-endian. Stride-1 GEP, byte-granular aliasing.
    let m = build_module_arr("arr_i8", Ty::I8, 8, |fb, [a, b, c, d], arr_ty| {
        let base = fb.alloca(arr_ty);
        let ab = fb.binop(BinOp::Xor, Ty::I64, a, b);
        let bc = fb.binop(BinOp::Xor, Ty::I64, b, c);
        let cd = fb.binop(BinOp::Xor, Ty::I64, c, d);
        let da = fb.binop(BinOp::Xor, Ty::I64, d, a);
        let lanes = [a, b, c, d, ab, bc, cd, da];
        for (i, &v) in lanes.iter().enumerate() {
            let idx = fb.iconst(Ty::I64, i as i128);
            let p = fb.gep(Ty::I8, base, vec![idx]);
            let t = fb.cast(CastOp::Trunc, Ty::I64, Ty::I8, v);
            fb.store(Ty::I8, p, t);
        }
        let v = fb.load(Ty::I64, base); // wide read of the whole 8-byte region
        fb.ret(vec![v]);
    });
    check("array_i8_eight_lanes", &m, ROWS, |row| {
        let (a, b, c, d) = (row[0], row[1], row[2], row[3]);
        let lanes = [a, b, c, d, a ^ b, b ^ c, c ^ d, d ^ a];
        let mut out = 0u64;
        for (i, &v) in lanes.iter().enumerate() {
            out |= ((v as u64) & 0xff) << (i * 8);
        }
        out as i64
    });
}

// ===========================================================================
// ESCALATION 2 — NESTED AGGREGATE / MULTI-INDEX GEP.
//
// [[i64; 2]; 2] indexed with TWO GEP indices (outer, inner), at least one
// computed at runtime. Exercises the multi-index aggregate-layout walk.
// ===========================================================================

#[test]
fn nested_array_multi_index() {
    let mut mb = ModuleBuilder::new("nested_arr");
    let i64_id = mb.add_type(Ty::I64);
    let inner_id = mb.add_type(Ty::Array(i64_id, 2)); // [i64; 2]
    let outer = Ty::Array(inner_id, 2); // [[i64; 2]; 2]
    let fty = mb.add_func_type(vec![Ty::I64; 4], vec![Ty::I64]);
    let mut fb = mb.function("fuzz_fn", fty);
    let e = fb.create_block();
    let a = fb.add_block_param(e, Ty::I64);
    let b = fb.add_block_param(e, Ty::I64);
    let c = fb.add_block_param(e, Ty::I64);
    let d = fb.add_block_param(e, Ty::I64);
    fb.switch_to_block(e);
    let base = fb.alloca(outer.clone());
    // store args into [r][col] for (r,col) in row-major: (0,0)=a (0,1)=b (1,0)=c (1,1)=d
    //
    // GEP CONVENTION (ABI-critical, see adapter translate_gep / translate_multi_
    // index_gep): the LEADING index strides by sizeof(pointee_ty), and only the
    // SUBSEQUENT indices descend the aggregate. To index *within one* `outer`
    // value (rather than treating `base` as `*[outer]`), the leading index must
    // be 0 so we stay at the slot, then `r` descends `outer` -> inner (stride
    // sizeof([i64;2])=16) and `col` descends inner -> i64 (stride 8). Net offset
    // `base + 0*32 + r*16 + col*8`, which is exactly `grid[r][col]` and stays in
    // bounds. A 2-index `[r, col]` here would stride r by 32 (whole-grid size)
    // and write out of bounds.
    let coords = [(0i64, 0i64, a), (0, 1, b), (1, 0, c), (1, 1, d)];
    for (r, col, v) in coords {
        let z = fb.iconst(Ty::I64, 0);
        let ri = fb.iconst(Ty::I64, r as i128);
        let ci = fb.iconst(Ty::I64, col as i128);
        let p = fb.gep(outer.clone(), base, vec![z, ri, ci]);
        fb.store(Ty::I64, p, v);
    }
    // read [r1][c1] where r1 = (c & 1), c1 = (d & 1)  (runtime indices)
    let one = fb.iconst(Ty::I64, 1);
    let r1 = fb.binop(BinOp::And, Ty::I64, c, one);
    let c1 = fb.binop(BinOp::And, Ty::I64, d, one);
    let zr = fb.iconst(Ty::I64, 0);
    let rp = fb.gep(outer, base, vec![zr, r1, c1]);
    let v = fb.load(Ty::I64, rp);
    fb.ret(vec![v]);
    fb.build();
    let m = mb.build();
    check("nested_array_multi_index", &m, ROWS, |row| {
        let grid = [[row[0], row[1]], [row[2], row[3]]];
        grid[(row[2] & 1) as usize][(row[3] & 1) as usize]
    });
}

// ===========================================================================
// ESCALATION 3 — OVERLAPPING WIDE/NARROW READS AT EVERY OFFSET.
//
// Store a single i64 into a region, then read an i32 at each of byte offsets
// 0..=4 (5 overlapping windows) and xor-fold the (masked) results. A store-to-
// load forwarder that only matches exact-width/offset must fall back to memory
// and still get every window right.
// ===========================================================================

#[test]
fn overlapping_i32_windows() {
    // region [i8; 12] so offsets 0..=4 for an i32 stay in bounds with margin.
    let m = build_module_arr("ovl_win", Ty::I8, 12, |fb, [a, _b, _c, _d], arr_ty| {
        let base = fb.alloca(arr_ty);
        // zero the region first (bytes 8..12 must be defined).
        let z = fb.iconst(Ty::I64, 0);
        fb.store(Ty::I64, base, z);
        let p8 = gep_i8(fb, base, 8);
        let z32 = fb.iconst(Ty::I32, 0);
        fb.store(Ty::I32, p8, z32);
        // write i64 a at offset 0.
        fb.store(Ty::I64, base, a);
        let mut acc = fb.iconst(Ty::I64, 0);
        for off in 0..=4i64 {
            let p = gep_i8(fb, base, off);
            let w = fb.load(Ty::I32, p);
            let zw = fb.cast(CastOp::ZExt, Ty::I32, Ty::I64, w);
            acc = fb.binop(BinOp::Xor, Ty::I64, acc, zw);
        }
        fb.ret(vec![acc]);
    });
    check("overlapping_i32_windows", &m, ROWS, |row| {
        // 12-byte little-endian buffer: bytes 0..8 = a (LE), bytes 8..12 = 0.
        let mut buf = [0u8; 12];
        buf[0..8].copy_from_slice(&(row[0] as u64).to_le_bytes());
        let mut acc = 0u64;
        for off in 0..=4usize {
            let w = u32::from_le_bytes([buf[off], buf[off + 1], buf[off + 2], buf[off + 3]]);
            acc ^= w as u64;
        }
        acc as i64
    });
}

// ===========================================================================
// ESCALATION 4 — SCATTER then GATHER with computed indices in a loop.
//
// Write arg-derived values to permuted slots of [i64; 4] inside one loop, then
// gather them in a different permutation inside another loop. Maximises the
// chance that an aliasing/forwarding pass reorders dependent stores/loads.
// ===========================================================================

#[test]
fn scatter_gather_loop() {
    let m = build_module_arr("scatter", Ty::I64, 4, |fb, [a, b, c, d], arr_ty| {
        let base = fb.alloca(arr_ty);
        // init all 4 slots to 0 so every slot is defined.
        let z0 = fb.iconst(Ty::I64, 0);
        for i in 0..4i64 {
            let idx = fb.iconst(Ty::I64, i as i128);
            let p = gep_elem(fb, Ty::I64, base, idx);
            fb.store(Ty::I64, p, z0);
        }
        // scatter: slot[(i*3) & 3] = vals[i]
        let vals = [a, b, c, d];
        for (i, &v) in vals.iter().enumerate() {
            let dst = fb.iconst(Ty::I64, ((i * 3) & 3) as i128);
            let p = gep_elem(fb, Ty::I64, base, dst);
            fb.store(Ty::I64, p, v);
        }
        // gather: sum slot[(i*2 + (c&1)) & 3] for i in 0..4
        let one = fb.iconst(Ty::I64, 1);
        let cbit = fb.binop(BinOp::And, Ty::I64, c, one);
        let three = fb.iconst(Ty::I64, 3);
        let mut acc = fb.iconst(Ty::I64, 0);
        for i in 0..4i64 {
            let base_i = fb.iconst(Ty::I64, (i * 2) as i128);
            let raw = fb.binop(BinOp::Add, Ty::I64, base_i, cbit);
            let idx = fb.binop(BinOp::And, Ty::I64, raw, three);
            let p = gep_elem(fb, Ty::I64, base, idx);
            let v = fb.load(Ty::I64, p);
            acc = fb.binop(BinOp::Add, Ty::I64, acc, v);
        }
        fb.ret(vec![acc]);
    });
    check("scatter_gather_loop", &m, ROWS, |row| {
        let vals = [row[0], row[1], row[2], row[3]];
        let mut slot = [0i64; 4];
        for (i, &v) in vals.iter().enumerate() {
            slot[(i * 3) & 3] = v;
        }
        let cbit = (row[2] & 1) as usize;
        let mut acc = 0i64;
        for i in 0..4usize {
            acc = acc.wrapping_add(slot[(i * 2 + cbit) & 3]);
        }
        acc
    });
}

// ===========================================================================
// ESCALATION 5 — STORE-FORWARD ACROSS AN ALIASING STORE.
//
// store X to p; store Y to q (q may == p depending on a runtime select); load p.
// If q == p the load sees Y, else X. A forwarder that assumes p and q never
// alias (because they are different SSA pointers) would wrongly forward X.
// ===========================================================================

#[test]
fn may_alias_forwarding() {
    let m = build_module_arr("may_alias", Ty::I64, 2, |fb, [a, b, c, _d], arr_ty| {
        let base = fb.alloca(arr_ty);
        let e0 = {
            let i = fb.iconst(Ty::I64, 0);
            gep_elem(fb, Ty::I64, base, i)
        };
        let e1 = {
            let i = fb.iconst(Ty::I64, 1);
            gep_elem(fb, Ty::I64, base, i)
        };
        // p is always element 0.
        fb.store(Ty::I64, e0, a);
        // q = (c & 1) ? e0 : e1  -- may alias p when bit set.
        let one = fb.iconst(Ty::I64, 1);
        let lobit = fb.binop(BinOp::And, Ty::I64, c, one);
        let zero = fb.iconst(Ty::I64, 0);
        let cond = fb.icmp(ICmpOp::Ne, Ty::I64, lobit, zero);
        let q = fb.select(Ty::Ptr, cond, e0, e1);
        fb.store(Ty::I64, q, b);
        // load element 0: == b if q aliased e0, else == a.
        let v = fb.load(Ty::I64, e0);
        fb.ret(vec![v]);
    });
    check("may_alias_forwarding", &m, ROWS, |row| {
        if row[2] & 1 != 0 { row[1] } else { row[0] }
    });
}
