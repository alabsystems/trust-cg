// trust-cg-codegen/tests/e2e_aarch64_i128_switch.rs
//
// Native controls for the two i128 forms of ledger row L04-P10:
//
//   * `Inst::Switch` over I128/U128 selectors. The adapter splits the selector
//     into its 64-bit halves and dispatches on BOTH (`translate_i128_switch`):
//     a compare tree over the distinct high halves of the case constants, each
//     leaf a 64-bit `Switch` over that group's low halves (a jump table when
//     dense, a compare chain otherwise). Every case constant is honored as a
//     full 128-bit value, so the interesting inputs are exactly the ones a
//     half-blind lowering would mis-dispatch: constants that differ ONLY in
//     their high half, low-half collisions across different high halves,
//     negative constants (all-ones high half), and the boundaries just outside
//     a dense low-half range.
//   * `Inst::Overflow { MulOverflow }` at I128/U128 on the product and flag
//     boundaries (i128::MIN * -1, i128::MAX * 2, 2^64 * 2^64, u128::MAX * 2,
//     ...), where the guarded __divti3/__udivti3 division identity the adapter
//     emits either recovers the operand or does not.
//
// Both are diffed at O0, O1, O2 and O3 against clang's native `__int128` /
// `unsigned __int128` arithmetic and `__builtin_mul_overflow`. This is testing
// evidence on the host CPU, not a proof; the registered obligations for the
// checked-multiply idiom live in trust-cg-verify (`checked_mul_i128_proofs`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#[path = "common/admission_expect.rs"]
mod admission_expect;

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    Block as TrustIrBlock, Constant, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, OverflowOp, SwitchCase, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

#[path = "common/native_host.rs"]
mod native_host;

/// AArch64 Linux GNU (ELF) or macOS (Mach-O): `Compiler::new` derives the
/// host's object format and ABI, and the host `cc` links it.
fn can_link_and_run_aarch64_native() -> bool {
    native_host::NATIVE
}

/// The trust-ir spelling of a 128-bit case constant for `selector_ty`:
/// `Constant::Int` for everything an i128 can hold, the canonical
/// `Constant::U128` for a `U128` value above `i128::MAX`.
fn case_constant(selector_ty: &Ty, pattern: u128) -> Constant {
    match selector_ty {
        Ty::U128 if pattern > i128::MAX as u128 => Constant::U128(pattern),
        _ => Constant::Int(pattern as i128),
    }
}

// A block `bbN:` that just returns the i64 constant `k`. `vid` is a
// function-unique SSA id for the constant.
fn ret_const_block(bb: u32, vid: u32, k: i64) -> TrustIrBlock {
    TrustIrBlock {
        id: BlockId::new(bb),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(k as i128),
            })
            .with_result(ValueId::new(vid)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(vid)],
            }),
        ],
    }
}

// Build `fn name(x: sel) -> i64 { switch (x) { case c_i: return v_i; default: return dflt } }`
// over a 128-bit selector. `arms` are (case pattern, return value).
fn build_switch_fn(
    m: &mut TrustIrModule,
    id: u32,
    name: &str,
    selector_ty: Ty,
    arms: &[(u128, i64)],
    dflt: i64,
) {
    let ft = m
        .add_func_type(FuncTy {
            params: vec![selector_ty.clone()],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));

    let default_bb = arms.len() as u32 + 1;
    let cases: Vec<SwitchCase> = arms
        .iter()
        .enumerate()
        .map(|(i, (pattern, _))| SwitchCase {
            value: case_constant(&selector_ty, *pattern),
            target: BlockId::new(i as u32 + 1),
            args: vec![],
        })
        .collect();

    let mut blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), selector_ty)],
        body: vec![InstrNode::new(Inst::Switch {
            value: ValueId::new(0),
            default: BlockId::new(default_bb),
            default_args: vec![],
            cases,
            exhaustive_enum_unreachable: false,
        })],
    }];
    for (i, (_, rv)) in arms.iter().enumerate() {
        blocks.push(ret_const_block(i as u32 + 1, 100 + i as u32, *rv));
    }
    blocks.push(ret_const_block(default_bb, 100 + arms.len() as u32, dflt));

    f.blocks = blocks;
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

// Build `fn name(x: i128) -> i64` whose switch edges all carry a block
// argument into one merge block (`merge(v: i64) { return v }`), so every edge
// needs its own copy block (issue #304) under the split dispatch.
fn build_switch_args_fn(
    m: &mut TrustIrModule,
    id: u32,
    name: &str,
    arms: &[(u128, i64)],
    dflt: i64,
) {
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I128],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));

    // Entry: materialize one i64 constant per arm (plus the default), then
    // switch, passing the arm's constant as the merge block's argument.
    let mut body = Vec::new();
    for (i, (_, rv)) in arms.iter().enumerate() {
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(*rv as i128),
            })
            .with_result(ValueId::new(100 + i as u32)),
        );
    }
    let dflt_vid = 100 + arms.len() as u32;
    body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(dflt as i128),
        })
        .with_result(ValueId::new(dflt_vid)),
    );
    let cases: Vec<SwitchCase> = arms
        .iter()
        .enumerate()
        .map(|(i, (pattern, _))| SwitchCase {
            value: Constant::Int(*pattern as i128),
            target: BlockId::new(1),
            args: vec![ValueId::new(100 + i as u32)],
        })
        .collect();
    body.push(InstrNode::new(Inst::Switch {
        value: ValueId::new(0),
        default: BlockId::new(1),
        default_args: vec![ValueId::new(dflt_vid)],
        cases,
        exhaustive_enum_unreachable: false,
    }));

    f.blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I128)],
            body,
        },
        TrustIrBlock {
            id: BlockId::new(1),
            params: vec![(ValueId::new(1), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            })],
        },
    ];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

// `fn(a: ty, b: ty) -> ret` doing a checked mul over `ty` and returning result[idx].
fn build_checked_mul(m: &mut TrustIrModule, id: u32, name: &str, ty: Ty, ret: Ty, result_idx: u32) {
    let ft = m
        .add_func_type(FuncTy {
            params: vec![ty.clone(), ty.clone()],
            returns: vec![ret],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), ty.clone()), (ValueId::new(1), ty.clone())],
        body: vec![
            InstrNode::new(Inst::Overflow {
                op: OverflowOp::MulOverflow,
                ty,
                lhs: ValueId::new(0),
                rhs: ValueId::new(1),
            })
            .with_results(vec![ValueId::new(2), ValueId::new(3)]),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2 + result_idx)],
            }),
        ],
    }];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

const HI1: u128 = 1u128 << 64;
const HI70: u128 = 1u128 << 70;

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("i128_switch");
    let neg = |v: i128| v as u128;

    // Dense non-negative i128 cases 0..=7: one high-half group (hi == 0), a
    // jump table over the low halves.
    build_switch_fn(
        &mut m,
        0,
        "dense_i128",
        Ty::I128,
        &[
            (0, 100),
            (1, 101),
            (2, 102),
            (3, 103),
            (4, 104),
            (5, 105),
            (6, 106),
            (7, 107),
        ],
        -1,
    );
    // Dense across zero: -3..=3 splits into the all-ones high half (negative
    // cases, low halves 2^64-3..2^64-1) and the zero high half.
    build_switch_fn(
        &mut m,
        1,
        "dense_neg_i128",
        Ty::I128,
        &[
            (neg(-3), 1000),
            (neg(-2), 1001),
            (neg(-1), 1002),
            (0, 1003),
            (1, 1004),
            (2, 1005),
            (3, 1006),
        ],
        -99,
    );
    // Sparse i128 cases spanning several high halves, both extremes, and a
    // low-half collision between 3 (hi 0) and 2^70 + 3 (hi 64).
    build_switch_fn(
        &mut m,
        2,
        "sparse_i128",
        Ty::I128,
        &[
            (neg(-7), 40),
            (3, 10),
            (300, 20),
            (30000, 30),
            (HI70 + 3, 70),
            (neg(i128::MIN), 80),
            (i128::MAX as u128, 90),
        ],
        0,
    );
    // u128 cases that differ ONLY in their high half (low half is 5 in every
    // case) plus u128::MAX (a canonical `Constant::U128`).
    build_switch_fn(
        &mut m,
        3,
        "hi_only_u128",
        Ty::U128,
        &[
            (5, 1),
            (HI1 + 5, 2),
            (2 * HI1 + 5, 3),
            ((1u128 << 127) + 5, 4),
            ((u64::MAX as u128) * HI1 + 5, 5),
            (u128::MAX, 6),
        ],
        -1,
    );
    // Sparse u128 cases including every value that needs `Constant::U128`.
    build_switch_fn(
        &mut m,
        4,
        "sparse_u128",
        Ty::U128,
        &[
            (0, 11),
            (1, 12),
            (u64::MAX as u128, 13),
            (HI1, 14),
            (1u128 << 127, 15),
            (u128::MAX - 1, 16),
            (u128::MAX, 17),
        ],
        -1,
    );
    // Dense u128 cases 100..=107: one group, jump table on the low half.
    build_switch_fn(
        &mut m,
        5,
        "dense_u128",
        Ty::U128,
        &[
            (100, 200),
            (101, 201),
            (102, 202),
            (103, 203),
            (104, 204),
            (105, 205),
            (106, 206),
            (107, 207),
        ],
        -1,
    );
    // Block-argument edges into one merge block, with a low-half collision
    // between 1 (hi 0) and 2^64 + 1 (hi 1).
    build_switch_args_fn(
        &mut m,
        6,
        "args_i128",
        &[(1, 11), (2, 22), (HI1 + 1, 33), (neg(-1), 44)],
        0,
    );
    // Checked multiply: product and overflow flag, signed and unsigned.
    build_checked_mul(&mut m, 7, "smul_lo", Ty::I128, Ty::I128, 0);
    build_checked_mul(&mut m, 8, "smul_ovf", Ty::I128, Ty::Bool, 1);
    build_checked_mul(&mut m, 9, "umul_lo", Ty::U128, Ty::U128, 0);
    build_checked_mul(&mut m, 10, "umul_ovf", Ty::U128, Ty::Bool, 1);
    m
}

fn compile_at(module: &TrustIrModule, opt: OptLevel) -> Result<Vec<u8>, String> {
    let compiler = Compiler::new(CompilerConfig {
        opt_level: opt,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed());
    compiler
        .compile(module)
        .map(|r| r.object_code)
        .map_err(|e| format!("{e:?}"))
}

const DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
typedef unsigned __int128 u128;
typedef __int128 s128;

extern int64_t dense_i128(s128), dense_neg_i128(s128), sparse_i128(s128), args_i128(s128);
extern int64_t hi_only_u128(u128), sparse_u128(u128), dense_u128(u128);
extern s128  smul_lo(s128, s128);
extern _Bool smul_ovf(s128, s128);
extern u128  umul_lo(u128, u128);
extern _Bool umul_ovf(u128, u128);

#define HI1  ((u128)1 << 64)
#define HI70 ((u128)1 << 70)
#define B127 ((u128)1 << 127)
#define S128_MIN ((s128)B127)
#define S128_MAX ((s128)(B127 - 1))
#define U128_MAX (~(u128)0)

static int64_t dense_i128_ref(s128 x){
    if (x == 0) return 100; if (x == 1) return 101; if (x == 2) return 102; if (x == 3) return 103;
    if (x == 4) return 104; if (x == 5) return 105; if (x == 6) return 106; if (x == 7) return 107;
    return -1;
}
static int64_t dense_neg_i128_ref(s128 x){
    if (x == -3) return 1000; if (x == -2) return 1001; if (x == -1) return 1002; if (x == 0) return 1003;
    if (x == 1) return 1004; if (x == 2) return 1005; if (x == 3) return 1006;
    return -99;
}
static int64_t sparse_i128_ref(s128 x){
    if (x == -7) return 40; if (x == 3) return 10; if (x == 300) return 20; if (x == 30000) return 30;
    if (x == (s128)(HI70 + 3)) return 70; if (x == S128_MIN) return 80; if (x == S128_MAX) return 90;
    return 0;
}
static int64_t hi_only_u128_ref(u128 x){
    if (x == 5) return 1; if (x == HI1 + 5) return 2; if (x == 2 * HI1 + 5) return 3;
    if (x == B127 + 5) return 4; if (x == (u128)UINT64_MAX * HI1 + 5) return 5; if (x == U128_MAX) return 6;
    return -1;
}
static int64_t sparse_u128_ref(u128 x){
    if (x == 0) return 11; if (x == 1) return 12; if (x == UINT64_MAX) return 13; if (x == HI1) return 14;
    if (x == B127) return 15; if (x == U128_MAX - 1) return 16; if (x == U128_MAX) return 17;
    return -1;
}
static int64_t dense_u128_ref(u128 x){
    if (x == 100) return 200; if (x == 101) return 201; if (x == 102) return 202; if (x == 103) return 203;
    if (x == 104) return 204; if (x == 105) return 205; if (x == 106) return 206; if (x == 107) return 207;
    return -1;
}
static int64_t args_i128_ref(s128 x){
    if (x == 1) return 11; if (x == 2) return 22; if (x == (s128)(HI1 + 1)) return 33; if (x == -1) return 44;
    return 0;
}

static void show(const char *tag, unsigned i, u128 x, int64_t got, int64_t want){
    printf("%s probe %u (hi=%016llx lo=%016llx): got %lld want %lld\n", tag, i,
           (unsigned long long)(x >> 64), (unsigned long long)x, (long long)got, (long long)want);
}

int main(void){
    // Every case constant, its neighbours in the low half (the boundaries
    // just outside a dense range), the same low half under a different high
    // half (the mis-dispatch a half-blind lowering would make), the sign and
    // width extremes, and scattered default-hitting values.
    u128 probes[] = {
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 42, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 299, 300, 301,
        29999, 30000, 30001, 1000000,
        (u128)(s128)-1, (u128)(s128)-2, (u128)(s128)-3, (u128)(s128)-4, (u128)(s128)-7, (u128)(s128)-8, (u128)(s128)-99,
        UINT64_MAX, HI1 - 2, HI1, HI1 + 1, HI1 + 2, HI1 + 3, HI1 + 5, HI1 + 7, HI1 + 100, HI1 + 300,
        2 * HI1 + 5, 2 * HI1 + 6, 3 * HI1 + 5,
        HI70, HI70 + 3, HI70 + 4, HI70 + 300,
        B127, B127 + 1, B127 + 5, B127 - 1,
        (u128)UINT64_MAX * HI1, (u128)UINT64_MAX * HI1 + 5, (u128)UINT64_MAX * HI1 + 6,
        U128_MAX, U128_MAX - 1, U128_MAX - 2,
    };
    unsigned n = sizeof(probes)/sizeof(probes[0]);
    for (unsigned i = 0; i < n; i++) {
        u128 x = probes[i];
        s128 sx = (s128)x;
        int64_t got, want;
        got = dense_i128(sx);     want = dense_i128_ref(sx);     if (got != want) { show("dense_i128", i, x, got, want); return 1; }
        got = dense_neg_i128(sx); want = dense_neg_i128_ref(sx); if (got != want) { show("dense_neg_i128", i, x, got, want); return 2; }
        got = sparse_i128(sx);    want = sparse_i128_ref(sx);    if (got != want) { show("sparse_i128", i, x, got, want); return 3; }
        got = hi_only_u128(x);    want = hi_only_u128_ref(x);    if (got != want) { show("hi_only_u128", i, x, got, want); return 4; }
        got = sparse_u128(x);     want = sparse_u128_ref(x);     if (got != want) { show("sparse_u128", i, x, got, want); return 5; }
        got = dense_u128(x);      want = dense_u128_ref(x);      if (got != want) { show("dense_u128", i, x, got, want); return 6; }
        got = args_i128(sx);      want = args_i128_ref(sx);      if (got != want) { show("args_i128", i, x, got, want); return 7; }
    }

    // Checked multiply at the boundaries, against the compiler's own
    // __int128 overflow builtin.
    struct { s128 a, b; } S[] = {
        {S128_MIN, -1}, {-1, S128_MIN}, {S128_MIN, 1}, {S128_MIN, 0}, {S128_MAX, 1}, {S128_MAX, 2},
        {S128_MAX, -1}, {S128_MAX, -2}, {S128_MIN, 2}, {S128_MIN / 2, 2}, {S128_MIN / 2, -2},
        {(s128)HI1, (s128)HI1}, {(s128)(HI1 - 1), (s128)(HI1 - 1)}, {(s128)((u128)1 << 63), (s128)((u128)1 << 63)},
        {(s128)((u128)1 << 63), (s128)((u128)1 << 64)}, {-(s128)((u128)1 << 63), (s128)((u128)1 << 64)},
        {(s128)((u128)1 << 126), 2}, {(s128)((u128)1 << 126), -2}, {-(s128)((u128)1 << 126), -2}, {-(s128)((u128)1 << 126), 2},
        {0, S128_MAX}, {0, S128_MIN}, {5, 3}, {-5, 3}, {5, -3}, {-5, -3}, {S128_MAX, S128_MAX}, {S128_MIN, S128_MIN},
    };
    for (unsigned i = 0; i < sizeof(S)/sizeof(S[0]); i++) {
        s128 a = S[i].a, b = S[i].b, ref_lo;
        _Bool ref_ovf = __builtin_mul_overflow(a, b, &ref_lo);
        if (smul_ovf(a, b) != ref_ovf) { printf("smul_ovf case %u: got %d want %d\n", i, smul_ovf(a, b), ref_ovf); return 8; }
        if (smul_lo(a, b) != ref_lo)   { printf("smul_lo case %u mismatch\n", i); return 9; }
    }
    struct { u128 a, b; } U[] = {
        {0, U128_MAX}, {U128_MAX, 0}, {1, U128_MAX}, {U128_MAX, 1}, {U128_MAX, 2}, {2, U128_MAX},
        {B127, 2}, {B127, 1}, {B127 - 1, 2}, {HI1, HI1}, {HI1 - 1, HI1 - 1}, {HI1, HI1 - 1},
        {HI1 + 1, HI1 - 1}, {HI1 + 1, HI1 + 1}, {(u128)1 << 65, HI1}, {(u128)1 << 63, (u128)1 << 63},
        {(u128)1 << 63, (u128)1 << 65}, {(u128)1 << 63, (u128)1 << 64}, {7, 0}, {5, 3}, {U128_MAX, U128_MAX},
        {U128_MAX / 3, 3}, {U128_MAX / 3 + 1, 3},
    };
    for (unsigned i = 0; i < sizeof(U)/sizeof(U[0]); i++) {
        u128 a = U[i].a, b = U[i].b, ref_lo;
        _Bool ref_ovf = __builtin_mul_overflow(a, b, &ref_lo);
        if (umul_ovf(a, b) != ref_ovf) { printf("umul_ovf case %u: got %d want %d\n", i, umul_ovf(a, b), ref_ovf); return 10; }
        if (umul_lo(a, b) != ref_lo)   { printf("umul_lo case %u mismatch\n", i); return 11; }
    }
    printf("i128/u128 switch (dense, sparse, negative, high-half-only, block args) and checked mul boundaries match clang\n");
    return 0;
}
"#;

fn link_run(tag: &str, obj: &[u8]) -> Option<i32> {
    if !can_link_and_run_aarch64_native() {
        eprintln!("SKIP: needs an AArch64 Linux GNU or macOS host");
        return None;
    }
    let dir = std::env::temp_dir().join(format!("trust_cg_{tag}_e2e"));
    let _ = fs::create_dir_all(&dir);
    let obj_path = dir.join(format!("{tag}.o"));
    let drv_path = dir.join("driver.c");
    let bin_path = dir.join(format!("{tag}_bin"));
    fs::write(&obj_path, obj).unwrap();
    fs::write(&drv_path, DRIVER).unwrap();
    let link = Command::new("cc")
        .args([
            drv_path.to_str().unwrap(),
            obj_path.to_str().unwrap(),
            "-o",
            bin_path.to_str().unwrap(),
        ])
        .args(native_host::c_math_library_args())
        .output()
        .expect("cc");
    assert!(
        link.status.success(),
        "link:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let out = Command::new(bin_path.to_str().unwrap()).output().unwrap();
    if !out.stdout.is_empty() {
        eprint!("{}", String::from_utf8_lossy(&out.stdout));
    }
    let code = out.status.code().unwrap_or(-1);
    let _ = fs::remove_dir_all(&dir);
    Some(code)
}

/// The i128/u128 switch and checked-multiply module compiles at every opt
/// level and its native execution matches clang on the boundary battery.
#[test]
fn e2e_aarch64_i128_switch_and_checked_mul_match_clang() {
    let module = build_module();
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let obj = compile_at(&module, opt)
            .unwrap_or_else(|e| panic!("i128 switch module must compile at {opt:?}: {e}"));
        let Some(code) = link_run(&format!("i128_switch_{opt:?}"), &obj) else {
            return;
        };
        assert_eq!(
            code, 0,
            "i128 switch / checked-mul result mismatch at {opt:?}"
        );
    }
}

/// Fail-closed controls: a duplicate 128-bit case, a `Constant::U128` on an
/// I128 selector, a negative `Constant::Int` on a U128 selector and a
/// non-canonical `Constant::U128` are each refused BY NAME before any code is
/// produced. A refusal that named the wrong thing, or a silent acceptance,
/// would let a frontend's malformed switch reach the machine.
#[test]
fn e2e_aarch64_i128_switch_refuses_malformed_cases_by_name() {
    fn module_with(selector_ty: Ty, cases: Vec<Constant>) -> TrustIrModule {
        let mut m = TrustIrModule::new("i128_switch_refusal");
        let ft = m
            .add_func_type(FuncTy {
                params: vec![selector_ty.clone()],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut f = TrustIrFunction::new(FuncId::new(0), "sw", ft, BlockId::new(0));
        let n = cases.len() as u32;
        let mut blocks = vec![TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), selector_ty)],
            body: vec![InstrNode::new(Inst::Switch {
                value: ValueId::new(0),
                default: BlockId::new(n + 1),
                default_args: vec![],
                cases: cases
                    .into_iter()
                    .enumerate()
                    .map(|(i, value)| SwitchCase {
                        value,
                        target: BlockId::new(i as u32 + 1),
                        args: vec![],
                    })
                    .collect(),
                exhaustive_enum_unreachable: false,
            })],
        }];
        for i in 0..=n {
            blocks.push(ret_const_block(i + 1, 100 + i, i as i64));
        }
        f.blocks = blocks;
        m.try_add_function(f)
            .expect("Module::try_add_function: test fixture");
        m
    }

    // TrustIR's typed admission, which every compiler entry consumes first,
    // refuses the last three by name before the adapter's own range and
    // spelling arms (`overflows the I128/U128 selector`, `non-canonical
    // Constant::U128`) are reached; the duplicate still reaches the adapter.
    let controls: [(&str, Ty, Vec<Constant>, &str); 4] = [
        (
            "duplicate",
            Ty::I128,
            vec![Constant::Int(7), Constant::Int(9), Constant::Int(7)],
            "duplicate 128-bit switch case value",
        ),
        (
            "U128 constant on an I128 selector",
            Ty::I128,
            vec![Constant::Int(1), Constant::U128(u128::MAX)],
            "TrustIrAdmissionRefused { error: \"function 'sw' bb0 switch case 1: const type \
             mismatch: expected i128, got int\"",
        ),
        (
            "negative constant on a U128 selector",
            Ty::U128,
            vec![Constant::Int(1), Constant::Int(-1)],
            "TrustIrAdmissionRefused { error: \"function 'sw' bb0 switch case 1: const type \
             mismatch: expected u128, got int\"",
        ),
        (
            "non-canonical U128 constant",
            Ty::U128,
            vec![Constant::Int(1), Constant::U128(7)],
            "TrustIrAdmissionRefused { error: \"function 'sw' bb0 switch case 1: const type \
             mismatch: expected canonical integer spelling",
        ),
    ];
    for (label, selector_ty, cases, expected) in controls {
        let module = module_with(selector_ty, cases);
        let err = compile_at(&module, OptLevel::O0)
            .err()
            .unwrap_or_else(|| panic!("{label}: malformed i128 switch must be refused"));
        // Since WS7.3 a malformed case set trust-ir itself refuses is refused
        // at ingestion by trust-ir's finding, before the backend's own arm.
        match admission_expect::names_first_finding(&module, &err, &permit_unlicensed()) {
            Some(named) => assert!(
                named,
                "{label}: refusal must name trust-ir's finding {:?}; got {err}",
                admission_expect::first_finding(&module, &permit_unlicensed())
            ),
            None => assert!(
                err.contains(expected),
                "{label}: refusal must name its reason ({expected:?}); got {err}"
            ),
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
