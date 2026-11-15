// trust-cg-codegen/tests/e2e_aarch64_switch.rs
//
// Completeness: `Inst::Switch`. trust-cg picks between three lowering
// strategies (crates/trust-cg-lower/src/switch.rs `choose_strategy`):
//   * a DENSE jump table (PC-relative table indexed by the selector, then BR) --
//     the interesting path because it materializes a table address and does an
//     indirect branch through it;
//   * a balanced BINARY SEARCH tree of compares for more than three sparse
//     cases; and
//   * a LINEAR compare chain for at most three cases.
//
// All are checked differentially against a `switch` oracle compiled by the
// host C compiler (clang on macOS, GCC on the Linux floor host) over the whole
// interesting input range (each case value, the boundaries just outside it,
// and default-hitting values). A wrong table base, a wrong index bias, or an
// off-by-one in the range check would send some selector to the wrong arm and
// diverge from the oracle.
//
// A second family returns a boolean through a JOIN BLOCK PARAMETER, with
// several case keys sharing the constant-`1` or constant-`0` arm. Its sparse
// compare chain puts two or more conditional branches into the entry block,
// which the diamond/triangle if-conversion recognizers must not mistake for a
// two-way diamond. That shape was refused at O2/O3 from 6eafd20a8 until the
// shared `if_convert::header_branch_is_sole_block_exit` gate, so it runs at
// every optimization level.
//
// The third family is a selector-width matrix (L04-P11): i8/i16/i32/i64 and
// u8/u16/u32/u64 selectors over dense, negative, holed, top-of-range,
// type-boundary, three-case and wrapped-product case sets, the two i32 shapes
// of e2e_differential.rs (switch_basic, switch_many), switches whose edges
// carry block arguments, a 64-slot holed table and the density-threshold
// boundaries. Every function runs at O0-O3 against the C oracle: 8- and
// 16-bit selectors exhaustively, 32/64-bit selectors on the case
// neighbourhoods, the type boundaries and a fixed pseudo-random sweep. On
// AArch64 Linux GNU the 8/16/32-bit selectors are also called with garbage in
// the argument register's unspecified upper bits (AAPCS64 leaves them
// undefined; Apple's arm64 ABI does not, so that leg is Linux-only). Each
// function is also compiled alone and its decoded code words must show the
// strategy the matrix names (ADR + LDRSW [Xn, Xm, LSL #2] + BR for a jump
// table, no BR or ADR otherwise), and on Linux GNU binutils `objdump`
// disassembles the linked-in object's per-symbol code to the same
// conclusion. These are native execution controls on this host CPU, not
// proofs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fs;
use std::process::Command;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;

use trust_ir::{
    BinOp, Block as TrustIrBlock, Constant, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, SwitchCase, Ty, ValueId,
};
use trust_ir::{BlockId, FuncId};

#[path = "common/native_host.rs"]
mod native_host;

const ALL_OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// A qualifying run sets `L04P11_RETAIN_DIR` to keep the compiled objects and
/// C drivers (under `<dir>/<relative>`) for disassembly and hashing.
fn retain(relative: &str, bytes: &[u8]) {
    if let Some(dir) = std::env::var_os("L04P11_RETAIN_DIR") {
        let path = std::path::Path::new(&dir).join(relative);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, bytes).unwrap();
    }
}

/// AArch64 Linux GNU (ELF) or macOS (Mach-O): `Compiler::new` derives the
/// host's object format and ABI, and the host `cc` links it.
fn can_link_and_run_aarch64_native() -> bool {
    native_host::NATIVE
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

// Build `fn name(x: i64) -> i64 { switch (x) { case k_i: return v_i; default: return dflt } }`.
// `arms` are (case_value, return_value); default block returns `dflt`.
fn build_switch_fn(m: &mut TrustIrModule, id: u32, name: &str, arms: &[(i64, i64)], dflt: i64) {
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));

    // Entry block 0 holds the Switch terminator. Case i -> block (i+1),
    // default -> block (arms.len()+1). SSA ids for the case constants start
    // at 100 to stay clear of the selector (%0).
    let default_bb = arms.len() as u32 + 1;
    let cases: Vec<SwitchCase> = arms
        .iter()
        .enumerate()
        .map(|(i, (cv, _))| SwitchCase {
            value: Constant::Int(*cv as i128),
            target: BlockId::new(i as u32 + 1),
            args: vec![],
        })
        .collect();

    let mut blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
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

fn build_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("switch");
    // Dense, contiguous 0..=5 -> jump table.
    build_switch_fn(
        &mut m,
        0,
        "dense_sw",
        &[(0, 100), (1, 111), (2, 122), (3, 133), (4, 144), (5, 155)],
        -1,
    );
    // Sparse, scattered (incl. a negative) -> linear scan / BST. Exercises the
    // emit_cmp constant-materialization fix (negative -7, wide 30000).
    build_switch_fn(
        &mut m,
        1,
        "sparse_sw",
        &[(-7, 40), (3, 10), (300, 20), (30000, 30)],
        0,
    );
    // Dense over a NEGATIVE range (-3..=3) -> jump table with a negative
    // min_val, exercising the normalize-SUB materialization fix.
    build_switch_fn(
        &mut m,
        2,
        "dense_neg_sw",
        &[
            (-3, 1000),
            (-2, 1001),
            (-1, 1002),
            (0, 1003),
            (1, 1004),
            (2, 1005),
            (3, 1006),
        ],
        -99,
    );
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
extern int64_t dense_sw(int64_t);
extern int64_t sparse_sw(int64_t);
extern int64_t dense_neg_sw(int64_t);

static int64_t dense_ref(int64_t x){
    switch(x){
        case 0: return 100; case 1: return 111; case 2: return 122;
        case 3: return 133; case 4: return 144; case 5: return 155;
        default: return -1;
    }
}
static int64_t sparse_ref(int64_t x){
    switch(x){
        case -7: return 40; case 3: return 10; case 300: return 20;
        case 30000: return 30; default: return 0;
    }
}
static int64_t dense_neg_ref(int64_t x){
    switch(x){
        case -3: return 1000; case -2: return 1001; case -1: return 1002;
        case 0: return 1003; case 1: return 1004; case 2: return 1005;
        case 3: return 1006; default: return -99;
    }
}

int main(void){
    // Every case value, the boundaries just outside the dense range, and
    // scattered default-hitting values.
    int64_t probes[] = {-100,-8,-7,-6,-4,-3,-2,-1,0,1,2,3,4,5,6,7,42,299,300,301,29999,30000,30001,1000000};
    for(unsigned i=0;i<sizeof(probes)/sizeof(probes[0]);i++){
        int64_t x = probes[i];
        if(dense_sw(x)     != dense_ref(x))     { printf("dense  x=%lld\n",(long long)x); return 1; }
        if(sparse_sw(x)    != sparse_ref(x))    { printf("sparse x=%lld\n",(long long)x); return 2; }
        if(dense_neg_sw(x) != dense_neg_ref(x)) { printf("dneg   x=%lld\n",(long long)x); return 3; }
    }
    printf("switch: dense (0-based & negative-min jump table) and sparse (linear/BST) match clang\n");
    return 0;
}
"#;

fn link_run(tag: &str, obj: &[u8], driver: &str) -> Option<i32> {
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
    fs::write(&drv_path, driver).unwrap();
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
    let code = Command::new(bin_path.to_str().unwrap())
        .output()
        .unwrap()
        .status
        .code()
        .unwrap_or(-1);
    let _ = fs::remove_dir_all(&dir);
    Some(code)
}

#[test]
fn e2e_aarch64_switch_matches_clang() {
    let module = build_module();
    for opt in ALL_OPT_LEVELS {
        let obj = compile_at(&module, opt).expect("switch module must compile");
        let Some(code) = link_run("switch", &obj, DRIVER) else {
            return;
        };
        assert_eq!(code, 0, "switch result mismatch at {opt:?}");
    }
}

// A block `bbN:` that passes the i64 constant `k` to the join block `join`.
fn edge_const_block(bb: u32, vid: u32, k: i64, join: u32) -> TrustIrBlock {
    TrustIrBlock {
        id: BlockId::new(bb),
        params: vec![],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(k as i128),
            })
            .with_result(ValueId::new(vid)),
            InstrNode::new(Inst::Br {
                target: BlockId::new(join),
                args: vec![ValueId::new(vid)],
            }),
        ],
    }
}

// Build `fn name(x: i64) -> i64` whose switch sends each case to the shared
// `1` arm (bb1) or `0` arm (bb2); both arms pass their constant to the join
// block bb3, which returns its parameter. This is the SSA form of
// `matches!(x, k1 | k2 ..) as i64`: every key of one polarity shares an arm.
fn build_bool_switch_fn(
    m: &mut TrustIrModule,
    id: u32,
    name: &str,
    cases: &[(i64, bool)],
    default: bool,
) {
    let ft = m
        .add_func_type(FuncTy {
            params: vec![Ty::I64],
            returns: vec![Ty::I64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(id), name, ft, BlockId::new(0));
    let arm = |value: bool| BlockId::new(if value { 1 } else { 2 });
    let cases: Vec<SwitchCase> = cases
        .iter()
        .map(|&(key, value)| SwitchCase {
            value: Constant::Int(key as i128),
            target: arm(value),
            args: vec![],
        })
        .collect();
    f.blocks = vec![
        TrustIrBlock {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
            body: vec![InstrNode::new(Inst::Switch {
                value: ValueId::new(0),
                default: arm(default),
                default_args: vec![],
                cases,
                exhaustive_enum_unreachable: false,
            })],
        },
        edge_const_block(1, 101, 1, 3),
        edge_const_block(2, 102, 0, 3),
        TrustIrBlock {
            id: BlockId::new(3),
            params: vec![(ValueId::new(1), Ty::I64)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            })],
        },
    ];
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

fn build_bool_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("bool_switch");
    // Two keys share the `1` arm: `matches!(x, 1 | 3)`.
    build_bool_switch_fn(&mut m, 0, "bool_sw_pair", &[(1, true), (3, true)], false);
    // Two keys share the `0` arm; the default is `1`.
    build_bool_switch_fn(
        &mut m,
        1,
        "bool_sw_pair_inv",
        &[(1, false), (3, false)],
        true,
    );
    // The earlier key reaches the arm that the default also reaches, and the
    // final compare branches to the other arm.
    build_bool_switch_fn(&mut m, 2, "bool_sw_mixed", &[(1, true), (3, false)], true);
    // Four scattered keys (negative and wide) share the `1` arm.
    build_bool_switch_fn(
        &mut m,
        3,
        "bool_sw_quad",
        &[(-7, true), (0, true), (5, true), (300, true)],
        false,
    );
    m
}

const BOOL_DRIVER: &str = r#"
#include <stdio.h>
#include <stdint.h>
extern int64_t bool_sw_pair(int64_t);
extern int64_t bool_sw_pair_inv(int64_t);
extern int64_t bool_sw_mixed(int64_t);
extern int64_t bool_sw_quad(int64_t);

static int64_t pair_ref(int64_t x){ switch(x){ case 1: case 3: return 1; default: return 0; } }
static int64_t pair_inv_ref(int64_t x){ switch(x){ case 1: case 3: return 0; default: return 1; } }
static int64_t mixed_ref(int64_t x){ switch(x){ case 1: return 1; case 3: return 0; default: return 1; } }
static int64_t quad_ref(int64_t x){
    switch(x){ case -7: case 0: case 5: case 300: return 1; default: return 0; }
}

int main(void){
    int64_t extra[] = {-1000000, 29999, 30000, 1000000, INT64_MIN, INT64_MAX};
    for(int64_t x = -16; x <= 310; x++){
        if(bool_sw_pair(x)     != pair_ref(x))     { printf("pair  x=%lld\n",(long long)x); return 1; }
        if(bool_sw_pair_inv(x) != pair_inv_ref(x)) { printf("inv   x=%lld\n",(long long)x); return 2; }
        if(bool_sw_mixed(x)    != mixed_ref(x))    { printf("mixed x=%lld\n",(long long)x); return 3; }
        if(bool_sw_quad(x)     != quad_ref(x))     { printf("quad  x=%lld\n",(long long)x); return 4; }
    }
    for(unsigned i=0;i<sizeof(extra)/sizeof(extra[0]);i++){
        int64_t x = extra[i];
        if(bool_sw_pair(x) != pair_ref(x) || bool_sw_pair_inv(x) != pair_inv_ref(x)
           || bool_sw_mixed(x) != mixed_ref(x) || bool_sw_quad(x) != quad_ref(x)) {
            printf("extreme x=%lld\n",(long long)x); return 5;
        }
    }
    printf("bool switch: shared-arm keys match the C reference\n");
    return 0;
}
"#;

/// Shared-arm boolean switches compile at O0-O3 (no refusal) and every
/// compiled function agrees with the C `switch` reference over [-16, 310]
/// and the i64 extremes.
#[test]
fn e2e_aarch64_bool_switch_shared_arms_match_c_at_every_opt_level() {
    let module = build_bool_module();
    for opt in ALL_OPT_LEVELS {
        let obj = compile_at(&module, opt)
            .unwrap_or_else(|error| panic!("bool switch module must compile at {opt:?}: {error}"));
        let Some(code) = link_run("bool_switch", &obj, BOOL_DRIVER) else {
            return;
        };
        assert_eq!(code, 0, "bool switch result mismatch at {opt:?}");
    }
}

// ===========================================================================
// Selector-width and strategy matrix (L04-P11)
// ===========================================================================

/// The lowering strategy a matrix function's code words must show.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Strategy {
    JumpTable,
    BinarySearch,
    LinearScan,
}

/// Where the switched value comes from.
#[derive(Clone, Copy, Debug)]
enum Selector {
    /// The function's only parameter.
    Param,
    /// The parameter times a constant, wrapped to the selector type: a narrow
    /// product leaves dirty bits above its width in the W register.
    WrappedProduct(i64),
}

/// How the arms deliver the function result.
#[derive(Clone, Copy, Debug)]
enum Arms {
    /// One returning block per distinct result; equal results share a target.
    ReturnBlocks,
    /// Every edge, the default included, passes its result as the argument of
    /// one merge block.
    EdgeArguments,
}

struct SwitchSpec {
    name: String,
    selector_ty: Ty,
    ret_ty: Ty,
    selector: Selector,
    arms: Arms,
    cases: Vec<(i128, i64)>,
    default: i64,
    strategy: Strategy,
}

/// `(bits, signed)` of an integer selector type.
fn int_facts(ty: &Ty) -> (u32, bool) {
    match ty {
        Ty::I8 => (8, true),
        Ty::I16 => (16, true),
        Ty::I32 => (32, true),
        Ty::I64 => (64, true),
        Ty::U8 => (8, false),
        Ty::U16 => (16, false),
        Ty::U32 => (32, false),
        Ty::U64 => (64, false),
        other => panic!("no integer facts for {other:?}"),
    }
}

fn type_min(ty: &Ty) -> i128 {
    match int_facts(ty) {
        (bits, true) => -(1i128 << (bits - 1)),
        (_, false) => 0,
    }
}

fn type_max(ty: &Ty) -> i128 {
    match int_facts(ty) {
        (bits, true) => (1i128 << (bits - 1)) - 1,
        (bits, false) => (1i128 << bits) - 1,
    }
}

/// `v` wrapped into `ty`'s value range.
fn wrap(ty: &Ty, v: i128) -> i128 {
    let (bits, signed) = int_facts(ty);
    let modulus = 1i128 << bits;
    let r = v.rem_euclid(modulus);
    if signed && r > type_max(ty) {
        r - modulus
    } else {
        r
    }
}

fn ty_tag(ty: &Ty) -> &'static str {
    match ty {
        Ty::I8 => "i8",
        Ty::I16 => "i16",
        Ty::I32 => "i32",
        Ty::I64 => "i64",
        Ty::U8 => "u8",
        Ty::U16 => "u16",
        Ty::U32 => "u32",
        Ty::U64 => "u64",
        other => panic!("no tag for {other:?}"),
    }
}

fn c_type(ty: &Ty) -> &'static str {
    match ty {
        Ty::I8 => "int8_t",
        Ty::I16 => "int16_t",
        Ty::I32 => "int32_t",
        Ty::I64 => "int64_t",
        Ty::U8 => "uint8_t",
        Ty::U16 => "uint16_t",
        Ty::U32 => "uint32_t",
        Ty::U64 => "uint64_t",
        other => panic!("no C type for {other:?}"),
    }
}

fn c_unsigned_type(ty: &Ty) -> &'static str {
    match int_facts(ty).0 {
        8 => "uint8_t",
        16 => "uint16_t",
        32 => "uint32_t",
        _ => "uint64_t",
    }
}

/// A C integer constant expression of type `ty` holding `v`.
fn c_literal(ty: &Ty, v: i128) -> String {
    assert!(type_min(ty) <= v && v <= type_max(ty), "{v} out of {ty:?}");
    match ty {
        Ty::I32 if v == type_min(ty) => "INT32_MIN".into(),
        Ty::I64 if v == type_min(ty) => "INT64_MIN".into(),
        Ty::I8 | Ty::I16 | Ty::I32 | Ty::U8 | Ty::U16 => format!("{v}"),
        Ty::I64 => format!("INT64_C({v})"),
        Ty::U32 => format!("UINT32_C({v})"),
        Ty::U64 => format!("UINT64_C({v})"),
        other => panic!("no C literal for {other:?}"),
    }
}

fn spec(
    name: String,
    selector_ty: Ty,
    selector: Selector,
    cases: Vec<(i128, i64)>,
    default: i64,
    strategy: Strategy,
) -> SwitchSpec {
    SwitchSpec {
        name,
        selector_ty,
        ret_ty: Ty::I64,
        selector,
        arms: Arms::ReturnBlocks,
        cases,
        default,
        strategy,
    }
}

/// The matrix. Each function names the strategy `choose_strategy` must pick
/// for its NORMALIZED case values: 8/16-bit selectors compare their
/// zero-extended patterns, so a signed narrow case set that straddles zero is
/// sparse there although it is dense as signed values.
fn switch_matrix() -> Vec<SwitchSpec> {
    use Strategy::*;
    let mut specs = Vec::new();
    for ty in [
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
    ] {
        let tag = ty_tag(&ty);
        let (bits, signed) = int_facts(&ty);
        let (min, max) = (type_min(&ty), type_max(&ty));
        let values = |keys: &[i128], base: i64| -> Vec<(i128, i64)> {
            keys.iter()
                .enumerate()
                .map(|(i, &k)| (k, base + 37 * i as i64))
                .collect()
        };
        // Dense 0..=7: a jump table at every width.
        let dense: Vec<i128> = (0..8).collect();
        specs.push(spec(
            format!("sw_dense_{tag}"),
            ty.clone(),
            Selector::Param,
            values(&dense, 1000),
            -1,
            JumpTable,
        ));
        // Seven of ten slots: the holes route to the default through the table.
        let holed = [10, 11, 13, 14, 16, 17, 19];
        specs.push(spec(
            format!("sw_holed_{tag}"),
            ty.clone(),
            Selector::Param,
            values(&holed, 2000),
            -2,
            JumpTable,
        ));
        // The six largest values of the type (for signed types -6..=-1): a
        // table whose normalized minimum is far from zero.
        let top: Vec<i128> = if signed {
            (-6..=-1).collect()
        } else {
            (max - 5..=max).collect()
        };
        specs.push(spec(
            format!("sw_top_{tag}"),
            ty.clone(),
            Selector::Param,
            values(&top, 3000),
            -3,
            JumpTable,
        ));
        // The type's boundary values: sparse at every width.
        let edges: Vec<i128> = if signed {
            vec![min, min + 1, -1, 0, 1, max - 1, max]
        } else {
            vec![0, 1, 2, max / 2, max - 2, max - 1, max]
        };
        specs.push(spec(
            format!("sw_edges_{tag}"),
            ty.clone(),
            Selector::Param,
            values(&edges, 4000),
            -4,
            BinarySearch,
        ));
        // Three cases: the linear compare chain, with the extremes
        // materialized as compare operands.
        let three: Vec<i128> = if signed {
            vec![min, 0, max]
        } else {
            vec![0, max / 2, max]
        };
        specs.push(spec(
            format!("sw_three_{tag}"),
            ty.clone(),
            Selector::Param,
            values(&three, 5000),
            -5,
            LinearScan,
        ));
        if signed {
            // -4..=3: dense as signed values. A 32/64-bit selector compares at
            // its own width (a jump table); an 8/16-bit selector compares its
            // zero-extended pattern, where -4..=-1 sit at the top of the range
            // (a binary search).
            let straddle: Vec<i128> = (-4..=3).collect();
            specs.push(spec(
                format!("sw_straddle_{tag}"),
                ty.clone(),
                Selector::Param,
                values(&straddle, 6000),
                -6,
                if bits >= 32 { JumpTable } else { BinarySearch },
            ));
        }
        if bits <= 16 {
            // A wrapped narrow product (the audit G13 hazard): x * 3 over a
            // dense 0..=7 table, and x * 20 over a sparse case set.
            specs.push(spec(
                format!("sw_mul3_{tag}"),
                ty.clone(),
                Selector::WrappedProduct(3),
                values(&dense, 7000),
                -7,
                JumpTable,
            ));
            let mut sparse_products: Vec<i128> = Vec::new();
            for k in [3, 7, 12, 13, 50, 100] {
                let p = wrap(&ty, k * 20);
                if !sparse_products.contains(&p) {
                    sparse_products.push(p);
                }
            }
            specs.push(spec(
                format!("sw_mul20_{tag}"),
                ty.clone(),
                Selector::WrappedProduct(20),
                values(&sparse_products, 8000),
                -8,
                BinarySearch,
            ));
        }
    }

    // The two i32 -> i32 shapes of e2e_differential.rs (Apple-only there).
    let mut basic = spec(
        "sw_basic_i32".into(),
        Ty::I32,
        Selector::Param,
        vec![(0, 10), (1, 20), (2, 30)],
        99,
        LinearScan,
    );
    basic.ret_ty = Ty::I32;
    specs.push(basic);
    let mut many = spec(
        "sw_many_i32".into(),
        Ty::I32,
        Selector::Param,
        (0..8).map(|k| (k, 11 * k as i64)).collect(),
        -1,
        JumpTable,
    );
    many.ret_ty = Ty::I32;
    specs.push(many);

    // Edge arguments into one merge block: every switch edge needs its own
    // copy, through the table and through the compare tree.
    let mut args_dense = spec(
        "sw_args_dense_i64".into(),
        Ty::I64,
        Selector::Param,
        (0..10).map(|k| (k, 9000 + 13 * k as i64)).collect(),
        -9,
        JumpTable,
    );
    args_dense.arms = Arms::EdgeArguments;
    specs.push(args_dense);
    let mut args_sparse = spec(
        "sw_args_sparse_i32".into(),
        Ty::I32,
        Selector::Param,
        vec![(-50000, 1), (-7, 2), (0, 3), (9, 4), (4096, 5), (70000, 6)],
        -10,
        BinarySearch,
    );
    args_sparse.arms = Arms::EdgeArguments;
    specs.push(args_sparse);

    // Sixteen dense keys sharing three targets: repeated table entries.
    specs.push(spec(
        "sw_shared_i64".into(),
        Ty::I64,
        Selector::Param,
        (0..16).map(|k| (k, 100 + (k % 3) as i64)).collect(),
        -11,
        JumpTable,
    ));
    // A 64-slot table with every fifth slot a hole (51 cases).
    specs.push(spec(
        "sw_wide_i64".into(),
        Ty::I64,
        Selector::Param,
        (0..64)
            .filter(|k| k % 5 != 0)
            .map(|k| (k, (k * k) as i64 - 7 * k as i64))
            .collect(),
        -12,
        JumpTable,
    ));
    // The density threshold: 4 of 10 slots is sparse, 5 of 10 is dense, and
    // three dense cases stay a compare chain.
    specs.push(spec(
        "sw_density40_i64".into(),
        Ty::I64,
        Selector::Param,
        vec![(0, 1), (3, 2), (6, 3), (9, 4)],
        -13,
        BinarySearch,
    ));
    specs.push(spec(
        "sw_density50_i64".into(),
        Ty::I64,
        Selector::Param,
        vec![(0, 1), (2, 2), (4, 3), (6, 4), (9, 5)],
        -14,
        JumpTable,
    ));
    specs.push(spec(
        "sw_three_dense_i64".into(),
        Ty::I64,
        Selector::Param,
        vec![(0, 1), (1, 2), (2, 3)],
        -15,
        LinearScan,
    ));
    // Tables far from zero: a 33-bit minimum, a large negative minimum and
    // i64::MIN itself (the normalizing SUB needs a materialized constant).
    let far = 1i128 << 32;
    specs.push(spec(
        "sw_far_i64".into(),
        Ty::I64,
        Selector::Param,
        (0..8).map(|k| (far + k, 50 + k as i64)).collect(),
        -16,
        JumpTable,
    ));
    let far_negative = -1_000_000_000_000i128;
    specs.push(spec(
        "sw_farneg_i64".into(),
        Ty::I64,
        Selector::Param,
        (0..8).map(|k| (far_negative + k, 60 + k as i64)).collect(),
        -17,
        JumpTable,
    ));
    specs.push(spec(
        "sw_minval_i64".into(),
        Ty::I64,
        Selector::Param,
        (0..6)
            .map(|k| (i64::MIN as i128 + k, 70 + k as i64))
            .collect(),
        -18,
        JumpTable,
    ));
    specs
}

fn ret_const_node(ty: &Ty, vid: u32, value: i64) -> InstrNode {
    InstrNode::new(Inst::Const {
        ty: ty.clone(),
        value: Constant::Int(value as i128),
    })
    .with_result(ValueId::new(vid))
}

fn return_node(vid: u32) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: vec![ValueId::new(vid)],
    })
}

fn build_spec_fn(m: &mut TrustIrModule, id: u32, spec: &SwitchSpec) {
    let ft = m
        .add_func_type(FuncTy {
            params: vec![spec.selector_ty.clone()],
            returns: vec![spec.ret_ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut f = TrustIrFunction::new(FuncId::new(id), &spec.name, ft, BlockId::new(0));
    let mut entry = Vec::new();
    let selector = match spec.selector {
        Selector::Param => ValueId::new(0),
        Selector::WrappedProduct(factor) => {
            entry.push(
                InstrNode::new(Inst::Const {
                    ty: spec.selector_ty.clone(),
                    value: Constant::Int(factor as i128),
                })
                .with_result(ValueId::new(1)),
            );
            entry.push(
                InstrNode::new(Inst::BinOp {
                    op: BinOp::Mul,
                    ty: spec.selector_ty.clone(),
                    lhs: ValueId::new(0),
                    rhs: ValueId::new(1),
                })
                .with_result(ValueId::new(2)),
            );
            ValueId::new(2)
        }
    };
    let mut results: Vec<i64> = Vec::new();
    for &(_, r) in &spec.cases {
        if !results.contains(&r) {
            results.push(r);
        }
    }
    let result_index =
        |r: i64| u32::try_from(results.iter().position(|&x| x == r).unwrap()).unwrap();
    let entry_params = vec![(ValueId::new(0), spec.selector_ty.clone())];
    let mut blocks = Vec::new();
    match spec.arms {
        Arms::ReturnBlocks => {
            let default_bb = results.len() as u32 + 1;
            let cases = spec
                .cases
                .iter()
                .map(|&(k, r)| SwitchCase {
                    value: Constant::Int(k),
                    target: BlockId::new(result_index(r) + 1),
                    args: vec![],
                })
                .collect();
            entry.push(InstrNode::new(Inst::Switch {
                value: selector,
                default: BlockId::new(default_bb),
                default_args: vec![],
                cases,
                exhaustive_enum_unreachable: false,
            }));
            blocks.push(TrustIrBlock {
                id: BlockId::new(0),
                params: entry_params,
                body: entry,
            });
            for (i, &r) in results.iter().enumerate() {
                let vid = 100 + i as u32;
                blocks.push(TrustIrBlock {
                    id: BlockId::new(i as u32 + 1),
                    params: vec![],
                    body: vec![ret_const_node(&spec.ret_ty, vid, r), return_node(vid)],
                });
            }
            let vid = 100 + results.len() as u32;
            blocks.push(TrustIrBlock {
                id: BlockId::new(default_bb),
                params: vec![],
                body: vec![
                    ret_const_node(&spec.ret_ty, vid, spec.default),
                    return_node(vid),
                ],
            });
        }
        Arms::EdgeArguments => {
            for (i, &r) in results.iter().enumerate() {
                entry.push(ret_const_node(&spec.ret_ty, 100 + i as u32, r));
            }
            let default_vid = 100 + results.len() as u32;
            entry.push(ret_const_node(&spec.ret_ty, default_vid, spec.default));
            let cases = spec
                .cases
                .iter()
                .map(|&(k, r)| SwitchCase {
                    value: Constant::Int(k),
                    target: BlockId::new(1),
                    args: vec![ValueId::new(100 + result_index(r))],
                })
                .collect();
            entry.push(InstrNode::new(Inst::Switch {
                value: selector,
                default: BlockId::new(1),
                default_args: vec![ValueId::new(default_vid)],
                cases,
                exhaustive_enum_unreachable: false,
            }));
            blocks.push(TrustIrBlock {
                id: BlockId::new(0),
                params: entry_params,
                body: entry,
            });
            blocks.push(TrustIrBlock {
                id: BlockId::new(1),
                params: vec![(ValueId::new(3), spec.ret_ty.clone())],
                body: vec![return_node(3)],
            });
        }
    }
    f.blocks = blocks;
    m.try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

fn build_matrix_module(specs: &[&SwitchSpec]) -> TrustIrModule {
    let mut m = TrustIrModule::new("switch_matrix");
    for (id, spec) in specs.iter().enumerate() {
        build_spec_fn(&mut m, id as u32, spec);
    }
    m
}

/// 32/64-bit probes: every case value's +-2 neighbourhood and the type's
/// boundaries, wrapped into the type. 8/16-bit selectors are probed
/// exhaustively instead.
fn wide_probes(spec: &SwitchSpec) -> Vec<i128> {
    let ty = &spec.selector_ty;
    let mut probes = std::collections::BTreeSet::new();
    let anchors = spec
        .cases
        .iter()
        .map(|&(k, _)| k)
        .chain([type_min(ty), type_max(ty), 0]);
    for anchor in anchors {
        for delta in -2..=2 {
            probes.insert(wrap(ty, anchor + delta));
        }
    }
    probes.into_iter().collect()
}

/// The C driver: each function against its C `switch` oracle. With
/// `dirty_upper_bits`, every 8/16/32-bit function is also called through an
/// assembler-name alias taking `uint64_t`, with pseudo-random garbage above
/// the selector's width (the AAPCS64 caller leaves those bits unspecified).
fn matrix_driver(specs: &[&SwitchSpec], dirty_upper_bits: bool) -> String {
    let mut c = String::from(
        "#include <stdio.h>\n#include <stdint.h>\n\
         static uint64_t lcg_state = UINT64_C(0x9E3779B97F4A7C15);\n\
         static uint64_t lcg(void){ lcg_state = lcg_state * UINT64_C(6364136223846793005) \
         + UINT64_C(1442695040888963407); return lcg_state; }\n\
         static long calls = 0, mismatches = 0;\n\
         static void report(const char *name, long long x, unsigned long long raw, \
         long long got, long long want){\n\
         \x20   if (mismatches < 24) printf(\"%s x=%lld raw=0x%llx got=%lld want=%lld\\n\", \
         name, x, raw, got, want);\n    mismatches++;\n}\n",
    );
    for spec in specs {
        let name = &spec.name;
        let sel = c_type(&spec.selector_ty);
        let usel = c_unsigned_type(&spec.selector_ty);
        let ret = c_type(&spec.ret_ty);
        let (bits, _) = int_facts(&spec.selector_ty);
        let selector_expr = match spec.selector {
            Selector::Param => "x".to_string(),
            Selector::WrappedProduct(factor) => {
                format!("({sel})(({usel})x * ({usel}){factor})")
            }
        };
        c.push_str(&format!("extern {ret} {name}({sel});\n"));
        let dirty = dirty_upper_bits && bits < 64;
        if dirty {
            c.push_str(&format!(
                "extern {ret} {name}__raw(uint64_t) __asm__(\"{}\");\n",
                native_host::c_symbol(name)
            ));
        }
        c.push_str(&format!(
            "static {ret} ref_{name}({sel} x){{ {sel} s = {selector_expr}; switch (s) {{"
        ));
        for &(k, r) in &spec.cases {
            c.push_str(&format!(
                " case {}: return {};",
                c_literal(&spec.selector_ty, k),
                c_literal(&spec.ret_ty, r as i128)
            ));
        }
        c.push_str(&format!(
            " default: return {}; }} }}\n",
            c_literal(&spec.ret_ty, spec.default as i128)
        ));
        c.push_str(&format!(
            "static void probe_{name}({sel} x){{\n    {ret} want = ref_{name}(x);\n    \
             {ret} got = {name}(x);\n    calls++;\n    if (got != want) report(\"{name}\", \
             (long long)x, 0, (long long)got, (long long)want);\n"
        ));
        if dirty {
            let mask = (1u128 << bits) - 1;
            c.push_str(&format!(
                "    uint64_t raw = (lcg() & ~UINT64_C({mask})) | (uint64_t)({usel})x;\n    \
                 got = {name}__raw(raw);\n    calls++;\n    if (got != want) \
                 report(\"{name} (dirty upper bits)\", (long long)x, (unsigned long long)raw, \
                 (long long)got, (long long)want);\n"
            ));
        }
        c.push_str("}\n");
        c.push_str(&format!("static void check_{name}(void){{\n"));
        if bits <= 16 {
            c.push_str(&format!(
                "    for (long v = {}; v <= {}; v++) probe_{name}(({sel})v);\n",
                type_min(&spec.selector_ty),
                type_max(&spec.selector_ty)
            ));
        } else {
            let probes: Vec<String> = wide_probes(spec)
                .into_iter()
                .map(|p| c_literal(&spec.selector_ty, p))
                .collect();
            c.push_str(&format!(
                "    static const {sel} probes[] = {{{}}};\n    for (unsigned i = 0; i < \
                 sizeof probes / sizeof probes[0]; i++) probe_{name}(probes[i]);\n    for (int \
                 i = 0; i < 4096; i++) probe_{name}(({sel})lcg());\n",
                probes.join(", ")
            ));
        }
        c.push_str("}\n");
    }
    c.push_str("int main(void){\n");
    for spec in specs {
        c.push_str(&format!("    check_{}();\n", spec.name));
    }
    c.push_str(&format!(
        "    printf(\"switch matrix: %ld calls over {} functions, %ld mismatches\\n\", \
         calls, mismatches);\n    return mismatches != 0;\n}}\n",
        specs.len()
    ));
    c
}

/// Link `obj` with `driver` using the host `cc` and run it; returns the exit
/// code and the program's standard output.
fn link_run_capture(tag: &str, obj: &[u8], driver: &str) -> (i32, String) {
    let dir = std::env::temp_dir().join(format!("trust_cg_{tag}_{}_e2e", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let obj_path = dir.join(format!("{tag}.o"));
    let drv_path = dir.join("driver.c");
    let bin_path = dir.join(format!("{tag}_bin"));
    fs::write(&obj_path, obj).unwrap();
    fs::write(&drv_path, driver).unwrap();
    let link = Command::new("cc")
        .args(["-O1", "-w"])
        .arg(&drv_path)
        .arg(&obj_path)
        .arg("-o")
        .arg(&bin_path)
        .args(native_host::c_math_library_args())
        .output()
        .expect("cc");
    assert!(
        link.status.success(),
        "link {tag}:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(&bin_path).output().unwrap();
    let _ = fs::remove_dir_all(&dir);
    (
        run.status.code().unwrap_or(-1),
        String::from_utf8_lossy(&run.stdout).into_owned(),
    )
}

/// Instruction-word facts of one compiled function's code section, decoded
/// here from the Arm ARM encodings (not by the compiler's decoder).
#[derive(Debug, Default)]
struct WordFacts {
    /// `BR Xn`.
    br: usize,
    /// `ADR Xd, label`.
    adr: usize,
    /// `LDRSW Xt, [Xn, Xm, LSL #2]` (register offset, scaled).
    ldrsw_scaled: usize,
    /// `B.cond` with a condition other than EQ/NE.
    ordered_bcond: usize,
}

fn word_facts(words: &[u32]) -> WordFacts {
    let mut facts = WordFacts::default();
    for &w in words {
        if w & 0xFFFF_FC1F == 0xD61F_0000 {
            facts.br += 1;
        }
        if w & 0x9F00_0000 == 0x1000_0000 {
            facts.adr += 1;
        }
        // LDRSW (register): 10 111 0 00 10 1 Rm option S 10 Rn Rt with
        // option = 011 (LSL) and S = 1 (scaled by 4).
        if w & 0xFFE0_FC00 == 0xB8A0_7800 {
            facts.ldrsw_scaled += 1;
        }
        if w & 0xFF00_0010 == 0x5400_0000 && w & 0xF > 1 {
            facts.ordered_bcond += 1;
        }
    }
    facts
}

/// The strategy is visible in the code: a jump table needs ADR, the scaled
/// LDRSW and BR; the compare strategies have no BR and no ADR, and at O0 a
/// binary search's inner nodes branch on an ordered condition while a linear
/// chain branches only on EQ/NE.
fn assert_strategy_words(spec: &SwitchSpec, opt: OptLevel, facts: &WordFacts) {
    let context = format!("{} at {opt:?}: {facts:?}", spec.name);
    match spec.strategy {
        Strategy::JumpTable => {
            assert!(facts.br >= 1, "jump table without BR: {context}");
            assert!(facts.adr >= 1, "jump table without ADR: {context}");
            assert!(
                facts.ldrsw_scaled >= 1,
                "jump table without LDRSW [Xn, Xm, LSL #2]: {context}"
            );
        }
        Strategy::BinarySearch | Strategy::LinearScan => {
            assert_eq!(facts.br, 0, "compare strategy with a BR: {context}");
            assert_eq!(facts.adr, 0, "compare strategy with an ADR: {context}");
            if opt == OptLevel::O0 {
                if spec.strategy == Strategy::BinarySearch {
                    assert!(
                        facts.ordered_bcond >= 1,
                        "binary search without an ordered branch: {context}"
                    );
                } else {
                    assert_eq!(
                        facts.ordered_bcond, 0,
                        "linear chain with an ordered branch: {context}"
                    );
                }
            }
        }
    }
}

/// binutils `objdump -d` of an ELF object: each function symbol's mnemonics.
fn objdump_functions(obj: &[u8], tag: &str) -> std::collections::BTreeMap<String, Vec<String>> {
    let dir = std::env::temp_dir().join(format!("trust_cg_{tag}_{}_objdump", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{tag}.o"));
    fs::write(&path, obj).unwrap();
    let out = Command::new("objdump")
        .args(["-d", "--no-show-raw-insn"])
        .arg(&path)
        .output()
        .expect("binutils objdump is required on the Linux floor host");
    let _ = fs::remove_dir_all(&dir);
    assert!(
        out.status.success(),
        "objdump: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let text = String::from_utf8(out.stdout).unwrap();
    let mut functions = std::collections::BTreeMap::new();
    let mut current: Option<String> = None;
    for line in text.lines() {
        if let Some(rest) = line.strip_suffix(">:")
            && let Some(start) = rest.find(" <")
        {
            let name = rest[start + 2..].to_string();
            functions.insert(name.clone(), Vec::new());
            current = Some(name);
            continue;
        }
        if let Some(name) = &current
            && let Some((_, insn)) = line.split_once(":\t")
        {
            let mnemonic = insn.split_whitespace().next().unwrap_or("").to_string();
            functions.get_mut(name).unwrap().push(mnemonic);
        }
    }
    functions
}

/// Every matrix function agrees with the C `switch` oracle at O0-O3, compiles
/// to the strategy the matrix names, and (Linux GNU) binutils reads the same
/// strategy back from the linked object.
#[test]
fn e2e_aarch64_switch_selector_matrix_matches_c_at_every_opt_level() {
    if !can_link_and_run_aarch64_native() {
        eprintln!("SKIP: needs an AArch64 Linux GNU or macOS host");
        return;
    }
    let specs = switch_matrix();
    let all: Vec<&SwitchSpec> = specs.iter().collect();
    for strategy in [
        Strategy::JumpTable,
        Strategy::BinarySearch,
        Strategy::LinearScan,
    ] {
        for ty in [Ty::I8, Ty::I16, Ty::I32, Ty::I64] {
            assert!(
                specs
                    .iter()
                    .any(|s| s.strategy == strategy && s.selector_ty == ty),
                "matrix lacks a {strategy:?} over {ty:?}"
            );
        }
    }
    let module = build_matrix_module(&all);
    let driver = matrix_driver(&all, native_host::LINUX_GNU);
    retain("switch_matrix/driver.c", driver.as_bytes());
    let mut checked_calls = 0u64;
    for opt in ALL_OPT_LEVELS {
        let obj = compile_at(&module, opt)
            .unwrap_or_else(|error| panic!("switch matrix must compile at {opt:?}: {error}"));
        native_host::assert_native_object(&obj);
        retain(&format!("switch_matrix/matrix_{opt:?}.o"), &obj);
        let (code, stdout) = link_run_capture(&format!("switch_matrix_{opt:?}"), &obj, &driver);
        assert_eq!(code, 0, "switch matrix mismatch at {opt:?}:\n{stdout}");
        let calls: u64 = stdout
            .split("switch matrix: ")
            .nth(1)
            .and_then(|rest| rest.split_whitespace().next())
            .and_then(|n| n.parse().ok())
            .unwrap_or_else(|| panic!("no call count at {opt:?}:\n{stdout}"));
        assert!(calls > 1_000_000, "vacuous matrix run at {opt:?}: {stdout}");
        checked_calls += calls;
        if native_host::LINUX_GNU {
            let functions = objdump_functions(&obj, &format!("switch_matrix_{opt:?}"));
            for spec in &specs {
                let body = functions
                    .get(&spec.name)
                    .unwrap_or_else(|| panic!("objdump has no <{}> at {opt:?}", spec.name));
                let has = |m: &str| body.iter().any(|x| x == m);
                match spec.strategy {
                    Strategy::JumpTable => assert!(
                        has("br") && has("adr") && has("ldrsw"),
                        "objdump: {} at {opt:?} is not a jump table: {body:?}",
                        spec.name
                    ),
                    _ => assert!(
                        !has("br") && !has("adr"),
                        "objdump: {} at {opt:?} has an indirect branch: {body:?}",
                        spec.name
                    ),
                }
            }
        }
        for spec in &specs {
            let single = build_matrix_module(&[spec]);
            let obj = compile_at(&single, opt)
                .unwrap_or_else(|error| panic!("{} must compile at {opt:?}: {error}", spec.name));
            let facts = word_facts(&native_host::text_words(&obj));
            assert_strategy_words(spec, opt, &facts);
        }
    }
    println!(
        "switch matrix on {}: {} functions x O0-O3, {checked_calls} checked calls",
        native_host::HOST,
        specs.len()
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
