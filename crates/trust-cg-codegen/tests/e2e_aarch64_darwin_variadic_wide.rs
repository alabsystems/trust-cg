// trust-cg-codegen/tests/e2e_aarch64_darwin_variadic_wide.rs
//
// DarwinPCS anonymous 16-byte variadic arguments against a clang oracle.
//
// Apple arm64 passes every anonymous argument on the stack. Eight-byte
// scalars take 8-aligned slots, but a 16-byte-aligned anonymous argument --
// `__int128` and a 128-bit vector -- starts at the next 16-aligned offset
// (LLVM `CC_AArch64_DarwinPCS_VarArg`: split i128 is `CCAssignToStack<8, 16>`,
// 128-bit vectors are `CCAssignToStack<16, 16>`; clang's `va_arg` for such a
// type rounds the `char *` cursor up to 16). clang's own caller for
// `take(1, int64_t a, __int128 w)` stores `a` at `[sp]` and `w` at `[sp, #16]`.
// After one 8-byte vararg the two rules disagree; after two they coincide, so
// both shapes are exercised, each followed by a trailing 8-byte vararg that
// pins the next-slot arithmetic. Aggregates pin the refinement: a
// non-homogeneous 16-aligned `struct { __int128 }` is coerced to i128 and
// starts 16-aligned, while an 8-aligned `struct { int64_t a, b; }` and a
// 24-byte `struct { double a, b, c; }` HFA stay inline and 8-aligned.
//
// trust-cg emits the variadic CALLER (loading each value through a pointer so
// fixed-argument register rules cannot mask a placement defect); clang
// compiles the variadic callee and the checking driver. Every received value
// must agree bit-for-bit at O0-O3.
//
// The anonymous tail also starts after the last packed FIXED stack byte: with
// two narrow fixed `int32_t` stack arguments at `[sp]` and `[sp, #4]`, clang
// puts the first anonymous `int64_t` at `[sp, #8]`, not one slot later.
//
// Two anonymous shapes have no inline placement and must be refused by name:
// a >16-byte non-homogeneous aggregate (clang passes a pointer to a caller
// copy) and a short-vector HVA such as `struct { int32x4_t v; }`, for which
// clang's own caller (8-aligned block) and `va_arg` (16-aligned read) disagree.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::fs;
use std::process::Command;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::{
    Block, BlockId, Constant, Endianness, FieldDef, FuncId, FuncTy, Function, Inst, InstrNode,
    Linkage, Module, StructDef, StructId, StructPassingPolicy, StructRepr, TargetInfo, Ty, ValueId,
};

const TRIPLE: &str = "aarch64-apple-darwin";

fn v4i32() -> Ty {
    Ty::Vector(Box::new(Ty::I32), 4)
}

fn define_struct(module: &mut Module, name: &str, fields: &[Ty], size: u64, align: u64) -> Ty {
    let id = StructId::new(module.structs.len() as u32);
    let mut offset = 0;
    module.structs.push(StructDef {
        origin: None,
        id,
        name: name.into(),
        size: Some(size),
        align: Some(align),
        repr: StructRepr::C,
        fields: fields
            .iter()
            .enumerate()
            .map(|(index, ty)| {
                let field_size = match ty {
                    Ty::I64 | Ty::F64 => 8,
                    _ => 16,
                };
                let field = FieldDef {
                    name: format!("f{index}"),
                    ty: ty.clone(),
                    offset: Some(offset),
                };
                offset += field_size;
                field
            })
            .collect(),
    });
    Ty::Struct(id)
}

fn declare_variadic(module: &mut Module, name: &str) -> FuncId {
    let ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![],
            abi: None,
            is_vararg: true,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, ty, BlockId::new(0));
    function.linkage = Linkage::External;
    function.blocks = Vec::new();
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    id
}

/// Define `name(ptr...) -> void` that loads each pointee with the matching
/// type and forwards the loaded values, after a fixed `int count`, to the
/// variadic `callee`.
fn define_forwarder(module: &mut Module, name: &str, callee: FuncId, loads: &[Ty], count: i64) {
    let ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr; loads.len()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, ty, BlockId::new(0));
    let mut body = Vec::new();
    let mut args = Vec::new();
    let count_value = ValueId::new(100);
    body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(count.into()),
        })
        .with_result(count_value),
    );
    args.push(count_value);
    for (index, load_ty) in loads.iter().enumerate() {
        let loaded = ValueId::new(200 + index as u32);
        let align = match load_ty {
            Ty::I64 => 8,
            Ty::Struct(id) => module.structs[id.index() as usize]
                .align
                .expect("fixture structs carry an explicit alignment"),
            _ => 16,
        };
        body.push(
            InstrNode::new(Inst::Load {
                ty: load_ty.clone(),
                ptr: ValueId::new(index as u32),
                volatile: false,
                align: Some(align),
            })
            .with_result(loaded),
        );
        args.push(loaded);
    }
    body.push(InstrNode::new(Inst::Call { callee, args }));
    body.push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: (0..loads.len())
            .map(|index| (ValueId::new(index as u32), Ty::Ptr))
            .collect(),
        body,
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn build_module() -> Module {
    let mut module = Module::new("darwin_variadic_wide");
    module.target_info = Some(TargetInfo {
        triple: TRIPLE.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    let take_i128_1 = declare_variadic(&mut module, "take_i128_1");
    let take_i128_2 = declare_variadic(&mut module, "take_i128_2");
    let take_v_1 = declare_variadic(&mut module, "take_v_1");
    let take_v_2 = declare_variadic(&mut module, "take_v_2");
    let take_s16_1 = declare_variadic(&mut module, "take_s16_1");
    let take_d3_1 = declare_variadic(&mut module, "take_d3_1");
    let take_p16_1 = declare_variadic(&mut module, "take_p16_1");
    let s16 = define_struct(&mut module, "S16", &[Ty::I128], 16, 16);
    let d3 = define_struct(&mut module, "D3", &[Ty::F64, Ty::F64, Ty::F64], 24, 8);
    let p16 = define_struct(&mut module, "P16", &[Ty::I64, Ty::I64], 16, 8);
    define_forwarder(
        &mut module,
        "cg_i128_1",
        take_i128_1,
        &[Ty::I64, Ty::I128, Ty::I64],
        1,
    );
    define_forwarder(
        &mut module,
        "cg_i128_2",
        take_i128_2,
        &[Ty::I64, Ty::I64, Ty::I128, Ty::I64],
        2,
    );
    define_forwarder(
        &mut module,
        "cg_v_1",
        take_v_1,
        &[Ty::I64, v4i32(), Ty::I64],
        1,
    );
    define_forwarder(
        &mut module,
        "cg_v_2",
        take_v_2,
        &[Ty::I64, Ty::I64, v4i32(), Ty::I64],
        2,
    );
    define_forwarder(
        &mut module,
        "cg_s16_1",
        take_s16_1,
        &[Ty::I64, s16, Ty::I64],
        1,
    );
    define_forwarder(
        &mut module,
        "cg_d3_1",
        take_d3_1,
        &[Ty::I64, d3, Ty::I64],
        1,
    );
    define_forwarder(
        &mut module,
        "cg_p16_1",
        take_p16_1,
        &[Ty::I64, p16, Ty::I64],
        1,
    );
    module
}

const DRIVER: &str = r#"
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef int32_t v4i32 __attribute__((vector_size(16)));
struct S16 { __int128 x; };
struct D3 { double a, b, c; };
struct P16 { int64_t a, b; };

static int seen_n;
static int64_t seen_a, seen_b, seen_c;
static __int128 seen_w;
static v4i32 seen_v;
static struct S16 seen_s16;
static struct D3 seen_d3;
static struct P16 seen_p16;

static void reset(void) {
    seen_n = -1; seen_a = seen_b = seen_c = 0; seen_w = 0;
    memset(&seen_v, 0, sizeof seen_v);
    memset(&seen_s16, 0, sizeof seen_s16);
    memset(&seen_d3, 0, sizeof seen_d3);
    memset(&seen_p16, 0, sizeof seen_p16);
}

void take_i128_1(int n, ...) {
    va_list ap; va_start(ap, n);
    seen_n = n;
    seen_a = va_arg(ap, int64_t);
    seen_w = va_arg(ap, __int128);
    seen_c = va_arg(ap, int64_t);
    va_end(ap);
}
void take_i128_2(int n, ...) {
    va_list ap; va_start(ap, n);
    seen_n = n;
    seen_a = va_arg(ap, int64_t);
    seen_b = va_arg(ap, int64_t);
    seen_w = va_arg(ap, __int128);
    seen_c = va_arg(ap, int64_t);
    va_end(ap);
}
void take_v_1(int n, ...) {
    va_list ap; va_start(ap, n);
    seen_n = n;
    seen_a = va_arg(ap, int64_t);
    seen_v = va_arg(ap, v4i32);
    seen_c = va_arg(ap, int64_t);
    va_end(ap);
}
void take_v_2(int n, ...) {
    va_list ap; va_start(ap, n);
    seen_n = n;
    seen_a = va_arg(ap, int64_t);
    seen_b = va_arg(ap, int64_t);
    seen_v = va_arg(ap, v4i32);
    seen_c = va_arg(ap, int64_t);
    va_end(ap);
}

void take_s16_1(int n, ...) {
    va_list ap; va_start(ap, n);
    seen_n = n;
    seen_a = va_arg(ap, int64_t);
    seen_s16 = va_arg(ap, struct S16);
    seen_c = va_arg(ap, int64_t);
    va_end(ap);
}
void take_d3_1(int n, ...) {
    va_list ap; va_start(ap, n);
    seen_n = n;
    seen_a = va_arg(ap, int64_t);
    seen_d3 = va_arg(ap, struct D3);
    seen_c = va_arg(ap, int64_t);
    va_end(ap);
}
void take_p16_1(int n, ...) {
    va_list ap; va_start(ap, n);
    seen_n = n;
    seen_a = va_arg(ap, int64_t);
    seen_p16 = va_arg(ap, struct P16);
    seen_c = va_arg(ap, int64_t);
    va_end(ap);
}

extern void cg_s16_1(const int64_t *, const struct S16 *, const int64_t *);
extern void cg_d3_1(const int64_t *, const struct D3 *, const int64_t *);
extern void cg_p16_1(const int64_t *, const struct P16 *, const int64_t *);
extern void cg_i128_1(const int64_t *, const __int128 *, const int64_t *);
extern void cg_i128_2(const int64_t *, const int64_t *, const __int128 *, const int64_t *);
extern void cg_v_1(const int64_t *, const v4i32 *, const int64_t *);
extern void cg_v_2(const int64_t *, const int64_t *, const v4i32 *, const int64_t *);

static int same_v(v4i32 x, v4i32 y) { return memcmp(&x, &y, sizeof x) == 0; }

int main(void) {
    const int64_t a = 0x1111222233334444LL;
    const int64_t b = -0x5555666677778888LL;
    const int64_t c = 0x0123456789abcdefLL;
    const __int128 w = ((__int128)0x7edcba9876543210LL << 64) | (__int128)0x0f1e2d3c4b5a6978ULL;
    const v4i32 v = {0x10203040, -0x50607080, 0x0badf00d, -1};

    reset(); cg_i128_1(&a, &w, &c);
    if (seen_n != 1 || seen_a != a || seen_w != w || seen_c != c) {
        printf("i128 after one 8-byte vararg: n=%d a_ok=%d w_ok=%d c_ok=%d\n",
               seen_n, seen_a == a, seen_w == w, seen_c == c);
        return 1;
    }
    reset(); cg_i128_2(&a, &b, &w, &c);
    if (seen_n != 2 || seen_a != a || seen_b != b || seen_w != w || seen_c != c) {
        printf("i128 after two 8-byte varargs: n=%d a_ok=%d b_ok=%d w_ok=%d c_ok=%d\n",
               seen_n, seen_a == a, seen_b == b, seen_w == w, seen_c == c);
        return 2;
    }
    reset(); cg_v_1(&a, &v, &c);
    if (seen_n != 1 || seen_a != a || !same_v(seen_v, v) || seen_c != c) {
        printf("v128 after one 8-byte vararg: n=%d a_ok=%d v_ok=%d c_ok=%d\n",
               seen_n, seen_a == a, same_v(seen_v, v), seen_c == c);
        return 3;
    }
    reset(); cg_v_2(&a, &b, &v, &c);
    if (seen_n != 2 || seen_a != a || seen_b != b || !same_v(seen_v, v) || seen_c != c) {
        printf("v128 after two 8-byte varargs: n=%d a_ok=%d b_ok=%d v_ok=%d c_ok=%d\n",
               seen_n, seen_a == a, seen_b == b, same_v(seen_v, v), seen_c == c);
        return 4;
    }
    const struct S16 s16 = {w};
    const struct D3 d3 = {1.25, -2.5, 3.75};
    const struct P16 p16 = {b, a};
    reset(); cg_s16_1(&a, &s16, &c);
    if (seen_n != 1 || seen_a != a || memcmp(&seen_s16, &s16, sizeof s16) != 0 || seen_c != c) {
        printf("struct{__int128} after one 8-byte vararg: n=%d a_ok=%d s_ok=%d c_ok=%d\n",
               seen_n, seen_a == a, memcmp(&seen_s16, &s16, sizeof s16) == 0, seen_c == c);
        return 5;
    }
    reset(); cg_d3_1(&a, &d3, &c);
    if (seen_n != 1 || seen_a != a || memcmp(&seen_d3, &d3, sizeof d3) != 0 || seen_c != c) {
        printf("struct{double a,b,c} after one 8-byte vararg: n=%d a_ok=%d s_ok=%d c_ok=%d\n",
               seen_n, seen_a == a, memcmp(&seen_d3, &d3, sizeof d3) == 0, seen_c == c);
        return 6;
    }
    reset(); cg_p16_1(&a, &p16, &c);
    if (seen_n != 1 || seen_a != a || memcmp(&seen_p16, &p16, sizeof p16) != 0 || seen_c != c) {
        printf("struct{int64_t,int64_t} after one 8-byte vararg: n=%d a_ok=%d s_ok=%d c_ok=%d\n",
               seen_n, seen_a == a, memcmp(&seen_p16, &p16, sizeof p16) == 0, seen_c == c);
        return 7;
    }
    printf("DarwinPCS 16-byte anonymous varargs agree with clang\n");
    return 0;
}
"#;

fn compile_at(module: &Module, opt_level: OptLevel) -> Vec<u8> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(TRIPLE).expect("Darwin triple parses"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .unwrap_or_else(|error| {
        panic!("Darwin wide-vararg caller must compile at {opt_level:?}: {error:?}")
    })
    .object_code
}

fn link_and_run(tag: &str, object: &[u8], driver: &str) -> (i32, String) {
    let dir = fresh_dir::create(&format!("trust-cg-darwin-vararg-wide-{tag}-"));
    let object_path = dir.join("module.o");
    let driver_path = dir.join("driver.c");
    let binary_path = dir.join("driver");
    fs::write(&object_path, object).expect("write object");
    fs::write(&driver_path, driver).expect("write driver");
    // An optimized oracle: an O0 callee could spill and re-read in ways that
    // mask a caller placement defect.
    let link = Command::new("cc")
        .arg("-O2")
        .arg(&driver_path)
        .arg(&object_path)
        .arg("-o")
        .arg(&binary_path)
        .output()
        .expect("cc is required on the macOS aarch64 host");
    assert!(
        link.status.success(),
        "{tag}: link failed; files={dir:?}\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(&binary_path)
        .output()
        .expect("run the linked driver");
    let stdout = String::from_utf8_lossy(&run.stdout).into_owned();
    let code = run.status.code().unwrap_or(-1);
    if code == 0 {
        let _ = fs::remove_dir_all(&dir);
    }
    (code, stdout)
}

#[test]
fn darwin_sixteen_byte_anonymous_varargs_match_clang_o0_to_o3() {
    let module = build_module();
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let object = compile_at(&module, opt_level);
        assert_eq!(
            &object[..4],
            &[0xcf, 0xfa, 0xed, 0xfe],
            "the Darwin target must emit a Mach-O object"
        );
        let (code, stdout) = link_and_run(&format!("{opt_level:?}"), &object, DRIVER);
        assert_eq!(
            code, 0,
            "DarwinPCS wide vararg placement diverged from clang at {opt_level:?}: {stdout}"
        );
    }
}

#[test]
fn darwin_unplaceable_anonymous_aggregates_fail_closed_by_name() {
    for (label, fields, size, align) in [
        ("short-vector HVA", vec![v4i32()], 16, 16),
        (
            "by-reference aggregate",
            vec![Ty::I64, Ty::I64, Ty::I64],
            24,
            8,
        ),
    ] {
        let mut module = Module::new("darwin_variadic_refused");
        module.target_info = build_module().target_info;
        let take = declare_variadic(&mut module, "take_refused");
        let aggregate = define_struct(&mut module, "Refused", &fields, size, align);
        define_forwarder(
            &mut module,
            "cg_refused",
            take,
            &[Ty::I64, aggregate, Ty::I64],
            1,
        );
        for opt_level in [OptLevel::O0, OptLevel::O2] {
            let error = Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level,
                    ..CompilerConfig::default()
                },
                TargetSpec::parse(TRIPLE).expect("Darwin triple parses"),
            )
            .with_codegen_license(permit_unlicensed())
            .compile(&module)
            .map(|_| ())
            .expect_err("an unplaceable Darwin anonymous aggregate must not compile");
            let message = format!("{error:?}");
            assert!(
                message.contains("[TCG-VARARG-ABI]"),
                "{label} at {opt_level:?}: {message}"
            );
        }
    }
}

/// `take_narrow_fixed(int64_t r0..r7, int32_t s0, int32_t s1, ...)`: the two
/// narrow fixed arguments overflow onto the stack, where DarwinPCS packs them
/// at their natural size (`s0` at `[sp]`, `s1` at `[sp, #4]`). The anonymous
/// tail then starts at the next 8-aligned offset after the LAST FIXED BYTE
/// (`[sp, #8]`), not after an 8-byte slot per fixed argument.
fn build_narrow_fixed_module() -> Module {
    let mut module = Module::new("darwin_variadic_after_narrow_fixed");
    module.target_info = build_module().target_info;
    let mut fixed = vec![Ty::I64; 8];
    fixed.extend([Ty::I32, Ty::I32]);
    let callee_ty = module
        .add_func_type(FuncTy {
            params: fixed,
            returns: vec![],
            abi: None,
            is_vararg: true,
        })
        .expect("Module::add_func_type: test fixture");
    let callee = FuncId::new(module.functions.len() as u32);
    let mut declaration = Function::new(callee, "take_narrow_fixed", callee_ty, BlockId::new(0));
    declaration.linkage = Linkage::External;
    declaration.blocks = Vec::new();
    module
        .try_add_function(declaration)
        .expect("Module::try_add_function: test fixture");

    // cg_narrow_fixed(const int32_t *s0, const int32_t *s1, const int64_t *a,
    //                 const __int128 *w, const int64_t *c)
    let loads = [
        (Ty::I32, 4),
        (Ty::I32, 4),
        (Ty::I64, 8),
        (Ty::I128, 16),
        (Ty::I64, 8),
    ];
    let ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr; loads.len()],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, "cg_narrow_fixed", ty, BlockId::new(0));
    let mut body = Vec::new();
    let mut args = Vec::new();
    for register in 0..8u32 {
        let value = ValueId::new(100 + register);
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(i128::from(register + 1)),
            })
            .with_result(value),
        );
        args.push(value);
    }
    for (index, (load_ty, align)) in loads.iter().enumerate() {
        let loaded = ValueId::new(200 + index as u32);
        body.push(
            InstrNode::new(Inst::Load {
                ty: load_ty.clone(),
                ptr: ValueId::new(index as u32),
                volatile: false,
                align: Some(*align),
            })
            .with_result(loaded),
        );
        args.push(loaded);
    }
    body.push(InstrNode::new(Inst::Call { callee, args }));
    body.push(InstrNode::new(Inst::Return { values: vec![] }));
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: (0..loads.len())
            .map(|index| (ValueId::new(index as u32), Ty::Ptr))
            .collect(),
        body,
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

const DRIVER_NARROW_FIXED: &str = r#"
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>

static int64_t seen_sum, seen_a, seen_c;
static int32_t seen_s0, seen_s1;
static __int128 seen_w;

void take_narrow_fixed(int64_t r0, int64_t r1, int64_t r2, int64_t r3, int64_t r4,
                       int64_t r5, int64_t r6, int64_t r7, int32_t s0, int32_t s1, ...) {
    va_list ap; va_start(ap, s1);
    seen_sum = r0 + r1 + r2 + r3 + r4 + r5 + r6 + r7;
    seen_s0 = s0;
    seen_s1 = s1;
    seen_a = va_arg(ap, int64_t);
    seen_w = va_arg(ap, __int128);
    seen_c = va_arg(ap, int64_t);
    va_end(ap);
}

extern void cg_narrow_fixed(const int32_t *, const int32_t *, const int64_t *,
                            const __int128 *, const int64_t *);

int main(void) {
    const int32_t s0 = -0x12345678, s1 = 0x0badcafe;
    const int64_t a = 0x1111222233334444LL;
    const int64_t c = 0x0123456789abcdefLL;
    const __int128 w = ((__int128)0x7edcba9876543210LL << 64) | (__int128)0x0f1e2d3c4b5a6978ULL;
    cg_narrow_fixed(&s0, &s1, &a, &w, &c);
    if (seen_sum != 36 || seen_s0 != s0 || seen_s1 != s1 || seen_a != a || seen_w != w
        || seen_c != c) {
        printf("anonymous tail after packed narrow fixed stack args: sum=%lld s0_ok=%d "
               "s1_ok=%d a_ok=%d w_ok=%d c_ok=%d\n",
               (long long)seen_sum, seen_s0 == s0, seen_s1 == s1, seen_a == a,
               seen_w == w, seen_c == c);
        return 1;
    }
    printf("DarwinPCS anonymous tail after packed narrow fixed args agrees with clang\n");
    return 0;
}
"#;

/// The anonymous tail's start offset follows the packed narrow FIXED stack
/// arguments: clang puts `s0` at `[sp]`, `s1` at `[sp, #4]`, the first
/// anonymous `int64_t` at `[sp, #8]`, the `__int128` at `[sp, #16]` and the
/// trailing `int64_t` at `[sp, #32]`. Rounding each fixed stack argument to
/// its own 8-byte slot before the tail would start it at `[sp, #16]`.
#[test]
fn darwin_anonymous_tail_after_packed_narrow_fixed_stack_args_matches_clang() {
    let module = build_narrow_fixed_module();
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let object = compile_at(&module, opt_level);
        let (code, stdout) = link_and_run(
            &format!("narrow-fixed-{opt_level:?}"),
            &object,
            DRIVER_NARROW_FIXED,
        );
        assert_eq!(
            code, 0,
            "DarwinPCS anonymous tail after packed narrow fixed args diverged from clang at \
             {opt_level:?}: {stdout}"
        );
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
