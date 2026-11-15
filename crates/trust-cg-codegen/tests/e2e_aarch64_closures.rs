// trust-cg-codegen/tests/e2e_aarch64_closures.rs
//
// Ledger L05-P4: first-class closure values on aarch64-apple-darwin.
//
// trust-ir (G18-2) states a `Ty::Closure` value as N explicit typed captures
// whose `func` lane has no runtime layout, introduces it with
// `Const { Constant::Closure { func, captures } }` (+ per-capture
// `InsertField`), projects a capture with `ExtractField`, and ELIMINATES it
// with `CallIndirect` over the closure callee: the edge declares the closure's
// APPARENT signature (`ClosureTy::func`) and the captured environment is
// supplied as LEADING arguments, spread in capture order, so the target's
// physical signature is `captures ++ apparent params -> apparent returns`.
// Application is BY VALUE (ratified 2026-09-19): a by-reference capture is a
// pointer-typed capture slot.
//
// trust-cg materializes a closure literal as the struct of its captures (the
// layout `Ty::Closure` already lowers to) and lowers each application as the
// direct call `target(captures.., args..)` to the closure's STATIC code
// identity, read off the defining literal through `Copy`/`InsertField`. A
// closure whose code identity is not statically visible is refused by name.
//
// Every positive case executes natively at O0-O3 against TWO independent
// oracles: trust-ir's reference interpreter (which evaluates the same module,
// closure application included) and a C model in the driver. The C driver
// only reports success when native, interpreter and C model agree. The
// negative cases pin the named refusals for what stays outside the lowering.
//
// Since WS7.3 every ingestion entry refuses what trust-ir's codegen admission
// refuses, and its lowerability layer refuses closure application
// (`UnlowerableForCodegen`, F-055: `ClosureTy` has no layout or capture mode,
// closed by trust-ir WS3.13). Until trust-ir admits it, each positive case
// still checks its interpreter oracle and then pins that named refusal at
// every level instead of executing (`run_native_at_every_level`).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::pipeline::OptLevel;
use trust_ir::constant::Constant;
use trust_ir::interpret::{InterpretValue, Interpreter};
use trust_ir::{ClosureTy, Module, Ty};
use trust_ir_build::builder::ModuleBuilder;

#[path = "common/aarch64_native.rs"]
mod aarch64_native;

#[path = "common/admission_expect.rs"]
mod admission_expect;

const OPTS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// Run `name(args)` under trust-ir's reference interpreter and return its
/// single integer result.
fn interpret_int(
    module: &Module,
    name: &str,
    args: Vec<InterpretValue>,
) -> trust_ir::interpret::InterpretInt {
    let function = module
        .function_by_name(name)
        .unwrap_or_else(|| panic!("fixture defines @{name}"));
    let outcome = Interpreter::with_module(module)
        .execute_function(function, args)
        .unwrap_or_else(|error| panic!("interpreter oracle for @{name}: {error:?}"));
    let [ret] = outcome.returns.as_slice() else {
        panic!("@{name}: expected one result, got {:?}", outcome.returns)
    };
    ret.as_int()
        .unwrap_or_else(|| panic!("@{name}: integer result expected"))
}

/// Signed view of an interpreter result (for `i64`-returning fixtures).
fn interpret(module: &Module, name: &str, args: Vec<InterpretValue>) -> i128 {
    interpret_int(module, name, args).as_signed()
}

/// Unsigned view of an interpreter result (for `u64`-returning fixtures).
fn interpret_u64(module: &Module, name: &str, args: Vec<InterpretValue>) -> u64 {
    u64::try_from(interpret_int(module, name, args).as_unsigned()).expect("u64 result")
}

fn int(ty: Ty, value: i128) -> InterpretValue {
    InterpretValue::int(ty, value).expect("interpreter argument")
}

/// Compile at every opt level and run the C driver against each object.
/// Returns false when the host cannot execute AArch64 natively (the harness
/// prints its SKIP line).
///
/// F-055 / WS3.13: trust-ir's codegen lowerability layer refuses every
/// `CallIndirect` over a `Ty::Closure` callee (`UnlowerableForCodegen`:
/// `ClosureTy` has no layout or capture mode yet), and since WS7.3 every
/// trust-cg ingestion entry refuses what that layer refuses. While trust-ir
/// refuses the module, this asserts that named refusal at every level and
/// returns false; the day trust-ir admits closure application, the native
/// differential runs again unchanged.
fn run_native_at_every_level(tag: &str, module: &Module, driver: &str) -> bool {
    let pinned = aarch64_native::pinned(module);
    let license = aarch64_native::permit_unlicensed();
    if let Some((variant, text)) = admission_expect::first_finding(&pinned, &license) {
        assert!(
            variant == "UnlowerableForCodegen" && text.contains("Ty::Closure"),
            "{tag}: trust-ir refuses the module for a reason other than closure \
             application: {variant}: {text}"
        );
        for opt in OPTS {
            let error = aarch64_native::try_compile(module, opt)
                .err()
                .unwrap_or_else(|| panic!("{tag}: trust-ir refuses it, so must trust-cg"));
            assert!(
                error.contains("UnlowerableForCodegen") && error.contains("Ty::Closure"),
                "{tag} at {opt:?}: {error}"
            );
        }
        eprintln!("REFUSED {tag}: closure application is outside trust-ir's lowering subset");
        return false;
    }
    for opt in OPTS {
        let object = aarch64_native::compile(module, opt);
        let Some(code) = aarch64_native::link_run(&format!("{tag}_{opt:?}"), &object, driver)
        else {
            return false;
        };
        assert_eq!(code, 0, "{tag}: native driver failed at {opt:?}");
    }
    true
}

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

/// Zero captures: `closure.0 = { func: (i64)->(i64), captures: [] }` applied to
/// `add_ten`. The environment is empty; the application is the direct call.
fn build_zero_captures() -> Module {
    let mut mb = ModuleBuilder::new("closure_zero_captures");
    let apparent = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let clos_id = mb.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![],
    });
    let clos = Ty::Closure(clos_id);

    let add_ten = {
        let mut fb = mb.function("add_ten", apparent);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I64);
        fb.switch_to_block(e);
        let ten = fb.iconst(Ty::I64, 10);
        let r = fb.add(Ty::I64, x, ten);
        fb.ret(vec![r]);
        fb.build()
    };
    {
        let mut fb = mb.function("apply0", apparent);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I64);
        fb.switch_to_block(e);
        let c = fb.const_value(
            clos,
            Constant::Closure {
                func: add_ten,
                captures: vec![],
            },
        );
        let r = fb.call_indirect(c, apparent, vec![x]);
        fb.ret(vec![r]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

const ZERO_CAPTURES_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
extern int64_t apply0(int64_t);
static int64_t model(int64_t x) { return x + 10; }
int main(void) {
    const int64_t xs[] = {0, 5, -3, 1000000007LL, -9223372036854775807LL - 1};
    const int64_t interp[] = {INTERP_0, INTERP_1, INTERP_2, INTERP_3, INTERP_4};
    for (int i = 0; i < 5; i++) {
        int64_t got = apply0(xs[i]);
        int64_t want = model(xs[i]);
        if (got != want || got != interp[i]) {
            printf("apply0(%lld) native=%lld C=%lld interpreter=%lld\n",
                   (long long)xs[i], (long long)got, (long long)want, (long long)interp[i]);
            return 1 + i;
        }
    }
    return 0;
}
"#;

#[test]
fn closure_with_zero_captures_applies_natively_at_every_level() {
    let module = build_zero_captures();
    let xs: [i64; 5] = [0, 5, -3, 1_000_000_007, i64::MIN];
    let mut driver = ZERO_CAPTURES_DRIVER.to_string();
    for (i, x) in xs.iter().enumerate() {
        let want = interpret(&module, "apply0", vec![int(Ty::I64, i128::from(*x))]);
        assert_eq!(
            want,
            i128::from(x.wrapping_add(10)),
            "interpreter oracle apply0({x})"
        );
        driver = driver.replace(&format!("INTERP_{i}"), &format!("{want}LL"));
    }
    run_native_at_every_level("closure_zero", &module, &driver);
}

/// One `U64` capture, applied twice: the ratified by-value program (a counter
/// bumped twice reported as `first * 10 + second`). Both applications see the
/// seed, so the answer is 11, not 12. `program_seed` rebuilds capture 0 with
/// `InsertField` from a runtime argument before applying.
fn build_one_capture_by_value() -> Module {
    let mut mb = ModuleBuilder::new("closure_one_capture_by_value");
    let apparent = mb.add_func_type(vec![], vec![Ty::U64]);
    let physical = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let unary = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let clos_id = mb.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![Ty::U64],
    });
    let clos = Ty::Closure(clos_id);

    let bump = {
        let mut fb = mb.function("bump", physical);
        let e = fb.create_block();
        let n = fb.add_block_param(e, Ty::U64);
        fb.switch_to_block(e);
        let one = fb.uconst(Ty::U64, 1);
        let n1 = fb.add(Ty::U64, n, one);
        fb.ret(vec![n1]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let c = fb.const_value(
            clos.clone(),
            Constant::Closure {
                func: bump,
                captures: vec![Constant::Int(0)],
            },
        );
        let a = fb.call_indirect(c, apparent, vec![]);
        let b = fb.call_indirect(c, apparent, vec![]);
        let ten = fb.uconst(Ty::U64, 10);
        let a10 = fb.mul(Ty::U64, a, ten);
        let r = fb.add(Ty::U64, a10, b);
        fb.ret(vec![r]);
        fb.build();
    }
    {
        let mut fb = mb.function("program_seed", unary);
        let e = fb.create_block();
        let seed = fb.add_block_param(e, Ty::U64);
        fb.switch_to_block(e);
        let literal = fb.const_value(
            clos.clone(),
            Constant::Closure {
                func: bump,
                captures: vec![Constant::Int(0)],
            },
        );
        let c = fb.insert_field(clos.clone(), literal, 0, seed);
        let c2 = fb.copy(clos, c);
        let a = fb.call_indirect(c2, apparent, vec![]);
        let b = fb.call_indirect(c2, apparent, vec![]);
        let ten = fb.uconst(Ty::U64, 10);
        let a10 = fb.mul(Ty::U64, a, ten);
        let r = fb.add(Ty::U64, a10, b);
        fb.ret(vec![r]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

const ONE_CAPTURE_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
extern uint64_t program(void);
extern uint64_t program_seed(uint64_t);
/* By-value application: both applications see the seed. */
static uint64_t model(uint64_t seed) { return (seed + 1) * 10 + (seed + 1); }
int main(void) {
    uint64_t got = program();
    if (got != 11 || got != INTERP_PROGRAM) {
        printf("program native=%llu expected 11 interpreter=%llu\n",
               (unsigned long long)got, (unsigned long long)INTERP_PROGRAM);
        return 1;
    }
    const uint64_t seeds[] = {0, 1, 41, 18446744073709551614ULL};
    const uint64_t interp[] = {INTERP_0, INTERP_1, INTERP_2, INTERP_3};
    for (int i = 0; i < 4; i++) {
        uint64_t r = program_seed(seeds[i]);
        if (r != model(seeds[i]) || r != interp[i]) {
            printf("program_seed(%llu) native=%llu C=%llu interpreter=%llu\n",
                   (unsigned long long)seeds[i], (unsigned long long)r,
                   (unsigned long long)model(seeds[i]), (unsigned long long)interp[i]);
            return 2 + i;
        }
    }
    return 0;
}
"#;

#[test]
fn closure_with_one_capture_applies_by_value_at_every_level() {
    let module = build_one_capture_by_value();
    let program = interpret_u64(&module, "program", vec![]);
    assert_eq!(
        program, 11,
        "interpreter oracle: by-value application reads the seed twice"
    );
    let mut driver = ONE_CAPTURE_DRIVER.replace("INTERP_PROGRAM", &format!("{program}ULL"));
    let seeds: [u64; 4] = [0, 1, 41, u64::MAX - 1];
    for (i, seed) in seeds.iter().enumerate() {
        let model = interpret_u64(
            &module,
            "program_seed",
            vec![int(Ty::U64, i128::from(*seed))],
        );
        assert_eq!(
            model,
            seed.wrapping_add(1)
                .wrapping_mul(10)
                .wrapping_add(seed.wrapping_add(1)),
            "interpreter oracle program_seed({seed})"
        );
        driver = driver.replace(&format!("INTERP_{i}"), &format!("{model}ULL"));
    }
    run_native_at_every_level("closure_one", &module, &driver);
}

/// A BY-REFERENCE capture is a `Ptr`-typed capture slot: the pointer is passed
/// by value, so the pointee is shared across applications and the counter
/// program reports 12. `program_ptr` receives the cell from C (which also
/// checks the cell afterwards); `program_ptr_local` allocates it so the
/// interpreter can evaluate the same closure body.
fn build_pointer_capture() -> Module {
    let mut mb = ModuleBuilder::new("closure_pointer_capture");
    let apparent = mb.add_func_type(vec![], vec![Ty::U64]);
    let physical = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let takes_ptr = mb.add_func_type(vec![Ty::Ptr], vec![Ty::U64]);
    let clos_id = mb.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![Ty::Ptr],
    });
    let clos = Ty::Closure(clos_id);

    let bump_ptr = {
        let mut fb = mb.function("bump_ptr", physical);
        let e = fb.create_block();
        let env = fb.add_block_param(e, Ty::Ptr);
        fb.switch_to_block(e);
        let n = fb.load(Ty::U64, env);
        let one = fb.uconst(Ty::U64, 1);
        let n1 = fb.add(Ty::U64, n, one);
        fb.store(Ty::U64, env, n1);
        fb.ret(vec![n1]);
        fb.build()
    };
    {
        let mut fb = mb.function("program_ptr", takes_ptr);
        let e = fb.create_block();
        let cell = fb.add_block_param(e, Ty::Ptr);
        fb.switch_to_block(e);
        let seed = fb.const_value(
            clos.clone(),
            Constant::Closure {
                func: bump_ptr,
                captures: vec![Constant::Int(0)],
            },
        );
        let c = fb.insert_field(clos.clone(), seed, 0, cell);
        let a = fb.call_indirect(c, apparent, vec![]);
        let b = fb.call_indirect(c, apparent, vec![]);
        let ten = fb.uconst(Ty::U64, 10);
        let a10 = fb.mul(Ty::U64, a, ten);
        let r = fb.add(Ty::U64, a10, b);
        fb.ret(vec![r]);
        fb.build();
    }
    {
        let mut fb = mb.function("program_ptr_local", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let env = fb.alloca(Ty::U64);
        let zero = fb.uconst(Ty::U64, 0);
        fb.store(Ty::U64, env, zero);
        let seed = fb.const_value(
            clos.clone(),
            Constant::Closure {
                func: bump_ptr,
                captures: vec![Constant::Int(0)],
            },
        );
        let c = fb.insert_field(clos, seed, 0, env);
        let a = fb.call_indirect(c, apparent, vec![]);
        let b = fb.call_indirect(c, apparent, vec![]);
        let ten = fb.uconst(Ty::U64, 10);
        let a10 = fb.mul(Ty::U64, a, ten);
        let r = fb.add(Ty::U64, a10, b);
        fb.ret(vec![r]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

const POINTER_CAPTURE_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
extern uint64_t program_ptr(uint64_t *);
extern uint64_t program_ptr_local(void);
int main(void) {
    uint64_t cell = 0;
    uint64_t got = program_ptr(&cell);
    if (got != 12 || cell != 2) {
        printf("program_ptr native=%llu cell=%llu expected 12 / 2\n",
               (unsigned long long)got, (unsigned long long)cell);
        return 1;
    }
    cell = 40;
    got = program_ptr(&cell);
    if (got != 41 * 10 + 42 || cell != 42) {
        printf("program_ptr(40) native=%llu cell=%llu expected 452 / 42\n",
               (unsigned long long)got, (unsigned long long)cell);
        return 2;
    }
    got = program_ptr_local();
    if (got != 12 || got != INTERP_LOCAL) {
        printf("program_ptr_local native=%llu expected 12 interpreter=%llu\n",
               (unsigned long long)got, (unsigned long long)INTERP_LOCAL);
        return 3;
    }
    return 0;
}
"#;

#[test]
fn closure_with_pointer_capture_shares_the_pointee_at_every_level() {
    let module = build_pointer_capture();
    let local = interpret_u64(&module, "program_ptr_local", vec![]);
    assert_eq!(
        local, 12,
        "interpreter oracle: a pointer capture shares its pointee"
    );
    let driver = POINTER_CAPTURE_DRIVER.replace("INTERP_LOCAL", &format!("{local}ULL"));
    run_native_at_every_level("closure_ptr", &module, &driver);
}

/// Three captures of mixed widths (`i64`, `i32`, `i8`) spread ahead of two
/// apparent parameters (`i64`, `i16`): the physical signature is
/// `(i64, i32, i8, i64, i16) -> i64`, exercising narrow-argument extension on
/// both sides of the spread. `mix_override` rebuilds capture 1 at run time.
fn build_several_captures() -> Module {
    let mut mb = ModuleBuilder::new("closure_several_captures");
    let apparent = mb.add_func_type(vec![Ty::I64, Ty::I16], vec![Ty::I64]);
    let physical = mb.add_func_type(
        vec![Ty::I64, Ty::I32, Ty::I8, Ty::I64, Ty::I16],
        vec![Ty::I64],
    );
    let override_sig = mb.add_func_type(vec![Ty::I64, Ty::I16, Ty::I32], vec![Ty::I64]);
    let clos_id = mb.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![Ty::I64, Ty::I32, Ty::I8],
    });
    let clos = Ty::Closure(clos_id);

    let body = {
        let mut fb = mb.function("mix_body", physical);
        let e = fb.create_block();
        let a = fb.add_block_param(e, Ty::I64);
        let b = fb.add_block_param(e, Ty::I32);
        let c = fb.add_block_param(e, Ty::I8);
        let x = fb.add_block_param(e, Ty::I64);
        let y = fb.add_block_param(e, Ty::I16);
        fb.switch_to_block(e);
        // a*x + b - c + y, every narrow operand sign-extended to i64.
        let ax = fb.mul(Ty::I64, a, x);
        let b64 = fb.sext(Ty::I32, Ty::I64, b);
        let c64 = fb.sext(Ty::I8, Ty::I64, c);
        let y64 = fb.sext(Ty::I16, Ty::I64, y);
        let t1 = fb.add(Ty::I64, ax, b64);
        let t2 = fb.sub(Ty::I64, t1, c64);
        let r = fb.add(Ty::I64, t2, y64);
        fb.ret(vec![r]);
        fb.build()
    };
    let literal = Constant::Closure {
        func: body,
        captures: vec![Constant::Int(1000), Constant::Int(-7), Constant::Int(-3)],
    };
    {
        let mut fb = mb.function("mix", apparent);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I64);
        let y = fb.add_block_param(e, Ty::I16);
        fb.switch_to_block(e);
        let c = fb.const_value(clos.clone(), literal.clone());
        let r = fb.call_indirect(c, apparent, vec![x, y]);
        fb.ret(vec![r]);
        fb.build();
    }
    {
        let mut fb = mb.function("mix_override", override_sig);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I64);
        let y = fb.add_block_param(e, Ty::I16);
        let b = fb.add_block_param(e, Ty::I32);
        fb.switch_to_block(e);
        let c0 = fb.const_value(clos.clone(), literal);
        let c = fb.insert_field(clos, c0, 1, b);
        let r = fb.call_indirect(c, apparent, vec![x, y]);
        fb.ret(vec![r]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

const SEVERAL_CAPTURES_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
extern int64_t mix(int64_t, int16_t);
extern int64_t mix_override(int64_t, int16_t, int32_t);
static int64_t model(int64_t a, int32_t b, int8_t c, int64_t x, int16_t y) {
    return a * x + (int64_t)b - (int64_t)c + (int64_t)y;
}
int main(void) {
    const int64_t xs[] = {0, 3, -5, 123456789};
    const int16_t ys[] = {0, -1, 32767, -32768};
    const int32_t bs[] = {0, -2147483647 - 1, 2147483647, 77};
    const int64_t interp_mix[] = {MIX_0, MIX_1, MIX_2, MIX_3};
    const int64_t interp_over[] = {OVER_0, OVER_1, OVER_2, OVER_3};
    for (int i = 0; i < 4; i++) {
        int64_t got = mix(xs[i], ys[i]);
        int64_t want = model(1000, -7, -3, xs[i], ys[i]);
        if (got != want || got != interp_mix[i]) {
            printf("mix(%lld,%d) native=%lld C=%lld interpreter=%lld\n", (long long)xs[i],
                   (int)ys[i], (long long)got, (long long)want, (long long)interp_mix[i]);
            return 1 + i;
        }
        got = mix_override(xs[i], ys[i], bs[i]);
        want = model(1000, bs[i], -3, xs[i], ys[i]);
        if (got != want || got != interp_over[i]) {
            printf("mix_override(%lld,%d,%d) native=%lld C=%lld interpreter=%lld\n",
                   (long long)xs[i], (int)ys[i], (int)bs[i], (long long)got, (long long)want,
                   (long long)interp_over[i]);
            return 5 + i;
        }
    }
    return 0;
}
"#;

#[test]
fn closure_with_several_mixed_width_captures_applies_at_every_level() {
    let module = build_several_captures();
    let xs: [i64; 4] = [0, 3, -5, 123_456_789];
    let ys: [i16; 4] = [0, -1, i16::MAX, i16::MIN];
    let bs: [i32; 4] = [0, i32::MIN, i32::MAX, 77];
    let mut driver = SEVERAL_CAPTURES_DRIVER.to_string();
    for i in 0..4 {
        let (x, y, b) = (xs[i], ys[i], bs[i]);
        let mix = interpret(
            &module,
            "mix",
            vec![int(Ty::I64, i128::from(x)), int(Ty::I16, i128::from(y))],
        );
        let model = |b: i32| 1000i64 * x + i64::from(b) + 3 + i64::from(y);
        assert_eq!(
            mix,
            i128::from(model(-7)),
            "interpreter oracle mix({x},{y})"
        );
        let over = interpret(
            &module,
            "mix_override",
            vec![
                int(Ty::I64, i128::from(x)),
                int(Ty::I16, i128::from(y)),
                int(Ty::I32, i128::from(b)),
            ],
        );
        assert_eq!(
            over,
            i128::from(model(b)),
            "interpreter oracle mix_override({x},{y},{b})"
        );
        driver = driver
            .replace(&format!("MIX_{i}"), &format!("{mix}LL"))
            .replace(&format!("OVER_{i}"), &format!("{over}LL"));
    }
    run_native_at_every_level("closure_mix", &module, &driver);
}

/// Closure, `FnDef` and `SymbolAddr` constants nested as aggregate fields. The
/// tuple `(i64, closure.0, fn(i64)->i64, ptr)` is one in-body literal; its
/// closure field's capture is projected, its `FnDef` field is applied through
/// a `Ty::Func` `CallIndirect`, and its `SymbolAddr` field through a `Ty::Ptr`
/// `CallIndirect`. `nested_fndef` omits the `SymbolAddr` lane so the reference
/// interpreter (which has no `(Ty::Ptr, SymbolAddr)` rule) evaluates the rest.
fn build_nested_constants() -> Module {
    let mut mb = ModuleBuilder::new("closure_nested_constants");
    let sig1 = mb.add_func_type(vec![Ty::I64], vec![Ty::I64]);
    let physical = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let clos_id = mb.add_closure_type(ClosureTy {
        func: sig1,
        captures: vec![Ty::I64],
    });
    let clos = Ty::Closure(clos_id);

    let add_cap = {
        let mut fb = mb.function("add_cap", physical);
        let e = fb.create_block();
        let cap = fb.add_block_param(e, Ty::I64);
        let x = fb.add_block_param(e, Ty::I64);
        fb.switch_to_block(e);
        let r = fb.add(Ty::I64, cap, x);
        fb.ret(vec![r]);
        fb.build()
    };
    let add_ten = {
        let mut fb = mb.function("nested_add_ten", sig1);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I64);
        fb.switch_to_block(e);
        let ten = fb.iconst(Ty::I64, 10);
        let r = fb.add(Ty::I64, x, ten);
        fb.ret(vec![r]);
        fb.build()
    };
    let inner = Constant::Closure {
        func: add_cap,
        captures: vec![Constant::Int(2)],
    };
    {
        // (5, closure{add_cap, [2]}, add_ten, &nested_add_ten) -> 5 + 2 + (x+10) + (x+10)
        let tuple_ty = Ty::Tuple(vec![Ty::I64, clos.clone(), Ty::Func(sig1), Ty::Ptr]);
        let mut fb = mb.function("nested", sig1);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I64);
        fb.switch_to_block(e);
        let t = fb.const_value(
            tuple_ty,
            Constant::Aggregate(vec![
                Constant::Int(5),
                inner.clone(),
                Constant::FnDef(add_ten),
                Constant::SymbolAddr {
                    symbol: "nested_add_ten".to_string(),
                    addend: 0,
                },
            ]),
        );
        let k = fb.extract_field(Ty::I64, t, 0);
        let c = fb.extract_field(clos.clone(), t, 1);
        let cap = fb.extract_field(Ty::I64, c, 0);
        let fp = fb.extract_field(Ty::Func(sig1), t, 2);
        let r1 = fb.call_indirect(fp, sig1, vec![x]);
        let sp = fb.extract_field(Ty::Ptr, t, 3);
        let r2 = fb.call_indirect(sp, sig1, vec![x]);
        let s1 = fb.add(Ty::I64, k, cap);
        let s2 = fb.add(Ty::I64, s1, r1);
        let r = fb.add(Ty::I64, s2, r2);
        fb.ret(vec![r]);
        fb.build();
    }
    {
        // (5, closure{add_cap, [2]}, add_ten) -> 5 + 2 + (x+10)
        let tuple_ty = Ty::Tuple(vec![Ty::I64, clos.clone(), Ty::Func(sig1)]);
        let mut fb = mb.function("nested_fndef", sig1);
        let e = fb.create_block();
        let x = fb.add_block_param(e, Ty::I64);
        fb.switch_to_block(e);
        let t = fb.const_value(
            tuple_ty,
            Constant::Aggregate(vec![Constant::Int(5), inner, Constant::FnDef(add_ten)]),
        );
        let k = fb.extract_field(Ty::I64, t, 0);
        let c = fb.extract_field(clos, t, 1);
        let cap = fb.extract_field(Ty::I64, c, 0);
        let fp = fb.extract_field(Ty::Func(sig1), t, 2);
        let r1 = fb.call_indirect(fp, sig1, vec![x]);
        let s1 = fb.add(Ty::I64, k, cap);
        let r = fb.add(Ty::I64, s1, r1);
        fb.ret(vec![r]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

const NESTED_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
extern int64_t nested(int64_t);
extern int64_t nested_fndef(int64_t);
int main(void) {
    const int64_t xs[] = {0, 1, -27, 4000000000LL};
    const int64_t interp[] = {INTERP_0, INTERP_1, INTERP_2, INTERP_3};
    for (int i = 0; i < 4; i++) {
        int64_t got = nested(xs[i]);
        int64_t want = 5 + 2 + (xs[i] + 10) + (xs[i] + 10);
        if (got != want) {
            printf("nested(%lld) native=%lld C=%lld\n", (long long)xs[i], (long long)got,
                   (long long)want);
            return 1 + i;
        }
        got = nested_fndef(xs[i]);
        want = 5 + 2 + (xs[i] + 10);
        if (got != want || got != interp[i]) {
            printf("nested_fndef(%lld) native=%lld C=%lld interpreter=%lld\n", (long long)xs[i],
                   (long long)got, (long long)want, (long long)interp[i]);
            return 5 + i;
        }
    }
    return 0;
}
"#;

#[test]
fn nested_closure_fndef_and_symbol_addr_constants_materialize_at_every_level() {
    let module = build_nested_constants();
    let xs: [i64; 4] = [0, 1, -27, 4_000_000_000];
    let mut driver = NESTED_DRIVER.to_string();
    for (i, x) in xs.iter().enumerate() {
        let want = interpret(&module, "nested_fndef", vec![int(Ty::I64, i128::from(*x))]);
        assert_eq!(
            want,
            i128::from(x + 17),
            "interpreter oracle nested_fndef({x})"
        );
        driver = driver.replace(&format!("INTERP_{i}"), &format!("{want}LL"));
    }
    run_native_at_every_level("closure_nested", &module, &driver);
}

// ---------------------------------------------------------------------------
// Fail-closed controls: what stays outside the lowering, refused by name.
// ---------------------------------------------------------------------------

/// A counter closure module with one `U64` capture whose `program` body is
/// produced by `shape`, which receives the builder positioned in the entry
/// block, the closure type, the apparent signature and the code target and
/// must return the value to apply.
fn build_refusal_module(
    name: &str,
    shape: impl FnOnce(
        &mut trust_ir_build::builder::FunctionBuilder<'_>,
        Ty,
        trust_ir::FuncTyId,
        trust_ir::FuncId,
    ) -> trust_ir::ValueId,
) -> Module {
    let mut mb = ModuleBuilder::new(name);
    let apparent = mb.add_func_type(vec![], vec![Ty::U64]);
    let physical = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let clos_id = mb.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![Ty::U64],
    });
    let clos = Ty::Closure(clos_id);
    let bump = {
        let mut fb = mb.function("bump", physical);
        let e = fb.create_block();
        let n = fb.add_block_param(e, Ty::U64);
        fb.switch_to_block(e);
        let one = fb.uconst(Ty::U64, 1);
        let n1 = fb.add(Ty::U64, n, one);
        fb.ret(vec![n1]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let c = shape(&mut fb, clos, apparent, bump);
        let r = fb.call_indirect(c, apparent, vec![]);
        fb.ret(vec![r]);
        fb.build();
    }
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// `module` is refused at every level: by trust-ir's own first admission
/// finding when trust-ir refuses it (WS7.3: ingestion admission runs before
/// any backend arm), else by the backend's refusal naming every `needle`.
/// trust-ir judges the module as [`aarch64_native::try_compile`] compiles it:
/// pinned, under its license policy.
fn expect_refusal(tag: &str, module: &Module, needles: &[&str]) {
    let pinned = aarch64_native::pinned(module);
    let license = aarch64_native::permit_unlicensed();
    for opt in OPTS {
        let error = aarch64_native::try_compile(module, opt)
            .err()
            .unwrap_or_else(|| panic!("{tag}: must be refused at {opt:?}"));
        if let Some(named) = admission_expect::names_first_finding(&pinned, &error, &license) {
            assert!(
                named,
                "{tag} at {opt:?}: refusal must name trust-ir's admission finding {:?}, got: \
                 {error}",
                admission_expect::first_finding(&pinned, &license)
            );
            continue;
        }
        for needle in needles {
            assert!(
                error.contains(needle),
                "{tag} at {opt:?}: refusal must name `{needle}`, got: {error}"
            );
        }
    }
}

#[test]
fn closure_application_without_static_code_identity_is_refused_by_name() {
    // A `Select` between two literals: the value model would carry the code
    // identity, but no runtime lane does, so the site is refused.
    let selected = build_refusal_module("closure_refusal_select", |fb, clos, _, bump| {
        let a = fb.const_value(
            clos.clone(),
            Constant::Closure {
                func: bump,
                captures: vec![Constant::Int(1)],
            },
        );
        let b = fb.const_value(
            clos.clone(),
            Constant::Closure {
                func: bump,
                captures: vec![Constant::Int(2)],
            },
        );
        let cond = fb.bool_const(true);
        fb.select(clos, cond, a, b)
    });
    expect_refusal(
        "select",
        &selected,
        &[
            "[TCG-CLOSURE]",
            "produced by Inst::Select",
            "not statically visible",
        ],
    );

    // A closure projected out of an enclosing aggregate literal.
    let projected = build_refusal_module("closure_refusal_projected", |fb, clos, _, bump| {
        let tuple_ty = Ty::Tuple(vec![Ty::I64, clos.clone()]);
        let t = fb.const_value(
            tuple_ty,
            Constant::Aggregate(vec![
                Constant::Int(9),
                Constant::Closure {
                    func: bump,
                    captures: vec![Constant::Int(1)],
                },
            ]),
        );
        fb.extract_field(clos, t, 1)
    });
    expect_refusal(
        "projected",
        &projected,
        &[
            "[TCG-CLOSURE]",
            "produced by Inst::ExtractField",
            "not statically visible",
        ],
    );

    // A closure arriving as a function parameter.
    let mut mb = ModuleBuilder::new("closure_refusal_parameter");
    let apparent = mb.add_func_type(vec![], vec![Ty::U64]);
    let clos_id = mb.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![Ty::U64],
    });
    let clos = Ty::Closure(clos_id);
    let takes_closure = mb.add_func_type(vec![clos.clone()], vec![Ty::U64]);
    {
        let mut fb = mb.function("apply_param", takes_closure);
        let e = fb.create_block();
        let c = fb.add_block_param(e, clos);
        fb.switch_to_block(e);
        let r = fb.call_indirect(c, apparent, vec![]);
        fb.ret(vec![r]);
        fb.build();
    }
    expect_refusal(
        "parameter",
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &[
            "[TCG-CLOSURE]",
            "function or block parameter",
            "not statically visible",
        ],
    );
}

#[test]
fn closure_signature_mismatches_are_refused_by_name() {
    // The edge declares a signature that is not the closure's apparent one.
    let mut mb = ModuleBuilder::new("closure_refusal_apparent_sig");
    let apparent = mb.add_func_type(vec![], vec![Ty::U64]);
    let other = mb.add_func_type(vec![Ty::I64], vec![Ty::U64]);
    let physical = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let clos_id = mb.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![Ty::U64],
    });
    let clos = Ty::Closure(clos_id);
    let bump = {
        let mut fb = mb.function("bump", physical);
        let e = fb.create_block();
        let n = fb.add_block_param(e, Ty::U64);
        fb.switch_to_block(e);
        fb.ret(vec![n]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let c = fb.const_value(
            clos,
            Constant::Closure {
                func: bump,
                captures: vec![Constant::Int(1)],
            },
        );
        let x = fb.iconst(Ty::I64, 1);
        let r = fb.call_indirect(c, other, vec![x]);
        fb.ret(vec![r]);
        fb.build();
    }
    expect_refusal(
        "apparent",
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &["[TCG-CLOSURE]", "apparent signature is functy"],
    );

    // The literal names a function whose physical signature lacks the capture.
    let mut mb = ModuleBuilder::new("closure_refusal_physical_sig");
    let apparent = mb.add_func_type(vec![], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::U64]);
    let clos_id = mb.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![Ty::U64],
    });
    let clos = Ty::Closure(clos_id);
    let wrong = {
        let mut fb = mb.function("wrong", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let one = fb.uconst(Ty::U64, 1);
        fb.ret(vec![one]);
        fb.build()
    };
    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let c = fb.const_value(
            clos,
            Constant::Closure {
                func: wrong,
                captures: vec![Constant::Int(1)],
            },
        );
        let r = fb.call_indirect(c, apparent, vec![]);
        fb.ret(vec![r]);
        fb.build();
    }
    expect_refusal(
        "physical",
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &[
            "[TCG-CLOSURE]",
            "physical signature",
            "1 capture(s) then 0 apparent parameter(s)",
        ],
    );
}

#[test]
fn unlowered_closure_adjacent_constants_stay_refused_by_name() {
    // A captured closure at a non-closure type.
    let mut mb = ModuleBuilder::new("closure_refusal_wrong_type");
    let apparent = mb.add_func_type(vec![], vec![Ty::U64]);
    let physical = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let nullary = mb.add_func_type(vec![], vec![Ty::I64]);
    mb.add_closure_type(ClosureTy {
        func: apparent,
        captures: vec![Ty::U64],
    });
    let bump = mb.declare_function("bump", physical);
    {
        let mut fb = mb.function("program", nullary);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let c = fb.const_value(
            Ty::I64,
            Constant::Closure {
                func: bump,
                captures: vec![Constant::Int(1)],
            },
        );
        fb.ret(vec![c]);
        fb.build();
    }
    // It is no constant of `i64`: TrustIR's typed admission, which every
    // compiler entry consumes first, refuses it by name before the adapter's
    // own `[TCG-CLOSURE]` arm (kept for callers below admission) is reached.
    expect_refusal(
        "wrong type",
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &[
            "TrustIrAdmissionRefused",
            "function 'program' bb0: const type mismatch: expected i64, got closure<func.0>[1]",
        ],
    );

    // `phantomdata` is trust-ir's one spelling of the value of `()`: it lowers
    // as the empty aggregate at `()` did. At any other type it is no constant
    // of that type and is refused by name.
    for (ty, refused) in [(Ty::Unit, false), (Ty::I64, true)] {
        let mut mb = ModuleBuilder::new("closure_refusal_phantom");
        let sig = mb.add_func_type(vec![], vec![ty.clone()]);
        {
            let mut fb = mb.function("program", sig);
            let e = fb.create_block();
            fb.switch_to_block(e);
            let p = fb.const_value(ty, Constant::PhantomData);
            fb.ret(vec![p]);
            fb.build();
        }
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        if refused {
            expect_refusal(
                "phantom",
                &module,
                &[
                    "TrustIrAdmissionRefused",
                    "function 'program' bb0: const type mismatch: expected i64, got phantomdata",
                ],
            );
        } else {
            for opt in OPTS {
                aarch64_native::try_compile(&module, opt)
                    .unwrap_or_else(|error| panic!("`phantomdata` at `()` {opt:?}: {error}"));
            }
        }
    }

    // A bitset `Set` constant stays a named refusal: trust-ir states no
    // universe for its bit image (a boxed set lowers, see
    // `e2e_aarch64_sequences.rs`).
    let mut mb = ModuleBuilder::new("closure_refusal_set");
    let elem = mb.add_type(Ty::I64);
    let set_ty = Ty::Set(elem, trust_ir::SetRepr::Bitset);
    let sig = mb.add_func_type(vec![], vec![set_ty.clone()]);
    {
        let mut fb = mb.function("program", sig);
        let e = fb.create_block();
        fb.switch_to_block(e);
        let s = fb.const_value(set_ty, Constant::Set(vec![Constant::Int(1)]));
        fb.ret(vec![s]);
        fb.build();
    }
    expect_refusal(
        "set",
        &mb.build().expect("ModuleBuilder::build: test fixture"),
        &["[TCG-SEQ]", "SetRepr::Bitset"],
    );
}
