// trust-cg-codegen/tests/bool_load_semantics.rs - a loaded `bool` is its byte read as `!= 0`
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! trust-ir's `Load Bool` reads the byte `m` and yields `m != 0` (the pinned
//! reference interpreter's `decode_leaf`: `bytes[0] != 0`); no trust-ir or LIR
//! rule says `m` is 0 or 1. Every backend must compute exactly that.
//!
//! One module, where every loaded byte is one of 0, 1, 2, 0x80 and 0xFF:
//!
//! * callees taking a pointer: return the loaded bool (plain, volatile and
//!   atomic loads, and a field at `+7`), widen it to `u32`, branch on it,
//!   select with it, pass it to a module callee, `&` two loaded bools, and
//!   pass one to a host callee that reads its whole 32-bit argument;
//! * drivers `drive_*(raw: u8, ...) -> u32` that store the raw byte(s) into
//!   a local with a `u8` store and call the callee with the local's address.
//!
//! Oracles: the pinned trust-ir reference interpreter runs every driver (and
//! must itself agree with the closed form `m != 0`). The x86-64 backend runs
//! natively on an x86-64 host (JIT, O0-O3): each driver, and each callee
//! called directly with a pointer into host memory, whose returned register
//! must be exactly the reference value in all 32 bits (the backend's clean
//! bool). The x86-64 compiler refuses the volatile callee (its VOL-2 trace
//! gate models no `B1` access), which the native leg asserts; the selector's
//! volatile `bool` load runs natively in `x86_64_bool_load_abi`. The AArch64
//! backend's Mach-O object (O0-O3) is decoded and interpreted on any host
//! (`common::a64_interp`), drivers and callees alike.
#![cfg(all(
    any(target_arch = "aarch64", target_arch = "x86_64"),
    any(target_os = "linux", target_os = "macos")
))]

mod common;

use std::collections::HashMap;

use common::a64_interp::run_func;
use trust_cg_codegen::compiler::JitValidationMode;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{
    CodegenLicensePolicy, Compiler, CompilerConfig, CoreHostJitTarget, Target,
    UnlicensedBodyPolicy, pipeline::OptLevel,
};
use trust_ir::interpret::{InterpretOptions, InterpretValue, Interpreter};
use trust_ir::{BinOp, FuncId, Module, Ordering, Ty};
use trust_ir_build::ModuleBuilder;

/// Loaded bytes: the two valid bools and three others.
const BYTES: [u8; 5] = [0, 1, 2, 0x80, 0xFF];

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// How a callee reads its loaded bool.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Use {
    /// `-> bool { *p }` (plain load).
    Return,
    /// `-> bool { volatile *p }`.
    ReturnVolatile,
    /// `-> bool { atomic(acquire) *p }`.
    ReturnAtomic,
    /// `-> bool { *(p + 7) }`: a bool field.
    Field,
    /// `-> u32 { *p as u32 }`.
    Widen,
    /// `-> u32 { if *p { 7 } else { 3 } }`.
    Branch,
    /// `-> u32 { select(*p, 11, 22) }`.
    Select,
    /// `-> u32 { sink(*p) }`, `sink(b: bool) -> u32 { b as u32 }` in the module.
    Pass,
    /// `-> bool { *p & *q }` (two loads, `BAnd`).
    And,
    /// `-> u32 { host_sink(*p) }`, a host callee returning its whole 32-bit
    /// argument register (native leg only: the reference has no host).
    PassToHost,
}

const USES: [Use; 10] = [
    Use::Return,
    Use::ReturnVolatile,
    Use::ReturnAtomic,
    Use::Field,
    Use::Widen,
    Use::Branch,
    Use::Select,
    Use::Pass,
    Use::And,
    Use::PassToHost,
];

impl Use {
    fn callee(self) -> String {
        format!("{self:?}").to_lowercase()
    }

    fn driver(self) -> String {
        format!("drive_{}", self.callee())
    }

    fn pointers(self) -> usize {
        if self == Use::And { 2 } else { 1 }
    }

    fn returns_bool(self) -> bool {
        matches!(
            self,
            Use::Return | Use::ReturnVolatile | Use::ReturnAtomic | Use::Field | Use::And
        )
    }

    /// The closed form of the driver's result: trust-ir's `m != 0`.
    fn expected(self, bytes: &[u8]) -> u32 {
        let flag = |byte: u8| byte != 0;
        match self {
            Use::Branch => {
                if flag(bytes[0]) {
                    7
                } else {
                    3
                }
            }
            Use::Select => {
                if flag(bytes[0]) {
                    11
                } else {
                    22
                }
            }
            Use::And => u32::from(flag(bytes[0]) && flag(bytes[1])),
            _ => u32::from(flag(bytes[0])),
        }
    }

    /// The raw-byte cases the driver is run with.
    fn cases(self) -> Vec<Vec<u8>> {
        if self.pointers() == 2 {
            BYTES
                .iter()
                .flat_map(|a| BYTES.iter().map(move |b| vec![*a, *b]))
                .collect()
        } else {
            BYTES.iter().map(|byte| vec![*byte]).collect()
        }
    }
}

/// Where a driver's local puts the raw byte: the bool field is at `+7` of an
/// eight-byte local.
fn field_offset(use_: Use) -> Option<u64> {
    (use_ == Use::Field).then_some(7)
}

fn build_module(uses: &[Use]) -> Module {
    let mut builder = ModuleBuilder::new("bool_load_semantics");
    let sink_ty = builder.add_func_type(vec![Ty::Bool], vec![Ty::U32]);
    let host_sink = builder.declare_function("host_sink", sink_ty);
    let sink = {
        let mut f = builder.function("sink", sink_ty);
        let entry = f.create_block();
        let b = f.add_block_param(entry, Ty::Bool);
        f.switch_to_block(entry);
        let wide = f.zext(Ty::Bool, Ty::U32, b);
        f.ret(vec![wide]);
        f.build()
    };
    let mut callees: HashMap<Use, FuncId> = HashMap::new();
    for &use_ in uses {
        let result = if use_.returns_bool() {
            Ty::Bool
        } else {
            Ty::U32
        };
        let ty = builder.add_func_type(vec![Ty::Ptr; use_.pointers()], vec![result]);
        let mut f = builder.function(use_.callee(), ty);
        let entry = f.create_block();
        let pointers: Vec<_> = (0..use_.pointers())
            .map(|_| f.add_block_param(entry, Ty::Ptr))
            .collect();
        f.switch_to_block(entry);
        let p = pointers[0];
        let value = match use_ {
            Use::Return => f.load(Ty::Bool, p),
            Use::ReturnVolatile => f.load_volatile(Ty::Bool, p),
            Use::ReturnAtomic => f.atomic_load(Ty::Bool, p, Ordering::Acquire),
            Use::Field => {
                let field = f.gep_byte_offset(p, 7);
                f.load(Ty::Bool, field)
            }
            Use::Widen => {
                let flag = f.load(Ty::Bool, p);
                f.zext(Ty::Bool, Ty::U32, flag)
            }
            Use::Branch => {
                let flag = f.load(Ty::Bool, p);
                let (yes, no) = (f.create_block(), f.create_block());
                f.condbr(flag, yes, vec![], no, vec![]);
                for (block, value) in [(yes, 7), (no, 3)] {
                    f.switch_to_block(block);
                    let value = f.iconst(Ty::U32, value);
                    f.ret(vec![value]);
                }
                callees.insert(use_, f.build());
                continue;
            }
            Use::Select => {
                let flag = f.load(Ty::Bool, p);
                let (a, b) = (f.iconst(Ty::U32, 11), f.iconst(Ty::U32, 22));
                f.select(Ty::U32, flag, a, b)
            }
            Use::Pass => {
                let flag = f.load(Ty::Bool, p);
                f.call(sink, vec![flag])
            }
            Use::And => {
                let a = f.load(Ty::Bool, p);
                let b = f.load(Ty::Bool, pointers[1]);
                f.binop(BinOp::BAnd, Ty::Bool, a, b)
            }
            Use::PassToHost => {
                let flag = f.load(Ty::Bool, p);
                f.call(host_sink, vec![flag])
            }
        };
        f.ret(vec![value]);
        callees.insert(use_, f.build());
    }
    for &use_ in uses {
        let ty = builder.add_func_type(vec![Ty::U8; use_.pointers()], vec![Ty::U32]);
        let mut f = builder.function(use_.driver(), ty);
        let entry = f.create_block();
        let raws: Vec<_> = (0..use_.pointers())
            .map(|_| f.add_block_param(entry, Ty::U8))
            .collect();
        f.switch_to_block(entry);
        let locals: Vec<_> = raws
            .iter()
            .map(|raw| {
                let local = f.alloca(Ty::U64);
                let at = match field_offset(use_) {
                    Some(offset) => f.gep_byte_offset(local, offset),
                    None => local,
                };
                f.store(Ty::U8, at, *raw);
                local
            })
            .collect();
        let result = f.call(callees[&use_], locals);
        let result = if use_.returns_bool() {
            f.zext(Ty::Bool, Ty::U32, result)
        } else {
            result
        };
        f.ret(vec![result]);
        f.build();
    }
    let module = builder.build().expect("ModuleBuilder::build: test fixture");
    // Target-independent validation: the one refusal is the host callee's FFI
    // boundary, which pins no target here; each leg pins its own (`pinned`).
    let errors: Vec<String> = trust_ir_build::validate_module(&module)
        .iter()
        .map(|error| format!("{error:?}"))
        .collect();
    assert_eq!(
        errors,
        ["TargetInfoRequired { boundary: \"bodyless external declaration `host_sink`\" }"]
    );
    module
}

/// `module` pinned to the target a leg compiles for. The module's FFI
/// boundary (`host_sink`) requires a pinned target, and every ingestion entry
/// refuses what trust-ir's validator refuses (WS7.3), so each leg binds its
/// own target before compiling.
fn pinned(module: &Module, target_info: trust_ir::TargetInfo) -> Module {
    let mut module = module.clone();
    module.target_info = Some(target_info);
    assert_eq!(trust_ir_build::validate_module(&module), []);
    module
}

/// The AArch64 Mach-O target the object leg compiles for.
fn aarch64_darwin_target_info() -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

fn function_id(module: &Module, name: &str) -> FuncId {
    module
        .functions
        .iter()
        .find(|function| function.name == name)
        .unwrap_or_else(|| panic!("no function {name}"))
        .id
}

/// The pinned trust-ir reference interpreter's result for `use_`'s driver.
fn reference(module: &Module, use_: Use, bytes: &[u8]) -> u32 {
    let result = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 1_000,
            max_call_depth: 4,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(
            function_id(module, &use_.driver()),
            bytes
                .iter()
                .map(|byte| InterpretValue::int(Ty::U8, i128::from(*byte)).unwrap()),
        )
        .unwrap_or_else(|error| panic!("{use_:?} {bytes:?}: reference: {error}"));
    assert_eq!(result.returns.len(), 1);
    u32::try_from(result.returns[0].as_int().unwrap().as_unsigned()).unwrap()
}

/// Every driver's reference value, checked against the closed form.
fn references(module: &Module, uses: &[Use]) -> Vec<(Use, Vec<u8>, u32)> {
    let mut rows = Vec::new();
    for &use_ in uses {
        for bytes in use_.cases() {
            let expected = use_.expected(&bytes);
            if use_ != Use::PassToHost {
                assert_eq!(
                    reference(module, use_, &bytes),
                    expected,
                    "{use_:?} {bytes:?}: the reference interpreter reads the byte as != 0"
                );
            }
            rows.push((use_, bytes, expected));
        }
    }
    rows
}

/// A host callee of a `bool` argument that reads its whole 32-bit argument
/// register, as an LLVM callee does (`fn(b: bool) -> u32 { b as u32 }` is
/// `movl %edi, %eax`).
extern "C" fn host_sink(argument: u32) -> u32 {
    argument
}

#[test]
fn the_reference_interpreter_reads_a_loaded_bool_byte_as_nonzero() {
    let module = build_module(&USES);
    let rows = references(&module, &USES);
    assert_eq!(rows.len(), 9 * BYTES.len() + BYTES.len() * BYTES.len());
    eprintln!("BOOL_LOAD_REFERENCE rows={}", rows.len());
}

/// The native JIT, in its dev-only `Unchecked` validation mode: this test
/// judges the executed values, not proof promotion (the drivers' locals and
/// calls are outside every x86-64 proof lane, and the loaded-bool bodies'
/// theorems are qualified in `trust-cg-verify`'s x86 body tests).
fn native_compiler(opt: OptLevel, host: &CoreHostJitTarget) -> Compiler {
    let mut config = CompilerConfig::jit_fast(Target::host());
    config.opt_level = opt;
    config.jit_validation_mode_override = Some(JitValidationMode::Unchecked);
    Compiler::new_for_target_spec(config, host.target_spec()).with_codegen_license(
        CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
    )
}

/// The native leg's callees. The x86-64 compiler refuses a volatile `bool`
/// load before and after this change (its volatile-trace gate, VOL-2, models
/// no `B1` access, so the compile fails closed; checked below); the x86-64
/// selection of that load runs natively in `x86_64_bool_load_abi`.
fn native_uses() -> Vec<Use> {
    USES.into_iter()
        .filter(|use_| !(cfg!(target_arch = "x86_64") && *use_ == Use::ReturnVolatile))
        .collect()
}

/// x86-64 (or an AArch64 host), natively through the JIT at O0-O3: every
/// driver, and every callee called with a pointer into host memory, returns
/// exactly the reference value in all 32 bits of its result register.
#[test]
fn native_backend_reads_a_loaded_bool_byte_as_nonzero() {
    let uses = native_uses();
    let module = build_module(&uses);
    let rows = references(&module, &uses);
    let host = CoreHostJitTarget::detect().expect("supported native test host");
    let mut symbols: HashMap<String, *const u8> = HashMap::new();
    symbols.insert("host_sink".into(), host_sink as *const u8);
    if cfg!(target_arch = "x86_64") {
        let Err(error) = native_compiler(OptLevel::O0, &host).compile_module_to_jit(
            &pinned(&build_module(&USES), host.trust_ir_target_info().clone()),
            &symbols,
        ) else {
            panic!("the x86-64 compiler refuses a volatile bool load");
        };
        assert!(
            error.to_string().contains(
                "volatile access trace changed in `returnvolatile`: 1 volatile access(es) have \
                 a LIR type this obligation does not model"
            ),
            "{error}"
        );
    }
    let native = pinned(&module, host.trust_ir_target_info().clone());
    let mut failures = Vec::new();
    let mut calls = 0usize;
    for opt in OPT_LEVELS {
        let compiler = native_compiler(opt, &host);
        let result = compiler
            .compile_module_to_jit(&native, &symbols)
            .unwrap_or_else(|error| panic!("{opt:?}: {error}"));
        for (use_, bytes, expected) in &rows {
            // SAFETY: each driver is `extern "C" fn(u8[, u8]) -> u32` and each
            // callee `extern "C" fn(*const u8[, *const u8]) -> bool/u32`; a
            // `bool` result is read as the whole 32-bit register it is
            // returned in. The buffer outlives the calls; the pointers are
            // live host bytes.
            let (driven, direct) = unsafe {
                if use_.pointers() == 2 {
                    let driver = result
                        .buffer
                        .get_fn_bound::<extern "C" fn(u8, u8) -> u32>(&use_.driver())
                        .unwrap();
                    let callee = result
                        .buffer
                        .get_fn_bound::<extern "C" fn(*const u8, *const u8) -> u32>(&use_.callee())
                        .unwrap();
                    (
                        driver.as_ref()(bytes[0], bytes[1]),
                        callee.as_ref()(&bytes[0], &bytes[1]),
                    )
                } else {
                    let driver = result
                        .buffer
                        .get_fn_bound::<extern "C" fn(u8) -> u32>(&use_.driver())
                        .unwrap();
                    let callee = result
                        .buffer
                        .get_fn_bound::<extern "C" fn(*const u8) -> u32>(&use_.callee())
                        .unwrap();
                    let mut field = [0xA5u8; 8];
                    field[7] = bytes[0];
                    let pointer = if field_offset(*use_).is_some() {
                        field.as_ptr()
                    } else {
                        &bytes[0]
                    };
                    (driver.as_ref()(bytes[0]), callee.as_ref()(pointer))
                }
            };
            calls += 2;
            for (how, got) in [("driver", driven), ("callee", direct)] {
                if got != *expected {
                    failures.push(format!(
                        "{opt:?} {use_:?} {how} bytes={bytes:02x?}: got {got:#x}, reference \
                         {expected:#x}"
                    ));
                }
            }
        }
    }
    eprintln!(
        "BOOL_LOAD_NATIVE target={:?} calls={calls} failures={}",
        Target::host(),
        failures.len()
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// The AArch64 backend's Mach-O object at O0-O3, decoded and interpreted on
/// any host: every driver, and every callee with its byte in modeled memory,
/// returns exactly the reference value in W0.
#[test]
fn aarch64_backend_reads_a_loaded_bool_byte_as_nonzero() {
    const MEMORY: u64 = 0x2000_0000;
    let module = build_module(&USES);
    let rows = references(&module, &USES);
    let mut failures = Vec::new();
    let mut runs = 0usize;
    for opt in OPT_LEVELS {
        let compiler = Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: opt,
                ..CompilerConfig::default()
            },
            TargetSpec::parse("aarch64-apple-darwin").unwrap(),
        )
        // The fixture is hand-built and claim-less (`body_gate: None`), which
        // trust-cg refuses by default (roadmap WS7.5, DG-73): state Permit.
        .with_codegen_license(
            CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
        );
        let object = compiler
            .compile(&pinned(&module, aarch64_darwin_target_info()))
            .unwrap_or_else(|error| panic!("{opt:?}: {error}"))
            .object_code;
        for (use_, bytes, expected) in &rows {
            // The host callee has no AArch64 body to interpret.
            if *use_ == Use::PassToHost {
                continue;
            }
            let driven = run_func(&object, &format!("_{}", use_.driver()), |interp| {
                for (i, byte) in bytes.iter().enumerate() {
                    interp.set_x(i, u64::from(*byte));
                }
            });
            let direct = run_func(&object, &format!("_{}", use_.callee()), |interp| {
                for (i, byte) in bytes.iter().enumerate() {
                    let base = MEMORY + 0x100 * i as u64;
                    let at = base + field_offset(*use_).unwrap_or(0);
                    // The bytes around the loaded one are set too.
                    for k in 0..8 {
                        interp.mem.insert(base + k, 0xA5);
                    }
                    interp.mem.insert(at, *byte);
                    interp.set_x(i, base);
                }
            });
            runs += 2;
            for (how, got) in [("driver", driven), ("callee", direct)] {
                match got {
                    Ok(x0) if x0 as u32 == *expected => {}
                    other => failures.push(format!(
                        "{opt:?} {use_:?} {how} bytes={bytes:02x?}: got {other:x?}, reference \
                         {expected:#x}"
                    )),
                }
            }
        }
    }
    eprintln!("BOOL_LOAD_AARCH64 runs={runs} failures={}", failures.len());
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
