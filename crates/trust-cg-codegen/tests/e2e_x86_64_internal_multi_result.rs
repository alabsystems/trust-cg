// trust-cg-codegen/tests/e2e_x86_64_internal_multi_result.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// ===========================================================================
// x86-64 System V: TrustCG's INTERNAL multi-result convention past RAX:RDX
// ===========================================================================
//
// A TrustIR function may return any number of independent results
// (`FuncTy.returns`). AArch64 places them in X0-X7 / V0-V7. On x86-64 the
// selector used to allocate only from System V's C return file (RAX,RDX /
// XMM0,XMM1) and refused the third result of a class, so every producer with a
// wider multi-result convention (TY's semantic lane returns five scalar lanes
// from its internal `Fast` functions) was AArch64-only. The selector now
// continues into TrustCG's internal file (`X86_INTERNAL_RET_GPRS` =
// RAX,RDX,RCX,RSI,RDI,R8,R9; `X86_INTERNAL_RET_XMMS` = XMM0-XMM7), of which the
// C file is a same-index prefix, and the adapter admits that only on an edge
// TrustCG compiles at both ends (`[TCG-X86-MULTI-RESULT]`).
//
// THE EVIDENCE HERE, and its strength:
//
//  (A) ADMISSION, always run: every shape below compiles for both System V
//      x86-64 object formats (Mach-O and ELF) at O0-O3, and each foreign edge
//      is refused BY NAME — a C or Rust convention, an exported definition, a
//      bodyless declaration, a C-convention indirect call — while Windows x64
//      still refuses and a shape past the file is refused by the selector.
//      Non-vacuity: a C-shaped return under the same C convention compiles.
//  (B) MACHINE-CODE SHAPE, always run where an `objdump` is present: the
//      wrappers keep real `call`s (direct and through a register) at every
//      optimization level, so (C) exercises the call ABI and not an inlined
//      copy.
//  (C) EXECUTION, where an x86-64 executor exists (a native x86-64 host, or
//      Rosetta 2 — `x86_64_oracle_enabled`): the objects are linked with a C
//      driver and run; every result of two chained calls, twelve values live
//      across both calls and the callee's side effect are compared
//      byte-for-byte with a reference computed HERE, in Rust, never by
//      TrustCG. With `TRUST_CG_X86_MULTI_RESULT_ARTIFACTS=<dir>` the test also
//      writes the Darwin objects and the expected bytes there, so an external
//      executor (the 2026-09-28 record ran them under the Unicorn x86-64
//      emulator on an Apple Silicon host without Rosetta) can check them.
//  (D) JIT EXECUTION, on a System V x86-64 host: the same modules through
//      the in-process JIT at O0-O3 under the dev-only `Unchecked` mode the
//      compile states (uncertified bytes, the same strength as (C)), and the
//      verifying default held to publishing with proof or refusing at the
//      proof gate (OD-219).
//
// WHAT IS NOT PROVEN: this is execution evidence on chosen inputs, not a proof
// of the convention; the Windows x64 extension is not defined; no C compiler
// can call the internal functions, so the callee half is observed through
// TrustCG-compiled wrappers here (the external executor additionally reads the
// callee's result registers directly).

mod common;

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use common::rosetta::{
    codegen_link_timeout, codegen_run_timeout, command_output_with_timeout,
    run_executable_with_timeout,
};
use common::x86_64_corpus::x86_64_oracle_enabled;

use trust_cg_codegen::compiler::{CompileError, Compiler, CompilerConfig, JitValidationMode};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};
use trust_ir::{BinOp, CallingConv, CastOp, FuncId, FuncTyId, ICmpOp, Linkage, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder, validate_module};

const ALL_OPT: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

/// The System V triples. Both use the same register convention; only the
/// object format differs.
const DARWIN: &str = "x86_64-apple-darwin";
const LINUX: &str = "x86_64-unknown-linux-gnu";

/// The triple this host links and executes x86-64 code for.
const HOST_X86_TRIPLE: &str = if cfg!(target_os = "macos") {
    DARWIN
} else {
    LINUX
};

/// Values loaded before the calls and stored after them: they must survive two
/// multi-result calls, so the allocator has to move every result out of the
/// caller-saved result registers.
const LIVE_LANES: usize = 12;

/// Every stored lane occupies 16 bytes (an `i128` needs all of them); narrower
/// stores leave the remaining bytes at the fill pattern.
const LANE_BYTES: usize = 16;
const FILL: u8 = 0xa5;

/// Added to the seed between the two calls.
const SECOND_SEED_DELTA: u64 = 0x1234;

struct Shape {
    tag: &'static str,
    returns: Vec<Ty>,
}

fn shapes() -> Vec<Shape> {
    vec![
        // Three integers: the first shape the C file cannot place (RCX).
        Shape {
            tag: "int3",
            returns: vec![Ty::I64, Ty::I32, Ty::U64],
        },
        // TY's semantic-lane width, with narrow carriers.
        Shape {
            tag: "int5",
            returns: vec![Ty::I64, Ty::I32, Ty::I8, Ty::Bool, Ty::U64],
        },
        // The whole integer file: RAX,RDX,RCX,RSI,RDI,R8,R9.
        Shape {
            tag: "int7",
            returns: vec![
                Ty::U64,
                Ty::I32,
                Ty::I16,
                Ty::I8,
                Ty::Bool,
                Ty::I64,
                Ty::U32,
            ],
        },
        // The whole SSE file, both widths: XMM0-XMM7.
        Shape {
            tag: "fp8",
            returns: vec![
                Ty::F64,
                Ty::F32,
                Ty::F64,
                Ty::F32,
                Ty::F64,
                Ty::F32,
                Ty::F64,
                Ty::F32,
            ],
        },
        // Both files full at once, interleaved: two independent counters.
        Shape {
            tag: "mix15",
            returns: vec![
                Ty::F64,
                Ty::I64,
                Ty::F32,
                Ty::I32,
                Ty::F64,
                Ty::I8,
                Ty::F32,
                Ty::Bool,
                Ty::F64,
                Ty::I16,
                Ty::F32,
                Ty::U64,
                Ty::F64,
                Ty::U32,
                Ty::F32,
            ],
        },
        // `i128` pairs past the C file: RAX:RDX, RCX, RSI:RDI, R8.
        Shape {
            tag: "i128",
            returns: vec![Ty::I128, Ty::I64, Ty::I128, Ty::I32],
        },
    ]
}

// ---------------------------------------------------------------------------
// The reference — computed here, never by TrustCG.
// ---------------------------------------------------------------------------

/// A distinct odd multiplier per result index.
fn multiplier(index: usize) -> u64 {
    (0x9e37_79b9_7f4a_7c15_u64 ^ ((index as u64) << 32)) | 1
}

/// The 64-bit word result `index` is derived from, given the call's seed and
/// the counter value it read.
fn word(seed: u64, before: u64, index: usize) -> u64 {
    seed.wrapping_mul(multiplier(index))
        .wrapping_add(before)
        .wrapping_add(index as u64)
}

const I128_HIGH_MASK: u64 = 0x5555_5555_5555_5555;

/// Little-endian bytes of result `index` of type `ty`, exactly as a store of
/// that type writes them.
fn result_bytes(ty: &Ty, seed: u64, before: u64, index: usize) -> Vec<u8> {
    let w = word(seed, before, index);
    match ty {
        Ty::U64 | Ty::I64 => w.to_le_bytes().to_vec(),
        Ty::U32 | Ty::I32 => (w as u32).to_le_bytes().to_vec(),
        Ty::I16 => (w as u16).to_le_bytes().to_vec(),
        Ty::I8 => vec![w as u8],
        Ty::Bool => vec![u8::from((w >> 7) & 1 == 1)],
        Ty::F64 => ((w >> 11) as f64).to_le_bytes().to_vec(),
        Ty::F32 => ((w >> 40) as f32).to_le_bytes().to_vec(),
        Ty::I128 => {
            let value = (u128::from(w ^ I128_HIGH_MASK) << 64) | u128::from(w);
            value.to_le_bytes().to_vec()
        }
        other => panic!("no reference for {other:?}"),
    }
}

fn live_value(lane: usize) -> u64 {
    0x0123_4567_89ab_cdef_u64.wrapping_mul(lane as u64 + 3)
}

/// The exact output buffer a wrapper call must produce, and the final counter.
fn expected_output(shape: &Shape, seed: u64, state: u64) -> (Vec<u8>, u64) {
    let n = shape.returns.len();
    let mut out = vec![FILL; (2 * n + LIVE_LANES) * LANE_BYTES];
    let mut put = |lane: usize, bytes: &[u8]| {
        out[lane * LANE_BYTES..lane * LANE_BYTES + bytes.len()].copy_from_slice(bytes);
    };
    for (call, (call_seed, before)) in [
        (seed, state),
        (seed.wrapping_add(SECOND_SEED_DELTA), state.wrapping_add(1)),
    ]
    .into_iter()
    .enumerate()
    {
        for (index, ty) in shape.returns.iter().enumerate() {
            put(
                call * n + index,
                &result_bytes(ty, call_seed, before, index),
            );
        }
    }
    for lane in 0..LIVE_LANES {
        put(2 * n + lane, &live_value(lane).to_le_bytes());
    }
    (out, state.wrapping_add(2))
}

const SEEDS: [(u64, u64); 4] = [
    (0, 0),
    (1, 41),
    (0xdead_beef_cafe_f00d, 0x0102_0304_0506_0708),
    (u64::MAX, u64::MAX - 1),
];

// ---------------------------------------------------------------------------
// The module under test
// ---------------------------------------------------------------------------

fn target_info(triple: &str) -> trust_ir::TargetInfo {
    trust_ir::TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    }
}

/// A call returning `n` results, for an `n` known only at run time.
fn call_n(
    f: &mut FunctionBuilder<'_>,
    callee: Result<FuncId, (ValueId, FuncTyId, CallingConv)>,
    args: Vec<ValueId>,
    n: usize,
) -> Vec<ValueId> {
    macro_rules! dispatch {
        ($($k:literal)*) => {
            match n {
                $($k => match callee {
                    Ok(id) => f.call_results::<$k>(id, args).to_vec(),
                    Err((ptr, sig, cc)) => {
                        f.call_indirect_results_cc::<$k>(ptr, sig, args, cc).to_vec()
                    }
                },)*
                _ => panic!("no dispatch arm for {n} results"),
            }
        };
    }
    dispatch!(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16)
}

/// Emit result `index` of type `ty` from `(seed, before)`, mirroring
/// [`result_bytes`].
fn emit_result(
    f: &mut FunctionBuilder<'_>,
    ty: &Ty,
    seed: ValueId,
    before: ValueId,
    index: usize,
) -> ValueId {
    let mul = f.iconst(Ty::U64, i128::from(multiplier(index)));
    let product = f.binop(BinOp::Mul, Ty::U64, seed, mul);
    let with_before = f.binop(BinOp::Add, Ty::U64, product, before);
    let offset = f.iconst(Ty::U64, index as i128);
    let w = f.binop(BinOp::Add, Ty::U64, with_before, offset);
    let shifted = |f: &mut FunctionBuilder<'_>, amount: i128| {
        let amount = f.iconst(Ty::U64, amount);
        f.binop(BinOp::LShr, Ty::U64, w, amount)
    };
    match ty {
        Ty::U64 => w,
        Ty::I64 => f.cast(CastOp::Bitcast, Ty::U64, Ty::I64, w),
        Ty::U32 | Ty::I32 | Ty::I16 | Ty::I8 => f.cast(CastOp::Trunc, Ty::U64, ty.clone(), w),
        Ty::Bool => {
            let bit = shifted(f, 7);
            let one = f.iconst(Ty::U64, 1);
            let masked = f.binop(BinOp::And, Ty::U64, bit, one);
            let zero = f.iconst(Ty::U64, 0);
            f.icmp(ICmpOp::Ne, Ty::U64, masked, zero)
        }
        Ty::F64 => {
            let exact = shifted(f, 11);
            f.cast(CastOp::UIToFP, Ty::U64, Ty::F64, exact)
        }
        Ty::F32 => {
            let exact = shifted(f, 40);
            f.cast(CastOp::UIToFP, Ty::U64, Ty::F32, exact)
        }
        Ty::I128 => {
            let mask = f.iconst(Ty::U64, i128::from(I128_HIGH_MASK));
            let high = f.binop(BinOp::Xor, Ty::U64, w, mask);
            let low = f.cast(CastOp::ZExt, Ty::U64, Ty::I128, w);
            let high = f.cast(CastOp::ZExt, Ty::U64, Ty::I128, high);
            let sixty_four = f.iconst(Ty::I128, 64);
            let high = f.binop(BinOp::Shl, Ty::I128, high, sixty_four);
            f.binop(BinOp::Or, Ty::I128, high, low)
        }
        other => panic!("no lowering for {other:?}"),
    }
}

/// How the multi-result producer and relay are declared, so each control
/// varies exactly one property of the otherwise-admitted module.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Producer {
    /// `Fast`, `External`: admitted, and linkable into an AOT object (the x86-64
    /// object path cannot yet bind a reference to an `Internal` function).
    Admitted,
    /// `Fast`, `Internal`: TY's semantic-lane shape. Admitted; the x86-64 JIT
    /// compiles it, the x86-64 object path refuses its local references.
    Internal,
    /// `External` under the given convention.
    Convention(CallingConv),
}

/// The module for one shape:
///
/// * `produce_<tag>(state, seed) -> (returns…)` — the multi-result callee. A
///   volatile read-modify-write of `*state` makes it impure, so it is never
///   spliced into a caller.
/// * `relay_<tag>(state, seed) -> (returns…)` — calls `produce` and returns
///   its results: a callee that is also a caller of the convention.
/// * `direct_<tag>(state, live, seed, out)` — exported C wrapper: loads
///   `LIVE_LANES` values, calls `produce` then `relay`, and stores every result
///   of both calls and every live value.
/// * `indirect_<tag>(callee, state, live, seed, out)` — the same through a
///   `Fast` `CallIndirect` of the pointer it is given.
/// * `produce_addr_<tag>() -> ptr` — exported; the producer's address, so a C
///   driver can hand it to `indirect_<tag>` without naming the producer.
fn shape_module(shape: &Shape, triple: &str, producer: Producer) -> trust_ir::Module {
    let tag = shape.tag;
    let n = shape.returns.len();
    let mut m = ModuleBuilder::new_with_target_info(
        format!("x86_64_internal_multi_result_{tag}"),
        target_info(triple),
    );
    let sig = m.add_func_type(vec![Ty::Ptr, Ty::U64], shape.returns.clone());
    let internal = |f: &mut FunctionBuilder<'_>| {
        let (cc, linkage) = match producer {
            Producer::Admitted => (CallingConv::Fast, Linkage::External),
            Producer::Internal => (CallingConv::Fast, Linkage::Internal),
            Producer::Convention(cc) => (cc, Linkage::External),
        };
        f.set_calling_conv(cc);
        f.set_linkage(linkage);
    };
    let call_cc = match producer {
        Producer::Convention(cc) => cc,
        _ => CallingConv::Fast,
    };

    let produce = {
        let mut f = m.function(format!("produce_{tag}"), sig);
        internal(&mut f);
        let entry = f.create_block();
        let state = f.add_block_param(entry, Ty::Ptr);
        let seed = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let before = f.load_volatile(Ty::U64, state);
        let one = f.iconst(Ty::U64, 1);
        let after = f.binop(BinOp::Add, Ty::U64, before, one);
        f.store_volatile(Ty::U64, state, after);
        let results: Vec<_> = shape
            .returns
            .iter()
            .enumerate()
            .map(|(index, ty)| emit_result(&mut f, ty, seed, before, index))
            .collect();
        f.ret(results);
        f.build()
    };

    let relay = {
        let mut f = m.function(format!("relay_{tag}"), sig);
        internal(&mut f);
        let entry = f.create_block();
        let state = f.add_block_param(entry, Ty::Ptr);
        let seed = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let results = call_n(&mut f, Ok(produce), vec![state, seed], n);
        f.ret(results);
        f.build()
    };

    for indirect in [false, true] {
        let mut params = vec![];
        if indirect {
            params.push(Ty::Func(sig));
        }
        params.extend([Ty::Ptr, Ty::Ptr, Ty::U64, Ty::Ptr]);
        let wrapper_sig = m.add_func_type(params.clone(), vec![]);
        let name = if indirect { "indirect" } else { "direct" };
        let mut f = m.function(format!("{name}_{tag}"), wrapper_sig);
        let entry = f.create_block();
        let args: Vec<_> = params
            .into_iter()
            .map(|ty| f.add_block_param(entry, ty))
            .collect();
        let offset = usize::from(indirect);
        let (state, live, seed, out) = (
            args[offset],
            args[offset + 1],
            args[offset + 2],
            args[offset + 3],
        );
        f.switch_to_block(entry);
        let preserved: Vec<_> = (0..LIVE_LANES)
            .map(|lane| {
                let pointer = f.gep_byte_offset(live, (lane * 8) as u64);
                f.load_volatile(Ty::U64, pointer)
            })
            .collect();
        let delta = f.iconst(Ty::U64, i128::from(SECOND_SEED_DELTA));
        let (first, second) = if indirect {
            let callee: Result<FuncId, _> = Err((args[0], sig, call_cc));
            let first = call_n(&mut f, callee, vec![state, seed], n);
            let seed2 = f.binop(BinOp::Add, Ty::U64, seed, delta);
            let second = call_n(&mut f, callee, vec![state, seed2], n);
            (first, second)
        } else {
            let first = call_n(&mut f, Ok(produce), vec![state, seed], n);
            let seed2 = f.binop(BinOp::Add, Ty::U64, seed, delta);
            let second = call_n(&mut f, Ok(relay), vec![state, seed2], n);
            (first, second)
        };
        let lanes = first
            .into_iter()
            .zip(shape.returns.iter().cloned())
            .chain(second.into_iter().zip(shape.returns.iter().cloned()))
            .chain(preserved.into_iter().map(|value| (value, Ty::U64)));
        for (lane, (value, ty)) in lanes.enumerate() {
            let pointer = f.gep_byte_offset(out, (lane * LANE_BYTES) as u64);
            // A volatile i128 store is refused (it would split into two
            // accesses) and a volatile `bool` access is outside the
            // volatile-trace obligation's model; the out buffer escapes, so a
            // plain store is kept either way.
            if matches!(ty, Ty::I128 | Ty::Bool) {
                f.store(ty, pointer, value);
            } else {
                f.store_volatile(ty, pointer, value);
            }
        }
        f.ret(vec![]);
        f.build();
    }

    {
        let addr_sig = m.add_func_type(vec![], vec![Ty::Func(sig)]);
        let mut f = m.function(format!("produce_addr_{tag}"), addr_sig);
        let entry = f.create_block();
        f.switch_to_block(entry);
        let address = f.fn_addr(sig, produce);
        f.ret(vec![address]);
        f.build();
    }

    let module = m.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(
        validate_module(&module),
        [],
        "{tag}: the probe module is valid IR"
    );
    module
}

fn compile(module: &trust_ir::Module, triple: &str, opt: OptLevel) -> Result<Vec<u8>, String> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).expect("a known triple"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .map(|result| result.object_code)
    .map_err(|e| format!("{e:?}"))
}

// ===========================================================================
// (A) Admission
// ===========================================================================

#[test]
fn every_shape_compiles_for_both_system_v_object_formats_at_every_level() {
    for shape in shapes() {
        for triple in [DARWIN, LINUX] {
            let module = shape_module(&shape, triple, Producer::Admitted);
            for opt in ALL_OPT {
                let object = compile(&module, triple, opt).unwrap_or_else(|e| {
                    panic!(
                        "{} {triple} {opt:?}: the admitted shape must compile: {e}",
                        shape.tag
                    )
                });
                assert!(!object.is_empty());
            }
        }
    }
}

fn refusal(module: &trust_ir::Module, triple: &str) -> String {
    compile(module, triple, OptLevel::O0)
        .err()
        .unwrap_or_else(|| panic!("expected a fail-closed refusal for {triple}"))
}

/// A C-family or Rust convention names an ABI implemented outside TrustCG, and
/// none of them returns a third integer in RCX: the definition is refused by
/// name, whatever its linkage.
#[test]
fn a_foreign_convention_definition_is_refused_by_name() {
    let shape = &shapes()[0];
    // (Conventions outside the C register ABI, such as SysV64 or Win64, are
    // refused before this gate by the adapter's convention guard.)
    for cc in [CallingConv::C, CallingConv::Rust] {
        let module = shape_module(shape, DARWIN, Producer::Convention(cc));
        let error = refusal(&module, DARWIN);
        assert!(
            error.contains("[TCG-X86-MULTI-RESULT]")
                && error.contains("function `produce_int3` returns 3 results")
                && error.contains(&format!("under calling convention {cc:?}")),
            "{cc:?}: {error}"
        );
    }
}

/// A module with one call edge to a bodyless declaration of a three-integer
/// signature, under `callee_cc`.
fn declaration_call_module(callee_cc: CallingConv) -> trust_ir::Module {
    let mut m = ModuleBuilder::new_with_target_info("decl_callee", target_info(DARWIN));
    let sig = m.add_func_type(vec![], vec![Ty::I64; 3]);
    let decl = m.declare_function("elsewhere", sig);
    let caller_sig = m.add_func_type(vec![], vec![Ty::I64]);
    let mut f = m.function("caller", caller_sig);
    let entry = f.create_block();
    f.switch_to_block(entry);
    let [first, _, _] = f.call_results::<3>(decl, vec![]);
    f.ret(vec![first]);
    f.build();
    let mut module = m.build().expect("ModuleBuilder::build: test fixture");
    for function in &mut module.functions {
        if function.name == "elsewhere" {
            function.calling_conv = callee_cc;
        }
    }
    module
}

/// The DIRECT-CALL site reads the callee's convention: a C declaration is
/// refused by name, a Fast one (a TrustCG-convention callee in another
/// object) is admitted.
#[test]
fn a_direct_call_is_decided_by_the_callee_convention() {
    let error = refusal(&declaration_call_module(CallingConv::C), DARWIN);
    assert!(
        error.contains("[TCG-X86-MULTI-RESULT]")
            && error.contains("a direct call to `elsewhere` returns 3 results")
            && error.contains("under calling convention C"),
        "{error}"
    );
    let module = declaration_call_module(CallingConv::Fast);
    for opt in ALL_OPT {
        compile(&module, DARWIN, opt).unwrap_or_else(|e| panic!("{opt:?}: {e}"));
    }
}

/// The INDIRECT-CALL site reads its own declared convention: a C-convention
/// `CallIndirect` of a three-integer signature is refused by name.
#[test]
fn a_c_convention_indirect_call_is_refused_by_name() {
    let mut m = ModuleBuilder::new_with_target_info("indirect_c", target_info(DARWIN));
    let sig = m.add_func_type(vec![], vec![Ty::I64; 3]);
    let caller_sig = m.add_func_type(vec![Ty::Func(sig)], vec![Ty::I64]);
    let mut f = m.function("caller", caller_sig);
    let entry = f.create_block();
    let callee = f.add_block_param(entry, Ty::Func(sig));
    f.switch_to_block(entry);
    let [first, _, _] = f.call_indirect_results_cc::<3>(callee, sig, vec![], CallingConv::C);
    f.ret(vec![first]);
    f.build();
    let error = refusal(
        &m.build().expect("ModuleBuilder::build: test fixture"),
        DARWIN,
    );
    assert!(
        error.contains("[TCG-X86-MULTI-RESULT]")
            && error.contains("a CallIndirect returns 3 results")
            && error.contains("under calling convention C"),
        "{error}"
    );
}

/// NON-VACUITY: the same C convention with a C-shaped return (two integers,
/// RAX:RDX) is untouched by the gate.
#[test]
fn a_c_shaped_return_under_the_c_convention_still_compiles() {
    let shape = Shape {
        tag: "c2",
        returns: vec![Ty::I64, Ty::U64],
    };
    let module = shape_module(&shape, DARWIN, Producer::Convention(CallingConv::C));
    for opt in ALL_OPT {
        compile(&module, DARWIN, opt).unwrap_or_else(|e| panic!("{opt:?}: {e}"));
    }
}

/// Windows x64 defines no internal extension: its selector still refuses the
/// second integer result, by the Win64 ABI's own reason.
#[test]
fn windows_x64_still_refuses() {
    let triple = "x86_64-pc-windows-msvc";
    let module = shape_module(&shapes()[0], triple, Producer::Admitted);
    let error = refusal(&module, triple);
    assert!(
        error.contains("WindowsX64") && error.contains("no second integer result register"),
        "{error}"
    );
}

/// Eight integer results: one past R9. Refused by the selector, never aliased.
#[test]
fn a_shape_past_the_internal_file_is_refused() {
    let shape = Shape {
        tag: "int8",
        returns: vec![Ty::I64; 8],
    };
    let module = shape_module(&shape, DARWIN, Producer::Admitted);
    let error = refusal(&module, DARWIN);
    assert!(
        error.contains("result 7")
            && error.contains("RAX,RDX,RCX,RSI,RDI,R8,R9")
            && error.contains("never alias an earlier result"),
        "{error}"
    );
}

/// Target parity: the module every x86-64 test here compiles is also compiled
/// by the AArch64 backend (X0-X7 / V0-V7).
#[test]
fn the_same_modules_compile_for_aarch64() {
    for shape in shapes() {
        let module = shape_module(&shape, "aarch64-apple-darwin", Producer::Admitted);
        compile(&module, "aarch64-apple-darwin", OptLevel::O1)
            .unwrap_or_else(|e| panic!("{}: AArch64 compiles the same module: {e}", shape.tag));
    }
}

/// TY's Fast/Internal multi-result shape now compiles through the x86-64
/// Mach-O object path: local references have an emitted-byte binding check.
#[test]
fn internal_linkage_is_admitted_by_the_multi_result_gate() {
    for shape in shapes() {
        let module = shape_module(&shape, DARWIN, Producer::Internal);
        compile(&module, DARWIN, OptLevel::O0).unwrap_or_else(|error| {
            panic!("{}: internal Darwin calls must compile: {error}", shape.tag)
        });
    }
}

// ===========================================================================
// (B) Machine-code shape
// ===========================================================================

fn scratch_dir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_x86_internal_multi_result_{tag}_{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

/// `(direct calls, register-indirect calls)` in each function of an x86-64
/// object, from the host `objdump`, or `None` when there is none.
fn call_counts(object: &Path) -> Option<std::collections::BTreeMap<String, (usize, usize)>> {
    let output = Command::new("objdump")
        .args(["-d", "--no-show-raw-insn"])
        .arg(object)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let text = String::from_utf8_lossy(&output.stdout);
    let mut counts = std::collections::BTreeMap::new();
    let mut current: Option<String> = None;
    for line in text.lines() {
        let trimmed = line.trim();
        if let Some(label) = trimmed.strip_suffix(">:") {
            if let Some((_, name)) = label.split_once('<') {
                let name = name.trim_start_matches('_').to_string();
                counts.insert(name.clone(), (0, 0));
                current = Some(name);
            }
            continue;
        }
        let Some(name) = &current else { continue };
        let mut fields = trimmed.split_whitespace();
        // `<address>: <mnemonic> <operands>`.
        let (Some(_), Some(mnemonic)) = (fields.next(), fields.next()) else {
            continue;
        };
        if mnemonic == "call" || mnemonic == "callq" {
            let entry = counts.get_mut(name).expect("current function");
            if fields
                .next()
                .is_some_and(|operand| operand.starts_with('*'))
            {
                entry.1 += 1;
            } else {
                entry.0 += 1;
            }
        }
    }
    Some(counts)
}

#[test]
fn every_wrapper_keeps_real_calls_at_every_level() {
    let dir = scratch_dir("calls");
    for shape in shapes() {
        let module = shape_module(&shape, HOST_X86_TRIPLE, Producer::Admitted);
        for opt in ALL_OPT {
            let object = compile(&module, HOST_X86_TRIPLE, opt).expect("admitted");
            let path = dir.join(format!("{}_{opt:?}.o", shape.tag));
            fs::write(&path, &object).expect("write object");
            let Some(counts) = call_counts(&path) else {
                eprintln!("SKIP machine-code shape: no usable objdump on this host");
                return;
            };
            let tag = shape.tag;
            let get = |name: String| {
                *counts
                    .get(&name)
                    .unwrap_or_else(|| panic!("{tag} {opt:?}: no `{name}` in {counts:?}"))
            };
            assert!(
                get(format!("direct_{tag}")).0 >= 2,
                "{tag} {opt:?}: `direct` keeps both direct calls: {counts:?}"
            );
            assert!(
                get(format!("indirect_{tag}")).1 >= 2,
                "{tag} {opt:?}: `indirect` keeps both register calls: {counts:?}"
            );
            assert!(
                get(format!("relay_{tag}")).0 >= 1,
                "{tag} {opt:?}: `relay` keeps its call: {counts:?}"
            );
        }
    }
    let _ = fs::remove_dir_all(&dir);
}

// ===========================================================================
// (C) Execution
// ===========================================================================

fn c_driver(shapes: &[Shape]) -> String {
    let mut c = String::from(
        "#include <stdint.h>\n#include <stdio.h>\n#include <string.h>\n\n\
         typedef void *(*addr_fn)(void);\n\n",
    );
    for shape in shapes {
        let tag = shape.tag;
        writeln!(
            c,
            "void direct_{tag}(uint64_t *, const uint64_t *, uint64_t, uint8_t *);\n\
             void indirect_{tag}(void *, uint64_t *, const uint64_t *, uint64_t, uint8_t *);\n\
             void *produce_addr_{tag}(void);"
        )
        .unwrap();
    }
    c.push_str(
        "\nstatic void dump(const char *tag, int indirect, uint64_t seed, uint64_t state,\n\
         \x20                const uint8_t *out, size_t len) {\n\
         \x20   printf(\"%s %d %016llx %016llx \", tag, indirect, (unsigned long long)seed,\n\
         \x20          (unsigned long long)state);\n\
         \x20   for (size_t i = 0; i < len; i++) printf(\"%02x\", out[i]);\n\
         \x20   printf(\"\\n\");\n}\n\nint main(void) {\n",
    );
    writeln!(c, "    uint64_t live[{LIVE_LANES}];").unwrap();
    writeln!(
        c,
        "    for (int i = 0; i < {LIVE_LANES}; i++) live[i] = 0x0123456789abcdefULL * (uint64_t)(i + 3);"
    )
    .unwrap();
    for shape in shapes {
        let tag = shape.tag;
        let len = (2 * shape.returns.len() + LIVE_LANES) * LANE_BYTES;
        for (seed, state) in SEEDS {
            for indirect in [0, 1] {
                writeln!(
                    c,
                    "    {{ uint8_t out[{len}]; memset(out, 0x{FILL:02x}, sizeof out);\n\
                     \x20     uint64_t state = 0x{state:016x}ULL;\n\
                     \x20     {call};\n\
                     \x20     dump(\"{tag}\", {indirect}, 0x{seed:016x}ULL, state, out, sizeof out); }}",
                    call = if indirect == 1 {
                        format!(
                            "indirect_{tag}(produce_addr_{tag}(), &state, live, 0x{seed:016x}ULL, out)"
                        )
                    } else {
                        format!("direct_{tag}(&state, live, 0x{seed:016x}ULL, out)")
                    },
                )
                .unwrap();
            }
        }
    }
    c.push_str("    return 0;\n}\n");
    c
}

fn cc_x86_64(args: &[String]) -> (bool, String) {
    let mut cmd = Command::new("cc");
    if cfg!(target_os = "macos") {
        cmd.arg("-arch").arg("x86_64");
    }
    cmd.args(args);
    let out = command_output_with_timeout(&mut cmd, codegen_link_timeout()).expect("cc must spawn");
    (
        !out.timed_out && out.output.status.success(),
        String::from_utf8_lossy(&out.output.stderr).into_owned(),
    )
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// The expected driver output line for one call.
fn expected_line(shape: &Shape, indirect: u8, seed: u64, state: u64) -> String {
    let (out, final_state) = expected_output(shape, seed, state);
    format!(
        "{} {indirect} {seed:016x} {final_state:016x} {}",
        shape.tag,
        hex(&out)
    )
}

#[test]
fn internal_multi_results_execute_exactly_at_every_level() {
    let all = shapes();
    if let Ok(dir) = std::env::var("TRUST_CG_X86_MULTI_RESULT_ARTIFACTS") {
        write_external_executor_artifacts(Path::new(&dir), &all);
    }
    if !x86_64_oracle_enabled("internal_multi_results_execute_exactly_at_every_level") {
        return;
    }
    let dir = scratch_dir("run");
    let driver = dir.join("driver.c");
    fs::write(&driver, c_driver(&all)).expect("write driver");
    let expected: Vec<String> = all
        .iter()
        .flat_map(|shape| {
            SEEDS.iter().flat_map(move |&(seed, state)| {
                [0u8, 1].map(|indirect| expected_line(shape, indirect, seed, state))
            })
        })
        .collect();
    for opt in ALL_OPT {
        let mut args = vec![
            "-O1".to_string(),
            "-o".to_string(),
            dir.join("bin").to_string_lossy().into_owned(),
            driver.to_string_lossy().into_owned(),
        ];
        for shape in &all {
            let module = shape_module(shape, HOST_X86_TRIPLE, Producer::Admitted);
            let object = compile(&module, HOST_X86_TRIPLE, opt).expect("admitted");
            let path = dir.join(format!("{}.o", shape.tag));
            fs::write(&path, &object).expect("write object");
            args.push(path.to_string_lossy().into_owned());
        }
        let (ok, stderr) = cc_x86_64(&args);
        assert!(ok, "{opt:?}: link failed; files={dir:?}\n{stderr}");
        let run = run_executable_with_timeout(&dir.join("bin"), codegen_run_timeout())
            .expect("run the multi-result driver");
        assert!(
            !run.timed_out && run.output.status.success(),
            "{opt:?}: driver failed"
        );
        let stdout = String::from_utf8_lossy(&run.output.stdout);
        let actual: Vec<&str> = stdout.lines().collect();
        assert_eq!(actual.len(), expected.len(), "{opt:?}: line count");
        for (actual, expected) in actual.iter().zip(&expected) {
            assert_eq!(
                actual, expected,
                "{opt:?}: a result, live value or side effect differs"
            );
        }
        eprintln!(
            "{opt:?}: {} calls x2 chained multi-result edges exact ({} shapes, direct + indirect)",
            expected.len(),
            all.len()
        );
    }
    let _ = fs::remove_dir_all(&dir);
}

/// Call every exported wrapper of `shape` in `buffer` (a JIT image of
/// [`shape_module`] for `Producer::Internal`) on every seed, directly and
/// through the indirect wrapper, and compare every result byte, the live
/// values and the side effect with [`expected_output`]. `label` names the
/// compile in a failure.
///
/// The JIT installs code for the host it runs on, so only a System V x86-64
/// host may call this.
fn assert_jit_image_executes_exactly(
    shape: &Shape,
    buffer: &trust_cg_codegen::jit::ExecutableBuffer,
    label: &str,
) {
    type Direct = extern "C" fn(*mut u64, *const u64, u64, *mut u8);
    type Indirect = extern "C" fn(*const u8, *mut u64, *const u64, u64, *mut u8);
    type Addr = extern "C" fn() -> *const u8;
    let tag = shape.tag;
    let live: Vec<u64> = (0..LIVE_LANES).map(live_value).collect();
    // SAFETY: only the exported C wrappers cross Rust's ABI, with the
    // signatures the module declares for them.
    let (direct, indirect, addr) = unsafe {
        (
            buffer
                .get_fn_bound::<Direct>(&format!("direct_{tag}"))
                .unwrap(),
            buffer
                .get_fn_bound::<Indirect>(&format!("indirect_{tag}"))
                .unwrap(),
            buffer
                .get_fn_bound::<Addr>(&format!("produce_addr_{tag}"))
                .unwrap(),
        )
    };
    let callee = addr.as_ref()();
    for (seed, state0) in SEEDS {
        for use_indirect in [false, true] {
            let (expected, expected_state) = expected_output(shape, seed, state0);
            let mut out = vec![FILL; expected.len()];
            let mut state = state0;
            if use_indirect {
                indirect.as_ref()(callee, &mut state, live.as_ptr(), seed, out.as_mut_ptr());
            } else {
                direct.as_ref()(&mut state, live.as_ptr(), seed, out.as_mut_ptr());
            }
            assert_eq!(
                (hex(&out), state),
                (hex(&expected), expected_state),
                "{label} indirect={use_indirect} seed={seed:#x}"
            );
        }
    }
}

/// The x86-64 JIT compile of TY's exact shape at `opt`: `jit_fast`'s profile
/// (its LinearScan allocator included) with the validation `mode` stated, or
/// the profile's own default when `mode` is `None`.
#[allow(clippy::result_large_err)] // Test helper returns the compiler's own error type unchanged.
fn jit_compile(
    module: &trust_ir::Module,
    opt: OptLevel,
    mode: Option<JitValidationMode>,
) -> Result<trust_cg_codegen::compiler::JitCompilationResult, CompileError> {
    let mut config = CompilerConfig::jit_fast(Target::X86_64);
    config.opt_level = opt;
    config.jit_validation_mode_override = mode;
    Compiler::new_for_target_spec(
        config,
        TargetSpec::parse(HOST_X86_TRIPLE).expect("a known triple"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile_module_to_jit(module, &std::collections::HashMap::new())
}

/// The JIT lane, TY's exact shape: `Internal` `Fast` multi-result functions
/// behind exported C wrappers, compiled by the x86-64 JIT at O0-O3 and called
/// in process. Type-checked on every host; EXECUTED only on an x86-64 host,
/// since the JIT installs code for the host it runs on.
///
/// The compiles state the dev-only `Unchecked` validation mode, the loud
/// opt-in the other x86-64 JIT codegen suites state
/// (`CompilerConfig::for_host_jit_unchecked`): the executed bytes carry no
/// proof evidence, and each image's provenance must say so. This is execution
/// evidence of the convention on chosen inputs. The verifying default refuses
/// these bodies; `the_verifying_x86_jit_publishes_these_bodies_only_with_proof`
/// holds that refusal to the proof gate (OD-219).
#[test]
fn jit_internal_linkage_multi_results_execute_exactly() {
    if !cfg!(target_arch = "x86_64") || cfg!(windows) {
        eprintln!("SKIP x86-64 JIT execution: this host is not System V x86-64");
        return;
    }
    for shape in shapes() {
        let tag = shape.tag;
        let module = shape_module(&shape, HOST_X86_TRIPLE, Producer::Internal);
        for opt in ALL_OPT {
            let compiled = jit_compile(&module, opt, Some(JitValidationMode::Unchecked))
                .unwrap_or_else(|e| panic!("{tag} {opt:?}: JIT compile failed: {e}"));
            let validation = compiled
                .validation
                .as_ref()
                .unwrap_or_else(|| panic!("{tag} {opt:?}: the JIT records its provenance"));
            assert_eq!(
                validation.mode,
                JitValidationMode::Unchecked,
                "{tag} {opt:?}: the image is labelled with the mode it ran under"
            );
            assert!(
                !validation.every_function_semantics_verified(),
                "{tag} {opt:?}: an Unchecked image claims no proof evidence"
            );
            assert_jit_image_executes_exactly(&shape, &compiled.buffer, &format!("{tag} {opt:?}"));
        }
    }
}

/// The same modules through the x86-64 JIT's default VERIFYING mode
/// (`jit_fast` resolves to `CachedVerified` on x86-64), which publishes a
/// function only when every emitted row has complete proof evidence. Each
/// compile either publishes with every function's semantics verified, and
/// then executes exactly like the unchecked lane, or is refused before
/// publication by the proof-promotion gate (`ProofPromotionRejected` for
/// x86-64): never published on lesser evidence, never another error. A row
/// whose only evidence is sampled (statistical) has no proof credit (E0.2),
/// so a body with such a row takes the refusal.
#[test]
fn the_verifying_x86_jit_publishes_these_bodies_only_with_proof() {
    if !cfg!(target_arch = "x86_64") || cfg!(windows) {
        eprintln!("SKIP x86-64 JIT execution: this host is not System V x86-64");
        return;
    }
    assert_eq!(
        CompilerConfig::jit_fast(Target::X86_64).jit_validation_mode(),
        JitValidationMode::CachedVerified,
        "the x86-64 JIT profile verifies by default"
    );
    let (mut published, mut refused) = (0usize, 0usize);
    for shape in shapes() {
        let tag = shape.tag;
        let module = shape_module(&shape, HOST_X86_TRIPLE, Producer::Internal);
        for opt in ALL_OPT {
            match jit_compile(&module, opt, None) {
                Ok(compiled) => {
                    let validation = compiled
                        .validation
                        .as_ref()
                        .unwrap_or_else(|| panic!("{tag} {opt:?}: the JIT records its provenance"));
                    assert!(
                        validation.mode.requires_jit_verification()
                            && validation.every_function_semantics_verified(),
                        "{tag} {opt:?}: a verifying JIT published an image whose functions are \
                         not all verified: {validation:?}"
                    );
                    assert_jit_image_executes_exactly(
                        &shape,
                        &compiled.buffer,
                        &format!("{tag} {opt:?} (verified)"),
                    );
                    published += 1;
                }
                Err(CompileError::ProofPromotionRejected {
                    target: Target::X86_64,
                    reason,
                }) => {
                    eprintln!("{tag} {opt:?}: refused by the proof gate: {reason}");
                    refused += 1;
                }
                Err(other) => panic!(
                    "{tag} {opt:?}: the verifying JIT must publish with proof or refuse at the \
                     proof gate, not fail otherwise: {other}"
                ),
            }
        }
    }
    eprintln!("verifying x86-64 JIT: {published} compile(s) published, {refused} refused");
}

/// Objects and expected bytes for an executor outside this process: one
/// Darwin object per shape and level, plus `expected.txt` with one line per
/// wrapper call in the driver's format and `layout.txt` naming each shape's
/// result types and result registers in order.
fn write_external_executor_artifacts(dir: &Path, shapes: &[Shape]) {
    fs::create_dir_all(dir).expect("artifact dir");
    let mut layout = String::new();
    let mut expected = String::new();
    for shape in shapes {
        let module = shape_module(shape, DARWIN, Producer::Admitted);
        for opt in ALL_OPT {
            let object = compile(&module, DARWIN, opt).expect("admitted");
            fs::write(dir.join(format!("{}_{opt:?}.o", shape.tag)), object).expect("object");
        }
        let (mut gpr, mut xmm) = (0usize, 0usize);
        let gprs = ["rax", "rdx", "rcx", "rsi", "rdi", "r8", "r9"];
        let registers: Vec<String> = shape
            .returns
            .iter()
            .map(|ty| match ty {
                Ty::F32 | Ty::F64 => {
                    xmm += 1;
                    format!("xmm{}", xmm - 1)
                }
                Ty::I128 => {
                    gpr += 2;
                    format!("{}:{}", gprs[gpr - 2], gprs[gpr - 1])
                }
                _ => {
                    gpr += 1;
                    gprs[gpr - 1].to_string()
                }
            })
            .collect();
        writeln!(
            layout,
            "{} {} {}",
            shape.tag,
            shape
                .returns
                .iter()
                .map(|ty| format!("{ty:?}"))
                .collect::<Vec<_>>()
                .join(","),
            registers.join(",")
        )
        .unwrap();
        for (seed, state) in SEEDS {
            for indirect in [0u8, 1] {
                writeln!(expected, "{}", expected_line(shape, indirect, seed, state)).unwrap();
            }
            // The callee alone: its result bytes for one call, for an executor
            // that reads the result registers directly.
            let bytes: Vec<String> = shape
                .returns
                .iter()
                .enumerate()
                .map(|(index, ty)| hex(&result_bytes(ty, seed, state, index)))
                .collect();
            writeln!(
                expected,
                "callee {} {seed:016x} {state:016x} {}",
                shape.tag,
                bytes.join(",")
            )
            .unwrap();
        }
    }
    let live: Vec<String> = (0..LIVE_LANES)
        .map(|lane| format!("{:016x}", live_value(lane)))
        .collect();
    writeln!(layout, "live {}", live.join(",")).unwrap();
    writeln!(layout, "lane_bytes {LANE_BYTES} fill {FILL:02x}").unwrap();
    fs::write(dir.join("layout.txt"), layout).expect("layout");
    fs::write(dir.join("expected.txt"), expected).expect("expected");
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
