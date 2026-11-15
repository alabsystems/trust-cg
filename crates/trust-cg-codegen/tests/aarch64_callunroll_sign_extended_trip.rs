// trust-cg-codegen - the unrollers' trip count of a narrow IV compared after a sign extension
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `i: iN = init; loop { body; i = i + 1; if sext(i) as iW >=u bound { break } }`
//! with `N < W` and `bound` above the `iN` range, run through the JIT at
//! O0/O2/O3.
//!
//! An `i8`/`i16` lives in a 32-bit register: ISel emits `AddRI t, i, #1`
//! (which does not wrap at `N` bits) followed by `Sxtb`/`Sxth w, t`, and the
//! exit compare reads `w`. The compared value is `sext_N(init + m)`: past
//! `iN::MAX` it turns negative, and as an unsigned `W`-bit value it is then
//! above `bound`, so the loop exits at the wrap. A trip model that reads the
//! extension as a copy counts `init + m` at the compare's width instead and
//! finds a later exit.
//!
//! The constant-trip tiers splice `K` body copies ahead of the one surviving
//! trip test, which is exact only when the modeled trip count is the real one:
//!
//! * `call-unroll` fully unrolls a call-bearing loop at `K = N_model` (4..=8),
//!   so a wrong model runs the body, and its call, `N_model` times;
//! * `partial-unroll` peels `N_model mod K` and tests once per `K` trips, so a
//!   wrong model runs the call-free twin past the real exit when it is not a
//!   multiple of `K`.
//!
//! The invariant these rows pin: a trip-count model reads an extension as the
//! extension it is (or refuses it), never as a copy. The shared IV recognizer
//! (`try_iv_increment`) admits a chain only when every step keeps at least the
//! compare's width of low bits, so both tiers decline the extended rows. The
//! `i32` control rows compare at the IV's own width, and both tiers still
//! unroll them. The call-bearing rows compare the
//! return value and the sequence of `obs` calls with a plain Rust model; the
//! call-free rows compare with the trust-ir reference interpreter. The rows
//! are bounded host executions; they are tests, not a proof.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, CastOp, FuncId, ICmpOp, InterpretOptions, InterpretValue, Interpreter, Ty};
use trust_ir_build::ModuleBuilder;

const TRIPLE: &str = if cfg!(target_os = "linux") {
    "aarch64-unknown-linux-gnu"
} else {
    "aarch64-apple-darwin"
};
const LEVELS: [OptLevel; 3] = [OptLevel::O0, OptLevel::O2, OptLevel::O3];

/// One loop: the narrow IV type and its bit width, the type the IV is
/// sign-extended to, the IV's initial value and the unsigned exit bound.
#[derive(Clone, Copy, Debug)]
struct Row {
    name: &'static str,
    narrow: NarrowTy,
    wide_bits: u32,
    init: i128,
    bound: i128,
}

#[derive(Clone, Copy, Debug)]
enum NarrowTy {
    I8,
    I16,
    /// The control: the IV is as wide as the compare, no extension.
    I32,
}

impl NarrowTy {
    fn ty(self) -> Ty {
        match self {
            NarrowTy::I8 => Ty::I8,
            NarrowTy::I16 => Ty::I16,
            NarrowTy::I32 => Ty::I32,
        }
    }

    fn bits(self) -> u32 {
        match self {
            NarrowTy::I8 => 8,
            NarrowTy::I16 => 16,
            NarrowTy::I32 => 32,
        }
    }
}

impl Row {
    fn wide_ty(self) -> Ty {
        if self.wide_bits == 64 {
            Ty::I64
        } else {
            Ty::I32
        }
    }

    /// The source's trip count: trips until `sext(i + 1) >=u bound`.
    fn source_trips(self) -> u64 {
        let bits = self.narrow.bits();
        let wide_mask: u128 = if self.wide_bits == 64 {
            u128::from(u64::MAX)
        } else {
            (1u128 << self.wide_bits) - 1
        };
        let mut i = self.init;
        for trip in 1..=1_000 {
            let raw = (i + 1) & ((1i128 << bits) - 1);
            i = if raw >> (bits - 1) == 1 {
                raw - (1i128 << bits)
            } else {
                raw
            };
            if (i as u128) & wide_mask >= (self.bound as u128) & wide_mask {
                return trip;
            }
        }
        panic!("{}: the source loop does not stop", self.name)
    }
}

/// Call-bearing rows: the trip counts the model derives are 4..=8, the window
/// `call-unroll` admits.
const CALL_ROWS: [Row; 3] = [
    Row {
        name: "cu_i16_to_i32",
        narrow: NarrowTy::I16,
        wide_bits: 32,
        init: 0x7FFC,
        bound: 0x8002,
    },
    Row {
        name: "cu_i8_to_i32",
        narrow: NarrowTy::I8,
        wide_bits: 32,
        init: 0x7C,
        bound: 0x82,
    },
    Row {
        name: "cu_i16_to_i64",
        narrow: NarrowTy::I16,
        wide_bits: 64,
        init: 0x7FFC,
        bound: 0x8002,
    },
];

/// Same-width control for `call-unroll`: an `i32` IV compared unsigned at 32
/// bits with no extension (6 trips). Its constants fit one `Movz` each.
const CALL_CONTROL: Row = Row {
    name: "cu_i32_control",
    narrow: NarrowTy::I32,
    wide_bits: 32,
    init: 0x10,
    bound: 0x16,
};

/// Same-width control for `partial-unroll` (25 trips).
const FACTOR_CONTROL: Row = Row {
    name: "pu_i32_control",
    narrow: NarrowTy::I32,
    wide_bits: 32,
    init: 0x10,
    bound: 0x29,
};

/// Call-free rows for `partial-unroll`, with a source trip count that is not
/// a multiple of the factor it picks.
const FACTOR_ROWS: [Row; 3] = [
    Row {
        name: "pu_i8_to_i32_a",
        narrow: NarrowTy::I8,
        wide_bits: 32,
        init: 0x73,
        bound: 0x8B,
    },
    Row {
        name: "pu_i16_to_i32",
        narrow: NarrowTy::I16,
        wide_bits: 32,
        init: 0x7FF3,
        bound: 0x800B,
    },
    Row {
        name: "pu_i8_to_i32_b",
        narrow: NarrowTy::I8,
        wide_bits: 32,
        init: 0x6F,
        bound: 0x95,
    },
];

thread_local! {
    static CALLS: std::cell::RefCell<Vec<u64>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// The kernels' external call: records its argument, returns `3v + 1`.
extern "C" fn obs(v: u64) -> u64 {
    CALLS.with(|calls| calls.borrow_mut().push(v));
    v.wrapping_mul(3).wrapping_add(1)
}

fn take_calls() -> Vec<u64> {
    CALLS.with(|calls| std::mem::take(&mut *calls.borrow_mut()))
}

/// `(x) -> acc`: `acc = x; i = init; loop { acc = body(acc); i += 1;
/// if sext(i) >=u bound { break } }; acc`, where `body` is `obs` (`with_call`)
/// or the same `3v + 1` inline.
fn module(row: Row, with_call: bool) -> (trust_ir::Module, FuncId) {
    let narrow = row.narrow.ty();
    let wide = row.wide_ty();
    let mut mb = ModuleBuilder::new(row.name);
    let obs_f = with_call.then(|| {
        let oty = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
        mb.declare_function("obs", oty)
    });
    let ty = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function(row.name, ty);
    let entry = fb.create_block();
    let x = fb.add_block_param(entry, Ty::U64);
    let header = fb.create_block();
    let i = fb.add_block_param(header, narrow.clone());
    let acc = fb.add_block_param(header, Ty::U64);
    let exit = fb.create_block();
    let result = fb.add_block_param(exit, Ty::U64);

    fb.switch_to_block(entry);
    let init = fb.iconst(narrow.clone(), row.init);
    fb.br(header, vec![init, x]);
    // The bound as the signed constant of the compare type.
    let bound_value = if row.bound >> (row.wide_bits - 1) == 1 {
        row.bound - (1i128 << row.wide_bits)
    } else {
        row.bound
    };

    fb.switch_to_block(header);
    let acc2 = match obs_f {
        Some(obs_f) => fb.call(obs_f, vec![acc]),
        None => {
            let three = fb.iconst(Ty::U64, 3);
            let one = fb.iconst(Ty::U64, 1);
            let scaled = fb.binop(BinOp::Mul, Ty::U64, acc, three);
            fb.binop(BinOp::Add, Ty::U64, scaled, one)
        }
    };
    let one = fb.iconst(narrow.clone(), 1);
    let next = fb.binop(BinOp::Add, narrow.clone(), i, one);
    let widened = if row.narrow.bits() == row.wide_bits {
        next
    } else {
        fb.cast(CastOp::SExt, narrow, wide.clone(), next)
    };
    let bound = fb.iconst(wide.clone(), bound_value);
    let done = fb.icmp(ICmpOp::Uge, wide, widened, bound);
    fb.condbr(done, exit, vec![acc2], header, vec![next, acc2]);

    fb.switch_to_block(exit);
    fb.ret(vec![result]);
    let fid = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), fid)
}

/// How many times `pass` changed the function at `opt_level`, with an explicit
/// empty disable list so the ambient `TRUST_CG_DISABLE_PASSES` cannot hide it.
fn pass_changes(module: &trust_ir::Module, opt_level: OptLevel, pass: &str) -> u32 {
    let lowered = trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
    .expect("lowering");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        target_triple: TRIPLE.into(),
        disabled_passes_override: Some(String::new()),
        ..PipelineConfig::default()
    });
    let mut changes = 0;
    for (function, _) in &lowered {
        let (_, metrics) = pipeline
            .prepare_function_with_metrics(function, None)
            .expect("prepare");
        for (name, count) in &metrics.optimization_pass_changes {
            if name == pass {
                changes += count;
            }
        }
    }
    changes
}

fn jit(module: &trust_ir::Module, opt_level: OptLevel, with_call: bool) -> JitCompilationResult {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    let symbols: HashMap<String, *const u8> = if with_call {
        HashMap::from([("obs".to_string(), obs as *const u8)])
    } else {
        HashMap::new()
    };
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &symbols)
        .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
}

/// The interpreter's result for `x`.
fn reference(module: &trust_ir::Module, fid: FuncId, x: u64) -> u64 {
    let args = vec![InterpretValue::int(Ty::U64, i128::from(x)).expect("u64 argument")];
    let out = Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 10_000_000,
            ..Default::default()
        })
        .execute_func(fid, args)
        .expect("interpreter");
    out.returns[0].as_int().expect("int").as_unsigned() as u64
}

type Kernel = extern "C" fn(u64) -> u64;

#[test]
fn the_source_trip_counts_stop_at_the_narrow_wrap() {
    // `i + 1` reaches `iN::MAX` after `MAX - init` trips and wraps on the next.
    assert_eq!(CALL_ROWS.map(Row::source_trips), [4, 4, 4]);
    assert_eq!(FACTOR_ROWS.map(Row::source_trips), [13, 13, 17]);
    assert_eq!(CALL_CONTROL.source_trips(), 6);
    assert_eq!(FACTOR_CONTROL.source_trips(), 25);
}

/// `call-unroll` declines every extended row and still unrolls the control.
#[test]
fn call_unroll_declines_the_extended_rows_and_unrolls_the_control() {
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        for row in CALL_ROWS {
            let (module, _) = module(row, true);
            assert_eq!(
                pass_changes(&module, opt_level, "call-unroll"),
                0,
                "{}: {opt_level:?}: call-unroll modeled a sign extension as a copy",
                row.name
            );
        }
        let (module, _) = module(CALL_CONTROL, true);
        assert!(
            pass_changes(&module, opt_level, "call-unroll") > 0,
            "{opt_level:?}: call-unroll must still unroll the same-width control"
        );
    }
}

/// `partial-unroll` declines every extended row and still unrolls the control.
#[test]
fn partial_unroll_declines_the_extended_rows_and_unrolls_the_control() {
    for row in FACTOR_ROWS {
        let (module, _) = module(row, false);
        assert_eq!(
            pass_changes(&module, OptLevel::O2, "partial-unroll"),
            0,
            "{}: partial-unroll modeled a sign extension as a copy",
            row.name
        );
    }
    let (module, _) = module(FACTOR_CONTROL, false);
    assert!(
        pass_changes(&module, OptLevel::O2, "partial-unroll") > 0,
        "partial-unroll must still unroll the same-width control"
    );
}

#[test]
fn call_unroll_runs_the_body_as_many_times_as_the_source() {
    let mut failures = Vec::new();
    for row in CALL_ROWS.into_iter().chain([CALL_CONTROL]) {
        let (module, _) = module(row, true);
        let trips = row.source_trips();
        for opt_level in LEVELS {
            let result = jit(&module, opt_level, true);
            // SAFETY: the signature matches the trust-ir type (u64) -> u64 and
            // `result` outlives the call.
            let entry =
                unsafe { result.buffer.get_fn_bound::<Kernel>(row.name) }.expect("entry symbol");
            for x in [1u64, 5] {
                take_calls();
                let got = entry.as_ref()(x);
                let got_calls = take_calls();
                let mut want = x;
                let mut want_calls = Vec::new();
                for _ in 0..trips {
                    want_calls.push(want);
                    want = want.wrapping_mul(3).wrapping_add(1);
                }
                if got != want || got_calls != want_calls {
                    failures.push(format!(
                        "{} {opt_level:?} x = {x}: {} calls {got_calls:?} -> {got}, \
                         want {} calls {want_calls:?} -> {want}",
                        row.name,
                        got_calls.len(),
                        want_calls.len()
                    ));
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn partial_unroll_stops_at_the_source_exit() {
    let mut failures = Vec::new();
    for row in FACTOR_ROWS.into_iter().chain([FACTOR_CONTROL]) {
        let (module, fid) = module(row, false);
        for opt_level in LEVELS {
            let result = jit(&module, opt_level, false);
            // SAFETY: the signature matches the trust-ir type (u64) -> u64 and
            // `result` outlives the call.
            let entry =
                unsafe { result.buffer.get_fn_bound::<Kernel>(row.name) }.expect("entry symbol");
            for x in [1u64, 7] {
                let want = reference(&module, fid, x);
                let got = entry.as_ref()(x);
                if got != want {
                    failures.push(format!(
                        "{} {opt_level:?} x = {x}: got {got}, want {want}",
                        row.name
                    ));
                }
            }
        }
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
