// trust-cg-codegen/tests/e2e_aarch64_post_ra_value_flow.rs
//
// AArch64 post-allocation value-flow validation (L10-P1) through the public
// `Pipeline`, on trust-ir kernels whose allocation exercises the post-RA
// stages: values live across calls (callee-saved registers, caller-saved
// clobbers), heavy pressure (spill stores, reloads, reload CSE, split load
// pairs), a jump-table switch (an early bounds-check exit and an indirect
// branch), stack-passed arguments in both directions, FP values across calls
// (D8-D15 low halves), a stack array (frame-slot addressing), a 32 KiB
// stack array (a counted stack-probe loop), a stack-protected array (the
// canary's frame cell and the epilogue check) and a 32-bit array sum (late
// post-index formation: a pointer advanced by a post-indexed load across the
// loop) and the pressure loop beside a live 16-byte stack array (spill slots
// next to a program slot); an AArch64 ELF global word exercises the lo12
// fusion of `ADRP`/`ADD` into the access (compiled only, its relocation form
// is ELF).
//
// * Every kernel at O0-O3 under the refusing policy compiles with the
//   composed comparison (`post-ra-value-flow`) and, split, both stage
//   comparisons (`post-ra-allocation`, `post-ra-frame-layout`) validated for
//   every function, and emits the object it emits with validation off.
// * Corruption controls: the real stage inputs are captured
//   (`post_ra_value_flow::snapshots`), the implementation is corrupted the way
//   a broken post-RA pass would, and the comparison must refuse it: a reload
//   from the wrong spill slot, a coalesce that merges interfering values, a
//   rematerialization of a value that changed, a callee-saved value moved to
//   a caller-saved register across a call, a frame offset off by eight, a
//   resolved branch retargeted to the wrong block, SP moved between the
//   stack-argument stores and the call, a store over a stack argument
//   between those stores and the call (a spill, an unflagged store, a store
//   of zero, frame lowering's exact stack probe), a spill slot moved
//   (consistently) onto a live program stack slot, a deleted and a
//   duplicated store, an altered use, a stack-probe loop one iteration
//   short, a stack-protector canary never stored, a post-indexed pointer
//   advanced by the wrong stride, and a fused lo12 access of another symbol.
//   The caller-saved, frame-offset, branch, SP, outgoing-area and spill-slot
//   controls judge the composed comparison the pipeline runs as well as the
//   split stage.
// * Wiring: a function outside the model (a dynamic stack allocation) is
//   refused by name under a refusing policy and reported under the
//   diagnostic one; the default schedulers tier records the post-allocation
//   stages as an uncovered run.
// * Native: the enforce-built kernels run against a C reference, and the
//   outgoing-area corruptions, emitted as is, disagree with it while the
//   uncorrupted stream agrees (macOS and Linux GNU AArch64 hosts).
//
// Evidence strength: per-compile translation validation under the
// comparison's model (`trust_cg_verify::post_ra_value_flow`) plus a bounded
// native differential on the listed inputs. Neither is a proof of the passes.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::fmt::Write as _;

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::post_ra_value_flow::snapshots::{self, Snapshot};
use trust_cg_ir::{AArch64Opcode, InstFlags, MachFunction, MachInst, MachOperand};
use trust_cg_opt::{PassValidationConfig, PassValidationSummary};
use trust_cg_verify::post_ra_value_flow::{Stage, StageInputs, Verdict, compare};

#[path = "common/fresh_dir.rs"]
mod fresh_dir;
#[path = "common/native_host.rs"]
mod native_host;

/// This file's kernels are parsed from text and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its lowerings state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}

/// One kernel: its defined function's name and a module text generator for
/// a symbol (the defined function's name at one level).
struct Kernel {
    name: &'static str,
    text: fn(&str) -> String,
}

fn header(module: &str) -> String {
    format!(
        "; TrustIr text format v1\nmodule \"{module}\"\ntarget \"{}\" 8 little abi=\"aapcs64\"\n",
        native_host::TRIPLE
    )
}

/// `acc ^= ext_step(x * i) + y` for `i < n`: `x`, `y`, `i` and `acc` live
/// across the call.
fn call_loop(symbol: &str) -> String {
    format!(
        "{}functy.0 = (u64) -> (u64)\nfuncty.1 = (u64, u64, u64) -> (u64)\n\
fn @ext_step(functy.0) {{\n}}\n\
fn @{symbol}(functy.1) {{\n\
bb0(%0: u64, %1: u64, %2: u64):\n\
    %3 = const u64 0\n\
    br bb1(%3, %3)\n\
bb1(%10: u64, %11: u64):\n\
    %12 = icmp ult u64 %10, %2\n\
    condbr %12, bb2, bb3\n\
bb2:\n\
    %13 = mul u64 %0, %10\n\
    %14 = call @func.0(%13)\n\
    %15 = add u64 %14, %1\n\
    %16 = xor u64 %11, %15\n\
    %17 = const u64 1\n\
    %18 = add u64 %10, %17\n\
    br bb1(%18, %16)\n\
bb3:\n\
    ret %11\n\
}}\n",
        header("call_loop")
    )
}

/// Width of the pressure kernel: enough live values to spill.
const PRESSURE: usize = 40;

/// `PRESSURE` values loaded from `a`, all live across a loop that mixes them
/// (`v[k] = (v[k] + v[k+1]) ^ i`), then summed.
fn pressure(symbol: &str) -> String {
    let n = PRESSURE;
    let mut t = header("pressure");
    writeln!(
        t,
        "functy.0 = (ptr, u64) -> (u64)\nfn @{symbol}(functy.0) {{\nbb0(%0: ptr, %1: u64):"
    )
    .unwrap();
    let mut v = 2usize;
    let mut vals = Vec::new();
    for i in 0..n {
        writeln!(t, "    %{v} = const i64 {i}").unwrap();
        writeln!(t, "    %{} = gep u64, ptr %0, %{v}", v + 1).unwrap();
        writeln!(t, "    %{} = load u64, ptr %{}", v + 2, v + 1).unwrap();
        vals.push(v + 2);
        v += 3;
    }
    let zero = v;
    v += 1;
    writeln!(t, "    %{zero} = const u64 0").unwrap();
    let args: Vec<String> = std::iter::once(format!("%{zero}"))
        .chain(vals.iter().map(|x| format!("%{x}")))
        .collect();
    writeln!(t, "    br bb1({})", args.join(", ")).unwrap();
    let i = v;
    v += 1;
    let params: Vec<usize> = (0..n).map(|k| v + k).collect();
    v += n;
    let mut hp = vec![format!("%{i}: u64")];
    hp.extend(params.iter().map(|p| format!("%{p}: u64")));
    writeln!(t, "bb1({}):", hp.join(", ")).unwrap();
    let c = v;
    v += 1;
    writeln!(
        t,
        "    %{c} = icmp ult u64 %{i}, %1\n    condbr %{c}, bb2, bb3\nbb2:"
    )
    .unwrap();
    let mut next = Vec::new();
    for k in 0..n {
        let a = params[k];
        let b = params[(k + 1) % n];
        writeln!(t, "    %{v} = add u64 %{a}, %{b}").unwrap();
        writeln!(t, "    %{} = xor u64 %{v}, %{i}", v + 1).unwrap();
        next.push(v + 1);
        v += 2;
    }
    let one = v;
    let ni = v + 1;
    v += 2;
    writeln!(
        t,
        "    %{one} = const u64 1\n    %{ni} = add u64 %{i}, %{one}"
    )
    .unwrap();
    let mut a2 = vec![format!("%{ni}")];
    a2.extend(next.iter().map(|x| format!("%{x}")));
    writeln!(t, "    br bb1({})\nbb3:", a2.join(", ")).unwrap();
    let mut acc = params[0];
    for &p in &params[1..] {
        writeln!(t, "    %{v} = add u64 %{acc}, %{p}").unwrap();
        acc = v;
        v += 1;
    }
    writeln!(t, "    ret %{acc}\n}}").unwrap();
    t
}

/// The pressure kernel plus a 16-byte stack array `arr = {n, n}` stored on
/// entry and read back as `arr[n & 1]` at the exit (`pressure + n`): spill
/// slots and a live program stack slot in one frame.
fn array_pressure(symbol: &str) -> String {
    let text = pressure(symbol).replacen(
        "bb0(%0: ptr, %1: u64):",
        "bb0(%0: ptr, %1: u64):\n    %900 = alloca (u64, u64), align 8\n    store u64 %1, ptr %900\n    %910 = const u64 1\n    %911 = gep u64, ptr %900, %910\n    store u64 %1, ptr %911",
        1,
    );
    let at = text
        .rfind("    ret %")
        .expect("the pressure kernel returns");
    let acc: String = text[at + "    ret %".len()..]
        .chars()
        .take_while(char::is_ascii_digit)
        .collect();
    format!(
        "{}    %912 = const u64 1\n    %913 = and u64 %1, %912\n    %914 = gep u64, ptr %900, %913\n    %901 = load u64, ptr %914\n    %902 = add u64 %{acc}, %901\n    ret %902\n}}\n",
        &text[..at]
    )
}

/// `s < 8 ? y * (3s + 7) : y` through a jump table.
fn switch_dense(symbol: &str) -> String {
    let mut t = header("switch_dense");
    writeln!(
        t,
        "functy.0 = (u64, u64) -> (u64)\nfn @{symbol}(functy.0) {{\nbb0(%0: u64, %1: u64):"
    )
    .unwrap();
    t.push_str("    switch %0 [");
    for k in 0..8 {
        write!(t, " {k}: bb{}", k + 1).unwrap();
    }
    t.push_str(" default: bb9 ]\n");
    for k in 0..8u64 {
        writeln!(t, "bb{}:", k + 1).unwrap();
        writeln!(t, "    %{} = const u64 {}", 10 + 2 * k, 3 * k + 7).unwrap();
        writeln!(t, "    %{} = mul u64 %1, %{}", 11 + 2 * k, 10 + 2 * k).unwrap();
        writeln!(t, "    br bb10(%{})", 11 + 2 * k).unwrap();
    }
    t.push_str("bb9:\n    br bb10(%1)\nbb10(%40: u64):\n    ret %40\n}\n");
    t
}

/// Twelve arguments (four arrive on the stack) passed on permuted to a
/// twelve-argument callee (four leave on the stack), plus three incoming
/// stack arguments.
fn many_args(symbol: &str) -> String {
    let mut t = header("many_args");
    let tys = ["u64"; 12].join(", ");
    writeln!(
        t,
        "functy.0 = ({tys}) -> (u64)\nfn @callee12(functy.0) {{\n}}\nfn @{symbol}(functy.0) {{"
    )
    .unwrap();
    let ps: Vec<String> = (0..12).map(|k| format!("%{k}: u64")).collect();
    writeln!(t, "bb0({}):", ps.join(", ")).unwrap();
    let args: Vec<String> = (0..12).map(|k| format!("%{}", (k * 5) % 12)).collect();
    writeln!(t, "    %20 = call @func.0({})", args.join(", ")).unwrap();
    t.push_str("    %21 = add u64 %20, %11\n    %22 = add u64 %21, %10\n    %23 = add u64 %22, %8\n    ret %23\n}\n");
    t
}

/// `acc = fext(acc * b) + b + acc`, `n` times: FP values across the call.
fn fp_calls(symbol: &str) -> String {
    format!(
        "{}functy.0 = (f64) -> (f64)\nfuncty.1 = (f64, f64, u64) -> (f64)\n\
fn @fext(functy.0) {{\n}}\n\
fn @{symbol}(functy.1) {{\n\
bb0(%0: f64, %1: f64, %2: u64):\n\
    %3 = const u64 0\n\
    br bb1(%3, %0)\n\
bb1(%10: u64, %11: f64):\n\
    %12 = icmp ult u64 %10, %2\n\
    condbr %12, bb2, bb3\n\
bb2:\n\
    %13 = fmul f64 %11, %1\n\
    %14 = call @func.0(%13)\n\
    %15 = fadd f64 %14, %1\n\
    %16 = fadd f64 %15, %11\n\
    %17 = const u64 1\n\
    %18 = add u64 %10, %17\n\
    br bb1(%18, %16)\n\
bb3:\n\
    ret %11\n\
}}\n",
        header("fp_calls")
    )
}

/// `arr[i] = i * x` for eight stack elements, then `acc = (acc ^ arr[i]) +
/// y`.
fn local_array(symbol: &str) -> String {
    format!(
        "{}functy.0 = (u64, u64) -> (u64)\n\
fn @{symbol}(functy.0) {{\n\
bb0(%0: u64, %1: u64):\n\
    %2 = alloca (u64, u64, u64, u64, u64, u64, u64, u64), align 8\n\
    %3 = const u64 0\n\
    br bb1(%3)\n\
bb1(%10: u64):\n\
    %11 = const u64 8\n\
    %12 = icmp ult u64 %10, %11\n\
    condbr %12, bb2, bb3(%3, %3)\n\
bb2:\n\
    %13 = mul u64 %10, %0\n\
    %14 = gep u64, ptr %2, %10\n\
    store u64 %13, ptr %14\n\
    %15 = const u64 1\n\
    %16 = add u64 %10, %15\n\
    br bb1(%16)\n\
bb3(%20: u64, %21: u64):\n\
    %22 = const u64 8\n\
    %23 = icmp ult u64 %20, %22\n\
    condbr %23, bb4, bb5\n\
bb4:\n\
    %24 = gep u64, ptr %2, %20\n\
    %25 = load u64, ptr %24\n\
    %26 = xor u64 %21, %25\n\
    %27 = add u64 %26, %1\n\
    %28 = const u64 1\n\
    %29 = add u64 %20, %28\n\
    br bb3(%29, %27)\n\
bb5:\n\
    ret %21\n\
}}\n",
        header("local_array")
    )
}

/// Elements of the big frame's stack array (32 KiB: a stack-probe loop).
const BIG: u64 = 4096;

/// `arr[i] = i * x` over a 32 KiB stack array, then `acc = (acc ^
/// arr[(7i) % BIG]) + y` for `i < n`: a frame large enough for a probe loop.
fn big_frame(symbol: &str) -> String {
    format!(
        "{}type ty.0 = u64\nfuncty.0 = (u64, u64, u64) -> (u64)\n\
fn @{symbol}(functy.0) {{\n\
bb0(%0: u64, %1: u64, %2: u64):\n\
    %3 = alloca [ty.0 x {BIG}], align 8\n\
    %4 = const u64 0\n\
    br bb1(%4)\n\
bb1(%10: u64):\n\
    %11 = const u64 {BIG}\n\
    %12 = icmp ult u64 %10, %11\n\
    condbr %12, bb2, bb3(%4, %4)\n\
bb2:\n\
    %13 = mul u64 %10, %0\n\
    %14 = gep u64, ptr %3, %10\n\
    store u64 %13, ptr %14\n\
    %15 = const u64 1\n\
    %16 = add u64 %10, %15\n\
    br bb1(%16)\n\
bb3(%20: u64, %21: u64):\n\
    %22 = icmp ult u64 %20, %2\n\
    condbr %22, bb4, bb5\n\
bb4:\n\
    %23 = const u64 7\n\
    %24 = mul u64 %20, %23\n\
    %25 = const u64 {}\n\
    %26 = and u64 %24, %25\n\
    %27 = gep u64, ptr %3, %26\n\
    %28 = load u64, ptr %27\n\
    %29 = xor u64 %21, %28\n\
    %30 = add u64 %29, %1\n\
    %31 = const u64 1\n\
    %32 = add u64 %20, %31\n\
    br bb3(%32, %30)\n\
bb5:\n\
    ret %21\n\
}}\n",
        header("big_frame"),
        BIG - 1
    )
}

/// `acc += *(u32 *)((u8 *)a + (i << 2))` for `i < n`: at O2/O3 late
/// post-index formation replaces the `LSL`/`LDR w, [a, x]` address
/// recompute with a pointer seeded before the loop and advanced by a
/// post-indexed load.
fn word_sum(symbol: &str) -> String {
    format!(
        "{}functy.0 = (ptr, u64) -> (u64)\n\
fn @{symbol}(functy.0) {{\n\
bb0(%0: ptr, %1: u64):\n\
    %2 = const u64 0\n\
    br bb1(%2, %2)\n\
bb1(%10: u64, %11: u64):\n\
    %12 = icmp ult u64 %10, %1\n\
    condbr %12, bb2, bb3\n\
bb2:\n\
    %19 = const u64 2\n\
    %20 = shl u64 %10, %19\n\
    %13 = gep u8, ptr %0, %20\n\
    %14 = load u32, ptr %13\n\
    %15 = zext u32 %14 to u64\n\
    %16 = add u64 %11, %15\n\
    %17 = const u64 1\n\
    %18 = add u64 %10, %17\n\
    br bb1(%18, %16)\n\
bb3:\n\
    ret %11\n\
}}\n",
        header("word_sum")
    )
}

/// The AArch64 ELF triple the lo12 fusion runs for.
const ELF_TRIPLE: &str = "aarch64-unknown-linux-gnu";

/// `return {symbol}_word * x` for a module-defined global word, for AArch64
/// ELF: frame lowering fuses the word's `ADRP`/`ADD #:lo12:` address into
/// the load (`LDR x, [page, #:lo12:word]`).
fn elf_global_word(symbol: &str) -> String {
    format!(
        "; TrustIr text format v1\nmodule \"global_word\"\ntarget \"{ELF_TRIPLE}\" 8 little abi=\"aapcs64\"\n\
functy.0 = (u64) -> (u64)\n\
global external mut visibility(default) @{symbol}_word u64 = 5\n\
fn @{symbol}(functy.0) {{\n\
bb0(%0: u64):\n\
    %1 = global_addr @global.0\n\
    %2 = load u64, ptr %1\n\
    %3 = mul u64 %2, %0\n\
    ret %3\n\
}}\n"
    )
}

const KERNELS: [Kernel; 10] = [
    Kernel {
        name: "call_loop",
        text: call_loop,
    },
    Kernel {
        name: "pressure",
        text: pressure,
    },
    Kernel {
        name: "switch_dense",
        text: switch_dense,
    },
    Kernel {
        name: "many_args",
        text: many_args,
    },
    Kernel {
        name: "fp_calls",
        text: fp_calls,
    },
    Kernel {
        name: "local_array",
        text: local_array,
    },
    Kernel {
        name: "big_frame",
        text: big_frame,
    },
    // The stack array with a stack protector requested (`StackGuard` is set
    // on the lowered function; see `protected`).
    Kernel {
        name: "protected_array",
        text: local_array,
    },
    Kernel {
        name: "word_sum",
        text: word_sum,
    },
    Kernel {
        name: "array_pressure",
        text: array_pressure,
    },
];

/// Kernels compiled with a stack protector.
fn protected(kernel: &Kernel) -> bool {
    kernel.name == "protected_array"
}

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];

fn level_tag(opt: OptLevel) -> &'static str {
    match opt {
        OptLevel::O0 => "o0",
        OptLevel::O1 => "o1",
        OptLevel::O2 => "o2",
        OptLevel::O3 => "o3",
    }
}

fn pipeline(opt: OptLevel, validation: PassValidationConfig) -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level: opt,
        target_triple: native_host::TRIPLE.into(),
        disabled_passes_override: Some(String::new()),
        ..PipelineConfig::default()
    })
    .with_pass_validation(validation)
}

/// One build: the object, the merged validation summary and the number of
/// functions with a body.
struct Built {
    object: Vec<u8>,
    validation: PassValidationSummary,
    defined: u32,
}

fn build(kernel: &Kernel, symbol: &str, opt: OptLevel, validation: PassValidationConfig) -> Built {
    let text = (kernel.text)(symbol);
    let module = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|error| panic!("{symbol}: parse: {error:?}\n{text}"));
    let mut lowered = permit_translate_module(&module)
        .unwrap_or_else(|error| panic!("{symbol}: lowering: {error}"));
    if protected(kernel) {
        for (function, _) in &mut lowered {
            function.stack_protector = trust_cg_ir::StackProtectorMode::StackGuard;
        }
    }
    let globals = trust_cg_codegen::compiler::module_object_globals(&module)
        .unwrap_or_else(|error| panic!("{symbol}: globals: {error}"));
    let pipeline = pipeline(opt, validation);
    let mut prepared = Vec::new();
    let mut summary = PassValidationSummary::new(validation);
    for (function, _) in &lowered {
        let (function, metrics) = pipeline
            .prepare_function_with_metrics(function, None)
            .unwrap_or_else(|error| panic!("{symbol} {opt:?} {validation:?}: {error}"));
        summary.merge(&metrics.pass_validation);
        prepared.push(function);
    }
    let object = pipeline
        .compile_module_with_globals(&prepared, &globals)
        .unwrap_or_else(|error| panic!("{symbol} {opt:?}: {error}"));
    native_host::assert_native_object(&object);
    Built {
        object,
        validation: summary,
        defined: lowered.len() as u32,
    }
}

fn validated(summary: &PassValidationSummary, stage: Stage) -> u32 {
    summary
        .passes
        .iter()
        .filter(|c| c.pass_name == stage.as_str())
        .map(|c| c.validated)
        .sum()
}

/// Every kernel at every level, under enforce and with validation off.
fn build_all() -> Vec<(String, Built)> {
    let mut out = Vec::new();
    for kernel in &KERNELS {
        for opt in LEVELS {
            let symbol = format!("{}_{}", kernel.name, level_tag(opt));
            let enforced = build(kernel, &symbol, opt, PassValidationConfig::enforce());
            let off = build(kernel, &symbol, opt, PassValidationConfig::off());
            assert_eq!(
                enforced.object, off.object,
                "{symbol}: validation must not change the emitted object"
            );
            out.push((symbol, enforced));
        }
    }
    out
}

/// Under enforce every kernel compiles at every level, the composed
/// comparison validates every function it defines, and the object is the
/// one validation off emits. Split at both stage boundaries, each stage
/// validates every function too.
#[test]
fn every_kernel_validates_composed_and_split_and_keeps_its_bytes() {
    let mut total = 0;
    for (symbol, built) in build_all() {
        let summary = &built.validation;
        assert_eq!(
            summary.refuted() + summary.unproved(),
            0,
            "{symbol}: {:?}",
            summary.failures
        );
        assert_eq!(
            validated(summary, Stage::Composed),
            built.defined,
            "{symbol}: every function's composed comparison validates"
        );
        total += built.defined;
    }
    let mut split = 0;
    for kernel in &KERNELS {
        for opt in LEVELS {
            let symbol = format!("{}_split_{}", kernel.name, level_tag(opt));
            let (built, list) = snapshots::capture_split(|| {
                build(kernel, &symbol, opt, PassValidationConfig::enforce())
            });
            for stage in [Stage::Allocation, Stage::FrameLayout] {
                assert_eq!(
                    validated(&built.validation, stage),
                    built.defined,
                    "{symbol}: every function's {} comparison validates",
                    stage.as_str()
                );
            }
            assert_eq!(list.len() as u32, 2 * built.defined, "{symbol}");
            split += list.len();
        }
    }
    eprintln!(
        "{total} functions: the composed post-RA comparison validated under enforce; \
         {split} split stage comparisons validated"
    );
}

// ---------------------------------------------------------------------------
// Corruption controls on the real stage inputs
// ---------------------------------------------------------------------------

/// The captured comparisons of `kernel`'s defined function at `opt`, split
/// at both stage boundaries or composed (the comparison the pipeline runs by
/// default).
fn captured(kernel: &Kernel, opt: OptLevel, split: bool) -> Vec<Snapshot> {
    let symbol = format!("{}_snap", kernel.name);
    let text = (kernel.text)(&symbol);
    let module = trust_ir::parser::parse_module(&text).expect("parse");
    let mut lowered = permit_translate_module(&module).expect("lower");
    if protected(kernel) {
        for (function, _) in &mut lowered {
            function.stack_protector = trust_cg_ir::StackProtectorMode::StackGuard;
        }
    }
    let pipeline = pipeline(opt, PassValidationConfig::enforce());
    let run = || {
        for (function, _) in &lowered {
            pipeline
                .prepare_function_with_metrics(function, None)
                .unwrap_or_else(|error| panic!("{symbol}: {error}"));
        }
    };
    let (_, list) = if split {
        snapshots::capture_split(run)
    } else {
        snapshots::capture(run)
    };
    let list: Vec<Snapshot> = list
        .into_iter()
        .filter(|s| s.implementation.name == symbol)
        .collect();
    let stages = if split { 2 } else { 1 };
    assert_eq!(list.len(), stages, "{symbol}: one comparison per stage");
    for snap in &list {
        assert_eq!(
            snap.report.verdict,
            Verdict::Validated,
            "{symbol} {:?}",
            snap.stage
        );
    }
    list
}

/// The split comparisons of `kernel`'s defined function at `opt`.
fn snapshots_of(kernel: &Kernel, opt: OptLevel) -> Vec<Snapshot> {
    captured(kernel, opt, true)
}

/// The composed comparison of `kernel`'s defined function at `opt`.
fn composed_of(kernel: &Kernel, opt: OptLevel) -> Snapshot {
    let mut list = captured(kernel, opt, false);
    let snap = list.pop().expect("one comparison");
    assert_eq!(snap.stage, Stage::Composed);
    snap
}

fn stage_of(list: &[Snapshot], stage: Stage) -> &Snapshot {
    list.iter().find(|s| s.stage == stage).expect("stage")
}

/// Re-run `snap`'s comparison against `implementation`.
fn judge(snap: &Snapshot, implementation: &MachFunction) -> Verdict {
    compare(StageInputs {
        spec: &snap.spec,
        implementation,
        stage: snap.stage,
        allocator_slot_start: snap.allocator_slot_start,
        frame: snap.frame.as_ref(),
        inserted_from: snap.inserted_from,
        reserved_x18: native_host::DARWIN,
    })
    .verdict
}

#[track_caller]
fn assert_refused(what: &str, snap: &Snapshot, corrupted: &MachFunction) {
    assert_eq!(
        judge(snap, &snap.implementation),
        Verdict::Validated,
        "{what}: the uncorrupted implementation validates"
    );
    match judge(snap, corrupted) {
        Verdict::Violation { kind, detail } => {
            eprintln!("{what}: refused ({}): {detail}", kind.tag());
        }
        other => panic!("{what}: the corruption must be refused, got {other:?}"),
    }
}

/// Laid-out instruction ids of `func`, in layout order.
fn laid_out(func: &MachFunction) -> Vec<trust_cg_ir::InstId> {
    func.block_order
        .iter()
        .flat_map(|b| func.block(*b).insts.iter().copied())
        .collect()
}

fn preg(op: &MachOperand) -> Option<u16> {
    match op {
        MachOperand::PReg(p) => Some(p.encoding()),
        _ => None,
    }
}

/// Rename every occurrence of physical register `from` (any view of the
/// same number) to `to` in `func`.
fn rename_gpr(func: &mut MachFunction, from: u16, to: u16) {
    for inst in &mut func.insts {
        for op in &mut inst.operands {
            if let MachOperand::PReg(p) = op {
                let e = p.encoding();
                if e == from {
                    *p = trust_cg_ir::PReg::new(to);
                } else if e == from + 32 {
                    *p = trust_cg_ir::PReg::new(to + 32);
                }
            }
        }
    }
}

#[test]
fn a_reload_from_the_wrong_spill_slot_is_refused() {
    let snap = stage_of(&snapshots_of(&KERNELS[1], OptLevel::O2), Stage::Allocation).clone();
    let mut corrupted = snap.implementation.clone();
    let start = snap.allocator_slot_start;
    let reload = laid_out(&corrupted)
        .into_iter()
        .find(|&id| {
            let inst = corrupted.inst(id);
            inst.opcode == AArch64Opcode::LdrRI
                && matches!(inst.operands.get(1), Some(MachOperand::StackSlot(s)) if s.0 >= start)
        })
        .expect("the pressure kernel reloads a spill");
    let MachOperand::StackSlot(slot) = corrupted.inst(reload).operands[1] else {
        unreachable!()
    };
    let other = (start..corrupted.stack_slots.len() as u32)
        .find(|&s| s != slot.0)
        .expect("a second spill slot");
    corrupted.inst_mut(reload).operands[1] =
        MachOperand::StackSlot(trust_cg_ir::types::StackSlotId(other));
    assert_refused("reload from the wrong slot", &snap, &corrupted);
}

#[test]
fn a_coalesce_that_merges_interfering_values_is_refused() {
    // call_loop keeps the counter and the accumulator (both zero on entry,
    // both live around the loop) in two registers joined by a copy; merging
    // them into one register is the interfering coalesce.
    let snap = stage_of(&snapshots_of(&KERNELS[0], OptLevel::O2), Stage::Allocation).clone();
    let mut corrupted = snap.implementation.clone();
    let ids = laid_out(&corrupted);
    let copy = ids
        .iter()
        .copied()
        .find(|&id| {
            let inst = corrupted.inst(id);
            inst.opcode == AArch64Opcode::MOVXrr && {
                let src = preg(&inst.operands[1]);
                ids.iter().any(|&d| {
                    let def = corrupted.inst(d);
                    def.opcode == AArch64Opcode::Movz
                        && preg(&def.operands[0]) == src
                        && def.operands[1] == MachOperand::Imm(0)
                })
            }
        })
        .expect("a copy of a zero-initialized loop variable");
    let dst = preg(&corrupted.inst(copy).operands[0]).unwrap();
    let src = preg(&corrupted.inst(copy).operands[1]).unwrap();
    corrupted.inst_mut(copy).opcode = AArch64Opcode::Nop;
    corrupted.inst_mut(copy).operands.clear();
    rename_gpr(&mut corrupted, dst, src);
    assert_refused("interfering coalesce", &snap, &corrupted);
}

#[test]
fn a_callee_saved_value_moved_to_a_caller_saved_register_is_refused() {
    // call_loop holds its loop state in callee-saved registers across the
    // call; moving one to X9 (caller-saved, unused) keeps it live across the
    // call in a register the call clobbers.
    let allocation = stage_of(&snapshots_of(&KERNELS[0], OptLevel::O2), Stage::Allocation).clone();
    let composed = composed_of(&KERNELS[0], OptLevel::O2);
    for snap in [&allocation, &composed] {
        let mut corrupted = snap.implementation.clone();
        let used = |n: u16| {
            corrupted.insts.iter().any(|inst| {
                inst.operands
                    .iter()
                    .any(|op| matches!(preg(op), Some(e) if e == n || e == n + 32))
            })
        };
        let callee_saved = (19u16..=28)
            .find(|&n| used(n))
            .expect("a callee-saved register in use");
        assert!(!used(9), "x9 is free in call_loop");
        rename_gpr(&mut corrupted, callee_saved, 9);
        assert_refused("caller-saved register across a call", snap, &corrupted);
    }
}

#[test]
fn a_rematerialization_of_a_changed_value_is_refused() {
    // Replace a spill reload in the pressure loop with a recomputation of the
    // reloaded slot's first spill store's value through the store's source
    // register, which was overwritten in between (the reload exists because
    // the register was reused).
    let snap = stage_of(&snapshots_of(&KERNELS[1], OptLevel::O2), Stage::Allocation).clone();
    let mut corrupted = snap.implementation.clone();
    let start = snap.allocator_slot_start;
    let ids = laid_out(&corrupted);
    let reload = ids
        .iter()
        .copied()
        .find(|&id| {
            let inst = corrupted.inst(id);
            inst.opcode == AArch64Opcode::LdrRI
                && matches!(inst.operands.get(1), Some(MachOperand::StackSlot(s)) if s.0 >= start)
        })
        .expect("a reload");
    // "Rematerialize" as a copy of the register the value was spilled from:
    // the register no longer holds it.
    let dst = corrupted.inst(reload).operands[0].clone();
    let MachOperand::StackSlot(slot) = corrupted.inst(reload).operands[1] else {
        unreachable!()
    };
    let store_src = ids
        .iter()
        .find_map(|&id| {
            let inst = corrupted.inst(id);
            (inst.opcode == AArch64Opcode::StrRI
                && inst.operands.get(1) == Some(&MachOperand::StackSlot(slot)))
            .then(|| inst.operands[0].clone())
        })
        .expect("the slot's spill store");
    let inst = corrupted.inst_mut(reload);
    inst.opcode = AArch64Opcode::MOVXrr;
    inst.operands = vec![dst, store_src];
    inst.flags = InstFlags::EMPTY;
    assert_refused("rematerialization of a changed value", &snap, &corrupted);
}

#[test]
fn a_frame_offset_off_by_eight_is_refused() {
    let frame = stage_of(&snapshots_of(&KERNELS[1], OptLevel::O2), Stage::FrameLayout).clone();
    let composed = composed_of(&KERNELS[1], OptLevel::O2);
    for snap in [&frame, &composed] {
        let mut corrupted = snap.implementation.clone();
        let reload = laid_out(&corrupted)
            .into_iter()
            .find(|&id| {
                let inst = corrupted.inst(id);
                inst.opcode == AArch64Opcode::LdrRI
                    && inst.flags.contains(InstFlags::SPILL_SLOT_ACCESS)
                    && matches!(inst.operands.get(1), Some(MachOperand::MemOp { .. }))
            })
            .expect("a lowered spill reload");
        if let MachOperand::MemOp { offset, .. } = &mut corrupted.inst_mut(reload).operands[1] {
            *offset += 8;
        }
        assert_refused("frame offset off by eight", snap, &corrupted);
    }
}

#[test]
fn a_stack_array_address_off_by_eight_is_refused() {
    let snap = stage_of(&snapshots_of(&KERNELS[5], OptLevel::O2), Stage::FrameLayout).clone();
    let mut corrupted = snap.implementation.clone();
    // The array's address: `SUB/ADD xN, x29|sp, #k`.
    let address = laid_out(&corrupted)
        .into_iter()
        .find(|&id| {
            let inst = corrupted.inst(id);
            matches!(inst.opcode, AArch64Opcode::SubRI | AArch64Opcode::AddRI)
                && matches!(preg(&inst.operands[0]), Some(e) if e < 29)
                && matches!(
                    inst.operands[1],
                    MachOperand::PReg(p) if p.encoding() == 29
                )
        })
        .expect("the stack array's address computation");
    if let MachOperand::Imm(k) = &mut corrupted.inst_mut(address).operands[2] {
        *k += 8;
    }
    assert_refused("stack array address off by eight", &snap, &corrupted);
}

#[test]
fn a_branch_retargeted_to_the_wrong_block_is_refused() {
    let frame = stage_of(&snapshots_of(&KERNELS[0], OptLevel::O2), Stage::FrameLayout).clone();
    let composed = composed_of(&KERNELS[0], OptLevel::O2);
    for snap in [&frame, &composed] {
        retarget_a_branch(snap);
    }
}

fn retarget_a_branch(snap: &Snapshot) {
    let func = &snap.implementation;
    // Block starts in instruction units.
    let mut starts = Vec::new();
    let mut offset = 0i64;
    let mut at = std::collections::HashMap::new();
    for &b in &func.block_order {
        starts.push(offset);
        for &id in &func.block(b).insts {
            if !func.inst(id).is_pseudo() {
                at.insert(id, offset);
                offset += 1;
            }
        }
    }
    let (branch, here, target) = laid_out(func)
        .into_iter()
        .find_map(|id| {
            let inst = func.inst(id);
            match (inst.opcode, inst.operands.get(1)) {
                (AArch64Opcode::BCond, Some(MachOperand::Imm(k))) => {
                    Some((id, at[&id], at[&id] + k))
                }
                _ => None,
            }
        })
        .expect("a resolved conditional branch");
    let wrong = starts
        .iter()
        .copied()
        .find(|&s| s != target && s != here + 1)
        .expect("another block start");
    let mut corrupted = func.clone();
    corrupted.inst_mut(branch).operands[1] = MachOperand::Imm(wrong - here);
    assert_refused("branch retargeted to the wrong block", snap, &corrupted);
}

#[test]
fn a_short_stack_probe_loop_is_refused() {
    // Frame lowering probes the 32 KiB frame with a counted loop (`MOVZ X16,
    // #n` before it); one iteration fewer leaves SP a page short, so every
    // frame access after it lands elsewhere.
    let snap = stage_of(&snapshots_of(&KERNELS[6], OptLevel::O2), Stage::FrameLayout).clone();
    let mut corrupted = snap.implementation.clone();
    let counter = laid_out(&corrupted)
        .into_iter()
        .find(|&id| {
            let inst = corrupted.inst(id);
            inst.opcode == AArch64Opcode::Movz && preg(&inst.operands[0]) == Some(16)
        })
        .expect("the probe loop's counter");
    if let MachOperand::Imm(n) = &mut corrupted.inst_mut(counter).operands[1] {
        assert!(*n >= 2, "a multi-iteration probe loop");
        *n -= 1;
    }
    assert_refused("short stack probe loop", &snap, &corrupted);
}

#[test]
fn an_unstored_stack_protector_canary_is_refused() {
    // The prologue stores the guard into the canary slot; without that
    // store the epilogue's compare is no longer of the guard with itself,
    // and the path to `__stack_chk_fail` (a call the specification does not
    // make) becomes reachable.
    let snap = stage_of(&snapshots_of(&KERNELS[7], OptLevel::O2), Stage::FrameLayout).clone();
    let mut corrupted = snap.implementation.clone();
    let inserted = snap.spec.insts.len() as u32;
    let (block, position) = corrupted
        .block_order
        .iter()
        .find_map(|&b| {
            corrupted
                .block(b)
                .insts
                .iter()
                .position(|&id| {
                    let inst = corrupted.inst(id);
                    id.0 >= inserted
                        && inst.opcode == AArch64Opcode::StrRI
                        && preg(&inst.operands[0]) == Some(16)
                })
                .map(|p| (b, p))
        })
        .expect("the canary store");
    corrupted.block_mut(block).insts.remove(position);
    assert_refused("unstored stack-protector canary", &snap, &corrupted);
}

#[test]
fn a_deleted_and_a_duplicated_store_are_refused() {
    let snap = stage_of(&snapshots_of(&KERNELS[5], OptLevel::O1), Stage::Allocation).clone();
    let func = &snap.implementation;
    let (block, position) = func
        .block_order
        .iter()
        .find_map(|&b| {
            func.block(b)
                .insts
                .iter()
                .position(|&id| {
                    let inst = func.inst(id);
                    inst.writes_memory() && !inst.flags.contains(InstFlags::SPILL_SLOT_ACCESS)
                })
                .map(|p| (b, p))
        })
        .expect("the array store");
    let mut deleted = func.clone();
    deleted.block_mut(block).insts.remove(position);
    assert_refused("deleted store", &snap, &deleted);
    let mut duplicated = func.clone();
    let store = duplicated.block(block).insts[position];
    duplicated.block_mut(block).insts.insert(position, store);
    assert_refused("duplicated store", &snap, &duplicated);
}

#[test]
fn an_altered_call_argument_is_refused() {
    let snap = stage_of(&snapshots_of(&KERNELS[3], OptLevel::O2), Stage::Allocation).clone();
    let mut corrupted = snap.implementation.clone();
    // The last write of x1 before the call now copies x2 instead.
    let ids = laid_out(&corrupted);
    let call = ids
        .iter()
        .position(|&id| corrupted.inst(id).is_call())
        .expect("the call");
    let setup = ids[..call]
        .iter()
        .rev()
        .copied()
        .find(|&id| {
            let inst = corrupted.inst(id);
            inst.opcode == AArch64Opcode::MOVXrr && preg(&inst.operands[0]) == Some(1)
        })
        .expect("an argument copy into x1");
    let src = preg(&corrupted.inst(setup).operands[1]).unwrap();
    let other = if src == 2 { 3 } else { 2 };
    corrupted.inst_mut(setup).operands[1] = MachOperand::PReg(trust_cg_ir::PReg::new(other));
    assert_refused("altered call argument", &snap, &corrupted);
}

#[test]
fn a_post_indexed_pointer_with_the_wrong_stride_is_refused() {
    // Late post-index formation runs before copy lowering: the allocation
    // stage's implementation carries `LDR w, [x16], #4`; advancing eight
    // bytes per four-byte element would read every other element.
    let snap = stage_of(&snapshots_of(&KERNELS[8], OptLevel::O2), Stage::Allocation).clone();
    let mut corrupted = snap.implementation.clone();
    let load = laid_out(&corrupted)
        .into_iter()
        .find(|&id| corrupted.inst(id).opcode == AArch64Opcode::LdrPostIndex)
        .expect("late post-index formation folded the loop's load");
    let Some(MachOperand::Imm(stride)) = corrupted.inst_mut(load).operands.get_mut(2) else {
        panic!("a post-indexed load with an immediate stride");
    };
    assert_eq!(*stride, 4, "the element stride");
    *stride = 8;
    assert_refused(
        "post-indexed pointer with the wrong stride",
        &snap,
        &corrupted,
    );
}

#[test]
fn a_fused_lo12_access_of_another_symbol_is_refused() {
    // Compiled for AArch64 ELF with the word's alignment known: frame
    // lowering fuses its `ADD #:lo12:` into the load, inside the frame
    // stage. (No native row: the fusion is an ELF relocation form.)
    let symbol = "global_word_snap";
    let text = elf_global_word(symbol);
    let module = trust_ir::parser::parse_module(&text).expect("parse");
    let lowered = permit_translate_module(&module).expect("lower");
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O2,
        target_triple: ELF_TRIPLE.into(),
        disabled_passes_override: Some(String::new()),
        ..PipelineConfig::default()
    })
    .with_pass_validation(PassValidationConfig::enforce())
    .with_elf_lo12_symbol_alignments(std::collections::BTreeMap::from([(
        format!("{symbol}_word"),
        8,
    )]));
    let (_, list) = snapshots::capture_split(|| {
        for (function, _) in &lowered {
            pipeline
                .prepare_function_with_metrics(function, None)
                .unwrap_or_else(|error| panic!("{symbol}: {error}"));
        }
    });
    let snap = list
        .into_iter()
        .find(|s| s.implementation.name == symbol && s.stage == Stage::FrameLayout)
        .expect("the frame stage comparison");
    assert_eq!(snap.report.verdict, Verdict::Validated, "{symbol}");
    let mut corrupted = snap.implementation.clone();
    let load = laid_out(&corrupted)
        .into_iter()
        .find(|&id| {
            let inst = corrupted.inst(id);
            inst.opcode == AArch64Opcode::LdrRI
                && matches!(inst.operands.get(2), Some(MachOperand::Symbol(_)))
        })
        .expect("the lo12 fusion folded the word's address into its load");
    corrupted.inst_mut(load).operands[2] = MachOperand::Symbol("another_word".into());
    assert_refused("fused lo12 access of another symbol", &snap, &corrupted);
}

#[test]
fn sp_moved_between_the_stack_arguments_and_the_call_is_refused() {
    // many_args stores four outgoing arguments at `[sp, #k]`; lowering SP
    // after those stores and raising it again after the call makes the
    // callee read them 16 bytes below where they were stored (wrong values),
    // or run on a misaligned SP (8). SP is back before the exit, so only the
    // call's view of SP differs.
    let frame = stage_of(&snapshots_of(&KERNELS[3], OptLevel::O2), Stage::FrameLayout).clone();
    let composed = composed_of(&KERNELS[3], OptLevel::O2);
    for snap in [&frame, &composed] {
        for delta in [16, 8] {
            let mut corrupted = snap.implementation.clone();
            let (block, at) = corrupted
                .block_order
                .iter()
                .find_map(|&b| {
                    corrupted
                        .block(b)
                        .insts
                        .iter()
                        .position(|&id| corrupted.inst(id).is_call())
                        .map(|p| (b, p))
                })
                .expect("the call");
            let sp = || MachOperand::Special(trust_cg_ir::SpecialReg::SP);
            let lower = corrupted.push_inst(MachInst::new(
                AArch64Opcode::SubRI,
                vec![sp(), sp(), MachOperand::Imm(delta)],
            ));
            let raise = corrupted.push_inst(MachInst::new(
                AArch64Opcode::AddRI,
                vec![sp(), sp(), MachOperand::Imm(delta)],
            ));
            corrupted.block_mut(block).insts.insert(at + 1, raise);
            corrupted.block_mut(block).insts.insert(at, lower);
            assert_refused(
                &format!("SP lowered by {delta} around the call ({:?})", snap.stage),
                snap,
                &corrupted,
            );
        }
    }
}

/// The call of `func` (its block and position) and the stack-argument store
/// laid out last before it (a program `STR` with an SP base).
fn call_and_last_stack_argument(
    func: &MachFunction,
    inserted_from: u32,
) -> (trust_cg_ir::BlockId, usize, trust_cg_ir::InstId) {
    let is_sp = |op: &MachOperand| {
        matches!(op, MachOperand::Special(trust_cg_ir::SpecialReg::SP))
            || matches!(op, MachOperand::PReg(p) if p.encoding() == 31)
    };
    for &b in &func.block_order {
        let insts = &func.block(b).insts;
        let Some(at) = insts.iter().position(|&id| func.inst(id).is_call()) else {
            continue;
        };
        let store = insts[..at]
            .iter()
            .copied()
            .rfind(|&id| {
                let inst = func.inst(id);
                id.0 < inserted_from
                    && inst.opcode == AArch64Opcode::StrRI
                    && !inst.flags.contains(InstFlags::SPILL_SLOT_ACCESS)
                    && inst.operands.get(1).is_some_and(is_sp)
            })
            .expect("a stack-argument store before the call");
        return (b, at, store);
    }
    panic!("no call in {}", func.name);
}

/// The first instruction id frame lowering appended in `snap`'s
/// implementation (the comparison's own default when the snapshot names
/// none: the specification's arena length).
fn first_inserted(snap: &Snapshot) -> u32 {
    snap.inserted_from
        .unwrap_or_else(|| u32::try_from(snap.spec.insts.len()).expect("arena length"))
}

/// The stores the outgoing-area control inserts between the last
/// stack-argument store and the call: over that argument, a spill store of
/// X0, an unflagged store of X0 and a store of zero; and frame lowering's
/// exact stack probe `STR XZR, [SP]`, over the argument at `[sp]`.
fn outgoing_area_stores(template: &MachInst) -> [(&'static str, MachInst); 4] {
    let x0 = MachOperand::PReg(trust_cg_ir::PReg::new(0));
    let xzr = || MachOperand::PReg(trust_cg_ir::PReg::new(160));
    let with = |data: MachOperand, spill: bool| {
        let mut store = template.clone();
        store.operands[0] = data;
        if spill {
            store.flags |= InstFlags::SPILL_SLOT_ACCESS;
        }
        store
    };
    let probe = MachInst::new(
        AArch64Opcode::StrRI,
        vec![
            xzr(),
            MachOperand::Special(trust_cg_ir::SpecialReg::SP),
            MachOperand::Imm(0),
        ],
    );
    [
        ("spill store of x0", with(x0.clone(), true)),
        ("store of x0", with(x0, false)),
        ("store of zero", with(xzr(), false)),
        ("stack probe at sp", probe),
    ]
}

/// `func` with `store` inserted right before its call.
fn with_store_before_the_call(
    func: &MachFunction,
    inserted_from: u32,
    store: MachInst,
) -> MachFunction {
    let (block, at, _) = call_and_last_stack_argument(func, inserted_from);
    let mut corrupted = func.clone();
    let id = corrupted.push_inst(store);
    corrupted.block_mut(block).insts.insert(at, id);
    corrupted
}

#[test]
fn a_store_over_the_outgoing_arguments_before_the_call_is_refused() {
    // many_args stores four outgoing arguments at `[sp, #k]` and then calls.
    // A store between those stores and the call, over an argument, changes
    // what the callee reads; it is no program effect (a spill, or an access
    // frame lowering inserted, including one shaped like a stack probe), so
    // only frame-storage privacy can see it: the outgoing area is not
    // storage. Every level, the frame stage and the composed comparison.
    let mut refusals = 0;
    for opt in LEVELS {
        let split = snapshots_of(&KERNELS[3], opt);
        let composed = composed_of(&KERNELS[3], opt);
        for snap in [stage_of(&split, Stage::FrameLayout), &composed] {
            let inserted_from = first_inserted(snap);
            let (_, _, template) =
                call_and_last_stack_argument(&snap.implementation, inserted_from);
            let template = snap.implementation.inst(template).clone();
            for (what, store) in outgoing_area_stores(&template) {
                let corrupted =
                    with_store_before_the_call(&snap.implementation, inserted_from, store);
                assert_refused(
                    &format!(
                        "{what} over a stack argument before the call ({opt:?} {:?})",
                        snap.stage
                    ),
                    snap,
                    &corrupted,
                );
                refusals += 1;
            }
        }
    }
    eprintln!("{refusals} stores over the outgoing arguments refused");
}

/// The outgoing-area corruptions are real miscompiles: the frame stage's
/// final stream, emitted as is, agrees with the C reference, and each
/// corrupted one does not.
#[cfg_attr(
    any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    ),
    test
)]
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn the_outgoing_area_corruptions_miscompile_natively() {
    use std::process::Command;

    let snap = stage_of(&snapshots_of(&KERNELS[3], OptLevel::O2), Stage::FrameLayout).clone();
    let symbol = snap.implementation.name.clone();
    let module = trust_ir::parser::parse_module(&many_args(&symbol)).expect("parse");
    let globals = trust_cg_codegen::compiler::module_object_globals(&module).expect("globals");
    let inserted_from = first_inserted(&snap);
    let (_, _, template) = call_and_last_stack_argument(&snap.implementation, inserted_from);
    let template = snap.implementation.inst(template).clone();
    let mut variants = vec![("uncorrupted", snap.implementation.clone())];
    for (what, store) in outgoing_area_stores(&template) {
        variants.push((
            what,
            with_store_before_the_call(&snap.implementation, inserted_from, store),
        ));
    }
    let dir = fresh_dir::create("trust_cg_post_ra_vf_outgoing_");
    let driver = format!(
        "#include <stdint.h>\n#include <stdio.h>\n\
uint64_t callee12(uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4, uint64_t a5,\n\
                  uint64_t a6, uint64_t a7, uint64_t a8, uint64_t a9, uint64_t a10, uint64_t a11) {{\n\
  return a0 * 1 + a1 * 3 + a2 * 5 + a3 * 7 + a4 * 11 + a5 * 13 + a6 * 17 + a7 * 19\n\
       + a8 * 23 + a9 * 29 + a10 * 31 + a11 * 37;\n\
}}\n\
uint64_t {symbol}(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t,\n\
                  uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t);\n\
int main(void) {{\n\
  uint64_t a[12], p[12];\n\
  for (int i = 0; i < 12; i++) a[i] = 1000 + 7 * i;\n\
  for (int k = 0; k < 12; k++) p[k] = a[(k * 5) % 12];\n\
  uint64_t want = callee12(p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7], p[8], p[9], p[10],\n\
                           p[11]) + a[11] + a[10] + a[8];\n\
  uint64_t got = {symbol}(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], a[10],\n\
                          a[11]);\n\
  printf(\"%s\\n\", got == want ? \"equal\" : \"differ\");\n\
  return 0;\n\
}}\n"
    );
    let driver_c = dir.join("driver.c");
    std::fs::write(&driver_c, driver).expect("write driver");
    let off = pipeline(OptLevel::O2, PassValidationConfig::off());
    for (k, (what, func)) in variants.iter().enumerate() {
        let object = off
            .compile_module_with_globals(std::slice::from_ref(func), &globals)
            .unwrap_or_else(|error| panic!("{what}: {error}"));
        let object_path = dir.join(format!("v{k}.o"));
        std::fs::write(&object_path, &object).expect("write object");
        let binary = dir.join(format!("v{k}"));
        let link = Command::new(native_host::C_COMPILER)
            .arg(&driver_c)
            .arg(&object_path)
            .args(native_host::link_hardening_args())
            .arg("-o")
            .arg(&binary)
            .output()
            .expect("run the linker");
        assert!(
            link.status.success(),
            "{what}: link:\n{}",
            String::from_utf8_lossy(&link.stderr)
        );
        let run = Command::new(&binary).output().expect("run");
        assert!(run.status.success(), "{what}: {run:?}");
        let verdict = String::from_utf8_lossy(&run.stdout).trim().to_string();
        let expected = if k == 0 { "equal" } else { "differ" };
        assert_eq!(verdict, expected, "{what} on {}", native_host::HOST);
        eprintln!("{what}: {verdict} ({})", native_host::HOST);
    }
}

/// The CFA offset a lowered frame access at operand `k` of `inst` names
/// (`MemOp`, or a base register then an immediate), with FP = CFA - 16 and
/// SP = CFA - `total`.
fn access_cfa(inst: &MachInst, k: usize, total: i64) -> Option<i64> {
    let (base, offset) = match (&inst.operands[k], inst.operands.get(k + 1)) {
        (MachOperand::MemOp { base, offset }, _) => (base.encoding(), *offset),
        (MachOperand::PReg(p), Some(MachOperand::Imm(o))) if k >= 1 => (p.encoding(), *o),
        (MachOperand::Special(trust_cg_ir::SpecialReg::SP), Some(MachOperand::Imm(o)))
            if k >= 1 =>
        {
            (31, *o)
        }
        _ => return None,
    };
    match base {
        29 => Some(offset - 16),
        31 => Some(offset - total),
        _ => None,
    }
}

/// The operand position of a spill access's frame address in `inst`.
fn spill_address(inst: &MachInst, total: i64) -> Option<(usize, i64)> {
    if !inst.flags.contains(InstFlags::SPILL_SLOT_ACCESS) {
        return None;
    }
    (0..inst.operands.len()).find_map(|k| access_cfa(inst, k, total).map(|cfa| (k, cfa)))
}

/// Every spill access's CFA offset in `func`, with its access count.
fn spill_cells(func: &MachFunction, total: i64) -> std::collections::BTreeMap<i64, usize> {
    let mut cells = std::collections::BTreeMap::new();
    for id in laid_out(func) {
        if let Some((_, cfa)) = spill_address(func.inst(id), total) {
            *cells.entry(cfa).or_insert(0) += 1;
        }
    }
    cells
}

/// Move every spill access at `CFA + from` to `CFA + to`, consistently
/// (stores and reloads alike); returns how many moved.
fn move_spill_cell(func: &mut MachFunction, total: i64, from: i64, to: i64) -> usize {
    let mut moved = 0;
    for inst in &mut func.insts {
        let Some((k, cfa)) = spill_address(inst, total) else {
            continue;
        };
        if cfa != from {
            continue;
        }
        match &mut inst.operands[k] {
            MachOperand::MemOp { offset, .. } => *offset += to - from,
            _ => {
                if let Some(MachOperand::Imm(offset)) = inst.operands.get_mut(k + 1) {
                    *offset += to - from;
                }
            }
        }
        moved += 1;
    }
    moved
}

#[test]
fn a_spill_slot_moved_onto_a_program_slot_is_refused() {
    // array_pressure keeps a 16-byte stack array live from the entry to the
    // exit while the loop spills. Moving a spill slot (every store and
    // reload of it, so the reload still reads what the spill stored) onto
    // the array overwrites the program's value: every such move, at every
    // level, in the frame stage and in the composed comparison.
    let kernel = KERNELS
        .iter()
        .find(|k| k.name == "array_pressure")
        .expect("the array_pressure kernel");
    let mut moves = 0;
    for opt in LEVELS {
        let split = snapshots_of(kernel, opt);
        let composed = composed_of(kernel, opt);
        for snap in [stage_of(&split, Stage::FrameLayout), &composed] {
            let facts = snap.frame.as_ref().expect("frame facts");
            let total = facts.total_frame_size;
            let array = (0..snap.allocator_slot_start as usize)
                .find_map(|slot| {
                    let start = facts.slot_cfa_offsets.get(slot).copied().flatten()?;
                    (facts.slot_sizes[slot] == 16).then_some(start)
                })
                .expect("the stack array's slot");
            let cells = spill_cells(&snap.implementation, total);
            assert!(!cells.is_empty(), "{opt:?}: the pressure loop spills");
            for &cell in cells.keys() {
                for target in [array, array + 8] {
                    let mut corrupted = snap.implementation.clone();
                    assert!(move_spill_cell(&mut corrupted, total, cell, target) > 0);
                    match judge(snap, &corrupted) {
                        Verdict::Violation { .. } => moves += 1,
                        other => panic!(
                            "{opt:?} {:?}: spill cell CFA{cell:+} moved onto the stack array at CFA{target:+} must be refused, got {other:?}",
                            snap.stage
                        ),
                    }
                }
            }
        }
    }
    eprintln!("{moves} spill-slot moves onto the stack array refused");
}

// ---------------------------------------------------------------------------
// Pipeline wiring: refusal by name, diagnostics, the default tier
// ---------------------------------------------------------------------------

/// `p = alloca u64 x n; *p = x; return ext_read(p)`: a dynamic stack
/// allocation (escaping, so it stays), which the comparison does not model.
fn dynamic_alloca(symbol: &str) -> String {
    format!(
        "{}functy.0 = (ptr) -> (u64)\nfuncty.1 = (u64, u64) -> (u64)\n\
fn @ext_read(functy.0) {{\n}}\n\
fn @{symbol}(functy.1) {{\n\
bb0(%0: u64, %1: u64):\n\
    %2 = alloca u64, %0\n\
    store u64 %1, ptr %2\n\
    %3 = call @func.0(%2)\n\
    ret %3\n\
}}\n",
        header("dynamic_alloca")
    )
}

/// Prepare `text`'s one function under `validation`.
fn prepare_one(
    text: &str,
    validation: PassValidationConfig,
) -> Result<PassValidationSummary, Box<trust_cg_codegen::pipeline::PipelineError>> {
    let module = trust_ir::parser::parse_module(text).expect("parse");
    let lowered = permit_translate_module(&module).expect("lower");
    assert_eq!(lowered.len(), 1);
    pipeline(OptLevel::O2, validation)
        .prepare_function_with_metrics(&lowered[0].0, None)
        .map(|(_, metrics)| metrics.pass_validation)
        .map_err(Box::new)
}

fn counts<'a>(
    summary: &'a PassValidationSummary,
    pass: &str,
) -> &'a trust_cg_opt::PassValidationCounts {
    summary
        .passes
        .iter()
        .find(|c| c.pass_name == pass)
        .unwrap_or_else(|| panic!("no `{pass}` record in {:?}", summary.passes))
}

#[test]
fn an_unmodeled_function_is_refused_by_name_under_a_refusing_policy() {
    let text = dynamic_alloca("dynamic_alloca_enforce");
    match prepare_one(&text, PassValidationConfig::enforce()).map_err(|error| *error) {
        Err(trust_cg_codegen::pipeline::PipelineError::PassValidationFailed {
            pass,
            validator,
            verdict,
            reason,
            ..
        }) => {
            assert_eq!(pass, Stage::Composed.as_str());
            assert_eq!(
                validator,
                trust_cg_opt::ValidatorKind::PostAllocationValueFlow.as_str()
            );
            assert_eq!(verdict, "unproved");
            assert!(reason.contains("dynamic stack allocation"), "{reason}");
        }
        other => panic!("an unmodeled function must be refused by name, got {other:?}"),
    }
}

#[test]
fn an_unmodeled_function_is_reported_under_the_diagnostic_policy() {
    let text = dynamic_alloca("dynamic_alloca_diagnostic");
    let config =
        PassValidationConfig::diagnostic().with_scope(trust_cg_opt::PassValidationScope::Dedicated);
    let summary = prepare_one(&text, config).expect("the diagnostic policy refuses nothing");
    let c = counts(&summary, Stage::Composed.as_str());
    assert_eq!((c.validated, c.unproved, c.uncovered), (0, 1, 0), "{c:?}");
    assert!(
        summary
            .failures
            .iter()
            .any(|r| r.pass_name == Stage::Composed.as_str()
                && r.validator == Some(trust_cg_opt::ValidatorKind::PostAllocationValueFlow)
                && r.verdict
                    .reason()
                    .is_some_and(|why| why.contains("dynamic stack allocation"))),
        "{:?}",
        summary.failures
    );
}

#[test]
fn the_default_tier_records_the_post_allocation_stages_as_uncovered() {
    // The schedulers tier does not run the comparison: the post-allocation
    // stages are one uncovered changed run, never silently skipped.
    let text = call_loop("call_loop_default_tier");
    let (summary, list) = snapshots::capture(|| {
        prepare_one(&text, PassValidationConfig::diagnostic()).expect("compiles")
    });
    assert!(list.is_empty(), "no comparison runs in the schedulers tier");
    let c = counts(&summary, Stage::Composed.as_str());
    assert_eq!((c.validated, c.unproved, c.uncovered), (0, 0, 1), "{c:?}");
    assert!(
        summary
            .failures
            .iter()
            .any(|r| r.pass_name == Stage::Composed.as_str()
                && r.validator.is_none()
                && r.verdict == trust_cg_opt::ValidationVerdict::Uncovered),
        "{:?}",
        summary.failures
    );
    // With validation off nothing is recorded.
    let off = prepare_one(&text, PassValidationConfig::off()).expect("compiles");
    assert!(
        off.passes
            .iter()
            .all(|c| c.pass_name != Stage::Composed.as_str())
    );
}

// ---------------------------------------------------------------------------
// Native rows (AArch64 Linux GNU and macOS hosts)
// ---------------------------------------------------------------------------

#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
const DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#include <string.h>

uint64_t ext_step(uint64_t v) { return (v * 0x9e3779b97f4a7c15ull) ^ (v >> 7); }
double fext(double v) { return v * 0.5 + 1.25; }
uint64_t callee12(uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4, uint64_t a5,
                  uint64_t a6, uint64_t a7, uint64_t a8, uint64_t a9, uint64_t a10, uint64_t a11) {
  return a0 * 1 + a1 * 3 + a2 * 5 + a3 * 7 + a4 * 11 + a5 * 13 + a6 * 17 + a7 * 19
       + a8 * 23 + a9 * 29 + a10 * 31 + a11 * 37;
}

#define DECL(L) \
  uint64_t call_loop_##L(uint64_t, uint64_t, uint64_t); \
  uint64_t pressure_##L(const uint64_t*, uint64_t); \
  uint64_t switch_dense_##L(uint64_t, uint64_t); \
  uint64_t many_args_##L(uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, \
                         uint64_t, uint64_t, uint64_t, uint64_t, uint64_t, uint64_t); \
  double fp_calls_##L(double, double, uint64_t); \
  uint64_t local_array_##L(uint64_t, uint64_t); \
  uint64_t big_frame_##L(uint64_t, uint64_t, uint64_t); \
  uint64_t protected_array_##L(uint64_t, uint64_t); \
  uint64_t word_sum_##L(const uint32_t*, uint64_t); \
  uint64_t array_pressure_##L(const uint64_t*, uint64_t);
DECL(o0) DECL(o1) DECL(o2) DECL(o3)

static uint64_t r_call_loop(uint64_t x, uint64_t y, uint64_t n) {
  uint64_t acc = 0;
  for (uint64_t i = 0; i < n; i++) acc ^= ext_step(x * i) + y;
  return acc;
}
static uint64_t r_pressure(const uint64_t* a, uint64_t n) {
  uint64_t v[40], w[40];
  for (int k = 0; k < 40; k++) v[k] = a[k];
  for (uint64_t i = 0; i < n; i++) {
    for (int k = 0; k < 40; k++) w[k] = (v[k] + v[(k + 1) % 40]) ^ i;
    memcpy(v, w, sizeof v);
  }
  uint64_t s = 0;
  for (int k = 0; k < 40; k++) s += v[k];
  return s;
}
static uint64_t r_switch_dense(uint64_t s, uint64_t y) { return s < 8 ? y * (3 * s + 7) : y; }
static uint64_t r_many_args(uint64_t* a) {
  uint64_t p[12];
  for (int k = 0; k < 12; k++) p[k] = a[(k * 5) % 12];
  return callee12(p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7], p[8], p[9], p[10], p[11])
       + a[11] + a[10] + a[8];
}
static double r_fp_calls(double a, double b, uint64_t n) {
  double acc = a;
  for (uint64_t i = 0; i < n; i++) acc = fext(acc * b) + b + acc;
  return acc;
}
static uint64_t r_local_array(uint64_t x, uint64_t y) {
  uint64_t arr[8], acc = 0;
  for (uint64_t i = 0; i < 8; i++) arr[i] = i * x;
  for (uint64_t i = 0; i < 8; i++) acc = (acc ^ arr[i]) + y;
  return acc;
}

static uint64_t r_big_frame(uint64_t x, uint64_t y, uint64_t n) {
  static uint64_t arr[4096];
  uint64_t acc = 0;
  for (uint64_t i = 0; i < 4096; i++) arr[i] = i * x;
  for (uint64_t i = 0; i < n; i++) acc = (acc ^ arr[(i * 7) & 4095]) + y;
  return acc;
}

static uint64_t r_word_sum(const uint32_t* a, uint64_t n) {
  uint64_t acc = 0;
  for (uint64_t i = 0; i < n; i++) acc += a[i];
  return acc;
}

static uint64_t word(uint64_t* s) {
  *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17;
  return *s;
}

static int bad = 0;
#define CHECK(what, got, want) do { uint64_t g_ = (got), w_ = (want); \
  if (g_ != w_) { printf("MISMATCH %s: got %llu want %llu\n", what, \
    (unsigned long long)g_, (unsigned long long)w_); bad = 1; } } while (0)
#define CHECKF(what, got, want) do { double g_ = (got), w_ = (want); \
  if (memcmp(&g_, &w_, sizeof g_) != 0) { printf("MISMATCH %s: got %a want %a\n", what, g_, w_); \
    bad = 1; } } while (0)

int main(void) {
  uint64_t s = 0x9e3779b97f4a7c15ull;
  static uint64_t buf[64];
  static uint32_t words[64];
  uint64_t a[12];
  for (int round = 0; round < 48; round++) {
    for (int i = 0; i < 64; i++) buf[i] = word(&s);
    for (int i = 0; i < 12; i++) a[i] = word(&s);
    for (int i = 0; i < 64; i++) words[i] = (uint32_t)word(&s);
    uint64_t x = word(&s), y = word(&s), n = word(&s) % 24, sel = word(&s) % 11;
    double fa = (double)(word(&s) % 1000) / 7.0, fb = (double)(word(&s) % 100) / 64.0;
#define ROW(L) \
    CHECK("call_loop_" #L, call_loop_##L(x, y, n), r_call_loop(x, y, n)); \
    CHECK("pressure_" #L, pressure_##L(buf, n), r_pressure(buf, n)); \
    CHECK("switch_dense_" #L, switch_dense_##L(sel, y), r_switch_dense(sel, y)); \
    CHECK("many_args_" #L, many_args_##L(a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], \
          a[8], a[9], a[10], a[11]), r_many_args(a)); \
    CHECKF("fp_calls_" #L, fp_calls_##L(fa, fb, n % 8), r_fp_calls(fa, fb, n % 8)); \
    CHECK("local_array_" #L, local_array_##L(x, y), r_local_array(x, y)); \
    CHECK("big_frame_" #L, big_frame_##L(x, y, n * 100), r_big_frame(x, y, n * 100)); \
    CHECK("protected_array_" #L, protected_array_##L(x, y), r_local_array(x, y)); \
    CHECK("word_sum_" #L, word_sum_##L(words, n), r_word_sum(words, n)); \
    CHECK("array_pressure_" #L, array_pressure_##L(buf, n), r_pressure(buf, n) + n);
    ROW(o0) ROW(o1) ROW(o2) ROW(o3)
  }
  printf("post-ra value-flow native rows: %s\n", bad ? "MISMATCH" : "all equal");
  return bad;
}
"#;

/// The enforce-built kernels agree with the C reference.
#[cfg_attr(
    any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    ),
    test
)]
#[cfg_attr(
    not(any(
        all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"),
        all(target_arch = "aarch64", target_os = "macos")
    )),
    allow(dead_code)
)]
fn enforce_built_kernels_match_the_c_reference_natively() {
    use std::process::Command;

    let builds = build_all();
    let dir = fresh_dir::create("trust_cg_post_ra_vf_");
    let mut objects = Vec::new();
    for (symbol, built) in &builds {
        let path = dir.join(format!("{symbol}.o"));
        std::fs::write(&path, &built.object).expect("write object");
        objects.push(path);
    }
    let driver_c = dir.join("driver.c");
    let binary = dir.join("post_ra_value_flow_rows");
    std::fs::write(&driver_c, DRIVER).expect("write driver");
    let link = Command::new(native_host::C_COMPILER)
        .arg("-O1")
        .arg(&driver_c)
        .args(&objects)
        .args(native_host::link_hardening_args())
        .arg("-o")
        .arg(&binary)
        .output()
        .expect("run the linker");
    assert!(
        link.status.success(),
        "link:\n{}",
        String::from_utf8_lossy(&link.stderr)
    );
    let run = Command::new(&binary).output().expect("run the rows");
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(
        run.status.success(),
        "native rows failed in {} (kept only with {} set):\n{stdout}{}",
        dir.display(),
        fresh_dir::KEEP_ON_FAILURE,
        String::from_utf8_lossy(&run.stderr)
    );
    assert!(stdout.contains("all equal"), "{stdout}");
    eprintln!("{} builds on {}: {stdout}", builds.len(), native_host::HOST);
}
