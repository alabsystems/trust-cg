// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AArch64 branch relaxation, end to end: TrustIR functions whose conditional
//! branches span more than their encoding range compile through the
//! production compiler and compute the right answers.
//!
//! Before relaxation existed, the pipeline resolved every branch straight to
//! a PC-relative immediate and the encoder refused any function in which one
//! did not fit (TY W4: `BCond branch offset 279712 out of signed 19-bit
//! range`); the original scalar tests below then fail at compile time. B.cond/CBZ/CBNZ reach
//! +/-1 MiB, TBZ/TBNZ +/-32 KiB.
//!
//! Two shapes, each with a long straight-line block (`v = (v op y) ^ v`, two
//! machine instructions per step) that some conditional branch must cross
//! whatever the layout:
//!
//! ```text
//! split(x, y):  if x & 8 { v = y; n steps of add } else { v = y; n steps of sub }
//! looped(k, y): if y == 0 return 7;
//!               v = y; do { n steps of add; k -= 1 } while again(k); return v
//! ```
//!
//! In `split` one arm is laid out after the branch and the other beyond it;
//! in `looped` the latch branches back over the whole body. The emitted code
//! is checked for the standard relaxation (a conditional branch skipping +2
//! instructions straight into an unconditional `B` whose target that
//! conditional could not encode), then executed: by the host-independent
//! decode-and-interpret harness (its step budget covers the long block at the
//! TBZ scale only) and, on an Apple-silicon host, natively through the raw JIT
//! lane TY drives.

mod common;

#[test]
fn actual_clean_300_case_module_compiles_under_its_original_explicit_license_policy() {
    use sha2::Digest;
    use trust_cg_codegen::compiler::CompileError;
    use trust_cg_lower::{AdapterError, CodegenLicensePolicy};
    let bytes = include_bytes!("fixtures/aarch64_local_address/layout_enum_300.tmbc");
    assert_eq!(
        format!("{:x}", sha2::Sha256::digest(bytes)),
        "00b5ebde6bfe21b4cf7fab9a34b6ec473755c3ca79dce8078f95f8259e16339e"
    );
    let module = trust_cg_codegen::pipeline::load_module_from_bytes(bytes).unwrap();
    assert_eq!(
        module
            .functions
            .iter()
            .filter(|f| !f.blocks.is_empty())
            .count(),
        8,
        "retain the complete original generated module, not only E.casesOn"
    );
    assert!(
        module
            .functions
            .iter()
            .any(|f| f.name == "E.casesOn" && !f.blocks.is_empty())
    );
    let compiler = || {
        Compiler::new_for_target_spec(
            CompilerConfig {
                opt_level: OptLevel::O0,
                target: Target::Aarch64,
                parallel: false,
                ..Default::default()
            },
            TargetSpec::parse("aarch64-apple-darwin").unwrap(),
        )
    };
    // Pair the restored native capability with the real default guard.
    let error = compiler()
        .compile(&module)
        .expect_err("default refuses this unvalidated authority");
    assert!(
        matches!(error, CompileError::Adapter(AdapterError::UnrecognizedGateAuthority { ref authority, .. }) if authority == "clean-compiler-unvalidated"),
        "{error}"
    );
    let policy =
        || CodegenLicensePolicy::default().with_recognized_authority("clean-compiler-unvalidated");
    let mut missing = module.clone();
    missing
        .functions
        .iter_mut()
        .find(|f| !f.blocks.is_empty())
        .unwrap()
        .body_gate = None;
    let error = compiler()
        .with_codegen_license(policy())
        .compile(&missing)
        .expect_err("claimless body still refuses");
    assert!(
        matches!(
            error,
            CompileError::Adapter(AdapterError::UnlicensedBody { .. })
        ),
        "{error}"
    );
    // EXACT original explicit recognition, with the default Refuse policy for
    // unlicensed bodies. No permit_unlicensed or emit-proof exception here.
    let output = compiler()
        .with_codegen_license(policy())
        .compile(&module)
        .expect("the real 300-case program must reach object emission");
    assert!(output.object_code.len() > 1 << 20);
}

use common::a64_interp::{A64Interp, extract_text, symbol_addrs, text_branch_relocs};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{Target, TargetSpec};

/// B.cond / CBZ / CBNZ reach +/-2^18 instructions.
const IMM19_REACH: i64 = 1 << 18;
/// TBZ / TBNZ reach +/-2^13 instructions.
const IMM14_REACH: i64 = 1 << 13;

/// A distinctive nonzero `y`.
const Y: u64 = 0x9E37_79B9_7F4A_7C15;

/// How `looped` decides to go round again.
#[derive(Clone, Copy, Debug)]
enum Latch {
    /// `k != 0`: B.cond or CBZ/CBNZ, +/-1 MiB.
    NonZero,
    /// `k & 8 == 0`: TBZ/TBNZ once fused, +/-32 KiB.
    Bit3Clear,
}

impl Latch {
    fn again(self, k: u64) -> bool {
        match self {
            Latch::NonZero => k != 0,
            Latch::Bit3Clear => k & 8 == 0,
        }
    }
}

/// Append `steps` steps of `v = (v op y) ^ v` from value `%v`, numbering new
/// values from `%next`; return the last value.
fn chain(
    s: &mut String,
    next: &mut usize,
    mut v: usize,
    y: usize,
    steps: usize,
    op: &str,
) -> usize {
    for _ in 0..steps {
        let (a, w) = (*next, *next + 1);
        *next += 2;
        s.push_str(&format!(
            "    %{a} = {op} u64 %{v}, %{y}\n    %{w} = xor u64 %{a}, %{v}\n"
        ));
        v = w;
    }
    v
}

fn reference_chain(mut v: u64, y: u64, steps: usize, op: fn(u64, u64) -> u64) -> u64 {
    for _ in 0..steps {
        v = op(v, y) ^ v;
    }
    v
}

const HEADER: &str = "; trust_ir text format v1\n\
                      module \"branch_relaxation\"\n\
                      target \"aarch64-apple-darwin\" 8 little\n\n\
                      functy.0 = (u64, u64) -> (u64)\n\n";

/// `split(x, y)`.
fn split_text(steps: usize) -> String {
    let mut s = String::from("fn @split(functy.0) {\nbb0(%0: u64, %1: u64):\n");
    s.push_str("    %2 = const u64 8\n    %3 = and u64 %0, %2\n    %4 = const u64 0\n");
    s.push_str("    %5 = icmp ne u64 %3, %4\n    condbr %5, bb1(%1), bb2(%1)\n");
    let mut next = 100;
    s.push_str("bb1(%6: u64):\n");
    let v = chain(&mut s, &mut next, 6, 1, steps, "add");
    s.push_str(&format!("    ret %{v}\nbb2(%7: u64):\n"));
    let v = chain(&mut s, &mut next, 7, 1, steps, "sub");
    s.push_str(&format!("    ret %{v}\n}}\n\n"));
    s
}

fn split_reference(steps: usize, x: u64, y: u64) -> u64 {
    if x & 8 != 0 {
        reference_chain(y, y, steps, u64::wrapping_add)
    } else {
        reference_chain(y, y, steps, u64::wrapping_sub)
    }
}

/// `looped(k, y)`.
fn looped_text(latch: Latch, steps: usize) -> String {
    let mut s = String::from("fn @looped(functy.0) {\nbb0(%0: u64, %1: u64):\n");
    s.push_str("    %2 = const u64 0\n    %3 = icmp eq u64 %1, %2\n");
    s.push_str("    condbr %3, bb3, bb1(%1, %0)\n");
    s.push_str("bb1(%4: u64, %5: u64):\n");
    let mut next = 100;
    let v = chain(&mut s, &mut next, 4, 1, steps, "add");
    s.push_str("    %10 = const u64 1\n    %11 = sub u64 %5, %10\n");
    match latch {
        Latch::NonZero => s.push_str("    %14 = icmp ne u64 %11, %2\n"),
        Latch::Bit3Clear => s.push_str(
            "    %12 = const u64 8\n    %13 = and u64 %11, %12\n    %14 = icmp eq u64 %13, %2\n",
        ),
    }
    s.push_str(&format!(
        "    condbr %14, bb1(%{v}, %11), bb2(%{v})\nbb2(%6: u64):\n    ret %6\n\
         bb3:\n    %7 = const u64 7\n    ret %7\n}}\n\n"
    ));
    s
}

fn looped_reference(latch: Latch, steps: usize, k: u64, y: u64) -> u64 {
    if y == 0 {
        return 7;
    }
    let (mut v, mut k) = (y, k);
    loop {
        v = reference_chain(v, y, steps, u64::wrapping_add);
        k = k.wrapping_sub(1);
        if !latch.again(k) {
            return v;
        }
    }
}

fn signed(word: u32, shift: u32, bits: u32) -> i64 {
    let raw = (word >> shift) & ((1 << bits) - 1);
    let sign = 1i64 << (bits - 1);
    (raw as i64 ^ sign) - sign
}

/// Offset and reach of a conditional branch word, if it is one.
fn conditional(word: u32) -> Option<(i64, i64)> {
    if word & 0xFF00_0010 == 0x5400_0000 || word & 0x7E00_0000 == 0x3400_0000 {
        // B.cond, CBZ/CBNZ: imm19.
        Some((signed(word, 5, 19), IMM19_REACH))
    } else if word & 0x7E00_0000 == 0x3600_0000 {
        // TBZ/TBNZ: imm14.
        Some((signed(word, 5, 14), IMM14_REACH))
    } else {
        None
    }
}

/// Offset of an unconditional `B` word, if it is one.
fn unconditional(word: u32) -> Option<i64> {
    (word & 0xFC00_0000 == 0x1400_0000).then(|| signed(word, 0, 26))
}

/// Relaxation sites in `text`: a conditional branch to +2 followed by a `B`
/// whose target that conditional could not have encoded. Returns the reach of
/// each site's conditional.
fn relaxation_sites(text: &[u8]) -> Vec<i64> {
    let words: Vec<u32> = text
        .as_chunks::<4>()
        .0
        .iter()
        .map(|w| u32::from_le_bytes(*w))
        .collect();
    words
        .windows(2)
        .filter_map(|pair| {
            let (offset, reach) = conditional(pair[0])?;
            // The B's target, seen from the conditional one word earlier.
            let from_conditional = unconditional(pair[1])? + 1;
            (offset == 2 && !(-reach..reach).contains(&from_conditional)).then_some(reach)
        })
        .collect()
}

fn compile_object(module: &trust_ir::Module, opt_level: OptLevel) -> Vec<u8> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            target: Target::Aarch64,
            parallel: false,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("aarch64-apple-darwin").expect("aarch64-apple-darwin"),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(module)
    .unwrap_or_else(|error| panic!("{opt_level:?}: far branches must relax, got {error}"))
    .object_code
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

fn interpret(object: &[u8], function: &str, x: u64, y: u64) -> u64 {
    let text = extract_text(object);
    let addresses = symbol_addrs(object);
    let address = addresses
        .get(&format!("_{function}"))
        .or_else(|| addresses.get(function))
        .unwrap_or_else(|| panic!("{function} missing from {:?}", addresses.keys()));
    let entry = (address - text.addr) as usize;
    let mut interp = A64Interp::new(text.bytes).with_branch_relocs(text_branch_relocs(object));
    interp.set_x(0, x);
    interp.set_x(1, y);
    interp
        .run(entry)
        .unwrap_or_else(|error| panic!("{function}({x:#x}, {y:#x}) must run: {error:?}"))
}

/// Split inputs: each arm.
const SPLIT_INPUTS: [(u64, u64); 3] = [(8, Y), (0b0111, Y), (0xF8, 3)];
/// Looped inputs: `y == 0` (the short path), then one or two trips, then
/// three or four.
const LOOPED_INPUTS: [(u64, u64); 3] = [(1, 0), (1, Y), (3, 5)];

#[test]
fn tbz_scale_functions_relax_and_compute_the_reference_at_o0_o1_o2() {
    // 12,000 instructions of long block: over TBZ's 8,191-instruction reach,
    // inside the interpreter's step budget (four loop trips included).
    let steps = 6_000;
    let latch = Latch::Bit3Clear;
    let text = format!("{HEADER}{}{}", split_text(steps), looped_text(latch, steps));
    let module = trust_ir::parser::parse_module(&text).expect("generated TrustIR parses");
    for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2] {
        let object = compile_object(&module, opt_level);
        if opt_level == OptLevel::O2 {
            // O2 fuses both bit tests into TBZ/TBNZ, and both then span the
            // long block: the split arm laid out second, the loop back-edge.
            let sites = relaxation_sites(&extract_text(&object).bytes);
            assert_eq!(sites, vec![IMM14_REACH; 2], "O2: both TBZ/TBNZ relaxed");
        }
        for (x, y) in SPLIT_INPUTS {
            assert_eq!(
                interpret(&object, "split", x, y),
                split_reference(steps, x, y),
                "{opt_level:?}: split({x:#x}, {y:#x})"
            );
        }
        for (k, y) in LOOPED_INPUTS {
            assert_eq!(
                interpret(&object, "looped", k, y),
                looped_reference(latch, steps, k, y),
                "{opt_level:?}: looped({k}, {y:#x})"
            );
        }
    }
    native::check(&module, |function, x, y| match function {
        "split" => split_reference(steps, x, y),
        _ => looped_reference(latch, steps, x, y),
    });
}

#[test]
fn a_loop_whose_back_edge_spans_more_than_1_mib_relaxes_and_runs() {
    // 264,000 instructions of loop body: the latch's branch back to the header
    // is past B.cond/CBNZ's 262,143-instruction reach. O1 is the raw-JIT
    // level.
    let steps = 132_000;
    let latch = Latch::NonZero;
    let text = format!("{HEADER}{}", looped_text(latch, steps));
    let module = trust_ir::parser::parse_module(&text).expect("generated TrustIR parses");
    let object = compile_object(&module, OptLevel::O1);
    let sites = relaxation_sites(&extract_text(&object).bytes);
    assert_eq!(sites, vec![IMM19_REACH], "O1: the back-edge was relaxed");
    // The interpreter's step budget covers the short path only.
    assert_eq!(interpret(&object, "looped", 1, 0), 7);
    native::check(&module, |_, k, y| looped_reference(latch, steps, k, y));
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod native {
    use super::*;
    use std::collections::HashMap;

    /// Compile through the raw JIT (the lane TY drives) and call every
    /// function natively on its inputs, long paths included.
    pub fn check(module: &trust_ir::Module, reference: impl Fn(&str, u64, u64) -> u64) {
        let buffer = Compiler::new(CompilerConfig::jit_fast(Target::Aarch64))
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(module, &HashMap::new())
            .unwrap_or_else(|error| panic!("raw JIT: far branches must relax, got {error}"))
            .buffer;
        for (function, inputs) in [("split", SPLIT_INPUTS), ("looped", LOOPED_INPUTS)] {
            let Some(pointer) = buffer.get_fn_ptr_bound(function) else {
                continue;
            };
            // SAFETY: every function here is `(u64, u64) -> (u64)` in TrustIR,
            // i.e. `extern "C" fn(u64, u64) -> u64`, and `buffer` outlives the
            // calls.
            let f: extern "C" fn(u64, u64) -> u64 =
                unsafe { std::mem::transmute(pointer.as_ptr()) };
            for (x, y) in inputs {
                assert_eq!(
                    f(x, y),
                    reference(function, x, y),
                    "native JIT: {function}({x:#x}, {y:#x})"
                );
            }
        }
    }
}

#[cfg(not(all(target_os = "macos", target_arch = "aarch64")))]
mod native {
    pub fn check(_: &trust_ir::Module, _: impl Fn(&str, u64, u64) -> u64) {}
}
