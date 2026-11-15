// trust-cg-codegen - LDP formation must not hoist a plain load above an acquire
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `a = p[0]; f = flag.load(Acquire); b = p[1]` keeps `p[1]`'s read AFTER the
//! load-acquire at every optimization level. The windowed LDP formation
//! (`trust-cg-opt` `mem_pair`) used to fuse the two plain loads at `p[0]`'s
//! position (`ldp a, b, [p]; ldar f, [flag]`), so the read of `p[1]` was no
//! longer ordered after the acquire.
//!
//! The reordering is invisible to a single-threaded run (the values are the
//! same), so besides the value check this pins the emitted code shape: no
//! non-frame load pair precedes the function's `LDAR`. It does not exercise a
//! concurrent observer.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, JitCompilationResult};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::Target;
use trust_ir::{BinOp, Ordering, Ty};
use trust_ir_build::ModuleBuilder;

const LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const FUNC: &str = "read_around_acquire";

/// `(p, flag) -> p[0] + flag.load(Acquire) + p[1]`, with `p[1]` read after
/// the acquire through a constant byte GEP.
fn read_around_acquire_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("mem_pair_acquire_order");
    let ty = mb.add_func_type(vec![Ty::Ptr, Ty::Ptr], vec![Ty::I64]);
    let mut fb = mb.function(FUNC, ty);
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, Ty::Ptr);
    let flag = fb.add_block_param(entry, Ty::Ptr);

    fb.switch_to_block(entry);
    let a = fb.load(Ty::I64, p);
    let f = fb.atomic_load(Ty::I64, flag, Ordering::Acquire);
    let eight = fb.iconst(Ty::U64, 8);
    let p1 = fb.gep(Ty::I8, p, vec![eight]);
    let b = fb.load(Ty::I64, p1);
    let af = fb.binop(BinOp::Add, Ty::I64, a, f);
    let sum = fb.binop(BinOp::Add, Ty::I64, af, b);
    fb.ret(vec![sum]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

fn jit(module: &trust_ir::Module, opt_level: OptLevel) -> JitCompilationResult {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|error| panic!("{opt_level:?}: {error}"))
}

/// `LDAR` of any width: `size 001000 1 1 0 11111 1 11111 Rn Rt`.
fn is_ldar(word: u32) -> bool {
    word & 0x3FFF_FC00 == 0x08DF_FC00
}

/// Any load pair (`LDP`/`LDNP`/`LDPSW`, GPR or FP/SIMD, every index form):
/// `opc 101 V 0 xx 1 imm7 Rt2 Rn Rt`.
fn is_load_pair(word: u32) -> bool {
    word & 0x3A40_0000 == 0x2840_0000
}

/// The pair's base register `Rn`; frame (`x29`) and `sp` (31) pairs are
/// callee-save restores, not the user loads under test.
fn load_pair_base(word: u32) -> u32 {
    (word >> 5) & 0x1F
}

/// The function's instruction words, in layout order.
fn function_words(result: &JitCompilationResult) -> Vec<u32> {
    let range = result
        .buffer
        .function_ranges()
        .iter()
        .find(|(name, _)| name.trim_start_matches('_') == FUNC)
        .map(|(_, range)| range.clone())
        .expect("function range");
    let code = result.buffer.code_slice();
    code[range.start as usize..range.end as usize]
        .as_chunks::<4>()
        .0
        .iter()
        .map(|w| u32::from_le_bytes(*w))
        .collect()
}

#[test]
fn a_plain_load_after_an_acquire_stays_after_it() {
    let module = read_around_acquire_module();
    let p: [i64; 2] = [1, 1000];
    let flag: i64 = 100_000;
    for opt_level in LEVELS {
        let result = jit(&module, opt_level);
        let words = function_words(&result);
        let ldar = words
            .iter()
            .position(|&w| is_ldar(w))
            .unwrap_or_else(|| panic!("{opt_level:?}: no LDAR in {words:08x?}"));
        let hoisted: Vec<(usize, u32)> = words[..ldar]
            .iter()
            .copied()
            .enumerate()
            .filter(|&(_, w)| is_load_pair(w) && !matches!(load_pair_base(w), 29 | 31))
            .collect();
        assert!(
            hoisted.is_empty(),
            "{opt_level:?}: load pair(s) {hoisted:08x?} placed before the LDAR at word \
             {ldar} in {words:08x?}"
        );

        // SAFETY: the trust-ir signature is (ptr, ptr) -> i64; `p` holds the
        // two i64 the function reads, `flag` one more, and `result` outlives
        // the call.
        let entry = unsafe {
            result
                .buffer
                .get_fn_bound::<extern "C" fn(*const i64, *const i64) -> i64>(FUNC)
        }
        .expect("entry symbol");
        assert_eq!(entry.as_ref()(p.as_ptr(), &flag), 101_001, "{opt_level:?}");
    }
}

/// Distinct source global symbols do not license non-aliasing after ordinary
/// integer address arithmetic. This uses the typed module JIT and its owned
/// writable data image, not raw external ADRP/ADD relocation publication.
#[cfg(target_os = "macos")]
mod symbol_alias {
    use super::LEVELS;
    use std::collections::HashMap;

    use trust_cg_codegen::compiler::{
        Compiler, CompilerConfig, JitCompilationResult, JitValidationMode,
    };
    use trust_cg_codegen::pipeline::OptLevel;
    use trust_ir::value::GlobalId;
    use trust_ir::{BinOp, CastOp, Constant, Global, Inst, Linkage, Module, Ty, Visibility};
    use trust_ir_build::ModuleBuilder;

    const ALIAS: &str = "store_around_integer_alias";
    const DISJOINT: &str = "store_around_same_base_disjoint";
    const A: &str = "mem_pair_a";
    const B: &str = "mem_pair_b";
    const INITIAL_A: [u64; 4] = [
        0x1020_3040_5060_7080,
        0x91a2_b3c4_d5e6_f708,
        0x1234_5678_9abc_def0,
        0xfedc_ba98_7654_3210,
    ];
    const INITIAL_B: [u64; 4] = [
        0x0f1e_2d3c_4b5a_6978,
        0x8899_aabb_ccdd_eeff,
        0x0123_4567_89ab_cdef,
        0xffee_ddcc_bbaa_9988,
    ];
    const VALUES: [(u64, u64, u64); 3] = [
        (11, 22, 32),
        (u64::MAX, 0x8000_0000_0000_0000, u64::MAX),
        (
            0x0000_0001_0000_0000,
            0xfeed_beef_dead_cafe,
            0x7fff_ffff_ffff_ffff,
        ),
    ];

    fn module() -> Module {
        let mut mb = ModuleBuilder::new("mem_pair_distinct_symbol_integer_alias");
        let word = mb.add_type(Ty::U64);
        for (name, initial) in [(A, INITIAL_A), (B, INITIAL_B)] {
            mb.add_global(Global {
                name: name.into(),
                ty: Ty::Array(word, initial.len() as u64),
                mutable: true,
                initializer: Some(Constant::Aggregate(
                    initial
                        .into_iter()
                        .map(|value| Constant::Int(i128::from(value)))
                        .collect(),
                )),
                linkage: Linkage::External,
                tls: None,
                align: Some(8),
                section: None,
                visibility: Visibility::Default,
                retained: false,
            });
        }

        let signature = mb.add_func_type(vec![Ty::U64; 4], vec![Ty::U64]);
        for (name, integer_alias) in [(ALIAS, true), (DISJOINT, false)] {
            let mut fb = mb.function(name, signature);
            let entry = fb.create_block();
            let delta = fb.add_block_param(entry, Ty::U64);
            let first = fb.add_block_param(entry, Ty::U64);
            let middle = fb.add_block_param(entry, Ty::U64);
            let seed = fb.add_block_param(entry, Ty::U64);
            fb.switch_to_block(entry);
            let a = fb.global_addr(GlobalId::new(0));
            let one = fb.iconst(Ty::U64, 1);
            // Source-defined integer byte-address arithmetic: the ordinary
            // scalar constant add lowers to ADD-immediate and then a canonical
            // STR-immediate field access. A typed GEP initially tried here
            // lowered through index multiplication to STR-register-offset,
            // which never exercised mem-pair's scalar-immediate candidates.
            let a_bits = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, a);
            let eight = fb.iconst(Ty::U64, 8);
            let a1_bits = fb.binop(BinOp::Add, Ty::U64, a_bits, eight);
            let a1 = fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, a1_bits);
            let gap = if integer_alias {
                let b = fb.global_addr(GlobalId::new(1));
                let b_bits = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, b);
                let address = fb.binop(BinOp::Add, Ty::U64, b_bits, delta);
                fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, address)
            } else {
                let sixteen = fb.iconst(Ty::U64, 16);
                let a2_bits = fb.binop(BinOp::Add, Ty::U64, a_bits, sixteen);
                fb.cast(CastOp::IntToPtr, Ty::U64, Ty::Ptr, a2_bits)
            };
            fb.store(Ty::U64, a, first);
            fb.store(Ty::U64, gap, middle);
            let last = fb.binop(BinOp::Add, Ty::U64, seed, one);
            fb.store(Ty::U64, a1, last);
            fb.ret(vec![last]);
            fb.build();
        }
        mb.build().expect("ModuleBuilder::build: test fixture")
    }

    fn assert_original_address_shape(module: &Module) {
        let function = module
            .functions
            .iter()
            .find(|function| function.name == ALIAS)
            .expect("original alias function");
        let nodes: Vec<_> = function
            .blocks
            .iter()
            .flat_map(|block| &block.body)
            .collect();
        let globals: Vec<_> = nodes
            .iter()
            .filter_map(|node| match node.inst {
                Inst::GlobalAddr { global } => Some(global),
                _ => None,
            })
            .collect();
        assert_eq!(globals, [GlobalId::new(0), GlobalId::new(1)]);
        for wanted in [CastOp::PtrToInt, CastOp::IntToPtr] {
            assert_eq!(
                nodes
                    .iter()
                    .filter(|node| matches!(node.inst, Inst::Cast { op, .. } if op == wanted))
                    .count(),
                2,
                "original source must retain {wanted:?}"
            );
        }
        assert_eq!(
            nodes
                .iter()
                .filter(|node| matches!(node.inst, Inst::Store { .. }))
                .count(),
            3
        );
        assert!(
            nodes
                .iter()
                .all(|node| !matches!(node.inst, Inst::GEP { .. }))
        );
        assert_eq!(
            nodes
                .iter()
                .filter(|node| matches!(
                    node.inst,
                    Inst::Const {
                        ty: Ty::U64,
                        value: Constant::Int(8)
                    }
                ))
                .count(),
            1,
            "original field address retains the constant eight-byte offset"
        );
    }

    fn compile(module: &Module, level: OptLevel) -> JitCompilationResult {
        let config = CompilerConfig {
            opt_level: level,
            emit_proofs: false,
            parallel: false,
            ..CompilerConfig::for_host_jit_unchecked()
        };
        assert_eq!(config.jit_validation_mode(), JitValidationMode::Unchecked);
        Compiler::new(config)
            .with_codegen_license(super::permit_unlicensed())
            .compile_module_to_jit(module, &HashMap::new())
            .unwrap_or_else(|error| panic!("{level:?}: typed module JIT failed: {error}"))
    }

    fn words(result: &JitCompilationResult, function: &str) -> Vec<u32> {
        let range = result
            .buffer
            .function_ranges()
            .iter()
            .find(|(name, _)| name.trim_start_matches('_') == function)
            .map(|(_, range)| range.clone())
            .expect("actual native function range");
        result.buffer.code_slice()[range.start as usize..range.end as usize]
            .as_chunks::<4>()
            .0
            .iter()
            .map(|word| u32::from_le_bytes(*word))
            .collect()
    }

    /// Non-writeback GPR X-width STP, excluding SP/x29 frame stores. This is
    /// only an emitted-code non-vacuity check; it is not a semantics evaluator.
    fn user_pairs(words: &[u32]) -> usize {
        words
            .iter()
            .filter(|&&word| {
                word & 0xffc0_0000 == 0xa900_0000 && !matches!((word >> 5) & 31, 29 | 31)
            })
            .count()
    }

    type Kernel = extern "C" fn(u64, u64, u64, u64) -> u64;

    #[test]
    fn distinct_global_symbol_integer_addresses_can_alias_an_earlier_store() {
        let module = module();
        assert_original_address_shape(&module);
        let original = serde_json::to_string(&module).expect("complete original module");
        let mut failures = Vec::new();
        for level in LEVELS {
            let result = compile(&module, level);
            assert_eq!(serde_json::to_string(&module).unwrap(), original);
            let alias_words = words(&result, ALIAS);
            let disjoint_words = words(&result, DISJOINT);
            let alias_pairs = user_pairs(&alias_words);
            let disjoint_pairs = user_pairs(&disjoint_words);
            println!(
                "mem_pair_symbol_alias level={level:?} mode=Unchecked \
                 alias_user_stp={alias_pairs} same_base_user_stp={disjoint_pairs} \
                 alias_words={alias_words:08x?} same_base_words={disjoint_words:08x?}"
            );
            if level == OptLevel::O2 {
                println!(
                    "mem_pair_symbol_alias level=O2 same_base_positive_route={} \
                     native_memory_checks=required pair_formation_not_required_at_this_level",
                    if disjoint_pairs == 0 {
                        "unpaired"
                    } else {
                        "paired"
                    }
                );
            }

            let a = result.buffer.data_symbol_ptr(A).expect("owned A data") as *mut u64;
            let b = result.buffer.data_symbol_ptr(B).expect("owned B data") as *mut u64;
            assert_ne!(a, b, "distinct placed globals, not external alias bindings");
            assert_eq!((a as usize) % 8, 0);
            assert_eq!((b as usize) % 8, 0);
            let (image_base, image_len) =
                result.buffer.data_image_range().expect("owned data image");
            let image_end = image_base.checked_add(image_len as u64).unwrap();
            for address in [a as u64, b as u64] {
                assert!(address >= image_base && address.checked_add(32).unwrap() <= image_end);
            }
            assert!((a as u64) + 32 <= b as u64 || (b as u64) + 32 <= a as u64);
            // SAFETY: both globals contain four initialized u64 words in this
            // live buffer's mutable JIT image. Every displacement below lands
            // exactly at B[0] or A[0..=2]; no dangling or out-of-image access.
            let alias = unsafe { result.buffer.get_fn_bound::<Kernel>(ALIAS) }.expect(ALIAS);
            // SAFETY: this function has the same four-U64 -> U64 signature.
            let disjoint =
                unsafe { result.buffer.get_fn_bound::<Kernel>(DISJOINT) }.expect(DISJOINT);
            let delta_a = (a as u64).wrapping_sub(b as u64);
            let placements = [
                ("B0", 0, None),
                ("A0", delta_a, Some(0)),
                ("A1", delta_a.wrapping_add(8), Some(1)),
                ("A2", delta_a.wrapping_add(16), Some(2)),
            ];
            for (placement, delta, aliased_word) in placements {
                assert_eq!(
                    (b as u64).wrapping_add(delta),
                    match aliased_word {
                        None => b as u64,
                        Some(index) => (a as u64).wrapping_add(8 * index as u64),
                    }
                );
                for (first, middle, seed) in VALUES {
                    // The independent expectation is the source's three stores
                    // in order, including the seed+1 wrapping U64 arithmetic.
                    let last = seed.wrapping_add(1);
                    let mut expected_a = INITIAL_A;
                    let mut expected_b = INITIAL_B;
                    expected_a[0] = first;
                    match aliased_word {
                        Some(index) => expected_a[index] = middle,
                        None => expected_b[0] = middle,
                    }
                    expected_a[1] = last;
                    unsafe {
                        std::ptr::copy_nonoverlapping(INITIAL_A.as_ptr(), a, INITIAL_A.len());
                        std::ptr::copy_nonoverlapping(INITIAL_B.as_ptr(), b, INITIAL_B.len());
                    }
                    let returned = alias.as_ref()(delta, first, middle, seed);
                    let actual_a = unsafe { std::ptr::read(a.cast::<[u64; 4]>()) };
                    let actual_b = unsafe { std::ptr::read(b.cast::<[u64; 4]>()) };
                    let matches =
                        returned == last && actual_a == expected_a && actual_b == expected_b;
                    println!(
                        "mem_pair_symbol_alias level={level:?} placement={placement} \
                         delta={delta:016x} first={first:016x} middle={middle:016x} \
                         seed={seed:016x} returned={returned:016x} \
                         A={actual_a:016x?} B={actual_b:016x?} matches={matches}"
                    );
                    if !matches {
                        failures.push(format!(
                            "{level:?} native miscompile {placement}: returned {returned:016x}/{last:016x}, \
                             A={actual_a:016x?}/{expected_a:016x?}, B={actual_b:016x?}/{expected_b:016x?}"
                        ));
                    }
                }
            }

            for (first, middle, seed) in VALUES {
                unsafe {
                    std::ptr::copy_nonoverlapping(INITIAL_A.as_ptr(), a, INITIAL_A.len());
                    std::ptr::copy_nonoverlapping(INITIAL_B.as_ptr(), b, INITIAL_B.len());
                }
                let last = seed.wrapping_add(1);
                let returned = disjoint.as_ref()(0, first, middle, seed);
                let actual_a = unsafe { std::ptr::read(a.cast::<[u64; 4]>()) };
                let actual_b = unsafe { std::ptr::read(b.cast::<[u64; 4]>()) };
                let matches = returned == last
                    && actual_a == [first, last, middle, INITIAL_A[3]]
                    && actual_b == INITIAL_B;
                println!(
                    "mem_pair_same_base_disjoint level={level:?} first={first:016x} \
                     middle={middle:016x} seed={seed:016x} returned={returned:016x} \
                     A={actual_a:016x?} B={actual_b:016x?} matches={matches}"
                );
                if !matches {
                    failures.push(format!(
                        "{level:?}: same-base disjoint native control corrupted memory"
                    ));
                }
            }
            if matches!(level, OptLevel::O2 | OptLevel::O3) && alias_pairs != 0 {
                failures.push(format!(
                    "{level:?}: integer-displacement alias body has {alias_pairs} user STP; \
                     unknown aliasing may not license sinking the first store"
                ));
            }
            // O3 is the qualified non-vacuous store-sink route for this
            // source shape. O2 retains separate materialized ADD-immediate
            // field bases, so its unpaired positive is an explicit route gap,
            // not a memory error. Every level still executes all memory cases;
            // both optimized levels must reject unknown-alias pair motion.
            if level == OptLevel::O3 && disjoint_pairs == 0 {
                failures.push(format!(
                    "{level:?}: same-base disjoint control has no user STP; \
                     pair-formation non-vacuity was not exercised"
                ));
            }
        }
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
