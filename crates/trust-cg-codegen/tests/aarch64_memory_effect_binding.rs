// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! The per-compile binding of the verifier's word-bound memory-effect
//! decomposition (`trust_cg_verify::aarch64_memory_effect`, ledger L07-P2 /
//! X-OPCODES-P1 / L04-P7) to the words the encoder emits.
//!
//! * For every admitted scalar (immediate, H/S/D/Q, sign-extending,
//!   pre/post-index and register-offset; L04-P1), pair and NEON LD1/ST1
//!   post-index memory shape enumerated here, the live encoder's word is the
//!   word every part of the
//!   decomposition carries, ENC-5 accepts it, and every part holds over it.
//!   A word that differs fails ENC-5 in its default `enforce` mode, naming the
//!   memory-effect binding.
//! * Native execution: programs whose frames save and restore callee-saved
//!   registers with STP/LDP and whose bodies load and store words, bytes and
//!   halfwords through pointers compile through the JIT at O0 and O2 with the
//!   binding enforced and return what the same computation returns in Rust
//!   (the host compiler, LLVM) on every input of a battery.
//! * The decomposition fires on the production route: in a proof-required
//!   compile of a pointer-reading function, the LDR row is judged by its own
//!   lane and the Formal-only bound-memory rule (credited `Formal` on a host
//!   whose checker the bound-memory manifest qualifies), and, uncredited, it
//!   carries its memory-effect decomposition's clause, which never credits.
//!
//! All of it is testing evidence about the encoder, the decomposition and the
//! binding; none of it is a proof, and nothing here credits an instruction.
#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::aarch64::decode_check::A64DecodeCheck;
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_codegen::decode_check::{DecodeCheck, DecodeCheckOutcome};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::{Compiler, CompilerConfig, Target};
use trust_cg_ir::{AArch64Opcode as Op, MachInst, MachOperand as Arg, PReg, SpecialReg};
use trust_cg_verify::aarch64_memory_effect::{
    InProcess, MEMORY_EFFECT_OPCODES, check_emitted_memory_effect_word, decide_in_process,
    memory_effect, memory_effect_word,
};
use trust_cg_verify::lowering_proof::VerificationConfig;
use trust_ir::{BinOp, Ty};
use trust_ir_build::ModuleBuilder;

#[path = "common/pinned_target.rs"]
mod pinned_target;

fn preg(n: u16) -> Arg {
    Arg::PReg(PReg::new(n))
}

fn imm(value: i64) -> Arg {
    Arg::Imm(value)
}

/// Every pair and scalar shape this test enumerates: each bank the opcode
/// names, register fields at both ends of the file (and SP / the zero
/// register where a slot can spell them), and offsets across and just past
/// each immediate field.
fn shapes() -> Vec<MachInst> {
    let mut out = Vec::new();
    // (bank base encoding, element bytes): W, X, Q, D, S.
    let banks = [(32u16, 4i64), (0, 8), (64, 16), (96, 8), (128, 4)];
    let bases = [preg(0), preg(17), preg(29), Arg::Special(SpecialReg::SP)];
    for opcode in [
        Op::StpRI,
        Op::LdpRI,
        Op::StpPreIndex,
        Op::LdpPostIndex,
        Op::NeonStpQPost,
        Op::NeonLdpQPost,
    ] {
        for (bank, size) in banks {
            for (rt, rt2) in [(0u16, 1u16), (19, 20), (29, 30), (30, 29), (7, 7)] {
                for base in &bases {
                    for scaled in [-65, -64, -2, -1, 0, 1, 2, 63, 64] {
                        out.push(MachInst::new(
                            opcode,
                            vec![
                                preg(bank + rt),
                                preg(bank + rt2),
                                base.clone(),
                                imm(scaled * size),
                            ],
                        ));
                    }
                }
            }
        }
        out.push(MachInst::new(
            opcode,
            vec![
                Arg::Special(SpecialReg::XZR),
                Arg::Special(SpecialReg::XZR),
                preg(3),
            ],
        ));
    }
    let data = [preg(0), preg(16), preg(30), preg(32), preg(47), preg(62)];
    for opcode in [
        Op::LdrRI,
        Op::StrRI,
        Op::LdrbRI,
        Op::StrbRI,
        Op::LdrhRI,
        Op::StrhRI,
    ] {
        for value in &data {
            for base in &bases {
                for offset in [
                    -257, -256, -9, -1, 0, 1, 2, 3, 4, 8, 255, 256, 4095, 8190, 16380, 32760,
                ] {
                    out.push(MachInst::new(
                        opcode,
                        vec![value.clone(), base.clone(), imm(offset)],
                    ));
                }
            }
        }
        out.push(MachInst::new(
            opcode,
            vec![Arg::Special(SpecialReg::XZR), preg(1)],
        ));
    }
    // L04-P1: the scalar forms the decomposition admits through the form
    // binder — H/S/D/Q immediates (the scalar form encoder's word), the
    // sign-extending immediates, W/X pre/post-index writeback, and register
    // offset in every packed mode (W/X and H/S/D/Q transfers, W/X/ZR index).
    let fpr = [
        preg(165),
        preg(165 + 31),
        preg(128 + 3),
        preg(96 + 30),
        preg(64),
        preg(64 + 31),
    ];
    for opcode in [Op::LdrRI, Op::StrRI] {
        for value in &fpr {
            for base in &bases {
                for offset in [
                    -257, -256, -16, -1, 0, 1, 2, 4, 8, 16, 255, 256, 4095, 8190, 65520,
                ] {
                    out.push(MachInst::new(
                        opcode,
                        vec![value.clone(), base.clone(), imm(offset)],
                    ));
                }
            }
        }
    }
    for opcode in [Op::LdrsbRI, Op::LdrshRI] {
        for value in &data {
            for base in &bases {
                for offset in [-257, -256, -1, 0, 1, 2, 255, 256, 4095, 8190] {
                    out.push(MachInst::new(
                        opcode,
                        vec![value.clone(), base.clone(), imm(offset)],
                    ));
                }
            }
        }
    }
    for opcode in [
        Op::LdrPreIndex,
        Op::LdrPostIndex,
        Op::StrPreIndex,
        Op::StrPostIndex,
    ] {
        for value in &data {
            for base in &bases {
                for offset in [-257, -256, -16, -1, 0, 8, 255, 256] {
                    out.push(MachInst::new(
                        opcode,
                        vec![value.clone(), base.clone(), imm(offset)],
                    ));
                }
            }
        }
    }
    let indices = [
        preg(3),
        preg(30),
        preg(32 + 4),
        Arg::Special(SpecialReg::XZR),
    ];
    for opcode in [
        Op::LdrRO,
        Op::StrRO,
        Op::LdrbRO,
        Op::LdrhRO,
        Op::StrbRO,
        Op::StrhRO,
    ] {
        for value in data.iter().chain(&fpr) {
            for base in &bases {
                for index in &indices {
                    for mode in 3..=16 {
                        out.push(MachInst::new(
                            opcode,
                            vec![value.clone(), base.clone(), index.clone(), imm(mode)],
                        ));
                    }
                }
            }
        }
    }
    // NEON LD1/ST1 (one register, immediate post-index; ledger L04-P6): Q
    // registers at both ends of the file, a D register (admitted for the
    // 64-bit arrangements only), a GPR (refused), every arrangement selector
    // and one past each end.
    for opcode in [Op::NeonLd1Post, Op::NeonSt1Post] {
        for transfer in [
            preg(64),
            preg(64 + 17),
            preg(64 + 31),
            preg(96 + 5),
            preg(3),
        ] {
            for base in &bases {
                for selector in -1..=7 {
                    out.push(MachInst::new(
                        opcode,
                        vec![transfer.clone(), base.clone(), imm(selector)],
                    ));
                }
            }
        }
    }
    out
}

#[test]
fn live_encoder_words_are_the_memory_effect_words_for_every_admitted_shape() {
    let config = VerificationConfig::with_sample_count(512);
    let mut admitted: HashMap<Op, usize> = HashMap::new();
    let mut failures = Vec::new();
    let shapes = shapes();
    for (index, inst) in shapes.iter().enumerate() {
        let Some(derived) = memory_effect_word(inst) else {
            continue;
        };
        *admitted.entry(inst.opcode).or_default() += 1;
        let word = match encode_instruction(inst) {
            Ok(word) => word,
            Err(error) => {
                failures.push(format!(
                    "{inst:?}: admitted but the encoder refuses: {error:?}"
                ));
                continue;
            }
        };
        if word != derived {
            failures.push(format!(
                "{inst:?}: encoder {word:#010x}, decomposition {derived:#010x}"
            ));
            continue;
        }
        if check_emitted_memory_effect_word(inst, word) != Some(Ok(())) {
            failures.push(format!("{inst:?}: binding rejects the encoder word"));
        }
        let outcome = A64DecodeCheck.check_one(inst, &word.to_le_bytes(), None);
        if !matches!(outcome, DecodeCheckOutcome::Match) {
            failures.push(format!("{inst:?} {word:#010x}: ENC-5 {outcome:?}"));
        }
        // Every part of every fourth shape is decided (the unit tests decide
        // the assembler anchors and a sweep at the production sample count).
        if index % 4 == 0 {
            for part in memory_effect(inst).expect("admitted").parts {
                if !matches!(decide_in_process(&part, &config), InProcess::Holds(_)) {
                    failures.push(format!("{inst:?}: {} does not hold", part.obligation.name));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
    let missing: Vec<Op> = MEMORY_EFFECT_OPCODES
        .iter()
        .copied()
        .filter(|opcode| !admitted.contains_key(opcode))
        .collect();
    assert_eq!(missing, Vec::<Op>::new());
    let total: usize = admitted.values().sum();
    assert_eq!((total, shapes.len()), (ADMITTED, ENUMERATED));
}

/// The enumeration's size and its admitted share; a change is a review item.
const ADMITTED: usize = 11_261;
const ENUMERATED: usize = 26_172;

#[test]
fn enc5_refuses_a_pair_word_the_decomposition_does_not_carry() {
    for (inst, word) in [
        (
            MachInst::new(
                Op::StpPreIndex,
                vec![preg(29), preg(30), Arg::Special(SpecialReg::SP), imm(-16)],
            ),
            0xa9bf_7bfdu32,
        ),
        (
            MachInst::new(
                Op::LdpPostIndex,
                vec![preg(29), preg(30), Arg::Special(SpecialReg::SP), imm(16)],
            ),
            0xa8c1_7bfd,
        ),
        (
            MachInst::new(Op::NeonStpQPost, vec![preg(64), preg(65), preg(0), imm(32)]),
            0xac81_0400,
        ),
    ] {
        assert!(matches!(
            A64DecodeCheck.check_one(&inst, &word.to_le_bytes(), None),
            DecodeCheckOutcome::Match
        ));
        for bit in [0, 5, 10, 15, 22, 23, 26, 30] {
            let corrupted = word ^ (1 << bit);
            match A64DecodeCheck.check_one(&inst, &corrupted.to_le_bytes(), None) {
                DecodeCheckOutcome::Mismatch(error) => assert!(
                    error
                        .message
                        .contains("the memory-effect obligations carry"),
                    "{inst:?} bit {bit}: {}",
                    error.message
                ),
                other => panic!("{inst:?} bit {bit}: {other:?}"),
            }
        }
    }
}

fn native_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("aarch64_memory_effect_binding");
    let mix = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![Ty::I64]);
    let spill = mb.add_func_type(vec![Ty::I64, Ty::I64, Ty::I64, Ty::I64], vec![Ty::I64]);
    let cells = mb.add_func_type(vec![Ty::Ptr, Ty::I64], vec![Ty::I64]);
    // 0: the host's `ext_mix` (`host_mix`), a real call at every level.
    let ext_mix = mb.declare_function("ext_mix", mix);
    assert_eq!(ext_mix, trust_ir::FuncId::new(0));
    {
        // 1: four values live across two calls: the frame saves and restores
        // callee-saved pairs (STP/LDP at SP) around the body.
        let mut fb = mb.function("keep_across_calls", spill);
        let entry = fb.create_block();
        let a = fb.add_block_param(entry, Ty::I64);
        let b = fb.add_block_param(entry, Ty::I64);
        let c = fb.add_block_param(entry, Ty::I64);
        let d = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let first = fb.call(trust_ir::FuncId::new(0), vec![a, b]);
        let second = fb.call(trust_ir::FuncId::new(0), vec![c, first]);
        let ab = fb.add(Ty::I64, a, b);
        let cd = fb.binop(BinOp::Xor, Ty::I64, c, d);
        let left = fb.add(Ty::I64, ab, cd);
        let right = fb.sub(Ty::I64, second, d);
        let result = fb.add(Ty::I64, left, right);
        fb.ret(vec![result]);
        fb.build();
    }
    {
        // 2: word, halfword and byte stores and loads through a pointer:
        // `p[1] = v; ((u32*)p)[5] = v; ((u16*)p)[13] = v; ((u8*)p)[31] = v;`
        // returns `p[1] + p[0] + ((u32*)p)[5] + ((u16*)p)[13] + ((u8*)p)[31]`.
        let mut fb = mb.function("cells", cells);
        let entry = fb.create_block();
        let p = fb.add_block_param(entry, Ty::Ptr);
        let v = fb.add_block_param(entry, Ty::I64);
        fb.switch_to_block(entry);
        let one = fb.iconst(Ty::I64, 1);
        let five = fb.iconst(Ty::I64, 5);
        let thirteen = fb.iconst(Ty::I64, 13);
        let thirty_one = fb.iconst(Ty::I64, 31);
        let slot64 = fb.gep(Ty::I64, p, vec![one]);
        let slot32 = fb.gep(Ty::I32, p, vec![five]);
        let slot16 = fb.gep(Ty::I16, p, vec![thirteen]);
        let slot8 = fb.gep(Ty::I8, p, vec![thirty_one]);
        let v32 = fb.trunc(Ty::I64, Ty::I32, v);
        let v16 = fb.trunc(Ty::I64, Ty::I16, v);
        let v8 = fb.trunc(Ty::I64, Ty::I8, v);
        fb.store(Ty::I64, slot64, v);
        fb.store(Ty::I32, slot32, v32);
        fb.store(Ty::I16, slot16, v16);
        fb.store(Ty::I8, slot8, v8);
        let l64 = fb.load(Ty::I64, slot64);
        let l0 = fb.load(Ty::I64, p);
        let l32 = fb.load(Ty::I32, slot32);
        let l16 = fb.load(Ty::I16, slot16);
        let l8 = fb.load(Ty::I8, slot8);
        let w32 = fb.zext(Ty::I32, Ty::I64, l32);
        let w16 = fb.zext(Ty::I16, Ty::I64, l16);
        let w8 = fb.zext(Ty::I8, Ty::I64, l8);
        let s0 = fb.add(Ty::I64, l64, l0);
        let s1 = fb.add(Ty::I64, s0, w32);
        let s2 = fb.add(Ty::I64, s1, w16);
        let result = fb.add(Ty::I64, s2, w8);
        fb.ret(vec![result]);
        fb.build();
    }
    let mut module = mb.build().expect("ModuleBuilder::build: test fixture");
    // `ext_mix` is a bodyless external, an FFI boundary trust-ir's validator
    // admits only under a pinned target (`TargetInfoRequired`), and every
    // ingestion entry refuses what that validator refuses since WS7.3. The JIT
    // and the macOS object both compile for the host.
    pinned_target::pin(&mut module, pinned_target::host_triple());
    module
}

fn inputs() -> Vec<i64> {
    let mut values = vec![0, 1, -1, 0x7f, 0x80, 0xff, 0x1234_5678, i64::MAX, i64::MIN];
    let mut state = 0x2545_f491_4f6c_dd1du64;
    for _ in 0..24 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        values.push(state as i64);
    }
    values
}

fn host_mix(a: i64, b: i64) -> i64 {
    a.wrapping_mul(31).wrapping_add(b ^ 0x5a)
}

extern "C" fn ext_mix(a: i64, b: i64) -> i64 {
    host_mix(a, b)
}

/// The `__text` bytes of a 64-bit Mach-O object (a minimal reader: the
/// header's load commands, `LC_SEGMENT_64`, and its `__text` section).
fn macho_text(object: &[u8]) -> &[u8] {
    let u32_at = |at: usize| u32::from_le_bytes(object[at..at + 4].try_into().unwrap());
    let u64_at = |at: usize| u64::from_le_bytes(object[at..at + 8].try_into().unwrap());
    assert_eq!(u32_at(0), 0xfeed_facf, "not a 64-bit Mach-O object");
    let mut command = 32;
    for _ in 0..u32_at(16) {
        let (kind, size) = (u32_at(command), u32_at(command + 4) as usize);
        if kind == 0x19 {
            let sections = u32_at(command + 64) as usize;
            for index in 0..sections {
                let section = command + 72 + index * 80;
                if object[section..section + 16].starts_with(b"__text\0") {
                    let size = u64_at(section + 40) as usize;
                    let offset = u32_at(section + 48) as usize;
                    return &object[offset..offset + size];
                }
            }
        }
        command += size;
    }
    panic!("no __text section");
}

/// How many words of each admitted memory family `text` carries:
/// `(pre-index STP, post-index LDP, other pairs, scalar stores by width
/// 1/2/4/8, scalar loads)`, by the verifier's independent decoders.
fn memory_families(text: &[u8]) -> (usize, usize, usize, [usize; 4], usize) {
    use trust_cg_verify::aarch64_instruction_word_proofs::{DecodedWord, decode_word};
    use trust_cg_verify::aarch64_pair_memory_proofs::{PairMode, decode_pair_memory_word};
    let (mut pre, mut post, mut other) = (0, 0, 0);
    let (mut stores, mut loads) = ([0usize; 4], 0);
    for chunk in text.as_chunks::<4>().0 {
        let word = u32::from_le_bytes(*chunk);
        if let Some(pair) = decode_pair_memory_word(word) {
            match (pair.mode, pair.load) {
                (PairMode::PreIndex, false) => pre += 1,
                (PairMode::PostIndex, true) => post += 1,
                _ => other += 1,
            }
            continue;
        }
        let scalar = match decode_word(word) {
            Some(DecodedWord::LoadStoreUnsigned {
                size, v: 0, opc, ..
            })
            | Some(DecodedWord::LoadStoreUnscaled {
                size, v: 0, opc, ..
            }) => Some((size, opc)),
            _ => None,
        };
        match scalar {
            Some((size, 0)) => stores[size as usize] += 1,
            Some((_, 1)) => loads += 1,
            _ => {}
        }
    }
    (pre, post, other, stores, loads)
}

#[test]
fn native_frames_and_memory_compile_with_the_binding_enforced_and_match_the_host() {
    let module = native_module();
    for level in [OptLevel::O0, OptLevel::O2] {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = level;
        let jit = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(
                &module,
                &HashMap::from([(
                    "ext_mix".to_string(),
                    ext_mix as extern "C" fn(i64, i64) -> i64 as *const u8,
                )]),
            )
            .unwrap_or_else(|error| panic!("{level:?}: {error}"));
        let buffer = jit.buffer;
        let function = |name: &str| {
            buffer
                .get_fn_ptr_bound(name)
                .unwrap_or_else(|| panic!("{name} missing"))
                .as_ptr()
        };
        // SAFETY: each symbol is the function of the matching signature
        // compiled above, and the buffer outlives every call.
        let keep: extern "C" fn(i64, i64, i64, i64) -> i64 =
            unsafe { std::mem::transmute(function("keep_across_calls")) };
        let cells: extern "C" fn(*mut u64, i64) -> i64 =
            unsafe { std::mem::transmute(function("cells")) };
        for a in inputs() {
            for b in inputs().into_iter().take(6) {
                let (c, d) = (a.rotate_left(17), b.wrapping_mul(7));
                let first = host_mix(a, b);
                let second = host_mix(c, first);
                let expected = a
                    .wrapping_add(b)
                    .wrapping_add(c ^ d)
                    .wrapping_add(second.wrapping_sub(d));
                assert_eq!(keep(a, b, c, d), expected, "{level:?} keep({a}, {b})");
            }
            let mut memory = [0u64; 4];
            memory[0] = (a as u64).rotate_left(9);
            let got = cells(memory.as_mut_ptr(), a);
            let v = a as u64;
            // Little-endian byte view of the four words after the stores.
            let mut bytes = [0u8; 32];
            bytes[..8].copy_from_slice(&memory[0].to_le_bytes());
            bytes[8..16].copy_from_slice(&v.to_le_bytes());
            bytes[20..24].copy_from_slice(&(v as u32).to_le_bytes());
            bytes[26..28].copy_from_slice(&(v as u16).to_le_bytes());
            bytes[31] = v as u8;
            for (index, word) in memory.iter().enumerate() {
                let expected_word =
                    u64::from_le_bytes(bytes[index * 8..index * 8 + 8].try_into().unwrap());
                assert_eq!(*word, expected_word, "{level:?} cells({a}) word {index}");
            }
            let expected = v
                .wrapping_add(memory[0])
                .wrapping_add(u64::from(v as u32))
                .wrapping_add(u64::from(v as u16))
                .wrapping_add(u64::from(v as u8));
            assert_eq!(got as u64, expected, "{level:?} cells({a})");
        }
        // The same module as a Darwin object (ENC-5 enforcing): its text
        // carries the admitted families the battery exercised. At O0 every
        // cell is an immediate-offset access of its own width. At O2 the
        // selector keeps the constant indices of the 64- and 32-bit cells in
        // registers and uses register-offset stores and loads for them
        // (`str x1, [x0, x2, lsl #3]`, measured 2026-09-30 at `c84d39e93`),
        // which this decomposition does not admit, so only the byte and
        // halfword stores are required there.
        if cfg!(target_os = "macos") {
            let object = Compiler::new(CompilerConfig {
                target: Target::Aarch64,
                opt_level: level,
                ..CompilerConfig::default()
            })
            .with_codegen_license(permit_unlicensed())
            .compile(&module)
            .unwrap_or_else(|error| panic!("{level:?} object: {error}"))
            .object_code;
            if let Some(dir) = std::env::var_os("MEMORY_EFFECT_OBJECT_DIR") {
                std::fs::write(
                    std::path::Path::new(&dir).join(format!("{level:?}.o")),
                    &object,
                )
                .unwrap();
            }
            let (pre, post, other, stores, loads) = memory_families(macho_text(&object));
            assert!(
                pre >= 1 && post >= 1 && pre + post + other >= 4,
                "{level:?}: the frames save and restore pairs ({pre}, {post}, {other})"
            );
            let required_widths = if level == OptLevel::O0 { 0..4 } else { 0..2 };
            assert!(
                stores[required_widths].iter().all(|count| *count >= 1) && loads >= 2,
                "{level:?}: stores by width {stores:?}, loads {loads}"
            );
        }
    }
}

/// On the production (object, proof-required) route, a pointer-reading
/// function's LDR row is judged by its instruction-derived obligation and the
/// Formal-only bound-memory rule (owner ruling 2026-09-29). On a host whose
/// checker the bound-memory manifest qualifies, the row is credited `Formal`
/// by its form certificate and no refusal names it. Elsewhere it is the
/// fail-closed checker-identity miss, and its reason ends with the word-bound
/// memory-effect decomposition of its word: every part holds, and the clause
/// is recorded, never credit.
#[cfg(feature = "verify")]
#[test]
fn proof_required_compile_judges_the_load_row_and_records_its_memory_effect() {
    use trust_cg_verify::bound_memory_authority::{
        BOUND_MEMORY_FORMAL_ONLY, CHECKER_IDENTITY_MISS, bound_memory_checker_qualification,
    };
    use trust_cg_verify::function_verifier::{
        INSTRUCTION_DERIVED_IS_NOT_CREDIT, MEMORY_EFFECT_IS_NOT_CREDIT,
        REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT,
    };
    let mut mb = ModuleBuilder::new("memory_effect_fires");
    let read = mb.add_func_type(vec![Ty::Ptr], vec![Ty::I64]);
    let mut fb = mb.function("read_first", read);
    let entry = fb.create_block();
    let p = fb.add_block_param(entry, Ty::Ptr);
    fb.switch_to_block(entry);
    let value = fb.load(Ty::I64, p);
    fb.ret(vec![value]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let outcome = Compiler::new(CompilerConfig {
        target: Target::Aarch64,
        emit_proofs: true,
        ..CompilerConfig::default()
    })
    .with_codegen_license(permit_unlicensed())
    .compile(&module);
    let qualified = bound_memory_checker_qualification().is_ok();
    let reason = match outcome {
        Ok(_) if qualified => return,
        Ok(_) => panic!("an uncredited load row must not promote"),
        Err(trust_cg_codegen::compiler::CompileError::ProofPromotionRejected {
            reason, ..
        }) => reason,
        Err(other) => panic!("expected a proof-promotion refusal, got {other}"),
    };
    let reason = trust_cg_verify::ay_bridge::without_solver_refusal_note(&reason);
    if qualified {
        assert!(
            !reason.contains("AArch64::LdrRI"),
            "the load row is credited by its form certificate: {reason}"
        );
        return;
    }
    let (_, row) = reason
        .split_once(&format!(
            "is AArch64::LdrRI ({INSTRUCTION_DERIVED_IS_NOT_CREDIT}: `A64 instruction word LdrRI \
             0xf9400001` holds"
        ))
        .unwrap_or_else(|| panic!("the load row must be refused first: {reason}"));
    assert!(
        row.contains(BOUND_MEMORY_FORMAL_ONLY)
            && row.contains(CHECKER_IDENTITY_MISS)
            && row.contains(&format!(
                "; {MEMORY_EFFECT_IS_NOT_CREDIT}: `A64 memory effect LdrRI 0xf9400001` holds in \
                 process: all 3 parts exactly; 0 of 3 parts have a Clean-checked certificate"
            )),
        "{reason}"
    );
    assert!(
        !reason.contains(REGISTRY_NAME_LOOKUP_IS_NOT_CREDIT),
        "{reason}"
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes (or is refused) because the license silently refused it.
fn permit_unlicensed() -> trust_cg_codegen::CodegenLicensePolicy {
    trust_cg_codegen::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_codegen::UnlicensedBodyPolicy::Permit)
}
