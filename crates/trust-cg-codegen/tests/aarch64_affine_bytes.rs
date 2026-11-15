// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig, encode_function_with_fixups};
use trust_cg_lower::Function as LirFunction;
use trust_cg_verify::aarch64_affine_lowering::{
    AffineByteError, TrustIrAffineLoweringError, check_aarch64_trust_ir_affine_bytes,
};
use trust_ir::{BinOp, Inst, Module, Ty};
use trust_ir_build::ModuleBuilder;

fn add_source(ty: Ty) -> (Module, LirFunction) {
    binary_source(ty, false)
}

fn binary_source(ty: Ty, subtract: bool) -> (Module, LirFunction) {
    let mut mb = ModuleBuilder::new("affine_bytes");
    let signature = mb.add_func_type(vec![ty.clone(), ty.clone()], vec![ty.clone()]);
    let mut fb = mb.function(if subtract { "sub" } else { "add" }, signature);
    let entry = fb.create_block();
    let a = fb.add_block_param(entry, ty.clone());
    let b = fb.add_block_param(entry, ty.clone());
    fb.switch_to_block(entry);
    let result = if subtract {
        fb.sub(ty, a, b)
    } else {
        fb.add(ty, a, b)
    };
    fb.ret(vec![result]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
    (module, lir)
}

fn compile(lir: &LirFunction, opt_level: OptLevel) -> Vec<u8> {
    let pipeline = Pipeline::new(PipelineConfig {
        opt_level,
        target_triple: "aarch64-unknown-linux-gnu".to_owned(),
        verify: false,
        ..Default::default()
    });
    let machine = pipeline.prepare_function(lir).unwrap();
    let (bytes, fixups) = encode_function_with_fixups(&machine).unwrap();
    assert!(
        fixups.is_empty(),
        "affine leaf cannot require pending fixups"
    );
    bytes
}

fn replace_word(bytes: &mut [u8], index: usize, instruction: u32) {
    bytes[index * 4..index * 4 + 4].copy_from_slice(&instruction.to_le_bytes());
}

fn words(words: &[u32]) -> Vec<u8> {
    words.iter().flat_map(|word| word.to_le_bytes()).collect()
}

fn select_source(ty: Ty, op: trust_ir::ICmpOp) -> (Module, LirFunction) {
    let mut mb = ModuleBuilder::new("integer_select_bytes");
    let signature = mb.add_func_type(vec![ty.clone(); 4], vec![ty.clone()]);
    let mut fb = mb.function("choose", signature);
    let entry = fb.create_block();
    let args: Vec<_> = (0..4)
        .map(|_| fb.add_block_param(entry, ty.clone()))
        .collect();
    fb.switch_to_block(entry);
    let cond = fb.icmp(op, ty.clone(), args[0], args[1]);
    let result = fb.select(ty, cond, args[2], args[3]);
    fb.ret(vec![result]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
    (module, lir)
}

#[test]
fn source_bound_integer_selects_match_actual_linux_bytes_all_conditions_and_levels() {
    use trust_ir::ICmpOp::*;
    for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
        for op in [Eq, Ne, Slt, Sle, Sgt, Sge, Ult, Ule, Ugt, Uge] {
            let (module, lir) = select_source(ty.clone(), op);
            for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let bytes = compile(&lir, level);
                check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes).unwrap_or_else(
                    |error| panic!("{ty:?}/{op:?}/{level:?}: {error}; bytes={bytes:02x?}"),
                );
            }
        }
    }
}

#[test]
fn source_bound_integer_select_bytes_reject_changed_data_flags_width_and_condition() {
    for ty in [Ty::I32, Ty::I64] {
        let (module, lir) = select_source(ty, trust_ir::ICmpOp::Slt);
        let original = compile(&lir, OptLevel::O2);
        let index = original
            .as_chunks::<4>()
            .0
            .iter()
            .position(|bytes| {
                let word = u32::from_le_bytes(*bytes);
                word & 0x7fe00c00 == 0x1a800000
            })
            .unwrap();
        let old = u32::from_le_bytes(original[index * 4..index * 4 + 4].try_into().unwrap());
        for bit in [0, 5, 10, 11, 12, 13, 16, 21, 29, 30, 31] {
            let mut changed = original.clone();
            replace_word(&mut changed, index, old ^ (1 << bit));
            assert!(
                check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &changed).is_err(),
                "accepted select bit mutation {bit}"
            );
        }
        // Replace the actual flags producer with a flag-preserving NOP.
        let cmp = original
            .as_chunks::<4>()
            .0
            .iter()
            .position(|bytes| {
                let word = u32::from_le_bytes(*bytes);
                word & 0x7f20001f == 0x6b00001f
            })
            .unwrap();
        let mut changed = original.clone();
        replace_word(&mut changed, cmp, 0xd503201f);
        assert!(check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &changed).is_err());
    }
}

#[test]
fn source_bound_select_variants_bind_increment_inversion_and_negation_to_false_arm() {
    for (ty, sf) in [(Ty::I32, 0), (Ty::I64, 1 << 31)] {
        for (variant, opcode) in [
            (0, 0x1a800000),
            (1, 0x1a800400),
            (2, 0x5a800000),
            (3, 0x5a800400),
        ] {
            let mut mb = ModuleBuilder::new("select_variant");
            let signature = mb.add_func_type(vec![ty.clone(); 4], vec![ty.clone()]);
            let mut fb = mb.function("select_variant", signature);
            let entry = fb.create_block();
            let args: Vec<_> = (0..4)
                .map(|_| fb.add_block_param(entry, ty.clone()))
                .collect();
            fb.switch_to_block(entry);
            let cond = fb.icmp(trust_ir::ICmpOp::Slt, ty.clone(), args[0], args[1]);
            let constant = fb.iconst(
                ty.clone(),
                match variant {
                    1 => 1,
                    2 => -1,
                    _ => 0,
                },
            );
            let otherwise = match variant {
                0 => args[3],
                1 => fb.add(ty.clone(), args[3], constant),
                _ => fb.sub(ty.clone(), constant, args[3]),
            };
            let result = fb.select(ty.clone(), cond, args[2], otherwise);
            fb.ret(vec![result]);
            fb.build();
            let module = mb.build().expect("ModuleBuilder::build: test fixture");
            let (lir, _) = trust_cg_lower::translate_function_with_license(
                &module.functions[0],
                &module,
                &permit_unlicensed(),
            )
            .unwrap();
            // Independent ISA words: CMP r0,r1; CS* r0,r2,r3,LT; RET.
            let select = sf | opcode | (3 << 16) | (11 << 12) | (2 << 5);
            let bytes = words(&[sf | 0x6b01001f, select, 0xd65f03c0]);
            check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes).unwrap();
            for bit in [10, 12, 30] {
                let wrong = words(&[sf | 0x6b01001f, select ^ (1 << bit), 0xd65f03c0]);
                assert!(
                    check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &wrong).is_err(),
                    "variant {variant}, mutation {bit}"
                );
            }
        }
    }
}

#[cfg(all(target_arch = "aarch64", any(target_os = "linux", target_os = "macos")))]
#[path = "common/native_host.rs"]
mod native_host;

/// Link the exact checked byte streams with the host C toolchain and execute
/// them through width-correct C ABI declarations. The C oracle independently
/// uses integer comparisons and both distinct result payloads. This is native
/// differential evidence, with no JIT verification or publication claim.
#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "linux", target_os = "macos")))]
fn source_bound_integer_selects_execute_checked_bytes_against_c_oracle() {
    use std::fmt::Write;
    use std::process::Command;
    use trust_ir::ICmpOp::*;
    let temp = tempfile::tempdir().unwrap();
    let mut asm = String::from(".text\n");
    let mut declarations = String::new();
    let mut calls = String::new();
    let mut functions = 0;
    for (ty, bits) in [(Ty::I32, 32), (Ty::U32, 32), (Ty::I64, 64), (Ty::U64, 64)] {
        for (condition, op) in [Eq, Ne, Slt, Sle, Sgt, Sge, Ult, Ule, Ugt, Uge]
            .into_iter()
            .enumerate()
        {
            let (module, lir) = select_source(ty.clone(), op);
            for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let bytes = compile(&lir, level);
                check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes).unwrap();
                let name = format!("select_{functions}");
                writeln!(
                    asm,
                    ".balign 4\n.global {name}\n.type {name}, %function\n{name}:"
                )
                .unwrap();
                for bytes in bytes.as_chunks::<4>().0 {
                    writeln!(asm, ".word 0x{:08x}", u32::from_le_bytes(*bytes)).unwrap();
                }
                writeln!(asm, ".size {name}, .-{name}").unwrap();
                writeln!(declarations, "extern uint{bits}_t {name}(uint{bits}_t,uint{bits}_t,uint{bits}_t,uint{bits}_t);").unwrap();
                writeln!(
                    calls,
                    "if (test{bits}({name}, {condition}, {functions})) return 1;"
                )
                .unwrap();
                functions += 1;
            }
        }
    }
    asm.push_str(".section .note.GNU-stack,\"\",%progbits\n");
    let c = format!(
        r#"#include <stdint.h>
#include <stdio.h>
{declarations}
static unsigned checks;
#define TEST(W) \
static int test##W(uint##W##_t (*fn)(uint##W##_t,uint##W##_t,uint##W##_t,uint##W##_t), int cc, int id) {{ \
    const uint##W##_t sign = (uint##W##_t)1 << (W-1), max = (uint##W##_t)-1; \
    const uint##W##_t values[] = {{0,1,2,sign-1,sign,sign+1,max-1,max}}; \
    const uint##W##_t payloads[][2] = {{{{0,max}},{{sign,sign-1}},{{max-1,2}}}}; \
    for (unsigned i=0;i<8;i++) for(unsigned j=0;j<8;j++) for(unsigned k=0;k<3;k++) {{ \
        const uint##W##_t a=values[i], b=values[j], t=payloads[k][0], f=payloads[k][1]; \
        const int##W##_t sa=(int##W##_t)a, sb=(int##W##_t)b; \
        int take; \
        switch(cc) {{case 0:take=a==b;break;case 1:take=a!=b;break; \
        case 2:take=sa<sb;break;case 3:take=sa<=sb;break;case 4:take=sa>sb;break;case 5:take=sa>=sb;break; \
        case 6:take=a<b;break;case 7:take=a<=b;break;case 8:take=a>b;break;default:take=a>=b;}} \
        if (fn(a,b,t,f)!=(take?t:f)) {{fprintf(stderr,"select %d case %u/%u/%u failed\n",id,i,j,k);return 1;}} \
        checks++; \
    }} return 0; \
}}
TEST(32)
TEST(64)
int main(void) {{
{calls}
printf("INTEGER_SELECT_NATIVE functions={functions} checks=%u\n", checks);
return checks == 30720 ? 0 : 2;
}}
"#
    );
    let assembly = temp.path().join("selects.s");
    let oracle = temp.path().join("oracle.c");
    let executable = temp.path().join("oracle");
    // The checked streams are the Linux-triple leaf bytes above; they carry no
    // fixups, so the same words execute under either host's C caller.
    std::fs::write(&assembly, native_host::assembly(&asm)).unwrap();
    std::fs::write(&oracle, &c).unwrap();
    let built = Command::new("cc")
        .args(["-O2", "-std=c11", "-Wall", "-Wextra", "-Werror"])
        .arg(&assembly)
        .arg(&oracle)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    assert!(
        built.status.success(),
        "C build failed: {}",
        String::from_utf8_lossy(&built.stderr)
    );
    let ran = Command::new(&executable).output().unwrap();
    assert!(
        ran.status.success(),
        "native oracle failed: {}",
        String::from_utf8_lossy(&ran.stderr)
    );
    let output = String::from_utf8(ran.stdout).unwrap();
    use sha2::{Digest, Sha256};
    println!(
        "INTEGER_SELECT_NATIVE_INPUTS {}",
        serde_json::json!({
            "assembly": asm, "oracle": c,
            "executable_sha256": format!("{:x}", Sha256::digest(std::fs::read(&executable).unwrap())),
        })
    );
    assert_eq!(functions, 160);
    assert!(
        output.contains("INTEGER_SELECT_NATIVE functions=160 checks=30720"),
        "{output}"
    );
    print!("{output}");
}

#[test]
fn exact_source_matches_actual_linux_final_bytes_at_all_optimization_levels() {
    for ty in [Ty::I32, Ty::U32, Ty::I64, Ty::U64] {
        for subtract in [false, true] {
            let (module, lir) = binary_source(ty.clone(), subtract);
            for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                let bytes = compile(&lir, opt_level);
                let checked =
                    check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes).unwrap();
                assert!(std::ptr::eq(checked.module(), &module));
                assert!(std::ptr::eq(checked.source(), &module.functions[0]));
                assert!(std::ptr::eq(checked.lir(), &lir));
                assert!(std::ptr::eq(checked.code(), bytes.as_slice()));
                assert_eq!(checked.statistics().private_stack_bytes, 16);
                assert_eq!(checked.statistics().machine_instructions, bytes.len() / 4);
            }
        }
    }
}

#[test]
fn real_constant_materialization_parameter_counts_and_void_returns() {
    for (ty, constant) in [
        (Ty::I32, i32::MIN as i128),
        (Ty::U32, u32::MAX as i128),
        (Ty::I64, i64::MIN as i128),
        (Ty::U64, 0xfade123456789abc_u64 as i128),
    ] {
        for parameter_count in 0..=8 {
            for returns_value in [true, false] {
                let mut mb = ModuleBuilder::new("byte_parameters");
                let signature = mb.add_func_type(
                    vec![ty.clone(); parameter_count],
                    if returns_value {
                        vec![ty.clone()]
                    } else {
                        vec![]
                    },
                );
                let mut fb = mb.function("sum", signature);
                let entry = fb.create_block();
                let parameters: Vec<_> = (0..parameter_count)
                    .map(|_| fb.add_block_param(entry, ty.clone()))
                    .collect();
                fb.switch_to_block(entry);
                let mut result = fb.iconst(ty.clone(), constant);
                for parameter in parameters {
                    result = fb.add(ty.clone(), result, parameter);
                }
                fb.ret(if returns_value { vec![result] } else { vec![] });
                fb.build();
                let module = mb.build().expect("ModuleBuilder::build: test fixture");
                let (lir, _) = trust_cg_lower::translate_function_with_license(
                    &module.functions[0],
                    &module,
                    &permit_unlicensed(),
                )
                .unwrap();
                for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                    let bytes = compile(&lir, level);
                    check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes)
                    .unwrap_or_else(|error| panic!("{ty:?}/{parameter_count}/{returns_value}/{level:?}: {error}; bytes={bytes:02x?}"));
                }
            }
        }
    }
}

#[test]
fn actual_final_bytes_reject_operand_opcode_width_and_return_mutations() {
    let (module, lir) = add_source(Ty::I64);
    let original = compile(&lir, OptLevel::O2);
    let add = original
        .as_chunks::<4>()
        .0
        .iter()
        .position(|word| u32::from_le_bytes(*word) == 0x8b010000)
        .unwrap();
    for mutated in [0xcb010000, 0x8b000000, 0x8b010001, 0x0b010000, 0x8b020000] {
        let mut bytes = original.clone();
        replace_word(&mut bytes, add, mutated);
        assert!(
            check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes).is_err(),
            "accepted {mutated:08x}"
        );
    }
    let mut wrong_return = original.clone();
    let last = wrong_return.len() / 4 - 1;
    replace_word(&mut wrong_return, last, 0xd65f0000); // RET X0
    assert!(check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &wrong_return).is_err());
    for length in [0, 1, original.len() - 1, original.len() - 4] {
        assert!(
            check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &original[..length]).is_err()
        );
    }
    let mut trailing = original.clone();
    trailing.extend_from_slice(&0xd503201f_u32.to_le_bytes());
    assert!(check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &trailing).is_err());
}

#[test]
fn final_byte_receipt_rechecks_changed_source_and_exact_module_ordinal() {
    let (mut module, lir) = add_source(Ty::I64);
    let bytes = compile(&lir, OptLevel::O2);
    assert!(check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes).is_ok());
    if let Inst::BinOp { op, .. } = &mut module.functions[0].blocks[0].body[0].inst {
        *op = BinOp::Sub;
    }
    assert!(matches!(
        check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes),
        Err(AffineByteError::Source(
            TrustIrAffineLoweringError::TrustIrLirMismatch
        ))
    ));
    assert!(matches!(
        check_aarch64_trust_ir_affine_bytes(&module, 1, &lir, &bytes),
        Err(AffineByteError::Source(
            TrustIrAffineLoweringError::InvalidTrustIr(_)
        ))
    ));
    module.functions[0].name.push_str("_wrong");
    assert!(matches!(
        check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes),
        Err(AffineByteError::Source(
            TrustIrAffineLoweringError::TrustIrLirMismatch
        ))
    ));
}

#[test]
fn frame_memory_control_and_reserved_register_mutations_cannot_hide_as_glue() {
    let (module, lir) = add_source(Ty::I64);
    let original = compile(&lir, OptLevel::O2);
    // Modified frame allocation, setup, restore offset and restored registers.
    for (index, instruction) in [
        (0, 0xa9be7bfd),
        (1, 0x910043fd),
        (3, 0xa8c27bfd),
        (3, 0xa8c17bfc),
    ] {
        let mut bytes = original.clone();
        replace_word(&mut bytes, index, instruction);
        assert!(check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes).is_err());
    }
    // Original source retained. Each inserted word is visited even though
    // arithmetic and returned bits would otherwise be unchanged.
    for instruction in [
        0xf90003e0_u32,
        0x94000000,
        0x14000000,
        0xd4200000,
        0xaa0003f2,
        0xaa0003f3,
        0xaa0003fe,
        0x910003e0,
        0x9100001f,
    ] {
        let mut bytes = original.clone();
        bytes.splice(8..8, instruction.to_le_bytes());
        assert!(
            check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes).is_err(),
            "accepted {instruction:08x}"
        );
    }
}

#[test]
fn unsupported_target_is_never_an_unsupported_source_downgrade() {
    let (module, lir) = add_source(Ty::I64);
    // MUL X0,X0,X1; RET X30. The admitted Add source must remain admitted.
    let bytes = words(&[0x9b017c00, 0xd65f03c0]);
    assert!(matches!(
        check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes),
        Err(AffineByteError::UnsupportedBytes { offset: 0, .. })
    ));
}

#[test]
fn each_changed_bit_of_live_add_and_fixed_frame_is_rechecked() {
    let (module, lir) = add_source(Ty::I64);
    let original = compile(&lir, OptLevel::O2);
    for index in 0..original.len() / 4 {
        let instruction =
            u32::from_le_bytes(original[index * 4..index * 4 + 4].try_into().unwrap());
        for bit in 0..32 {
            let mut changed = original.clone();
            replace_word(&mut changed, index, instruction ^ (1 << bit));
            assert!(
                check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &changed).is_err(),
                "accepted changed bit {bit} at word {index}"
            );
        }
    }
}

#[test]
fn independent_assembler_controls_cover_shifts_and_immediate_boundaries() {
    // GNU AArch64 assembler controls, independently assembled from this text:
    // mov r9,r0; add r9,r9,#4095,lsl#12; sub r9,r9,#4095;
    // add r0,r9,r0,lsl#2; ret. Source computes 5*x + 0xfff000 - 4095.
    for (ty, instructions) in [
        (
            Ty::I32,
            [0x2a0003e9, 0x117ffd29, 0x513ffd29, 0x0b000920, 0xd65f03c0],
        ),
        (
            Ty::I64,
            [0xaa0003e9, 0x917ffd29, 0xd13ffd29, 0x8b000920, 0xd65f03c0],
        ),
    ] {
        let mut mb = ModuleBuilder::new("assembler_control");
        let signature = mb.add_func_type(vec![ty.clone()], vec![ty.clone()]);
        let mut fb = mb.function("affine", signature);
        let entry = fb.create_block();
        let x = fb.add_block_param(entry, ty.clone());
        fb.switch_to_block(entry);
        let twice = fb.add(ty.clone(), x, x);
        let four = fb.add(ty.clone(), twice, twice);
        let five = fb.add(ty.clone(), four, x);
        let large = fb.iconst(ty.clone(), 0xfff000);
        let small = fb.iconst(ty.clone(), 4095);
        let biased = fb.add(ty.clone(), five, large);
        let result = fb.sub(ty.clone(), biased, small);
        fb.ret(vec![result]);
        fb.build();
        let module = mb.build().expect("ModuleBuilder::build: test fixture");
        let (lir, _) = trust_cg_lower::translate_function_with_license(
            &module.functions[0],
            &module,
            &permit_unlicensed(),
        )
        .unwrap();
        let code = words(&instructions);
        assert_eq!(
            check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &code)
                .unwrap()
                .statistics()
                .private_stack_bytes,
            0
        );
        let mut changed = code.clone();
        replace_word(&mut changed, 1, instructions[1] ^ (1 << 22));
        assert!(matches!(
            check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &changed),
            Err(AffineByteError::ReturnMismatch)
        ));
        replace_word(&mut changed, 1, instructions[1]);
        replace_word(&mut changed, 3, instructions[3] ^ (1 << 10));
        assert!(matches!(
            check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &changed),
            Err(AffineByteError::ReturnMismatch)
        ));
    }
}

#[test]
fn move_wide_preserves_untouched_halfwords_and_rejects_reserved_encodings() {
    let mut mb = ModuleBuilder::new("move_wide_control");
    let signature = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("constant", signature);
    let entry = fb.create_block();
    fb.switch_to_block(entry);
    let result = fb.iconst(Ty::U64, 0xffffffff12340000_u64 as i128);
    fb.ret(vec![result]);
    fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &permit_unlicensed(),
    )
    .unwrap();
    // Independently assembled MOVN X0,#65535; MOVK X0,#0x1234,LSL#16; RET.
    let bytes = words(&[0x929fffe0, 0xf2a24680, 0xd65f03c0]);
    assert!(check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &bytes).is_ok());
    for (index, instruction) in [
        (0, 0xd29fffe0),
        (1, 0xf2a246a0),
        (1, 0xf2c24680),
        (1, 0x72a24680),
    ] {
        let mut changed = bytes.clone();
        replace_word(&mut changed, index, instruction);
        assert!(check_aarch64_trust_ir_affine_bytes(&module, 0, &lir, &changed).is_err());
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
