//! Public encoder controls for the integer-width field of scalar FP conversions.
use trust_cg_codegen::aarch64::encode::encode_instruction;
use trust_cg_ir::regs::{
    B0, D0, D1, H0, H1, S0, S1, SP, SpecialReg, V0, V1, W0, W1, WSP, WZR, X0, X1, XZR,
};
use trust_cg_ir::{AArch64Opcode as Op, MachInst, MachOperand as Operand, RegClass, VReg};

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
mod common;

fn check(opcode: Op, to_fp: bool, base: u32) {
    // Base words name Rd=0/Rn=1, integer W and floating S. Only sf and
    // ftype change in this matrix; these constants are also checked against
    // the platform assembler in the native-host control below.
    for (sf, gpr) in [
        (0, if to_fp { W1 } else { W0 }),
        (1, if to_fp { X1 } else { X0 }),
    ] {
        for (ftype, fpr) in [
            (0, if to_fp { S0 } else { S1 }),
            (1, if to_fp { D0 } else { D1 }),
            (3, if to_fp { H0 } else { H1 }),
        ] {
            let operands = if to_fp {
                vec![Operand::PReg(fpr), Operand::PReg(gpr)]
            } else {
                vec![Operand::PReg(gpr), Operand::PReg(fpr)]
            };
            let inst = MachInst::new(opcode, operands);
            assert_eq!(
                encode_instruction(&inst).unwrap(),
                base | (sf << 31) | (ftype << 22),
                "{inst:?}"
            );
        }
    }
}

#[test]
fn signed_integer_to_fp_uses_source_width() {
    check(Op::ScvtfRR, true, 0x1e22_0020);
}
#[test]
fn unsigned_integer_to_fp_uses_source_width() {
    check(Op::UcvtfRR, true, 0x1e23_0020);
}
#[test]
fn fp_to_signed_integer_uses_destination_width() {
    check(Op::FcvtzsRR, false, 0x1e38_0020);
}
#[test]
fn fp_to_unsigned_integer_uses_destination_width() {
    check(Op::FcvtzuRR, false, 0x1e39_0020);
}

#[test]
fn conversion_rejects_wrong_register_files_stack_pointer_and_arity() {
    for (opcode, to_fp) in [
        (Op::ScvtfRR, true),
        (Op::UcvtfRR, true),
        (Op::FcvtzsRR, false),
        (Op::FcvtzuRR, false),
    ] {
        for bad in [
            Operand::PReg(SP),
            Operand::PReg(WSP),
            Operand::Special(SpecialReg::SP),
            Operand::PReg(V0),
            Operand::Imm(0),
            Operand::VReg(VReg::new(0, RegClass::Gpr64)),
        ] {
            let operands = if to_fp {
                vec![Operand::PReg(S0), bad]
            } else {
                vec![bad, Operand::PReg(S1)]
            };
            let inst = MachInst::new(opcode, operands);
            assert!(encode_instruction(&inst).is_err(), "{inst:?}");
        }
        for bad in [
            Operand::PReg(X0),
            Operand::PReg(B0),
            Operand::Imm(0),
            Operand::VReg(VReg::new(1, RegClass::Fpr32)),
        ] {
            let operands = if to_fp {
                vec![bad, Operand::PReg(W1)]
            } else {
                vec![Operand::PReg(W0), bad]
            };
            assert!(encode_instruction(&MachInst::new(opcode, operands)).is_err());
        }
        let valid = if to_fp {
            vec![Operand::PReg(S0), Operand::PReg(W1)]
        } else {
            vec![Operand::PReg(W0), Operand::PReg(S1)]
        };
        for operands in [
            vec![],
            valid[..1].to_vec(),
            [valid.clone(), vec![Operand::Imm(0)]].concat(),
        ] {
            assert!(encode_instruction(&MachInst::new(opcode, operands)).is_err());
        }
    }
}

#[test]
fn conversion_zero_registers_and_legacy_scalar_v_spellings_remain_supported() {
    for (op, base, to_fp) in [
        (Op::ScvtfRR, 0x1e22_0000, true),
        (Op::UcvtfRR, 0x1e23_0000, true),
        (Op::FcvtzsRR, 0x1e38_0000, false),
        (Op::FcvtzuRR, 0x1e39_0000, false),
    ] {
        for (sf, zeros) in [
            (0, [Operand::PReg(WZR), Operand::Special(SpecialReg::WZR)]),
            (1, [Operand::PReg(XZR), Operand::Special(SpecialReg::XZR)]),
        ] {
            for zero in zeros {
                let (operands, fields) = if to_fp {
                    (vec![Operand::PReg(S0), zero], 31 << 5)
                } else {
                    (vec![zero, Operand::PReg(S1)], (1 << 5) | 31)
                };
                assert_eq!(
                    encode_instruction(&MachInst::new(op, operands)).unwrap(),
                    base | (sf << 31) | fields
                );
            }
        }
        let operands = if to_fp {
            vec![Operand::PReg(V0), Operand::PReg(X1)]
        } else {
            vec![Operand::PReg(X0), Operand::PReg(V1)]
        };
        assert_eq!(
            encode_instruction(&MachInst::new(op, operands)).unwrap(),
            base | (1 << 31) | (1 << 22) | (1 << 5)
        );
    }
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
mod native_assembler {
    use super::*;
    use std::process::Command;
    use std::time::Duration;
    use trust_cg_codegen::macho::linker::MachOParser;

    #[test]
    fn all_conversion_width_words_match_platform_assembler() {
        let mut source = String::from(".text\n");
        let mut expected = Vec::new();
        for (opcode, mnemonic, to_fp) in [
            (Op::ScvtfRR, "scvtf", true),
            (Op::UcvtfRR, "ucvtf", true),
            (Op::FcvtzsRR, "fcvtzs", false),
            (Op::FcvtzuRR, "fcvtzu", false),
        ] {
            for (gp_name, gp_dest, gp_src) in [("w", W0, W1), ("x", X0, X1)] {
                for (fp_name, fp_dest, fp_src) in [("s", S0, S1), ("d", D0, D1), ("h", H0, H1)] {
                    let (dest, src, operands) = if to_fp {
                        (
                            format!("{fp_name}0"),
                            format!("{gp_name}1"),
                            vec![Operand::PReg(fp_dest), Operand::PReg(gp_src)],
                        )
                    } else {
                        (
                            format!("{gp_name}0"),
                            format!("{fp_name}1"),
                            vec![Operand::PReg(gp_dest), Operand::PReg(fp_src)],
                        )
                    };
                    source.push_str(&format!("{mnemonic} {dest}, {src}\n"));
                    expected.extend(
                        encode_instruction(&MachInst::new(opcode, operands))
                            .unwrap()
                            .to_le_bytes(),
                    );
                }
            }
        }
        assert_eq!(expected.len(), 24 * 4);
        let dir = tempfile::Builder::new()
            .prefix("trust-cg-fp-width-")
            .tempdir()
            .unwrap();
        let input = dir.path().join("widths.s");
        let output = dir.path().join("widths.o");
        std::fs::write(&input, source).unwrap();
        let mut command = Command::new("/usr/bin/clang");
        command
            .args(["-c", "-march=armv8.2-a+fp16"])
            .arg(&input)
            .arg("-o")
            .arg(&output);
        let result =
            common::rosetta::command_output_with_timeout(&mut command, Duration::from_secs(30))
                .unwrap();
        assert!(
            !result.timed_out && result.output.status.success(),
            "{:?}",
            result.output
        );
        let object = MachOParser::parse(&std::fs::read(output).unwrap()).unwrap();
        let text = object
            .sections
            .iter()
            .find(|section| section.name == "__text")
            .unwrap();
        assert_eq!(text.data, expected);
    }
}

#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
#[path = "common/native_host.rs"]
mod native_host;

/// Native full-pipeline controls supplement the direct encoder matrix above.
/// These are defined-range raw casts, not saturating casts or formal evidence.
#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
mod native_pipeline {
    // `common/rosetta.rs` is already loaded once via `mod common;` — alias it
    // here instead of compiling the file into this target a second time.
    use super::common::rosetta as native_process;
    use super::native_host;
    use std::{fmt::Write, fs, process::Command};
    use trust_cg_codegen::{Compiler, CompilerConfig, pipeline::OptLevel, target::TargetSpec};
    use trust_ir::{
        Block, BlockId, CastOp, FuncId, FuncTy, Function, Inst, InstrNode, Module, Ty, ValueId,
    };

    struct Case {
        name: &'static str,
        source: Ty,
        destination: Ty,
        c_source: &'static str,
        c_destination: &'static str,
        signed: bool,
        bits: u32,
        inputs: &'static str,
    }

    fn cases() -> Vec<Case> {
        // Hexadecimal endpoints are exactly representable in the named input
        // format. In particular, no f32 constant rounds to +2^31/+2^63/+2^64
        // before an otherwise-undefined C conversion. The independent driver
        // also validates every input's domain *before* calling either backend.
        vec![
            Case {
                name: "cg_f32_i32",
                source: Ty::F32,
                destination: Ty::I32,
                c_source: "float",
                c_destination: "int32_t",
                signed: true,
                bits: 32,
                inputs: "0.0f,-0.0f,0.75f,-0.75f,1.75f,-1.75f,127.75f,-128.75f,32767.5f,-32768.5f,16777215.0f,16777216.0f,0x1.fffffep30f,-0x1p31f,-0x1.fffffep30f,42.875f",
            },
            Case {
                name: "cg_f64_i32",
                source: Ty::F64,
                destination: Ty::I32,
                c_source: "double",
                c_destination: "int32_t",
                signed: true,
                bits: 32,
                inputs: "0.0,-0.0,0.75,-0.75,1.75,-1.75,127.75,-128.75,32767.5,-32768.5,16777217.0,2147483646.75,2147483647.0,-2147483648.0,-2147483647.75,42.875",
            },
            Case {
                name: "cg_f32_u32",
                source: Ty::F32,
                destination: Ty::U32,
                c_source: "float",
                c_destination: "uint32_t",
                signed: false,
                bits: 32,
                inputs: "0.0f,-0.0f,0.75f,1.75f,127.75f,128.75f,255.75f,32767.5f,32768.5f,65535.5f,16777215.0f,16777216.0f,0x1p31f,0x1.000002p31f,0x1.fffffep31f,42.875f",
            },
            Case {
                name: "cg_f64_u32",
                source: Ty::F64,
                destination: Ty::U32,
                c_source: "double",
                c_destination: "uint32_t",
                signed: false,
                bits: 32,
                inputs: "0.0,-0.0,0.75,1.75,127.75,128.75,255.75,32767.5,65535.5,16777217.0,2147483647.75,2147483648.0,2147483648.75,4294967294.75,4294967295.0,42.875",
            },
            Case {
                name: "cg_f32_i64",
                source: Ty::F32,
                destination: Ty::I64,
                c_source: "float",
                c_destination: "int64_t",
                signed: true,
                bits: 64,
                inputs: "0.0f,-0.0f,0.75f,-0.75f,1.75f,-1.75f,0x1p31f,-0x1p31f,0x1.000002p31f,-0x1.000002p31f,0x1p32f,-0x1p32f,0x1.fffffep62f,-0x1p63f,-0x1.fffffep62f,42.875f",
            },
            Case {
                name: "cg_f64_i64",
                source: Ty::F64,
                destination: Ty::I64,
                c_source: "double",
                c_destination: "int64_t",
                signed: true,
                bits: 64,
                inputs: "0.0,-0.0,0.75,-0.75,1.75,-1.75,2147483647.75,-2147483648.75,2147483648.75,-2147483649.75,4294967295.75,-4294967296.75,0x1.fffffffffffffp62,-0x1p63,-0x1.fffffffffffffp62,42.875",
            },
            Case {
                name: "cg_f32_u64",
                source: Ty::F32,
                destination: Ty::U64,
                c_source: "float",
                c_destination: "uint64_t",
                signed: false,
                bits: 64,
                inputs: "0.0f,-0.0f,0.75f,1.75f,127.75f,65535.5f,0x1p31f,0x1.fffffep31f,0x1p32f,0x1.000002p32f,0x1.fffffep62f,0x1p63f,0x1.000002p63f,0x1.8p63f,0x1.fffffep63f,42.875f",
            },
            Case {
                name: "cg_f64_u64",
                source: Ty::F64,
                destination: Ty::U64,
                c_source: "double",
                c_destination: "uint64_t",
                signed: false,
                bits: 64,
                inputs: "0.0,-0.0,0.75,1.75,127.75,65535.5,2147483647.75,2147483648.75,4294967295.75,4294967296.75,0x1.fffffffffffffp62,0x1p63,0x1.0000000000001p63,0x1.8p63,0x1.fffffffffffffp63,42.875",
            },
        ]
    }

    fn module(cases: &[Case]) -> Module {
        let mut module = Module::new("scalar_fp_to_integer_widths");
        module.target_info = Some(trust_ir::TargetInfo {
            triple: native_host::TRIPLE.into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        });
        for (index, case) in cases.iter().enumerate() {
            let signature = module
                .add_func_type(FuncTy {
                    params: vec![case.source.clone()],
                    returns: vec![case.destination.clone()],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut function = Function::new(
                FuncId::new(index as u32),
                case.name,
                signature,
                BlockId::new(0),
            );
            function.blocks = vec![Block {
                id: BlockId::new(0),
                params: vec![(ValueId::new(0), case.source.clone())],
                body: vec![
                    InstrNode::new(Inst::Cast {
                        op: if case.signed {
                            CastOp::FPToSI
                        } else {
                            CastOp::FPToUI
                        },
                        src_ty: case.source.clone(),
                        dst_ty: case.destination.clone(),
                        operand: ValueId::new(0),
                    })
                    .with_result(ValueId::new(1)),
                    InstrNode::new(Inst::Return {
                        values: vec![ValueId::new(1)],
                    }),
                ],
            }];
            module
                .try_add_function(function)
                .expect("Module::try_add_function: test fixture");
        }
        module
    }

    fn driver(cases: &[Case]) -> String {
        let mut source = String::from(
            "#include <stdint.h>\n#include <stdio.h>\n#include <string.h>\n#include <math.h>\n",
        );
        for case in cases {
            writeln!(source,
                "extern {dst} {name}({src});\n__attribute__((noinline)) static {dst} reference_{name}({src} value) {{ return ({dst})value; }}",
                name=case.name, src=case.c_source, dst=case.c_destination).unwrap();
        }
        source.push_str("int main(void) { unsigned calls=0, checks=0;\n");
        for case in cases {
            let upper_power = case.bits - u32::from(case.signed);
            let lower = if case.signed {
                format!("-0x1p{upper_power}L")
            } else {
                "0.0L".into()
            };
            writeln!(source, r#"
{{
    static const {src} values[] = {{{inputs}}};
    _Static_assert(sizeof(values)/sizeof(values[0]) == 16, "positive input count");
    for (unsigned index=0; index<16; ++index) {{
        volatile struct {{ uint64_t before; {src} value; uint64_t after; }} input = {{UINT64_C(0x123456789abcdef0),values[index],UINT64_C(0xfedcba9876543210)}};
        volatile struct {{ uint64_t before; {dst} value; uint64_t after; }} output = {{UINT64_C(0x55aa33cc77ee1199),0,UINT64_C(0x9966cc33ee771155)}};
        {src} value = input.value;
        if (!isfinite(value) || (long double)value < {lower} || (long double)value >= 0x1p{upper_power}L) {{
            fprintf(stderr,"invalid oracle domain {name}[%u]\n",index); return 2;
        }}
        {dst} expected = reference_{name}(value);
        output.value = {name}(value); ++calls;
        if (output.value != expected) {{ fprintf(stderr,"conversion mismatch {name}[%u]\n",index); return 3; }} ++checks;
        {src} unchanged = input.value;
        if (memcmp(&unchanged, &value, sizeof(value))) return 4; ++checks;
        if (input.before != UINT64_C(0x123456789abcdef0)) return 5; ++checks;
        if (input.after != UINT64_C(0xfedcba9876543210)) return 6; ++checks;
        if (output.before != UINT64_C(0x55aa33cc77ee1199)) return 7; ++checks;
        if (output.after != UINT64_C(0x9966cc33ee771155)) return 8; ++checks;
    }}
}}
"#, src=case.c_source, dst=case.c_destination, inputs=case.inputs, name=case.name).unwrap();
        }
        source.push_str("if (calls != 128 || checks != 768) return 9;\nprintf(\"PASS fp-to-int: calls=%u checks=%u\\n\",calls,checks); return 0; }\n");
        source
    }

    #[test]
    fn selected_fp_to_integer_native_defined_range_all_widths_and_opts() {
        let cases = cases();
        assert_eq!(cases.len(), 8);
        let module = module(&cases);
        let driver = driver(&cases);
        // TRUST_CG_KEEP_TEST_OBJECTS keeps the sources, objects and subprocess
        // logs of a failing run for review.
        let dir_scratch = crate::fresh_dir::create("trust-cg-fp-conversion-");
        let dir = dir_scratch.to_path_buf();
        let driver_path = dir.join("driver.c");
        fs::write(&driver_path, driver).unwrap();
        for opt_level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            let result = Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level,
                    ..CompilerConfig::default()
                },
                TargetSpec::parse(native_host::TRIPLE).unwrap(),
            )
            .with_codegen_license(super::permit_unlicensed())
            .compile(&module)
            .unwrap_or_else(|error| panic!("{opt_level:?}: {error:?}; artifacts={dir:?}"));
            native_host::assert_native_object(&result.object_code);
            let object_path = dir.join(format!("module-{opt_level:?}.o"));
            let executable = dir.join(format!("driver-{opt_level:?}"));
            fs::write(&object_path, result.object_code).unwrap();
            let link = native_process::command_output_with_timeout(
                Command::new("cc")
                    .arg("-O2")
                    .arg(&driver_path)
                    .arg(&object_path)
                    .arg("-lm")
                    .arg("-o")
                    .arg(&executable),
                native_process::codegen_link_timeout(),
            )
            .expect("native C compiler is required");
            fs::write(
                dir.join(format!("link-{opt_level:?}.stdout")),
                &link.output.stdout,
            )
            .unwrap();
            fs::write(
                dir.join(format!("link-{opt_level:?}.stderr")),
                &link.output.stderr,
            )
            .unwrap();
            assert!(
                !link.timed_out && link.output.status.success(),
                "native link failed; artifacts={dir:?}"
            );
            let run = native_process::run_executable_with_timeout(
                &executable,
                native_process::codegen_run_timeout(),
            )
            .expect("run native conversion differential");
            fs::write(
                dir.join(format!("run-{opt_level:?}.stdout")),
                &run.output.stdout,
            )
            .unwrap();
            fs::write(
                dir.join(format!("run-{opt_level:?}.stderr")),
                &run.output.stderr,
            )
            .unwrap();
            assert!(
                !run.timed_out && run.output.status.success(),
                "{opt_level:?}: native mismatch; artifacts={dir:?}"
            );
            assert_eq!(
                String::from_utf8(run.output.stdout).unwrap(),
                "PASS fp-to-int: calls=128 checks=768\n"
            );
        }
        eprintln!(
            "native FP-to-integer matrix: 4 executions, 512 CG calls, 3072 checks; artifacts={dir:?}"
        );
    }
}

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
///
/// Its only callers are the native-host controls, so it is compiled under
/// their gate (elsewhere it would be dead code, which `-D warnings` refuses).
#[cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
