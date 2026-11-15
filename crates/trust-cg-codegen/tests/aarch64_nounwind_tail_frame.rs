// Copyright 2026 Andrew Yates | Apache-2.0
//! Required Rust EH frames survive self and sibling tail-position calls.
//! Object controls decode the final branch instruction; Linux native controls
//! walk the real unwind stack using LLVM-built Rust and the real personality.
//! This is diagnostic frame retention, not certified EH or foreign-abort
//! admission through the rustc bridge.

use std::collections::BTreeSet;
use trust_cg_codegen::macho::linker::MachOParser;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{Compiler, CompilerConfig};
use trust_ir::{
    BinOp, Block, BlockId, Constant, FuncId, FuncTy, Function, ICmpOp, Inst, InstrNode, Linkage,
    Module, Producer, Ty, ValueId,
};

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "common/rosetta.rs"]
mod process;

fn fixture(recursive: bool, triple: &str) -> Module {
    let mut module = Module::new("required_exception_frame");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: trust_ir::Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: trust_ir::StructPassingPolicy::NativeC,
    });
    let scalar = module
        .add_func_type(FuncTy::unrecorded(vec![Ty::I64], vec![Ty::I64], false))
        .expect("finite fixture signature");
    let seed = module
        .add_func_type(FuncTy::unrecorded(vec![Ty::I64], vec![], false))
        .expect("finite fixture signature");
    let empty = module
        .add_func_type(FuncTy::unrecorded(vec![], vec![], false))
        .expect("finite fixture signature");
    for (id, name, ty) in [
        (0, "frame_seed", seed),
        (1, "observe_frame", scalar),
        (2, "abort", empty),
    ] {
        let mut function = Function::new(FuncId::new(id), name, ty, BlockId::new(0));
        function.blocks.clear();
        function.linkage = Linkage::External;
        module
            .try_add_function(function)
            .expect("finite fixture function");
    }
    let mut function = Function::new(FuncId::new(3), "tc_frame", scalar, BlockId::new(0));
    function.linkage = Linkage::External;
    function.producer = Some(Producer::TRust);
    let leaf = vec![
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(10)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(10)],
        }),
    ];
    function.blocks = vec![
        Block {
            id: BlockId::new(0),
            params: vec![(ValueId::new(0), Ty::I64)],
            body: vec![InstrNode::new(Inst::Invoke {
                callee: FuncId::new(0),
                args: vec![ValueId::new(0)],
                normal_dest: BlockId::new(1),
                normal_args: vec![],
                unwind_dest: BlockId::new(2),
            })],
        },
        Block {
            id: BlockId::new(1),
            params: vec![],
            body: if recursive {
                vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(0),
                    })
                    .with_result(ValueId::new(1)),
                    InstrNode::new(Inst::ICmp {
                        op: ICmpOp::Eq,
                        ty: Ty::I64,
                        lhs: ValueId::new(0),
                        rhs: ValueId::new(1),
                    })
                    .with_result(ValueId::new(2)),
                    InstrNode::new(Inst::CondBr {
                        cond: ValueId::new(2),
                        then_target: BlockId::new(3),
                        then_args: vec![],
                        else_target: BlockId::new(4),
                        else_args: vec![],
                    }),
                ]
            } else {
                leaf.clone()
            },
        },
        Block {
            id: BlockId::new(2),
            params: vec![],
            body: vec![
                InstrNode::new(Inst::LandingPad {
                    is_cleanup: true,
                    catch_type_indices: vec![],
                })
                .with_results(vec![ValueId::new(20), ValueId::new(21)]),
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(2),
                    args: vec![],
                }),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(-1),
                })
                .with_result(ValueId::new(22)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(22)],
                }),
            ],
        },
    ];
    if recursive {
        function.blocks.extend([
            Block {
                id: BlockId::new(3),
                params: vec![],
                body: leaf,
            },
            Block {
                id: BlockId::new(4),
                params: vec![],
                body: vec![
                    InstrNode::new(Inst::Const {
                        ty: Ty::I64,
                        value: Constant::Int(1),
                    })
                    .with_result(ValueId::new(3)),
                    InstrNode::new(Inst::BinOp {
                        op: BinOp::Sub,
                        ty: Ty::I64,
                        lhs: ValueId::new(0),
                        rhs: ValueId::new(3),
                    })
                    .with_result(ValueId::new(4)),
                    InstrNode::new(Inst::Call {
                        callee: FuncId::new(3),
                        args: vec![ValueId::new(4)],
                    })
                    .with_result(ValueId::new(5)),
                    InstrNode::new(Inst::Return {
                        values: vec![ValueId::new(5)],
                    }),
                ],
            },
        ]);
    }
    module
        .try_add_function(function)
        .expect("finite fixture function");
    let diagnostics = trust_ir_build::validate_module(&module);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
    module
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

fn compile(recursive: bool, level: OptLevel, required: bool, known: bool, triple: &str) -> Vec<u8> {
    let callees = if known {
        ["frame_seed", "observe_frame", "tc_frame", "abort"]
            .into_iter()
            .map(str::to_owned)
            .collect()
    } else {
        BTreeSet::new()
    };
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: level,
            emit_proofs: false,
            parallel: false,
            eh_frames_cannot_unwind: required,
            eh_nounwind_callees: callees,
            never_inline: ["tc_frame".to_owned()].into(),
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).unwrap(),
    )
    .with_codegen_license(permit_unlicensed())
    .compile(&fixture(recursive, triple))
    .expect("the modeled frame must compile")
    .object_code
}

#[test]
fn macho_nounwind_frames_keep_real_calls_at_every_optimization_level() {
    let mut cells = 0;
    for recursive in [false, true] {
        for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
            for required in [false, true] {
                for known in [false, true] {
                    let bytes = compile(recursive, level, required, known, "aarch64-apple-darwin");
                    let object = MachOParser::parse(&bytes).unwrap();
                    assert!(object.sections.iter().any(|s| s.name == "__gcc_except_tab"));
                    let text = object.sections.iter().find(|s| s.name == "__text").unwrap();
                    let sites: Vec<_> = text
                        .relocations
                        .iter()
                        .filter(|r| {
                            r.is_extern
                                && object.symbols[r.symbol_index as usize].name.as_str()
                                    == "_observe_frame"
                        })
                        .collect();
                    assert_eq!(sites.len(), 1, "one observer call is required");
                    let offset = sites[0].offset as usize;
                    let instruction =
                        u32::from_le_bytes(text.data[offset..offset + 4].try_into().unwrap());
                    let tail = !required && matches!(level, OptLevel::O2 | OptLevel::O3);
                    assert_eq!(
                        instruction & 0xfc00_0000,
                        if tail { 0x1400_0000 } else { 0x9400_0000 },
                        "{level:?} recursive={recursive} required={required} known={known}"
                    );
                    cells += 1;
                }
            }
        }
    }
    println!("Mach-O frame controls: {cells} object cells; no Darwin native claim");
}

#[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
mod linux {
    use super::{OptLevel, compile, process};
    use std::fs;
    use std::path::PathBuf;
    use std::process::Command;
    use std::sync::atomic::{AtomicU64, Ordering};
    fn checked(command: &mut Command) -> String {
        let result =
            process::command_output_with_timeout(command, process::codegen_link_timeout()).unwrap();
        assert!(
            !result.timed_out && result.output.status.success(),
            "{command:?}\nstdout={}\nstderr={}",
            String::from_utf8_lossy(&result.output.stdout),
            String::from_utf8_lossy(&result.output.stderr)
        );
        String::from_utf8(result.output.stdout).unwrap()
    }

    fn compiler() -> Command {
        let path = std::env::var_os("TRUST_TARGO")
            .map(|p| PathBuf::from(p).with_file_name("trustc"))
            .or_else(|| std::env::var_os("RUSTC").map(PathBuf::from))
            .unwrap_or_else(|| "trustc".into());
        let mut command = Command::new(path);
        for (key, _) in std::env::vars_os() {
            if key.to_string_lossy().starts_with("TRUST_CG_")
                || key.to_string_lossy().starts_with("TCG_")
            {
                command.env_remove(key);
            }
        }
        command.args([
            "--edition=2024",
            "-Ztrust-verify=off",
            "-Cpanic=unwind",
            "-Copt-level=2",
        ]);
        command
    }

    fn driver(size: usize, required: bool, optimized: bool, recursive: bool) -> String {
        format!(
            r#"
use std::ffi::c_void;
use std::sync::atomic::{{AtomicUsize, Ordering}};
unsafe extern "C" {{ fn backtrace(buffer: *mut *mut c_void, size: i32) -> i32; fn tc_frame(depth: i64) -> i64; }}
static SEEDS: AtomicUsize = AtomicUsize::new(0);
static SUM: AtomicUsize = AtomicUsize::new(0);
static OBSERVATIONS: AtomicUsize = AtomicUsize::new(0);
static FRAMES: AtomicUsize = AtomicUsize::new(0);
#[unsafe(no_mangle)]
pub extern "C" fn frame_seed(depth: i64) {{ SEEDS.fetch_add(1, Ordering::SeqCst); SUM.fetch_add(depth as usize, Ordering::SeqCst); }}
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn observe_frame(_: i64) -> i64 {{
    let mut pcs = [std::ptr::null_mut(); 64];
    let count = unsafe {{ backtrace(pcs.as_mut_ptr(), 64) }};
    assert!(count > 0 && count < 64);
    let low = tc_frame as *const () as usize;
    let high = low.checked_add({size}).unwrap();
    let frames = pcs[..count as usize].iter().filter(|pc| {{ let address = (**pc as usize).saturating_sub(1); address >= low && address < high }}).count();
    FRAMES.store(frames, Ordering::SeqCst);
    OBSERVATIONS.fetch_add(1, Ordering::SeqCst);
    4242
}}
fn main() {{
    for depth in [0_usize, 3] {{
        SEEDS.store(0, Ordering::SeqCst); SUM.store(0, Ordering::SeqCst); OBSERVATIONS.store(0, Ordering::SeqCst); FRAMES.store(usize::MAX, Ordering::SeqCst);
        let result = unsafe {{ tc_frame(depth as i64) }};
        let calls = if {recursive} {{ depth + 1 }} else {{ 1 }};
        let sum = if {recursive} {{ depth * (depth + 1) / 2 }} else {{ depth }};
        let expected_frames = if {required} || !{optimized} {{ calls }} else {{ 0 }};
        println!("depth={{depth}} result={{result}} seeds={{}} sum={{}} observations={{}} frames={{}} expected={{expected_frames}}", SEEDS.load(Ordering::SeqCst), SUM.load(Ordering::SeqCst), OBSERVATIONS.load(Ordering::SeqCst), FRAMES.load(Ordering::SeqCst));
        assert_eq!(result, 4242); assert_eq!(SEEDS.load(Ordering::SeqCst), calls); assert_eq!(SUM.load(Ordering::SeqCst), sum); assert_eq!(OBSERVATIONS.load(Ordering::SeqCst), 1); assert_eq!(FRAMES.load(Ordering::SeqCst), expected_frames);
    }}
}}
"#
        )
    }

    #[cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
    #[test]
    fn linux_nounwind_frames_survive_on_the_real_unwind_stack() {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let directory = std::env::temp_dir().join(format!(
            "trust-cg-tail-frame-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::SeqCst)
        ));
        fs::create_dir(&directory).unwrap();
        eprintln!("native frame artifacts: {}", directory.display());
        let mut cells = 0;
        for recursive in [false, true] {
            for level in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
                for required in [false, true] {
                    for known in [false, true] {
                        let lane = directory.join(format!(
                            "{level:?}-recursive-{recursive}-required-{required}-known-{known}"
                        ));
                        fs::create_dir(&lane).unwrap();
                        let object = lane.join("frame.o");
                        fs::write(
                            &object,
                            compile(
                                recursive,
                                level,
                                required,
                                known,
                                "aarch64-unknown-linux-gnu",
                            ),
                        )
                        .unwrap();
                        let symbols = checked(
                            Command::new("nm")
                                .args(["-S", "--defined-only"])
                                .arg(&object),
                        );
                        let row: Vec<_> = symbols
                            .lines()
                            .find(|line| line.split_whitespace().last() == Some("tc_frame"))
                            .unwrap()
                            .split_whitespace()
                            .collect();
                        let size = usize::from_str_radix(row[1], 16).unwrap();
                        assert!(size > 0);
                        let relocations = checked(Command::new("readelf").arg("-rW").arg(&object));
                        let rows: Vec<_> = relocations
                            .lines()
                            .filter(|line| line.split_whitespace().any(|s| s == "observe_frame"))
                            .collect();
                        assert_eq!(rows.len(), 1);
                        let tail = !required && matches!(level, OptLevel::O2 | OptLevel::O3);
                        let source = lane.join("driver.rs");
                        fs::write(
                            &source,
                            driver(
                                size,
                                required,
                                matches!(level, OptLevel::O2 | OptLevel::O3),
                                recursive,
                            ),
                        )
                        .unwrap();
                        let executable = lane.join("driver");
                        checked(
                            compiler()
                                .arg(&source)
                                .arg("-Clink-arg=-Wl,-z,noexecstack")
                                .arg(format!("-Clink-arg={}", object.display()))
                                .arg("-o")
                                .arg(&executable),
                        );
                        // Run the independent stack observer before checking
                        // the relocation, so a regressed image demonstrates
                        // the lost native frame rather than stopping at bytes.
                        eprintln!("native frame lane: {}", lane.display());
                        let stdout = checked(&mut Command::new(&executable));
                        assert_eq!(stdout.lines().count(), 2);
                        assert!(
                            rows[0].contains(if tail {
                                "R_AARCH64_JUMP26"
                            } else {
                                "R_AARCH64_CALL26"
                            }),
                            "{}",
                            rows[0]
                        );
                        println!(
                            "{level:?} recursive={recursive} required={required} known={known}\n{stdout}"
                        );
                        cells += 1;
                    }
                }
            }
        }
        println!(
            "Linux frame controls: {cells} native executions; {} source invocations",
            cells * 2
        );
        fs::remove_dir_all(&directory).unwrap();
    }
}
