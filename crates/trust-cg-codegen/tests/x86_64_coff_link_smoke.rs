// trust-cg-codegen/tests/x86_64_coff_link_smoke.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::cmp::Ordering;
use std::path::{Path, PathBuf};
use std::process::Command;

use trust_cg_codegen::x86_64::pipeline::X86RegAllocMode;
use trust_cg_codegen::x86_64::{X86OutputFormat, X86Pipeline, X86PipelineConfig};
use trust_cg_ir::regs::{RegClass, VReg};
use trust_cg_ir::x86_64_ops::X86Opcode;
use trust_cg_ir::x86_64_regs;
use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::Block;
use trust_cg_lower::x86_64_isel::{
    X86CallAbi, X86ISelConstPoolEntry, X86ISelFunction, X86ISelInst, X86ISelOperand,
};

#[derive(Debug, Clone)]
struct WindowsLinker {
    name: &'static str,
    path: PathBuf,
}

fn windows_x86_64_host() -> bool {
    cfg!(all(target_os = "windows", target_arch = "x86_64"))
}

fn find_windows_linker() -> Option<WindowsLinker> {
    for name in ["lld-link.exe", "link.exe"] {
        if let Some(path) = find_executable_with_where(name) {
            return Some(WindowsLinker { name, path });
        }
        if let Some(path) = find_executable_on_path(name) {
            return Some(WindowsLinker { name, path });
        }
    }

    if let Some(path) = find_visual_studio_build_tools_msvc_linker() {
        return Some(WindowsLinker {
            name: "link.exe",
            path,
        });
    }

    None
}

fn find_executable_with_where(name: &'static str) -> Option<PathBuf> {
    let output = Command::new("where.exe").arg(name).output().ok()?;
    if !output.status.success() {
        return None;
    }

    String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(str::trim)
        .find(|line| !line.is_empty())
        .map(PathBuf::from)
}

fn find_executable_on_path(name: &'static str) -> Option<PathBuf> {
    std::env::var_os("PATH").and_then(|path| {
        std::env::split_paths(&path)
            .map(|dir| dir.join(name))
            .find(|candidate| candidate.is_file())
    })
}

fn find_visual_studio_build_tools_msvc_linker() -> Option<PathBuf> {
    let program_files_x86 = std::env::var_os("ProgramFiles(x86)")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(r"C:\Program Files (x86)"));
    find_visual_studio_build_tools_msvc_linker_under(&program_files_x86)
}

fn find_visual_studio_build_tools_msvc_linker_under(program_files_x86: &Path) -> Option<PathBuf> {
    let visual_studio = program_files_x86.join("Microsoft Visual Studio");
    let mut candidates = Vec::new();

    for year in ["2022", "2019", "2017"] {
        let Some(year_number) = year.parse::<u16>().ok() else {
            continue;
        };
        let msvc_dir = visual_studio
            .join(year)
            .join("BuildTools")
            .join("VC")
            .join("Tools")
            .join("MSVC");
        let Ok(entries) = std::fs::read_dir(msvc_dir) else {
            continue;
        };

        for entry in entries.filter_map(Result::ok) {
            let toolset_dir = entry.path();
            let candidate = toolset_dir
                .join("bin")
                .join("Hostx64")
                .join("x64")
                .join("link.exe");
            if !candidate.is_file() {
                continue;
            }

            let toolset_version = entry
                .file_name()
                .to_string_lossy()
                .split('.')
                .map(str::parse::<u32>)
                .collect::<Result<Vec<_>, _>>()
                .unwrap_or_default();
            candidates.push((year_number, toolset_version, candidate));
        }
    }

    candidates.sort_by(|left, right| {
        left.0
            .cmp(&right.0)
            .then_with(|| compare_numeric_versions(&left.1, &right.1))
    });
    candidates.pop().map(|(_, _, path)| path)
}

fn compare_numeric_versions(left: &[u32], right: &[u32]) -> Ordering {
    for index in 0..left.len().max(right.len()) {
        match left
            .get(index)
            .copied()
            .unwrap_or(0)
            .cmp(&right.get(index).copied().unwrap_or(0))
        {
            Ordering::Equal => continue,
            ordering => return ordering,
        }
    }
    Ordering::Equal
}

fn windows_coff_pipeline() -> X86Pipeline {
    X86Pipeline::new(X86PipelineConfig {
        output_format: X86OutputFormat::Coff,
        opt_level: trust_cg_opt::OptLevel::O0,
        emit_frame: false,
        regalloc_mode: X86RegAllocMode::Simplified,
        call_abi: X86CallAbi::WindowsX64,
        ..X86PipelineConfig::default()
    })
}

fn windows_coff_framed_pipeline() -> X86Pipeline {
    X86Pipeline::new(X86PipelineConfig {
        output_format: X86OutputFormat::Coff,
        opt_level: trust_cg_opt::OptLevel::O0,
        emit_frame: true,
        regalloc_mode: X86RegAllocMode::Simplified,
        call_abi: X86CallAbi::WindowsX64,
        ..X86PipelineConfig::default()
    })
}

fn minimal_function(name: &str) -> X86ISelFunction {
    let sig = Signature {
        params: vec![],
        returns: vec![],
    };
    let mut func = X86ISelFunction::new(name.to_string(), sig);
    func.ensure_block(Block(0));
    func
}

fn frameless_leaf_object() -> Vec<u8> {
    let mut func = minimal_function("answer");
    func.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));

    windows_coff_pipeline()
        .compile_function(&func)
        .expect("frameless leaf COFF object should compile")
}

fn frameless_rdata_constant_pool_object() -> Vec<u8> {
    let mut func = minimal_function("answer_cp");
    func.const_pool_entries.push(X86ISelConstPoolEntry {
        data: 1.25f64.to_le_bytes().to_vec(),
        align: 8,
    });

    let dst = VReg::new(0, RegClass::Fpr64);
    func.next_vreg = 1;
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovsdRipRel,
            vec![X86ISelOperand::VReg(dst), X86ISelOperand::ConstPoolEntry(0)],
        ),
    );
    func.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));

    windows_coff_pipeline()
        .compile_function(&func)
        .expect("frameless .rdata constant-pool COFF object should compile")
}

fn framed_direct_call_module_object() -> Vec<u8> {
    let mut caller = minimal_function("caller");
    caller.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::Call,
            vec![X86ISelOperand::Symbol("callee".to_string())],
        ),
    );
    caller.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));

    let mut callee = minimal_function("callee");
    callee.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));

    windows_coff_framed_pipeline()
        .compile_module(&[caller, callee])
        .expect("framed non-leaf COFF module should compile with unwind metadata")
}

fn framed_callee_saved_gpr_object() -> Vec<u8> {
    let mut func = minimal_function("callee_saved_gprs");
    let rbx_vreg = VReg::new(0, RegClass::Gpr64);
    let r12_vreg = VReg::new(1, RegClass::Gpr64);
    func.next_vreg = 2;

    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![
                X86ISelOperand::VReg(rbx_vreg),
                X86ISelOperand::PReg(x86_64_regs::RBX),
            ],
        ),
    );
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![
                X86ISelOperand::VReg(r12_vreg),
                X86ISelOperand::PReg(x86_64_regs::R12),
            ],
        ),
    );
    func.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));

    windows_coff_framed_pipeline()
        .compile_function(&func)
        .expect("framed COFF function with callee-saved GPR pushes should compile")
}

fn framed_callee_saved_xmm_object() -> Vec<u8> {
    let mut func = minimal_function("callee_saved_xmms");
    for idx in 0..16 {
        let vreg = VReg::new(idx, RegClass::Fpr64);
        func.push_inst(
            Block(0),
            X86ISelInst::new(
                X86Opcode::MovsdRR,
                vec![
                    X86ISelOperand::VReg(vreg),
                    X86ISelOperand::PReg(x86_64_regs::XMM0),
                ],
            ),
        );
    }
    func.next_vreg = 16;
    func.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));

    windows_coff_framed_pipeline()
        .compile_function(&func)
        .expect("framed COFF function with callee-saved XMM saves should compile")
}

fn framed_dynamic_stack_alloc_object() -> Vec<u8> {
    let mut func = minimal_function("dynamic_stack_alloc");
    let stack_ptr = VReg::new(0, RegClass::Gpr64);
    func.next_vreg = 1;

    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::StackAlloc,
            vec![
                X86ISelOperand::VReg(stack_ptr),
                X86ISelOperand::Imm(2),
                X86ISelOperand::Imm(8),
                X86ISelOperand::Imm(16),
            ],
        ),
    );
    func.push_inst(
        Block(0),
        X86ISelInst::new(
            X86Opcode::MovRR,
            vec![
                X86ISelOperand::PReg(x86_64_regs::RAX),
                X86ISelOperand::VReg(stack_ptr),
            ],
        ),
    );
    func.push_inst(Block(0), X86ISelInst::new(X86Opcode::Ret, vec![]));

    windows_coff_framed_pipeline()
        .compile_function(&func)
        .expect("framed COFF function with dynamic stack allocation should compile")
}

fn link_object(linker: &WindowsLinker, entry: &str, obj_path: &Path, exe_path: &Path) {
    let output = Command::new(&linker.path)
        .arg(format!("/entry:{entry}"))
        .arg("/subsystem:console")
        .arg("/nodefaultlib")
        .arg(format!("/out:{}", exe_path.display()))
        .arg(obj_path)
        .output()
        .unwrap_or_else(|error| {
            panic!(
                "failed to run {} at {:?}: {error}",
                linker.name, linker.path
            )
        });

    if !output.status.success() {
        panic!(
            "{} failed linking {}:\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
            linker.name,
            obj_path.display(),
            output.status,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let metadata = std::fs::metadata(exe_path).unwrap_or_else(|error| {
        panic!("linked executable {} missing: {error}", exe_path.display())
    });
    assert!(
        metadata.len() > 0,
        "linked executable {} should not be empty",
        exe_path.display()
    );
}

fn unique_temp_dir() -> PathBuf {
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock should be after UNIX epoch")
        .as_nanos();
    std::env::temp_dir().join(format!(
        "trust_cg_x86_64_coff_link_smoke_{}_{}",
        std::process::id(),
        stamp
    ))
}

#[test]
fn windows_x86_64_coff_objects_link_with_system_linker() {
    if !windows_x86_64_host() {
        eprintln!("SKIP: Windows x86-64 COFF linker smoke requires a Windows x86-64 host");
        return;
    }

    let Some(linker) = find_windows_linker() else {
        eprintln!(
            "SKIP: Windows x86-64 COFF linker smoke requires lld-link.exe or link.exe on PATH or a Visual Studio Build Tools MSVC Hostx64/x64 link.exe"
        );
        return;
    };
    eprintln!(
        "Windows x86-64 COFF linker smoke using {} at {}",
        linker.name,
        linker.path.display()
    );

    let temp_dir = unique_temp_dir();
    std::fs::create_dir_all(&temp_dir)
        .unwrap_or_else(|error| panic!("failed to create {}: {error}", temp_dir.display()));

    let cases = [
        ("answer", "answer_leaf", frameless_leaf_object()),
        (
            "answer_cp",
            "answer_cp_rdata",
            frameless_rdata_constant_pool_object(),
        ),
        (
            "caller",
            "caller_framed_direct_call",
            framed_direct_call_module_object(),
        ),
        (
            "callee_saved_gprs",
            "callee_saved_gprs_framed",
            framed_callee_saved_gpr_object(),
        ),
        (
            "callee_saved_xmms",
            "callee_saved_xmms_framed",
            framed_callee_saved_xmm_object(),
        ),
        (
            "dynamic_stack_alloc",
            "dynamic_stack_alloc_framed",
            framed_dynamic_stack_alloc_object(),
        ),
    ];

    for (entry, name, obj) in cases {
        let obj_path = temp_dir.join(format!("{name}.obj"));
        let exe_path = temp_dir.join(format!("{name}.exe"));
        std::fs::write(&obj_path, obj)
            .unwrap_or_else(|error| panic!("failed to write {}: {error}", obj_path.display()));
        link_object(&linker, entry, &obj_path, &exe_path);
    }

    let _ = std::fs::remove_dir_all(&temp_dir);
}

#[test]
fn windows_x86_64_coff_module_direct_call_emits_unwind_metadata() {
    let obj = framed_direct_call_module_object();

    assert!(obj.windows(6).any(|window| window == b".pdata"));
    assert!(obj.windows(6).any(|window| window == b".xdata"));
}

#[test]
fn windows_x86_64_coff_callee_saved_gprs_emit_unwind_metadata() {
    let obj = framed_callee_saved_gpr_object();

    assert!(obj.windows(6).any(|window| window == b".pdata"));
    assert!(obj.windows(6).any(|window| window == b".xdata"));
}

#[test]
fn windows_x86_64_coff_callee_saved_xmms_emit_unwind_metadata() {
    let obj = framed_callee_saved_xmm_object();

    assert!(obj.windows(6).any(|window| window == b".pdata"));
    assert!(obj.windows(6).any(|window| window == b".xdata"));
}

#[test]
fn windows_x86_64_coff_dynamic_stack_alloc_emits_unwind_metadata() {
    let obj = framed_dynamic_stack_alloc_object();

    assert!(obj.windows(6).any(|window| window == b".pdata"));
    assert!(obj.windows(6).any(|window| window == b".xdata"));
}

#[test]
fn visual_studio_build_tools_linker_discovery_prefers_newest_toolset() {
    let temp_dir = unique_temp_dir();
    let old_link = temp_dir
        .join("Microsoft Visual Studio")
        .join("2019")
        .join("BuildTools")
        .join("VC")
        .join("Tools")
        .join("MSVC")
        .join("14.29.30133")
        .join("bin")
        .join("Hostx64")
        .join("x64")
        .join("link.exe");
    let new_link = temp_dir
        .join("Microsoft Visual Studio")
        .join("2022")
        .join("BuildTools")
        .join("VC")
        .join("Tools")
        .join("MSVC")
        .join("14.44.35207")
        .join("bin")
        .join("Hostx64")
        .join("x64")
        .join("link.exe");

    std::fs::create_dir_all(old_link.parent().expect("old link parent"))
        .expect("old link parent should be creatable");
    std::fs::create_dir_all(new_link.parent().expect("new link parent"))
        .expect("new link parent should be creatable");
    std::fs::write(&old_link, []).expect("old link stub should be writable");
    std::fs::write(&new_link, []).expect("new link stub should be writable");

    let discovered = find_visual_studio_build_tools_msvc_linker_under(&temp_dir)
        .expect("expected Build Tools link.exe discovery");
    assert_eq!(discovered, new_link);

    let _ = std::fs::remove_dir_all(&temp_dir);
}
