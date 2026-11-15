//! Required stack-guard admission and bounded native macOS ARM64 controls.
//! Stack canary lowering covers Apple Mach-O and AArch64 Linux ELF with a
//! global `__stack_chk_guard`; the admission split (Linux GNU admitted,
//! Android refused by name) is pinned on every host. The Linux ELF canary's
//! object and native controls live in `e2e_aarch64_link_runtime`.
//! No exception unwinding or foreign-architecture execution is involved.

mod common;

use trust_cg_codegen::frame;
use trust_cg_codegen::macho::linker::MachOParser;
use trust_cg_codegen::pipeline::{ObjectGlobal, OptLevel, Pipeline, PipelineConfig, PipelineError};
use trust_cg_ir::regs::{X0, XZR};
use trust_cg_ir::{
    AArch64Opcode as Op, MachFunction, MachInst, MachOperand as Operand, Signature,
    StackProtectorMode, StackSlot, Type,
};

fn function(corrupt: bool) -> MachFunction {
    let mut func = MachFunction::new(
        "guard_target".into(),
        Signature::new(vec![], vec![Type::I64]),
    );
    func.stack_protector = StackProtectorMode::StackGuard;
    frame::ensure_stack_protector_slot(&mut func).unwrap();
    if corrupt {
        // Deliberately corrupt the reserved guard after its generated save;
        // the epilogue must take the failure path rather than return 42.
        let store = func.push_inst(MachInst::new(
            Op::StrRI,
            vec![
                Operand::PReg(XZR),
                Operand::StackSlot(func.stack_protector_slot.unwrap()),
            ],
        ));
        func.append_inst(func.entry, store);
    }
    let mov = func.push_inst(MachInst::new(
        Op::Movz,
        vec![Operand::PReg(X0), Operand::Imm(42)],
    ));
    func.append_inst(func.entry, mov);
    let ret = func.push_inst(MachInst::new(Op::Ret, vec![]).with_implicit_uses(&[X0]));
    func.append_inst(func.entry, ret);
    func
}

fn pipeline() -> Pipeline {
    pipeline_for("aarch64-apple-darwin")
}

fn pipeline_for(triple: &str) -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level: OptLevel::O0,
        verify: true,
        target_triple: triple.into(),
        ..PipelineConfig::default()
    })
}

/// The Mach-O object the host-independent structure control parses.
fn object(corrupt: bool) -> Vec<u8> {
    object_for("aarch64-apple-darwin", corrupt)
}

fn object_for(triple: &str, corrupt: bool) -> Vec<u8> {
    trust_cg_codegen::env_lock::with_env_edits(|env| {
        // Normalize only optional allocation-quality search. Mandatory
        // verification, allocation and encoding checks remain enabled.
        env.remove("TCG_AY_REGALLOC");
        let mut func = function(corrupt);
        let pipeline = pipeline_for(triple);
        pipeline.prepare_ir_function(&mut func).unwrap();
        let guard = ObjectGlobal {
            name: "__stack_chk_guard".into(),
            data: 0x1234_5678_9abc_def0_u64.to_le_bytes().to_vec(),
            mutable: true,
            is_external: true,
            symbol_refs: vec![],
            is_thread_local: false,
            is_import: false,
            is_weak: false,
            align: 8,
            visibility: trust_ir::Visibility::Default,
            retained: false,
            section: None,
            comdat: false,
        };
        pipeline
            .compile_module_with_globals(&[func], &[guard])
            .unwrap()
    })
}

#[test]
fn stack_guard_public_pipeline_reports_guard_admission_as_frame_error() {
    trust_cg_codegen::env_lock::with_env_edits(|env| {
        env.remove("TCG_AY_REGALLOC");
        let mut func = function(false);
        func.stack_slots[0] = StackSlot::new(4, 4);
        let error = pipeline().prepare_ir_function(&mut func).unwrap_err();
        assert!(
            matches!(error, PipelineError::FrameLowering(_)),
            "{error:?}"
        );
        assert!(
            error
                .to_string()
                .contains("expected a fixed 8-byte, 16-aligned slot")
        );
    });
}

/// Stack canary admission by target, object-level on every host: the Linux
/// GNU triple is admitted (a global `__stack_chk_guard` read through the GOT),
/// while Android, whose bionic keeps the guard in a thread-pointer slot, must
/// refuse by name rather than emit an unguarded or wrongly guarded frame.
#[test]
fn stack_guard_target_admission_is_pinned_by_name() {
    trust_cg_codegen::env_lock::with_env_edits(|env| {
        env.remove("TCG_AY_REGALLOC");
        let mut func = function(false);
        pipeline_for("aarch64-unknown-linux-gnu")
            .prepare_ir_function(&mut func)
            .expect("Linux GNU ELF admits the global-guard canary");

        let mut func = function(false);
        let error = pipeline_for("aarch64-linux-android")
            .prepare_ir_function(&mut func)
            .unwrap_err();
        // A frame-lowering refusal (trust-core AD-8 / E0.3: typed by the layer
        // that raises it), naming the target and its object format.
        assert!(
            matches!(
                &error,
                PipelineError::FrameLowering(trust_cg_codegen::lower::LowerError::FrameLowering(
                    reason,
                )) if reason.ends_with("(target `aarch64-linux-android`, ELF)")
            ),
            "{error:?}"
        );
        assert!(
            error.to_string().contains(
                "stack canary lowering supports only AArch64 Apple Mach-O and AArch64 Linux ELF"
            ),
            "{error}"
        );
    });
}

#[test]
fn stack_guard_object_retains_independent_guard_and_failure_symbols() {
    let object = MachOParser::parse(&object(false)).unwrap();
    for name in ["_guard_target", "___stack_chk_guard", "___stack_chk_fail"] {
        assert!(
            object.symbols.iter().any(|symbol| symbol.name == name),
            "missing {name}"
        );
    }
    assert!(
        object
            .sections
            .iter()
            .any(|section| section.name == "__text" && !section.relocations.is_empty())
    );
}

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[test]
fn stack_guard_native_returns_normally_and_detects_corruption() {
    use std::process::Command;
    use std::time::Duration;

    // Use the platform linker as an independent consumer of the emitted GOT
    // relocations. The standalone-linker twin of this program lives in
    // e2e_macho_standalone_got_tlv.rs. No proof-policy change is involved.
    const CALLER: &str = r#"
#include <stdlib.h>
extern long guard_target(void);
__attribute__((noreturn)) void __stack_chk_fail(void) { _Exit(87); }
int main(void) { return guard_target() == 42 ? 0 : 1; }
"#;
    let directory = tempfile::Builder::new()
        .prefix("trust-cg-stack-guard-")
        .tempdir()
        .unwrap();
    let caller = directory.path().join("caller.c");
    let body = directory.path().join("guard.o");
    std::fs::write(&caller, CALLER).unwrap();
    for corrupt in [false, true] {
        let path = directory
            .path()
            .join(if corrupt { "corrupt" } else { "intact" });
        std::fs::write(&body, object(corrupt)).unwrap();
        let mut command = Command::new("/usr/bin/clang");
        command
            .arg("-fno-stack-protector")
            .arg(&caller)
            .arg(&body)
            .arg("-o")
            .arg(&path);
        let linked =
            common::rosetta::command_output_with_timeout(&mut command, Duration::from_secs(30))
                .expect("the macOS object control requires the platform C linker");
        assert!(!linked.timed_out, "platform linker timed out");
        assert!(linked.output.status.success(), "{:?}", linked.output);
        let result = common::rosetta::run_executable_with_timeout(
            &path,
            common::rosetta::exec_timeout(Duration::from_secs(5)),
        )
        .unwrap();
        assert!(!result.timed_out, "stack-guard native control timed out");
        assert_eq!(
            result.output.status.code(),
            Some(if corrupt { 87 } else { 0 }),
            "{:?}",
            result.output
        );
    }
}
