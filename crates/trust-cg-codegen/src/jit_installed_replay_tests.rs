// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Native controls of the installed-artifact replay (ledger `L11-P2`): a real
//! verifying AArch64 publication on this host, read back from its sealed
//! MAP_JIT mapping, and the same publication tampered AFTER the seal and the
//! cache walk but BEFORE hand-out (a flipped byte, a branch re-encoded to a
//! valid wrong target, a veneer literal moved). Each tamper must be refused
//! by name with no function pointer handed out. Execution here is testing.

use std::collections::HashMap;

use super::installed_replay_test_hooks::{InstalledTamper, TAMPER_INSTALLED_IMAGE};
use super::{JitCompiler, JitConfig, JitError};
use trust_cg_ir::function::{MachFunction, Signature, Type};
use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::X0;

extern "C" fn installed_replay_host_twice(value: i64) -> i64 {
    value.wrapping_mul(2)
}

const HOST: &str = "installed_replay_host_twice";

/// `callee: ADD X0, X0, #1; RET`, `tail_internal: B callee`,
/// `tail_external: B <HOST>` (through a veneer), laid out in this order.
fn functions() -> Vec<MachFunction> {
    let signature = || Signature::new(vec![Type::I64], vec![Type::I64]);
    let mut callee = MachFunction::new("callee".to_owned(), signature());
    let entry = callee.entry;
    let add = callee.push_inst(MachInst::new(
        AArch64Opcode::AddRI,
        vec![
            MachOperand::PReg(X0),
            MachOperand::PReg(X0),
            MachOperand::Imm(1),
        ],
    ));
    callee.append_inst(entry, add);
    let ret = callee.push_inst(MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(&[X0]));
    callee.append_inst(entry, ret);

    let tail = |name: &str, target: &str| {
        let mut function = MachFunction::new(name.to_owned(), signature());
        let entry = function.entry;
        let branch = function.push_inst(MachInst::new(
            AArch64Opcode::B,
            vec![MachOperand::Symbol(target.to_owned())],
        ));
        function.append_inst(entry, branch);
        function
    };
    vec![
        callee,
        tail("tail_internal", "callee"),
        tail("tail_external", HOST),
    ]
}

fn externs() -> HashMap<String, *const u8> {
    HashMap::from([(HOST.to_owned(), installed_replay_host_twice as *const u8)])
}

fn compile(
    verify: bool,
    tamper: Option<InstalledTamper>,
) -> Result<super::ExecutableBuffer, JitError> {
    TAMPER_INSTALLED_IMAGE.with(|slot| slot.set(tamper));
    let result = JitCompiler::new(JitConfig {
        verify,
        ..JitConfig::default()
    })
    .compile_raw(&functions(), &externs());
    // A hook the publisher did not reach must not leak into another test.
    TAMPER_INSTALLED_IMAGE.with(|slot| slot.set(None));
    result
}

fn call(buffer: &super::ExecutableBuffer, name: &str, value: i64) -> i64 {
    // SAFETY: every fixture function has the `(i64) -> i64` C ABI and the
    // buffer stays alive for the call.
    unsafe {
        (buffer
            .get_fn_bound::<extern "C" fn(i64) -> i64>(name)
            .expect("published symbol")
            .as_ref())(value)
    }
}

#[test]
fn verifying_publication_replays_its_installed_mapping_before_hand_out() {
    let buffer = compile(true, None).expect("a faithful installation publishes");
    let record = buffer
        .installed_replay()
        .expect("a verifying AArch64 publication carries its installed-artifact replay");
    assert!(record.covers_exactly(["callee", "tail_internal", "tail_external"]));
    // ADD and RET compared word for word; the two B sites decoded and
    // re-targeted; the one veneer's two words and literal checked.
    assert_eq!(
        (
            record.words_compared(),
            record.branch_sites(),
            record.veneers(),
            record.literals()
        ),
        (2, 2, 1, 0)
    );
    assert_eq!(
        record.installed_image_sha256(),
        buffer.published_image_sha256(),
        "the replay hashed the image the seal hashed"
    );
    assert_eq!(call(&buffer, "callee", 41), 42);
    assert_eq!(call(&buffer, "tail_internal", -1), 0);
    assert_eq!(call(&buffer, "tail_external", 21), 42);
}

#[test]
fn non_verifying_publication_carries_no_installed_replay() {
    let buffer = compile(false, None).expect("the raw route publishes");
    assert!(buffer.installed_replay().is_none());
    assert_eq!(call(&buffer, "tail_external", 4), 8);
}

fn expect_refusal(tamper: InstalledTamper) -> (String, u64, String) {
    match compile(true, Some(tamper)) {
        Err(JitError::InstalledArtifactReplayRejected {
            function,
            offset,
            detail,
        }) => (function, offset, detail),
        Err(other) => {
            panic!("{tamper:?}: expected the installed-artifact replay refusal, got {other}")
        }
        Ok(_) => panic!("{tamper:?}: a tampered installation was handed out"),
    }
}

#[test]
fn a_byte_flipped_after_publication_is_refused_before_hand_out() {
    // Byte 1 of `callee`'s ADD, at image offset 0.
    let (function, offset, detail) = expect_refusal(InstalledTamper::FlipByte(1));
    assert_eq!((function.as_str(), offset), ("callee", 0));
    assert!(
        detail.contains("differs from the certified word"),
        "{detail}"
    );
    // A flipped byte of the veneer's literal is a wrong resolved address.
    let (function, offset, detail) = expect_refusal(InstalledTamper::FlipByte(16 + 8));
    assert_eq!((function.as_str(), offset), ("tail_external", 24));
    assert!(detail.contains("not the resolved address"), "{detail}");
}

#[test]
fn a_relocation_patched_to_a_wrong_target_is_refused_before_hand_out() {
    // `tail_internal`'s B, re-encoded one word further: a valid B to the
    // callee's RET instead of its entry.
    let (function, offset, detail) = expect_refusal(InstalledTamper::RetargetFirstBranch);
    assert_eq!((function.as_str(), offset), ("tail_internal", 8));
    assert!(detail.contains("not function `callee`"), "{detail}");
    let (function, offset, detail) = expect_refusal(InstalledTamper::ShiftFirstVeneerLiteral);
    assert_eq!((function.as_str(), offset), ("tail_external", 24));
    assert!(detail.contains("not the resolved address"), "{detail}");
}
