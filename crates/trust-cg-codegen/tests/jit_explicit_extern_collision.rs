// Regression: explicit extern symbols must win over same-name JIT functions.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::jit::{JitCompiler, JitConfig};
use trust_cg_ir::function::{MachFunction, Signature, Type};
use trust_cg_ir::inst::{AArch64Opcode, MachInst};
use trust_cg_ir::operand::MachOperand;
use trust_cg_ir::regs::X0;

extern "C" fn host_collision_target(x: i64) -> i64 {
    x + 1
}

fn build_same_name_external_call(symbol: &str) -> MachFunction {
    let sig = Signature::new(vec![Type::I64], vec![Type::I64]);
    let mut func = MachFunction::new(symbol.to_string(), sig);
    let entry = func.entry;
    // Save and restore the frame record around the BL, as frame lowering
    // does: the final-stream frame net rejects a return through the link
    // register the BL clobbered. The BL is therefore the second word.
    let frame_record = |opcode: AArch64Opcode, offset: i64| {
        MachInst::new(
            opcode,
            vec![
                MachOperand::PReg(trust_cg_ir::regs::X29),
                MachOperand::PReg(trust_cg_ir::regs::X30),
                MachOperand::Special(trust_cg_ir::regs::SpecialReg::SP),
                MachOperand::Imm(offset),
            ],
        )
    };
    for inst in [
        frame_record(AArch64Opcode::StpPreIndex, -16),
        MachInst::new(
            AArch64Opcode::Bl,
            vec![MachOperand::Symbol(symbol.to_string())],
        ),
        frame_record(AArch64Opcode::LdpPostIndex, 16),
    ] {
        let id = func.push_inst(inst);
        func.append_inst(entry, id);
    }

    // Signature returns [I64] -> the ABI return-register alias set is [X0].
    let ret = MachInst::new(AArch64Opcode::Ret, vec![]).with_implicit_uses(&[X0]);
    let ret_id = func.push_inst(ret);
    func.append_inst(entry, ret_id);

    func
}

fn decode_aarch64_bl_target(call_site: *const u8) -> usize {
    let word = unsafe { std::ptr::read_unaligned(call_site.cast::<u32>()) };
    assert_eq!(
        word & 0xFC00_0000,
        0x9400_0000,
        "expected BL at {call_site:p}, got word 0x{word:08x}"
    );
    let imm26 = word & 0x03FF_FFFF;
    let signed_imm26 = if imm26 & 0x0200_0000 != 0 {
        (imm26 as i64) | !0x03FF_FFFFi64
    } else {
        imm26 as i64
    };
    (call_site as isize + (signed_imm26 as isize * 4)) as usize
}

#[test]
fn explicit_extern_same_name_does_not_patch_bl_to_compiled_function_itself() {
    let symbol = "trust_cg_jit_explicit_extern_collision";
    let func = build_same_name_external_call(symbol);

    let mut ext: HashMap<String, *const u8> = HashMap::new();
    ext.insert(symbol.to_string(), host_collision_target as *const u8);

    let buf = JitCompiler::new(JitConfig::default())
        .compile_raw(&[func], &ext)
        .expect("compile_raw should route same-name explicit extern through a veneer");

    let func_ptr = buf
        .get_fn_ptr_bound(symbol)
        .expect("compiled function remains publicly addressable")
        .as_ptr();
    // SAFETY: the compiled function's second word is the BL (after the
    // frame-record save); both words lie inside the published code.
    let bl_site = unsafe { func_ptr.add(4) };
    let bl_target = decode_aarch64_bl_target(bl_site);

    assert_ne!(
        bl_target, bl_site as usize,
        "same-name explicit extern was patched as an internal self-call"
    );
    assert!(
        bl_target > bl_site as usize,
        "same-name explicit extern should branch to an appended veneer, got {bl_target:#x}"
    );
}
