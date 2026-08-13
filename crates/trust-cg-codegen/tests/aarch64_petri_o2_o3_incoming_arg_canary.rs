#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::{Compiler, CompilerConfig, ExecutableBuffer, Target};
use trust_ir::{BinOp, ICmpOp, Ty, ValueId};
use trust_ir_build::{FunctionBuilder, ModuleBuilder};

const ENTRY_NAME: &str = "__petri_o2_o3_incoming_arg_canary";

type EntryFn = extern "C" fn(*mut u8, *const i64, u32, *mut u8, u32, *mut u8, u32, *mut u8, u32);

fn store_out_u64(fb: &mut FunctionBuilder<'_>, out: ValueId, byte_offset: u64, value: ValueId) {
    let offset = fb.iconst(Ty::U64, i128::from(byte_offset));
    let ptr = fb.gep(Ty::U8, out, vec![offset]);
    fb.store(Ty::U64, ptr, value);
}

fn store_out_u32(fb: &mut FunctionBuilder<'_>, out: ValueId, byte_offset: u64, value: ValueId) {
    let offset = fb.iconst(Ty::U64, i128::from(byte_offset));
    let ptr = fb.gep(Ty::U8, out, vec![offset]);
    fb.store(Ty::U32, ptr, value);
}

fn build_petri_canary_module() -> trust_ir::Module {
    let mut mb = ModuleBuilder::new("petri_o2_o3_incoming_arg_canary");
    let entry_ty = mb.add_func_type(
        vec![
            Ty::Ptr,
            Ty::Ptr,
            Ty::U32,
            Ty::Ptr,
            Ty::U32,
            Ty::Ptr,
            Ty::U32,
            Ty::Ptr,
            Ty::U32,
        ],
        vec![],
    );

    {
        let mut fb = mb.function(ENTRY_NAME, entry_ty);
        let entry = fb.create_block();
        let out = fb.add_block_param(entry, Ty::Ptr);
        let state = fb.add_block_param(entry, Ty::Ptr);
        let state_len = fb.add_block_param(entry, Ty::U32);
        let scratch_a = fb.add_block_param(entry, Ty::Ptr);
        let action_a = fb.add_block_param(entry, Ty::U32);
        let scratch_b = fb.add_block_param(entry, Ty::Ptr);
        let action_b = fb.add_block_param(entry, Ty::U32);
        let scratch_c = fb.add_block_param(entry, Ty::Ptr);
        let ninth_arg = fb.add_block_param(entry, Ty::U32);

        let merge = fb.create_block();
        let parent = fb.add_block_param(merge, Ty::U32);
        let child = fb.add_block_param(merge, Ty::U32);
        let token = fb.add_block_param(merge, Ty::U32);
        let rotated = fb.add_block_param(merge, Ty::U32);
        let alias = fb.add_block_param(merge, Ty::U32);
        let stack_arg_copy = fb.add_block_param(merge, Ty::U32);
        let zero_offset = fb.add_block_param(merge, Ty::U64);

        fb.switch_to_block(entry);
        let zero32 = fb.iconst(Ty::U32, 0);
        let one32 = fb.iconst(Ty::U32, 1);
        let two32 = fb.iconst(Ty::U32, 2);
        let three32 = fb.iconst(Ty::U32, 3);
        let five32 = fb.iconst(Ty::U32, 5);
        let seven32 = fb.iconst(Ty::U32, 7);
        let zero64 = fb.iconst(Ty::U64, 0);

        let action_sum = fb.binop(BinOp::Add, Ty::U32, action_a, action_b);
        let parent_even = fb.binop(BinOp::Add, Ty::U32, state_len, action_sum);
        let child_even = fb.binop(BinOp::Add, Ty::U32, ninth_arg, one32);
        let token_even = fb.binop(BinOp::Xor, Ty::U32, parent_even, child_even);
        let rotated_even = fb.binop(BinOp::Add, Ty::U32, action_a, five32);
        let alias_even = fb.binop(BinOp::Xor, Ty::U32, rotated_even, ninth_arg);

        let parent_odd = fb.binop(BinOp::Add, Ty::U32, ninth_arg, two32);
        let child_odd = fb.binop(BinOp::Add, Ty::U32, action_b, three32);
        let token_odd = fb.binop(BinOp::Xor, Ty::U32, child_odd, state_len);
        let rotated_odd = fb.binop(BinOp::Add, Ty::U32, action_sum, seven32);
        let alias_odd = fb.binop(BinOp::Xor, Ty::U32, parent_odd, rotated_odd);

        let low_bit = fb.binop(BinOp::And, Ty::U32, ninth_arg, one32);
        let is_odd = fb.icmp(ICmpOp::Ne, Ty::U32, low_bit, zero32);
        fb.condbr(
            is_odd,
            merge,
            vec![
                parent_odd,
                child_odd,
                token_odd,
                rotated_odd,
                alias_odd,
                ninth_arg,
                zero64,
            ],
            merge,
            vec![
                parent_even,
                child_even,
                token_even,
                rotated_even,
                alias_even,
                ninth_arg,
                zero64,
            ],
        );

        fb.switch_to_block(merge);
        let state0_ptr = fb.gep(Ty::I64, state, vec![zero_offset]);
        let state0 = fb.load(Ty::I64, state0_ptr);
        let petri_mix0 = fb.binop(BinOp::Add, Ty::U32, parent, child);
        let petri_mix1 = fb.binop(BinOp::Xor, Ty::U32, petri_mix0, token);
        let petri_mix2 = fb.binop(BinOp::Add, Ty::U32, petri_mix1, rotated);
        let petri_mix3 = fb.binop(BinOp::Xor, Ty::U32, petri_mix2, alias);

        store_out_u64(&mut fb, out, 0, state0);
        store_out_u32(&mut fb, out, 8, stack_arg_copy);
        store_out_u32(&mut fb, out, 12, petri_mix3);
        let scratch_zero_a = fb.iconst(Ty::U8, 0);
        let scratch_zero_b = fb.iconst(Ty::U8, 0);
        let scratch_zero_c = fb.iconst(Ty::U8, 0);
        fb.store(Ty::U8, scratch_a, scratch_zero_a);
        fb.store(Ty::U8, scratch_b, scratch_zero_b);
        fb.store(Ty::U8, scratch_c, scratch_zero_c);
        fb.ret(vec![]);

        fb.build();
    }

    mb.build()
}

fn compile_to_jit(module: &trust_ir::Module, opt_level: OptLevel) -> ExecutableBuffer {
    let mut config = CompilerConfig::jit_fast(Target::Aarch64);
    config.opt_level = opt_level;
    Compiler::new(config)
        .compile_module_to_jit(module, &HashMap::new())
        .unwrap_or_else(|err| panic!("{opt_level:?} compile failed: {err}"))
        .buffer
}

fn read_i64(bytes: &[u8], offset: usize) -> i64 {
    i64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
}

fn read_u32(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap())
}

fn expected_mix(state_len: u32, action_a: u32, action_b: u32, ninth_arg: u32) -> u32 {
    let action_sum = action_a.wrapping_add(action_b);
    let (parent, child, token, rotated, alias) = if ninth_arg & 1 != 0 {
        let parent = ninth_arg.wrapping_add(2);
        let child = action_b.wrapping_add(3);
        let token = child ^ state_len;
        let rotated = action_sum.wrapping_add(7);
        let alias = parent ^ rotated;
        (parent, child, token, rotated, alias)
    } else {
        let parent = state_len.wrapping_add(action_sum);
        let child = ninth_arg.wrapping_add(1);
        let token = parent ^ child;
        let rotated = action_a.wrapping_add(5);
        let alias = rotated ^ ninth_arg;
        (parent, child, token, rotated, alias)
    };

    (parent.wrapping_add(child) ^ token).wrapping_add(rotated) ^ alias
}

fn run_case(entry: EntryFn, opt_level: OptLevel, ninth_arg: u32) {
    let state = [2_i64, 1, 0, 0, 0, 0, 0, 0, 77];
    let mut out = [0_u8; 16];
    let mut scratch_a = [0xff_u8; 1];
    let mut scratch_b = [0xff_u8; 1];
    let mut scratch_c = [0xff_u8; 1];
    let action_a = 11;
    let action_b = 29;

    entry(
        out.as_mut_ptr(),
        state.as_ptr(),
        state.len() as u32,
        scratch_a.as_mut_ptr(),
        action_a,
        scratch_b.as_mut_ptr(),
        action_b,
        scratch_c.as_mut_ptr(),
        ninth_arg,
    );

    assert_eq!(
        read_i64(&out, 0),
        2,
        "{opt_level:?} zero-offset state load must read state[0], not state[8]"
    );
    assert_eq!(
        read_u32(&out, 8),
        ninth_arg,
        "{opt_level:?} ninth incoming stack argument remains readable"
    );
    assert_eq!(
        read_u32(&out, 12),
        expected_mix(state.len() as u32, action_a, action_b, ninth_arg),
        "{opt_level:?} block-param branch args should copy the selected Petri edge values"
    );
    assert_eq!(scratch_a, [0]);
    assert_eq!(scratch_b, [0]);
    assert_eq!(scratch_c, [0]);
}

#[test]
fn petri_incoming_arg_and_zero_offset_load_survive_o2_o3_pressure() {
    let module = build_petri_canary_module();
    for opt_level in [OptLevel::O2, OptLevel::O3] {
        let buffer = compile_to_jit(&module, opt_level);
        let raw = buffer
            .get_fn_ptr_bound(ENTRY_NAME)
            .expect("entry symbol should be present")
            .as_ptr();
        let entry: EntryFn = unsafe { std::mem::transmute(raw) };

        run_case(entry, opt_level, 123);
        run_case(entry, opt_level, 124);
    }
}
