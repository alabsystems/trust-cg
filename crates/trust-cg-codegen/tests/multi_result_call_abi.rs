//! Native AArch64 regression for the internal multi-scalar return convention.
//! Tests actual direct/indirect call edges and register pressure, not Core
//! admission, portable C aggregate ABI compatibility, or proof authority.
#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

use std::collections::HashMap;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::{Compiler, CompilerConfig, CoreHostJitTarget, ExecutableBuffer, Target};
use trust_ir::{BinOp, CallingConv, CastOp, Ty};
use trust_ir_build::{ModuleBuilder, validate_module};

const LANES: usize = 20;

fn module() -> trust_ir::Module {
    let host = CoreHostJitTarget::detect().expect("supported native AArch64 test host");
    let mut m = ModuleBuilder::new_with_target_info(
        "multi_result_call_abi",
        host.trust_ir_target_info().clone(),
    );
    let returns = vec![Ty::Ptr, Ty::U64, Ty::I64, Ty::U64, Ty::U64];
    let sig = m.add_func_type(vec![Ty::Ptr, Ty::U64], returns.clone());
    let mut f = m.function("five", sig);
    f.set_calling_conv(CallingConv::Fast);
    let entry = f.create_block();
    let state = f.add_block_param(entry, Ty::Ptr);
    let seed = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let before = f.load_volatile(Ty::U64, state);
    let one = f.iconst(Ty::U64, 1);
    let after = f.binop(BinOp::Add, Ty::U64, before, one);
    f.store_volatile(Ty::U64, state, after);
    let bias = f.iconst(Ty::U64, 17);
    let status = f.binop(BinOp::Add, Ty::U64, seed, bias);
    let mask = f.iconst(Ty::U64, 0xfedc_ba98_7654_3210_u64 as i128);
    let value = f.binop(BinOp::Xor, Ty::U64, seed, mask);
    let value = f.cast(CastOp::Bitcast, Ty::U64, Ty::I64, value);
    let factor = f.iconst(Ty::U64, 3);
    let site = f.binop(BinOp::Mul, Ty::U64, seed, factor);
    f.ret(vec![state, status, value, site, before]);
    let callee = f.build();

    for indirect in [false, true] {
        let mut params = vec![];
        if indirect {
            params.push(Ty::Func(sig));
        }
        params.extend([Ty::Ptr, Ty::Ptr, Ty::U64, Ty::Ptr]);
        let wrapper_sig = m.add_func_type(params.clone(), vec![]);
        let mut f = m.function(if indirect { "indirect" } else { "direct" }, wrapper_sig);
        let entry = f.create_block();
        let args: Vec<_> = params
            .into_iter()
            .map(|ty| f.add_block_param(entry, ty))
            .collect();
        let offset = usize::from(indirect);
        let (state, live, seed, out) = (
            args[offset],
            args[offset + 1],
            args[offset + 2],
            args[offset + 3],
        );
        f.switch_to_block(entry);
        let mut preserved = Vec::new();
        for lane in 0..LANES {
            let pointer = f.gep_byte_offset(live, (lane * 8) as u64);
            preserved.push(f.load_volatile(Ty::U64, pointer));
        }
        let first = if indirect {
            f.call_indirect_results_cc::<5>(args[0], sig, vec![state, seed], CallingConv::Fast)
        } else {
            f.call_results::<5>(callee, vec![state, seed])
        };
        let second = if indirect {
            f.call_indirect_results_cc::<5>(
                args[0],
                sig,
                vec![first[0], first[1]],
                CallingConv::Fast,
            )
        } else {
            f.call_results::<5>(callee, vec![first[0], first[1]])
        };
        for (lane, (value, ty)) in first
            .into_iter()
            .zip(returns.clone())
            .chain(second.into_iter().zip(returns.clone()))
            .chain(preserved.into_iter().map(|v| (v, Ty::U64)))
            .enumerate()
        {
            let pointer = f.gep_byte_offset(out, (lane * 8) as u64);
            f.store_volatile(ty, pointer, value);
        }
        f.ret(vec![]);
        f.build();
    }
    let m = m.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&m), []);
    m
}

fn words<'a>(buffer: &'a ExecutableBuffer, name: &str) -> &'a [u32] {
    let start = *buffer.symbol_offsets().get(name).unwrap() as usize;
    let end = buffer
        .symbols()
        .filter_map(|(_, offset)| {
            let offset = offset as usize;
            (offset > start).then_some(offset)
        })
        .min()
        .unwrap_or(buffer.code_len());
    let ptr = buffer.get_fn_ptr_bound(name).unwrap().as_ptr();
    assert_eq!((end - start) % 4, 0);
    // SAFETY: read only this symbol's retained executable buffer range.
    unsafe { std::slice::from_raw_parts(ptr.cast(), (end - start) / 4) }
}

#[test]
fn five_scalar_fast_returns_preserve_all_results_and_live_across_call_values() {
    let host = CoreHostJitTarget::detect().expect("supported native AArch64 test host");
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let module = module();
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt;
        let compiled = Compiler::new_for_target_spec(config, host.target_spec())
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module, &HashMap::new())
            .unwrap_or_else(|e| panic!("{opt:?} compile failed: {e}"));
        let buffer = compiled.buffer;
        let direct_calls = words(&buffer, "direct")
            .iter()
            .filter(|word| **word & 0xfc00_0000 == 0x9400_0000)
            .count();
        let indirect_calls = words(&buffer, "indirect")
            .iter()
            .filter(|word| **word & 0xffff_fc1f == 0xd63f_0000)
            .count();
        assert!(
            direct_calls >= 2,
            "{opt:?}: probe must retain direct calls, found {direct_calls}"
        );
        assert!(
            indirect_calls >= 2,
            "{opt:?}: probe must retain runtime BLR calls, found {indirect_calls}"
        );
        type Direct = extern "C" fn(*mut u64, *const u64, u64, *mut u64);
        type Indirect = extern "C" fn(*const u8, *mut u64, *const u64, u64, *mut u64);
        // SAFETY: only the outer, void-return C wrappers cross Rust's ABI.
        let direct = unsafe { buffer.get_fn_bound::<Direct>("direct") }.unwrap();
        let indirect = unsafe { buffer.get_fn_bound::<Indirect>("indirect") }.unwrap();
        let callback = buffer.get_fn_ptr_bound("five").unwrap();
        let inputs: Vec<_> = (0..LANES)
            .map(|i| 0x1234_5678_9abc_def0_u64.wrapping_mul(i as u64 + 1))
            .collect();
        for i in 0..100_u64 {
            let seed = i.wrapping_mul(0x9e37_79b9_7f4a_7c15);
            for use_indirect in [false, true] {
                let mut state = seed ^ 0xabcd;
                let before = state;
                let state_ptr = (&mut state as *mut u64) as u64;
                let mut output = [u64::MAX; 10 + LANES];
                let mut expected = [0; 10 + LANES];
                for call in 0..2 {
                    let argument = seed.wrapping_add(17 * call as u64);
                    expected[call * 5..call * 5 + 5].copy_from_slice(&[
                        state_ptr,
                        argument.wrapping_add(17),
                        argument ^ 0xfedc_ba98_7654_3210,
                        argument.wrapping_mul(3),
                        before.wrapping_add(call as u64),
                    ]);
                }
                expected[10..].copy_from_slice(&inputs);
                if use_indirect {
                    indirect.as_ref()(
                        callback.as_ptr(),
                        &mut state,
                        inputs.as_ptr(),
                        seed,
                        output.as_mut_ptr(),
                    );
                } else {
                    direct.as_ref()(&mut state, inputs.as_ptr(), seed, output.as_mut_ptr());
                }
                assert_eq!(
                    output, expected,
                    "{opt:?} indirect={use_indirect} seed={seed}"
                );
                assert_eq!(state, before.wrapping_add(2));
            }
        }
        eprintln!(
            "{opt:?}: 200 native invocations, BL={direct_calls}, BLR={indirect_calls}, five results + twenty live lanes exact"
        );
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
