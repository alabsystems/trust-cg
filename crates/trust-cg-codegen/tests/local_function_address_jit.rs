//! Local typed FnDef addresses must survive page-relative JIT relocation.
//! Native execution coverage, not a claim of Core/proof authority.
#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

use std::collections::HashMap;
use trust_cg_codegen::{Compiler, CompilerConfig, Target, pipeline::OptLevel};
use trust_ir::{BinOp, CallingConv, Constant, Ty};
use trust_ir_build::{ModuleBuilder, validate_module};

fn module() -> trust_ir::Module {
    let mut m = ModuleBuilder::new_with_target_info(
        "local_function_address",
        trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: trust_ir::Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        },
    );
    let sig = m.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let spacer_sig = m.add_func_type(vec![Ty::Ptr], vec![]);
    let wrapper_sig = m.add_func_type(vec![Ty::U64, Ty::Ptr], vec![]);
    // Layout forces both negative and positive ADRP page deltas, rather than
    // succeeding accidentally with zero pages in a tiny one-page image.
    let early = m.declare_function("early", sig);
    let before = m.declare_function("before", spacer_sig);
    let wrapper = m.declare_function("materialize_and_call", wrapper_sig);
    let after = m.declare_function("after", spacer_sig);
    let late = m.declare_function("late", sig);
    for (id, mask) in [
        (early, 0xfedc_ba98_7654_3210u64),
        (late, 0x1234_5678_9abc_def0),
    ] {
        let mut f = m.define_function(id).unwrap();
        f.set_calling_conv(CallingConv::Fast);
        let entry = f.create_block();
        let value = f.add_block_param(entry, Ty::U64);
        f.switch_to_block(entry);
        let mask = f.iconst(Ty::U64, i128::from(mask));
        let result = f.binop(BinOp::Xor, Ty::U64, value, mask);
        f.ret(vec![result]);
        f.build();
    }
    for id in [before, after] {
        let mut f = m.define_function(id).unwrap();
        let entry = f.create_block();
        let pointer = f.add_block_param(entry, Ty::Ptr);
        f.switch_to_block(entry);
        for _ in 0..1100 {
            f.load_volatile(Ty::U64, pointer);
        }
        f.ret(vec![]);
        f.build();
    }
    let mut f = m.define_function(wrapper).unwrap();
    let entry = f.create_block();
    let seed = f.add_block_param(entry, Ty::U64);
    let output = f.add_block_param(entry, Ty::Ptr);
    f.switch_to_block(entry);
    for (slot, callee) in [early, late].into_iter().enumerate() {
        let callback = f.const_value(Ty::Func(sig), Constant::FnDef(callee));
        let address_slot = f.gep_byte_offset(output, (slot * 16) as u64);
        f.store_volatile(Ty::Func(sig), address_slot, callback);
        // The ordinary memory roundtrip prevents static FnDef recovery from
        // deleting the runtime indirect call being tested.
        let callback = f.load_volatile(Ty::Func(sig), address_slot);
        let [value] = f.call_indirect_results_cc::<1>(callback, sig, vec![seed], CallingConv::Fast);
        let result_slot = f.gep_byte_offset(output, (slot * 16 + 8) as u64);
        f.store_volatile(Ty::U64, result_slot, value);
    }
    f.ret(vec![]);
    f.build();
    let mut m = m.build().expect("ModuleBuilder::build: test fixture");
    for function in &mut m.functions {
        if function.id == early || function.id == late {
            function.linkage = trust_ir::Linkage::Internal;
        }
    }
    assert_eq!(validate_module(&m), []);
    m
}

#[test]
fn typed_local_callbacks_materialize_across_pages_and_execute_indirectly() {
    for opt in [OptLevel::O0, OptLevel::O2, OptLevel::O3] {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt;
        let result = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module(), &HashMap::new())
            .unwrap_or_else(|error| panic!("{opt:?}: {error}"));
        let buffer = result.buffer;
        let offsets = buffer.symbol_offsets();
        assert!(offsets["materialize_and_call"] - offsets["early"] > 4096);
        assert!(offsets["late"] - offsets["materialize_and_call"] > 4096);
        let early = buffer.get_fn_ptr_bound("early").unwrap().as_ptr() as u64;
        let late = buffer.get_fn_ptr_bound("late").unwrap().as_ptr() as u64;
        type Entry = extern "C" fn(u64, *mut u64);
        // SAFETY: exact outer C signature and retained owning executable image.
        let entry = unsafe { buffer.get_fn_bound::<Entry>("materialize_and_call") }.unwrap();
        let start = offsets["materialize_and_call"] as usize;
        let end = offsets["after"] as usize;
        // SAFETY: read only this symbol's retained executable image extent.
        let pointer = buffer.get_fn_ptr_bound("materialize_and_call").unwrap();
        let words = unsafe {
            std::slice::from_raw_parts(pointer.as_ptr().cast::<u32>(), (end - start) / 4)
        };
        let indirect_calls = words
            .iter()
            .filter(|&&word| word & 0xffff_fc1f == 0xd63f_0000)
            .count();
        assert!(
            indirect_calls >= 2,
            "{opt:?}: runtime BLR edges must remain"
        );
        for n in 0..100_u64 {
            let seed = n.wrapping_mul(0x9e37_79b9_7f4a_7c15);
            let mut output = [0; 4];
            entry.as_ref()(seed, output.as_mut_ptr());
            assert_eq!(
                output,
                [
                    early,
                    seed ^ 0xfedc_ba98_7654_3210,
                    late,
                    seed ^ 0x1234_5678_9abc_def0
                ],
                "{opt:?} seed={seed}"
            );
        }
    }
}

extern "C" fn interposed_callback(_: u64) -> u64 {
    0xbad
}

#[test]
fn exact_local_callbacks_ignore_same_name_external_and_underscore_overrides() {
    for opt in [OptLevel::O0, OptLevel::O2, OptLevel::O3] {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt;
        let external = ["early", "_early", "late", "_late"]
            .into_iter()
            .map(|name| (name.to_owned(), interposed_callback as *const u8))
            .collect();
        let result = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&module(), &external)
            .unwrap_or_else(|error| panic!("{opt:?}: {error}"));
        let buffer = result.buffer;
        type Entry = extern "C" fn(u64, *mut u64);
        // SAFETY: fixture's exact C entry ABI and retained owning image.
        let entry = unsafe { buffer.get_fn_bound::<Entry>("materialize_and_call") }.unwrap();
        let early = buffer.get_fn_ptr_bound("early").unwrap().as_ptr() as u64;
        let late = buffer.get_fn_ptr_bound("late").unwrap().as_ptr() as u64;
        let mut output = [0; 4];
        entry.as_ref()(77, output.as_mut_ptr());
        assert_eq!(
            output,
            [
                early,
                77 ^ 0xfedc_ba98_7654_3210,
                late,
                77 ^ 0x1234_5678_9abc_def0
            ]
        );
    }
}

#[test]
#[cfg(feature = "verify")]
fn compiler_proof_requests_cannot_publish_unreplayed_local_page_fixups() {
    use trust_cg_codegen::{CompileError, JitError, compiler::JitValidationMode};
    // Only address materialization/return is needed here. Volatile memory in
    // the execution fixture is independently unproved and would reject before
    // reaching the relocation publication boundary this regression exercises.
    let mut m = ModuleBuilder::new_with_target_info(
        "local_function_proof_policy",
        module().target_info.unwrap(),
    );
    let sig = m.add_func_type(vec![], vec![Ty::U64]);
    let mut f = m.function("target", sig);
    let entry = f.create_block();
    f.switch_to_block(entry);
    let value = f.iconst(Ty::U64, 42);
    f.ret(vec![value]);
    let target = f.build();
    let address_sig = m.add_func_type(vec![], vec![Ty::Func(sig)]);
    let mut f = m.function("address", address_sig);
    let entry = f.create_block();
    f.switch_to_block(entry);
    let address = f.const_value(Ty::Func(sig), Constant::FnDef(target));
    f.ret(vec![address]);
    f.build();
    let input = m.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&input), []);
    for (emit_proofs, mode) in [
        (false, JitValidationMode::AlwaysVerify),
        (true, JitValidationMode::Unchecked),
        (true, JitValidationMode::AlwaysVerify),
    ] {
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = OptLevel::O0;
        config.emit_proofs = emit_proofs;
        config.jit_validation_mode_override = Some(mode);
        let error = Compiler::new(config)
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&input, &HashMap::new())
            .expect_err("no executable image without relocation replay");
        // Without proof emission the image reaches publication and is refused
        // at the relocation-replay boundary. With `emit_proofs`, object-proof
        // promotion runs first and, since E0.2, refuses this module's
        // uncredited rows by name (the ADRP/ADD page pair's registry-name
        // evidence, frame and constant rows without an independently replayed
        // certificate), so publication is refused before that boundary.
        let refused_at_relocation = matches!(
            error,
            CompileError::Jit(JitError::LocalFunctionAddressReplayUnavailable { .. })
        );
        let refused_at_promotion = emit_proofs
            && matches!(
                &error,
                CompileError::ProofPromotionRejected {
                    target: Target::Aarch64,
                    reason,
                } if reason.contains("non_verified proof entry")
                    && (reason.contains(" in address:") || reason.contains(" in target:"))
            );
        assert!(
            refused_at_relocation || refused_at_promotion,
            "emit_proofs={emit_proofs} mode={mode:?}: {error}"
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
