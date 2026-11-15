//! Actual external C aggregate returns, with canonical TrustIR result-typed
//! field extraction. This tests native bytes, not Core/proof authority.
#![cfg(all(
    target_arch = "aarch64",
    any(target_os = "macos", all(target_os = "linux", target_env = "gnu"))
))]

use std::collections::HashMap;
use trust_cg_codegen::{Compiler, CompilerConfig, CoreHostJitTarget, Target, pipeline::OptLevel};
use trust_ir::{BinOp, CallingConv, FieldDef, StructDef, StructId, StructRepr, Ty};
use trust_ir_build::{ModuleBuilder, validate_module};

#[repr(C)]
struct Pair {
    first: u64,
    second: i64,
}

extern "C" fn pair(seed: u64) -> Pair {
    Pair {
        first: seed ^ 0xfedc_ba98_7654_3210,
        second: seed.rotate_left(17) as i64,
    }
}

const LIVE: usize = 12;

fn module() -> trust_ir::Module {
    let host = CoreHostJitTarget::detect().expect("supported native AArch64 test host");
    let mut m = ModuleBuilder::new_with_target_info(
        "aggregate_call_results",
        host.trust_ir_target_info().clone(),
    );
    let aggregate = Ty::Struct(m.add_struct(StructDef {
        origin: None,
        id: StructId::new(0),
        name: "Pair".into(),
        fields: vec![
            FieldDef {
                name: "first".into(),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "second".into(),
                ty: Ty::I64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::C,
    }));
    let sig = m.add_func_type(vec![Ty::U64], vec![aggregate]);
    let callee = m.declare_function("external_pair", sig);
    for indirect in [false, true] {
        let mut params = vec![Ty::U64, Ty::Ptr, Ty::Ptr];
        if indirect {
            params.push(Ty::Func(sig));
        }
        let wrapper_sig = m.add_func_type(params.clone(), vec![]);
        let mut f = m.function(if indirect { "indirect" } else { "direct" }, wrapper_sig);
        let entry = f.create_block();
        let args: Vec<_> = params
            .into_iter()
            .map(|ty| f.add_block_param(entry, ty))
            .collect();
        f.switch_to_block(entry);
        let mut live = Vec::new();
        for lane in 0..LIVE {
            let pointer = f.gep_byte_offset(args[1], (lane * 8) as u64);
            live.push(f.load_volatile(Ty::U64, pointer));
        }
        let first = if indirect {
            f.call_indirect_results_cc::<1>(args[3], sig, vec![args[0]], CallingConv::C)[0]
        } else {
            f.call_results::<1>(callee, vec![args[0]])[0]
        };
        let seven = f.iconst(Ty::U64, 7);
        let seed = f.binop(BinOp::Add, Ty::U64, args[0], seven);
        let second = if indirect {
            f.call_indirect_results_cc::<1>(args[3], sig, vec![seed], CallingConv::C)[0]
        } else {
            f.call_results::<1>(callee, vec![seed])[0]
        };
        // Read BOTH first-call fields only after the second call. This checks
        // aggregate return storage and its live-across-call address carrier.
        for (i, result) in [first, second].into_iter().enumerate() {
            let a = f.extract_field(Ty::U64, result, 0);
            let b = f.extract_field(Ty::I64, result, 1);
            let pa = f.gep_byte_offset(args[2], (i * 16) as u64);
            let pb = f.gep_byte_offset(args[2], (i * 16 + 8) as u64);
            f.store_volatile(Ty::U64, pa, a);
            f.store_volatile(Ty::I64, pb, b);
        }
        for (i, value) in live.into_iter().enumerate() {
            let pointer = f.gep_byte_offset(args[2], ((i + 4) * 8) as u64);
            f.store_volatile(Ty::U64, pointer, value);
        }
        f.ret(vec![]);
        f.build();
    }
    let m = m.build().expect("ModuleBuilder::build: test fixture");
    assert_eq!(validate_module(&m), []);
    m
}

#[test]
fn external_c_pair_returns_survive_direct_indirect_calls_and_register_pressure() {
    let host = CoreHostJitTarget::detect().expect("supported native AArch64 test host");
    assert_eq!(std::mem::size_of::<Pair>(), 16);
    assert_eq!(std::mem::align_of::<Pair>(), 8);
    for opt in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3] {
        let m = module();
        let mut config = CompilerConfig::jit_fast(Target::Aarch64);
        config.opt_level = opt;
        let symbols = HashMap::from([("external_pair".into(), pair as *const u8)]);
        let compiled = Compiler::new_for_target_spec(config, host.target_spec())
            .with_codegen_license(permit_unlicensed())
            .compile_module_to_jit(&m, &symbols)
            .unwrap_or_else(|err| panic!("{opt:?}: {err}"));
        let buffer = compiled.buffer;
        type Direct = extern "C" fn(u64, *const u64, *mut u64);
        type Indirect = extern "C" fn(u64, *const u64, *mut u64, extern "C" fn(u64) -> Pair);
        // SAFETY: exact declared void-return C wrappers; buffer stays live.
        let direct = unsafe { buffer.get_fn_bound::<Direct>("direct") }.unwrap();
        let indirect = unsafe { buffer.get_fn_bound::<Indirect>("indirect") }.unwrap();
        let live: [u64; LIVE] =
            std::array::from_fn(|i| (i as u64 + 1).wrapping_mul(0x1234_5678_9abc_def0));
        for n in 0..100_u64 {
            let seed = n.wrapping_mul(0x9e37_79b9_7f4a_7c15);
            let a = pair(seed);
            let b = pair(seed.wrapping_add(7));
            let mut expected = [0; LIVE + 4];
            expected[..4].copy_from_slice(&[a.first, a.second as u64, b.first, b.second as u64]);
            expected[4..].copy_from_slice(&live);
            for use_indirect in [false, true] {
                let mut output = [0; LIVE + 4];
                if use_indirect {
                    indirect.as_ref()(seed, live.as_ptr(), output.as_mut_ptr(), pair);
                } else {
                    direct.as_ref()(seed, live.as_ptr(), output.as_mut_ptr());
                }
                assert_eq!(
                    output, expected,
                    "{opt:?} indirect={use_indirect} seed={seed}"
                );
            }
        }
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
