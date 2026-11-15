// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
// Query actual FnABIs, then test full count/payload transport with synthetic
// descriptors. Stop before input codegen; neither family establishes support
// for emitting leading dummy arguments or otherwise unsupported cast targets.
#![feature(rustc_private)]
extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_target;
extern crate trust_ir;

#[path = "../../../src/aapcs64_hfa.rs"]
mod aapcs64_hfa;
#[path = "../../../src/cast_abi.rs"]
mod cast_abi;
#[path = "../../../src/integer_cast_args.rs"]
mod integer_cast_args;
#[path = "../../../src/scalar_pair.rs"]
mod scalar_pair;

use rustc_abi::{Align, Reg, Size};
use rustc_driver::{Callbacks, Compilation};
use rustc_middle::ty::{self, TyCtxt};
use rustc_target::callconv::{
    ArgAttribute, ArgAttributes, ArgExtension, CastTarget, PassMode, Uniform,
};

struct Audit;

fn check(mode: &PassMode, target: &CastTarget, expected: u8) {
    let view = cast_abi::view(mode).expect("cast descriptor must remain a cast");
    assert_eq!(view.padding_words, expected, "exact leading argument count");
    assert_eq!(
        view.target, target,
        "complete cast payload including attributes"
    );
    assert!(
        std::ptr::eq(view.target, target),
        "borrow the original cast target"
    );
    assert_eq!(
        view.has_padding(),
        expected != 0,
        "all nonzero padding is unsupported"
    );
    let refusal = view.padding_refusal();
    match expected {
        0 => assert!(
            refusal.is_none(),
            "unpadded cast must retain its existing path"
        ),
        1 => assert_eq!(
            refusal.as_deref(),
            Some("`PassMode::Cast` with a `pad_i32` padding register")
        ),
        count => assert_eq!(
            refusal,
            Some(format!(
                "`PassMode::Cast` with {count} `pad_i32` padding registers"
            ))
        ),
    }
}

fn targets() -> Vec<CastTarget> {
    let mut offset = CastTarget::offset_pair(Reg::i32(), Size::from_bytes(12), Reg::f64());
    offset.attrs.arg_ext = ArgExtension::Zext;
    let mut rich = CastTarget::from(Uniform::new(Reg::i64(), Size::from_bytes(13)));
    for index in 0..8 {
        rich.prefix.push(if index % 2 == 0 {
            Reg::f32()
        } else {
            Reg::i64()
        });
    }
    rich.rest_offset = Some(Size::from_bytes(64));
    rich.attrs
        .set(ArgAttribute::InReg)
        .set(ArgAttribute::NoAlias)
        .set(ArgAttribute::NonNull)
        .set(ArgAttribute::ReadOnly);
    rich.attrs.arg_ext = ArgExtension::Sext;
    rich.attrs.pointee_size = Size::from_bytes(17);
    rich.attrs.pointee_align = Some(Align::from_bytes(16).unwrap());
    vec![
        CastTarget::from(Reg::i64()),
        CastTarget::from(Uniform::new(Reg::i32(), Size::from_bytes(3))),
        CastTarget::from(Uniform::consecutive(Reg::f32(), Size::from_bytes(8))),
        CastTarget::from(Uniform::consecutive(Reg::f64(), Size::from_bytes(32))),
        offset,
        rich,
    ]
}

fn check_carriers(mode: &PassMode, target: &CastTarget, index: usize, count: u8) {
    let integer = integer_cast_args::plan(mode, target.rest.total.bytes());
    if index == 0 && count == 0 {
        let integer = integer.expect("existing exact integer carrier");
        assert_eq!(integer.ty, trust_ir::Ty::U64);
        assert_eq!(integer.live_bytes, 8);
    } else {
        assert!(
            integer.is_none(),
            "padded or otherwise unsupported integer cast admitted"
        );
    }
    let float = index >= 2;
    assert_eq!(
        aapcs64_hfa::is_float_cast(mode),
        float,
        "float classification includes padded requests"
    );
    let size = target.rest.total.bytes();
    let align = target.rest.unit.size.bytes();
    let plan =
        aapcs64_hfa::plan_from_pass_mode(mode, size, align, Some((size, align, false)), None);
    if !float {
        assert!(plan.unwrap().is_none());
    } else if matches!(index, 2 | 3) && count == 0 {
        let plan = plan.unwrap().expect("existing exact HFA carrier");
        let (lane, integer, lanes, bytes) = if index == 2 {
            (trust_ir::Ty::F32, trust_ir::Ty::I32, 2, 4)
        } else {
            (trust_ir::Ty::F64, trust_ir::Ty::I64, 4, 8)
        };
        assert_eq!(plan.integer_lane_ty, integer);
        assert_eq!(plan.lanes, lanes);
        assert_eq!(plan.lane_bytes, bytes);
        assert!(!plan.scalarized);
        assert_eq!(plan.carrier_ty(), trust_ir::Ty::Tuple(vec![lane; lanes]));
        assert!(!plan.scalar_projection_layout_matches(1, 0, 0, bytes, bytes));
    } else {
        let refusal = plan.expect_err("padded or malformed float cast must refuse");
        assert!(refusal.starts_with("[TCG-AAPCS64-HFA]"), "{refusal}");
    }
}

fn check_other_carriers(tcx: TyCtxt<'_>) {
    let target = CastTarget::from(Uniform::consecutive(Reg::f64(), Size::from_bytes(8)));
    #[cfg(rustc_cast_pad_count)]
    let mode = PassMode::Cast {
        cast: Box::new(target),
        pad_i32_count: 0,
    };
    #[cfg(not(rustc_cast_pad_count))]
    let mode = PassMode::Cast {
        cast: Box::new(target),
        pad_i32: false,
    };
    let scalar = aapcs64_hfa::plan_from_pass_mode(&mode, 8, 8, None, Some(&trust_ir::Ty::F64))
        .unwrap()
        .expect("existing one-lane scalar HFA");
    assert_eq!(scalar.carrier_ty(), trust_ir::Ty::F64);
    assert!(scalar.scalarized);
    assert!(scalar.scalar_projection_layout_matches(1, 0, 0, 8, 8));
    assert!(!scalar.scalar_projection_layout_matches(1, 0, 1, 8, 8));
    let did = tcx
        .iter_local_def_id()
        .map(|local| local.to_def_id())
        .find(|did| {
            tcx.def_kind(*did) == rustc_hir::def::DefKind::TyAlias
                && tcx.item_name(*did).as_str() == "CarrierFloatPair"
        })
        .unwrap();
    let env = ty::TypingEnv::fully_monomorphized();
    let ty = tcx.normalize_erasing_regions(env, tcx.type_of(did).instantiate_identity());
    let layout = tcx.layout_of(env.as_query_input(ty)).unwrap();
    let pair = PassMode::Pair(ArgAttributes::new(), ArgAttributes::new());
    assert!(aapcs64_hfa::is_float_scalar_pair(
        &tcx,
        &pair,
        layout.backend_repr
    ));
    assert!(!aapcs64_hfa::is_float_scalar_pair(
        &tcx,
        &PassMode::Ignore,
        layout.backend_repr
    ));
    let plan = aapcs64_hfa::float_scalar_pair_carrier(
        &tcx,
        &pair,
        layout.backend_repr,
        layout.size.bytes(),
        layout.align.bytes(),
        Some((8, 4, false)),
    )
    .unwrap()
    .unwrap();
    assert_eq!(
        plan.carrier_ty(),
        trust_ir::Ty::Tuple(vec![trust_ir::Ty::F32; 2])
    );
    assert_eq!(plan.integer_lane_ty, trust_ir::Ty::I32);
}

impl Callbacks for Audit {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        assert_eq!(tcx.data_layout.pointer_size().bytes(), 8);
        let env = ty::TypingEnv::fully_monomorphized();
        let mut functions = 0;
        let mut modes = 0;
        let mut casts = 0;
        for local in tcx.iter_local_def_id() {
            let did = local.to_def_id();
            if tcx.def_kind(did) != rustc_hir::def::DefKind::Fn
                || !tcx.item_name(did).as_str().starts_with("case_")
            {
                continue;
            }
            let abi = tcx
                .fn_abi_of_instance(
                    env.as_query_input((ty::Instance::mono(tcx, did), ty::List::empty())),
                )
                .unwrap();
            for arg in abi.args.iter().chain(std::iter::once(&abi.ret)) {
                match &arg.mode {
                    #[cfg(rustc_cast_pad_count)]
                    PassMode::Cast {
                        cast,
                        pad_i32_count,
                    } => {
                        check(&arg.mode, cast.as_ref(), *pad_i32_count);
                        casts += 1;
                    }
                    #[cfg(not(rustc_cast_pad_count))]
                    PassMode::Cast { cast, pad_i32 } => {
                        check(&arg.mode, cast.as_ref(), u8::from(*pad_i32));
                        casts += 1;
                    }
                    _ => assert!(cast_abi::view(&arg.mode).is_none(), "real noncast"),
                }
                modes += 1;
            }
            functions += 1;
            println!(
                "REAL_CAST_ABI function={} casts={casts}",
                tcx.item_name(did)
            );
        }
        assert_eq!(functions, 8);
        assert_eq!(modes, 15);
        assert!(casts >= 4, "required real aggregate casts");
        let mut synthetic = 0;
        for (index, target) in targets().into_iter().enumerate() {
            #[cfg(rustc_cast_pad_count)]
            let counts = 0..=u8::MAX;
            #[cfg(not(rustc_cast_pad_count))]
            let counts = 0..=1u8;
            for count in counts {
                #[cfg(rustc_cast_pad_count)]
                let mode = PassMode::Cast {
                    cast: Box::new(target.clone()),
                    pad_i32_count: count,
                };
                #[cfg(not(rustc_cast_pad_count))]
                let mode = PassMode::Cast {
                    cast: Box::new(target.clone()),
                    pad_i32: count != 0,
                };
                // The expected payload and number are independently retained
                // from the constructor inputs, including every modern u8.
                let original = match &mode {
                    PassMode::Cast { cast, .. } => cast.as_ref(),
                    _ => unreachable!(),
                };
                check(&mode, original, count);
                check_carriers(&mode, original, index, count);
                assert_eq!(original, &target, "payload constructor control");
                synthetic += 1;
            }
        }
        for mode in [
            PassMode::Ignore,
            PassMode::Direct(ArgAttributes::new()),
            PassMode::Pair(ArgAttributes::new(), ArgAttributes::new()),
        ] {
            assert!(cast_abi::view(&mode).is_none(), "synthetic noncast");
        }
        assert_eq!(
            synthetic,
            if cfg!(rustc_cast_pad_count) { 1536 } else { 12 }
        );
        check_other_carriers(tcx);
        println!(
            "CAST_PADDING_QUERIES functions={functions} modes={modes} real_casts={casts} synthetic={synthetic} noncasts=3 count_api={}",
            cfg!(rustc_cast_pad_count)
        );
        Compilation::Stop
    }
}

fn main() {
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Audit);
}
