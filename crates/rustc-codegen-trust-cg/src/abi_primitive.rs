// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! Format-aware classification for the existing ABI machinery. This is not
//! admission of every IEEE width: each consumer keeps its own carrier limits.

use rustc_abi::{Float, RegKind};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum RegisterFile {
    Integer,
    Float,
    Vector,
}

/// The original descriptor stays at the caller. A vector's element hint is
/// optimization-only in rustc's contract; it does not choose a register file.
pub(super) fn register_file(kind: RegKind) -> Result<RegisterFile, &'static str> {
    match kind {
        RegKind::Integer => Ok(RegisterFile::Integer),
        RegKind::Float => Ok(RegisterFile::Float),
        RegKind::Vector {
            hint_vector_elem: _,
        } => Ok(RegisterFile::Vector),
        #[cfg(rustc_ppc_f128_register)]
        RegKind::PpcF128 => Err(
            "`RegKind::PpcF128` (IBM double-double uses two f64 registers); this ABI carrier is not implemented",
        ),
    }
}

/// Preserve IEEE format identity before using a byte width. bfloat16 and
/// IBM double-double must never alias IEEE half or IEEE binary128 carriers.
pub(super) fn ieee_bits(float: Float) -> Result<u64, &'static str> {
    match float {
        Float::F16 => Ok(16),
        Float::F32 => Ok(32),
        Float::F64 => Ok(64),
        Float::F128 => Ok(128),
        #[cfg(rustc_extended_float_formats)]
        Float::F16B => {
            Err("`Float::F16B` (bfloat16); an IEEE f16 carrier would change the floating format")
        }
        #[cfg(rustc_extended_float_formats)]
        Float::PpcF128 => Err(
            "`Float::PpcF128` (IBM double-double); an IEEE f128 carrier would change the floating format",
        ),
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        aapcs64_hfa, abi_primitive, abi_reg_lanes, indirect_abi, scalar_abi_admission, scalar_pair,
    };
    use rustc_abi::{BackendRepr, Float, HasDataLayout, Primitive, RegKind, Scalar};
    #[cfg(rustc_ppc_f128_register)]
    use rustc_abi::{Reg, Size};
    #[cfg(rustc_ppc_f128_register)]
    use rustc_target::callconv::CastTarget;
    use rustc_target::callconv::{ArgAttributes, PassMode};
    use trust_cg_lower::Type as LowerType;
    use trust_ir::Ty;

    struct Dl(rustc_abi::TargetDataLayout);
    impl HasDataLayout for Dl {
        fn data_layout(&self) -> &rustc_abi::TargetDataLayout {
            &self.0
        }
    }
    fn floats() -> Vec<Float> {
        let values = vec![Float::F16, Float::F32, Float::F64, Float::F128];
        #[cfg(rustc_extended_float_formats)]
        let values = {
            let mut v = values;
            v.extend([Float::F16B, Float::PpcF128]);
            v
        };
        values
    }
    fn unsupported(float: Float) -> bool {
        #[cfg(rustc_extended_float_formats)]
        if matches!(float, Float::F16B | Float::PpcF128) {
            return true;
        }
        let _ = float;
        false
    }
    fn scalar(float: Float) -> Scalar {
        Scalar::Initialized {
            value: Primitive::Float(float),
            valid_range: rustc_abi::WrappingRange::full(float.size()),
        }
    }

    #[test]
    fn every_float_keeps_its_format_in_production_placement_and_values() {
        let dl = Dl(rustc_abi::TargetDataLayout::default());
        let direct = PassMode::Direct(ArgAttributes::new());
        for float in floats() {
            let scalar = scalar(float);
            let repr = BackendRepr::Scalar(scalar);
            let bytes = float.size().bytes();
            let placement = abi_reg_lanes::rustc_placement(
                &dl,
                &direct,
                repr,
                bytes,
                "[MODEL-FLOAT]",
                "argument",
            );
            let values = abi_reg_lanes::rustc_backend_values(&dl, &direct, repr, bytes, bytes);
            let lane = scalar_abi_admission::scalar_pair_lane_ty(Primitive::Float(float));
            if unsupported(float) {
                assert!(
                    abi_primitive::ieee_bits(float).is_err(),
                    "special format aliased as IEEE"
                );
                assert!(
                    placement.unwrap_err().contains(&format!("{float:?}")),
                    "named format refusal"
                );
                assert!(
                    values.is_err(),
                    "special-format scalar was given an IEEE backend value"
                );
                assert!(
                    lane.is_none(),
                    "special-format pair lane was given an IEEE carrier"
                );
            } else {
                assert_eq!(abi_primitive::ieee_bits(float).unwrap(), bytes * 8);
                let abi_reg_lanes::ReturnPlacement::Registers(lanes) = placement.unwrap().unwrap()
                else {
                    panic!("IEEE scalar register control")
                };
                assert_eq!(lanes.len(), 1);
                assert_eq!(lanes[0].class, abi_reg_lanes::AbiRegClass::Float);
                assert_eq!(lanes[0].bytes, bytes);
                let expected = match float {
                    Float::F16 => Some(LowerType::F16),
                    Float::F32 => Some(LowerType::F32),
                    Float::F64 => Some(LowerType::F64),
                    _ => None,
                };
                match expected {
                    Some(ty) => {
                        let values = values.unwrap();
                        assert_eq!(values.len(), 1);
                        assert_eq!(values[0].ty, ty);
                    }
                    None => assert!(
                        values.is_err(),
                        "existing unsupported IEEE width must not gain a carrier"
                    ),
                }
                assert_eq!(
                    lane,
                    match float {
                        Float::F32 => Some(Ty::F32),
                        Float::F64 => Some(Ty::F64),
                        _ => None,
                    }
                );
            }
        }
    }

    #[test]
    fn unsupported_float_pairs_remain_recognized_and_refuse_without_integer_fallthrough() {
        let dl = Dl(rustc_abi::TargetDataLayout::default());
        let mode = PassMode::Pair(ArgAttributes::new(), ArgAttributes::new());
        for float in floats() {
            let s = scalar(float);
            let repr = scalar_pair::canonical(s, s, &dl);
            let bytes = float.size().bytes();
            assert!(
                aapcs64_hfa::is_float_scalar_pair(&dl, &mode, repr),
                "retain floating classification"
            );
            let plan = aapcs64_hfa::float_scalar_pair_carrier(
                &dl,
                &mode,
                repr,
                bytes * 2,
                bytes,
                Some((bytes * 2, bytes, false)),
            );
            if unsupported(float) {
                assert!(
                    plan.unwrap_err().contains(&format!("{float:?}")),
                    "named pair-format refusal"
                );
                assert!(
                    abi_reg_lanes::rustc_placement(
                        &dl,
                        &mode,
                        repr,
                        bytes * 2,
                        "[MODEL-PAIR]",
                        "argument"
                    )
                    .is_err()
                );
                assert!(
                    abi_reg_lanes::rustc_backend_values(&dl, &mode, repr, bytes * 2, bytes)
                        .is_err()
                );
            } else if matches!(float, Float::F32 | Float::F64) {
                let plan = plan.unwrap().unwrap();
                assert_eq!(plan.lane_bytes, bytes);
                assert_eq!(plan.lanes, 2);
                assert_eq!(
                    plan.carrier_ty(),
                    Ty::Tuple(vec![
                        scalar_abi_admission::scalar_pair_lane_ty(
                            Primitive::Float(float)
                        )
                        .unwrap();
                        2
                    ])
                );
            } else {
                assert!(plan.is_err(), "retain old half/quad pair refusal");
            }
        }
    }

    #[test]
    fn register_file_controls_retain_ordinary_files_and_vector_hints() {
        use abi_primitive::RegisterFile;
        assert_eq!(
            abi_primitive::register_file(RegKind::Integer).unwrap(),
            RegisterFile::Integer
        );
        assert_eq!(
            abi_primitive::register_file(RegKind::Float).unwrap(),
            RegisterFile::Float
        );
        for float in floats() {
            let hint = Primitive::Float(float);
            let kind = RegKind::Vector {
                hint_vector_elem: hint,
            };
            assert_eq!(
                abi_primitive::register_file(kind).unwrap(),
                RegisterFile::Vector
            );
            let RegKind::Vector { hint_vector_elem } = kind else {
                unreachable!()
            };
            assert_eq!(
                hint_vector_elem, hint,
                "classification does not rewrite original descriptor"
            );
        }
        // Also exercise the unchanged valid pointer/metadata distinction.
        let mode = indirect_abi::fixture(ArgAttributes::new(), None, false);
        let view = indirect_abi::checked(&mode).unwrap().unwrap();
        assert!(view.is_sized_pointer());
        assert_eq!(*view.attrs, ArgAttributes::new(), "retain data attributes");
        let dl = Dl(rustc_abi::TargetDataLayout::default());
        let placement = abi_reg_lanes::rustc_placement(
            &dl,
            &mode,
            BackendRepr::Memory { sized: true },
            32,
            "[MODEL-POINTER]",
            "argument",
        )
        .unwrap()
        .unwrap();
        assert!(placement.is_caller_buffer());
        use abi_reg_lanes::{ArgPlacementVerdict, ReturnPlacement, arg_memory_placement_verdict};
        for (placement, needle) in [
            (None, "arity"),
            (Some(ReturnPlacement::CallerBuffer), "POINTER"),
            (Some(ReturnPlacement::StackByValue), "BY VALUE"),
        ] {
            let ArgPlacementVerdict::Refuse(reason) =
                arg_memory_placement_verdict(None, false, placement, false)
            else {
                panic!("retain unsupported placement refusal")
            };
            assert!(
                reason
                    .describe()
                    .to_ascii_uppercase()
                    .contains(&needle.to_ascii_uppercase())
            );
        }
    }

    #[cfg(rustc_ppc_f128_register)]
    #[test]
    fn ibm_registers_refuse_in_prefix_rest_backend_values_and_scalar_declarations() {
        let dl = Dl(rustc_abi::TargetDataLayout::default());
        for prefix in [false, true] {
            let reg = Reg {
                kind: RegKind::PpcF128,
                size: Size::from_bytes(16),
            };
            let mut target = CastTarget::from(reg);
            if prefix {
                target = CastTarget::from(Reg::f64());
                target.prefix.push(reg);
            }
            let mode = crate::cast_abi::fixture(target, false);
            let repr = BackendRepr::Memory { sized: true };
            let why =
                abi_reg_lanes::rustc_placement(&dl, &mode, repr, 32, "[MODEL-REG]", "argument")
                    .unwrap_err();
            assert!(why.contains("PpcF128"), "{why}");
            let why = abi_reg_lanes::rustc_backend_values(&dl, &mode, repr, 32, 16).unwrap_err();
            assert!(why.contains("PpcF128"), "{why}");
            for ty in [Ty::F32, Ty::F64, Ty::I64, Ty::U8] {
                let why =
                    scalar_abi_admission::scalar_declared_mode_disagreement(&mode, &ty).unwrap();
                assert!(why.contains("PpcF128"), "{why}");
            }
        }
    }
}
