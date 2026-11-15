//! A single integer `Cast` aggregate argument travels as a scalar, not a C
//! composite. On Darwin the distinction affects later stack arguments.
//!
//! rustc emits `iN` for the one exact integer register in this plan. LLVM
//! allocates an i24 as four bytes, so its trust-ir carrier is U32; only the
//! three live bytes are packed or unpacked by the bridge. Neither the original
//! byte slot nor C aggregate classification changes.

use rustc_abi::RegKind;
use rustc_target::callconv::{ArgAttribute, ArgExtension, PassMode};
use trust_ir::Ty;

#[derive(Clone, Debug)]
pub(super) struct IntegerCastCarrier {
    pub(super) ty: Ty,
    pub(super) live_bytes: u64,
}

pub(super) fn plan(mode: &PassMode, rust_size: u64) -> Option<IntegerCastCarrier> {
    let view = crate::cast_abi::view(mode)?;
    let cast = view.target;
    if view.has_padding()
        || !cast.prefix.is_empty()
        || cast.rest_offset.is_some()
        || cast.rest.unit.kind != RegKind::Integer
        || cast.rest.unit.size.bytes() != rust_size
        || cast.rest.total.bytes() != rust_size
        || cast.attrs.contains(ArgAttribute::InReg)
        || cast.attrs.arg_ext != ArgExtension::None
    {
        return None;
    }
    let ty = match rust_size {
        1 => Ty::U8,
        2 => Ty::U16,
        3..=4 => Ty::U32,
        5..=8 => Ty::U64,
        _ => return None,
    };
    Some(IntegerCastCarrier {
        ty,
        live_bytes: rust_size,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_abi::{Reg, Size};
    use rustc_target::callconv::CastTarget;
    use trust_cg_lower::Type;
    use trust_cg_lower::abi::{AArch64AbiVariant, AppleAArch64ABI, ArgLocation};

    fn cast(bytes: u64) -> PassMode {
        crate::cast_abi::fixture(
            CastTarget::from(Reg {
                kind: RegKind::Integer,
                size: Size::from_bytes(bytes),
            }),
            false,
        )
    }

    #[test]
    fn single_integer_cast_carriers_preserve_live_extent() {
        for (bytes, ty) in [
            (1, Ty::U8),
            (2, Ty::U16),
            (3, Ty::U32),
            (4, Ty::U32),
            (5, Ty::U64),
            (6, Ty::U64),
            (7, Ty::U64),
            (8, Ty::U64),
        ] {
            let carrier = plan(&cast(bytes), bytes).unwrap();
            assert_eq!(carrier.ty, ty);
            assert_eq!(carrier.live_bytes, bytes);
        }
        for bytes in [0, 9, 16] {
            assert!(plan(&cast(bytes), bytes).is_none());
        }
    }

    #[test]
    fn special_or_nonexact_casts_keep_the_existing_path() {
        for change in 0..8 {
            let mut mode = cast(3);
            if change == 0 {
                crate::cast_abi::fixture_padding(&mut mode, true);
            }
            let PassMode::Cast { cast, .. } = &mut mode else {
                unreachable!()
            };
            match change {
                0 => (),
                1 => {
                    cast.prefix.push(Reg::i32());
                }
                2 => cast.rest_offset = Some(Size::from_bytes(4)),
                3 => cast.rest.unit.kind = RegKind::Float,
                4 => cast.rest.unit.size = Size::from_bytes(4),
                5 => cast.rest.total = Size::from_bytes(4),
                6 => {
                    cast.attrs.set(ArgAttribute::InReg);
                }
                7 => cast.attrs.arg_ext = ArgExtension::Zext,
                _ => unreachable!(),
            }
            assert!(plan(&mode, 3).is_none(), "case {change}");
        }
        assert!(
            plan(
                &PassMode::Direct(rustc_target::callconv::ArgAttributes::new()),
                3
            )
            .is_none()
        );
    }

    // Grounded in real FnABI+LLVM assembly: array2 is i16, struct3 is i24,
    // array4 is i32, and their trailing Darwin u32 is at incoming sp+4.
    // The historical C composite puts it at sp+8, including i24's three bytes.
    #[test]
    fn exhausted_cast_stack_slots_match_llvm_and_preserve_aapcs64() {
        for bytes in [2, 3, 4] {
            let carrier = plan(&cast(bytes), bytes).unwrap();
            let scalar = match carrier.ty {
                Ty::U16 => Type::I16,
                Ty::U32 => Type::I32,
                _ => unreachable!(),
            };
            for prior in [0, 7, 8, 9] {
                for variant in [AArch64AbiVariant::Darwin, AArch64AbiVariant::Aapcs64] {
                    let mut params = vec![Type::I64; prior];
                    params.extend([scalar.clone(), Type::I32]);
                    let locs = AppleAArch64ABI::classify_params_with(variant, &params);
                    if prior < 7 {
                        assert!(matches!(locs[prior], ArgLocation::Reg(_)));
                        assert!(matches!(locs[prior + 1], ArgLocation::Reg(_)));
                    } else if prior == 7 {
                        assert!(matches!(locs[prior], ArgLocation::Reg(_)));
                        assert!(matches!(
                            locs[prior + 1],
                            ArgLocation::Stack { offset: 0, .. }
                        ));
                    } else {
                        let start = ((prior - 8) * 8) as i64;
                        let next = start
                            + if variant == AArch64AbiVariant::Darwin {
                                4
                            } else {
                                8
                            };
                        assert!(
                            matches!(locs[prior], ArgLocation::Stack { offset, .. } if offset == start)
                        );
                        assert!(
                            matches!(locs[prior + 1], ArgLocation::Stack { offset, .. } if offset == next)
                        );
                    }
                }
            }
            let mut old = vec![Type::I64; 8];
            old.extend([Type::Struct(vec![Type::I8; bytes as usize]), Type::I32]);
            let old = AppleAArch64ABI::classify_params_with(AArch64AbiVariant::Darwin, &old);
            assert!(matches!(old[9], ArgLocation::Stack { offset: 8, .. }));
        }
    }
}
