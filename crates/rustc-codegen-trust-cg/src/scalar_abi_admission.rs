// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! The scalar declaration and scalar-pair lane admission decisions, shared by
//! the bridge and actual private-API model tests. Consumer scope stays separate.

use trust_ir::Ty as TrustIrTy;

pub(super) fn scalar_declared_mode_disagreement(
    mode: &rustc_target::callconv::PassMode,
    declared: &TrustIrTy,
) -> Option<String> {
    use rustc_target::callconv::PassMode;
    match crate::indirect_abi::checked(mode) {
        Err(reason) => return Some(reason),
        Ok(Some(view)) => {
            return Some(if view.kind == crate::indirect_abi::Kind::OnStack {
                "as a by-value copy in the outgoing argument area (`byval`)".to_owned()
            } else if view.meta_attrs.is_some() {
                "through an unsized data POINTER and a separate metadata value".to_owned()
            } else {
                "through a caller-made copy addressed by a POINTER (an argument's pointer, or a \
             return's hidden `sret` buffer)"
                    .to_owned()
            });
        }
        Ok(None) => {}
    }
    let declared_is_float = matches!(declared, TrustIrTy::F32 | TrustIrTy::F64);
    match mode {
        PassMode::Cast { .. } => {
            let Some(view) = crate::cast_abi::view(mode) else {
                return Some("a `PassMode::Cast` whose payload could not be read".to_owned());
            };
            if let Some(reason) = view.padding_refusal() {
                return Some(reason);
            }
            let cast = view.target;
            let kinds = cast
                .prefix
                .iter()
                .map(|reg| reg.kind)
                .chain(std::iter::once(cast.rest.unit.kind));
            let mut other_file = false;
            for kind in kinds {
                use crate::abi_primitive::{RegisterFile, register_file};
                other_file |= match register_file(kind) {
                    Ok(RegisterFile::Integer) => declared_is_float,
                    Ok(RegisterFile::Float) => !declared_is_float,
                    Ok(RegisterFile::Vector) => true,
                    Err(why) => return Some(why.to_owned()),
                };
            }
            other_file.then(|| {
                format!(
                    "in {} (a `Cast`), not the {} register a {declared:?} carrier rides",
                    if declared_is_float {
                        "a GENERAL-PURPOSE register"
                    } else {
                        "a floating-point / vector register"
                    },
                    if declared_is_float {
                        "floating-point"
                    } else {
                        "general-purpose"
                    }
                )
            })
        }
        _ => None,
    }
}

pub(super) fn scalar_pair_lane_ty(primitive: rustc_abi::Primitive) -> Option<TrustIrTy> {
    use rustc_abi::{Integer, Primitive};
    Some(match primitive {
        Primitive::Int(Integer::I8, _) => TrustIrTy::I8,
        Primitive::Int(Integer::I16, _) => TrustIrTy::I16,
        Primitive::Int(Integer::I32, _) => TrustIrTy::I32,
        Primitive::Int(Integer::I64, _) => TrustIrTy::I64,
        Primitive::Int(Integer::I128, _) => return None,
        Primitive::Pointer(_) => TrustIrTy::Ptr,
        Primitive::Float(float) => match crate::abi_primitive::ieee_bits(float).ok()? {
            32 => TrustIrTy::F32,
            64 => TrustIrTy::F64,
            _ => return None,
        },
    })
}

#[cfg(test)]
mod tests {
    /// The scalar arms' refusal (`refuse_scalar_declared_memory_arg`,
    /// `check_scalar_return_abi`) reads ONE fact from rustc's mode: whether a
    /// carrier of the declared scalar's type lands where rustc puts the value.
    /// Pins the shapes measured 2026-09-28 — a padded scalar rustc passes by
    /// pointer (or returns through the hidden buffer) or as a `byval` copy, and a
    /// padded `f32` rustc casts to an INTEGER register — and the ones that agree:
    /// a narrower integer scalar inside an integer cast (the extra bytes are the
    /// `repr(align)` padding) and a float scalar inside a float cast (an
    /// `extern "C"` `struct { f32 }`).
    #[test]
    fn a_scalar_declaration_disagrees_with_indirect_and_cross_file_casts() {
        use super::scalar_declared_mode_disagreement;
        use rustc_abi::Reg;
        use rustc_target::callconv::{ArgAttributes, CastTarget, PassMode};
        use trust_ir::Ty as TrustIrTy;
        let indirect =
            |on_stack| crate::indirect_abi::fixture(ArgAttributes::new(), None, on_stack);
        let cast = |reg| crate::cast_abi::fixture(CastTarget::from(reg), false);
        for declared in [TrustIrTy::U64, TrustIrTy::U8, TrustIrTy::F64] {
            assert!(scalar_declared_mode_disagreement(&indirect(false), &declared).is_some());
            assert!(scalar_declared_mode_disagreement(&indirect(true), &declared).is_some());
        }
        assert!(scalar_declared_mode_disagreement(&cast(Reg::i64()), &TrustIrTy::F32).is_some());
        assert!(scalar_declared_mode_disagreement(&cast(Reg::f64()), &TrustIrTy::U64).is_some());
        assert!(scalar_declared_mode_disagreement(&cast(Reg::i64()), &TrustIrTy::U32).is_none());
        assert!(scalar_declared_mode_disagreement(&cast(Reg::f32()), &TrustIrTy::F32).is_none());
        assert!(
            scalar_declared_mode_disagreement(
                &PassMode::Direct(ArgAttributes::new()),
                &TrustIrTy::F32
            )
            .is_none()
        );
    }

    #[test]
    fn scalar_declarations_reject_padding_in_matching_register_files() {
        use super::scalar_declared_mode_disagreement;
        use rustc_abi::Reg;
        use rustc_target::callconv::CastTarget;
        let mut controls = 0;
        let mut refusals = 0;
        let mut missing = Vec::new();
        for (name, reg, declared) in [
            ("integer", Reg::i64(), trust_ir::Ty::U32),
            ("float", Reg::f32(), trust_ir::Ty::F32),
        ] {
            for padded in [false, true] {
                let mode = crate::cast_abi::fixture(CastTarget::from(reg), padded);
                let disagreement = scalar_declared_mode_disagreement(&mode, &declared);
                if padded {
                    match disagreement {
                        Some(reason) => {
                            assert!(reason.contains("padding"), "{reason}");
                            refusals += 1;
                        }
                        None => missing.push(name),
                    }
                } else {
                    assert!(disagreement.is_none(), "unpadded {name}: {disagreement:?}");
                    controls += 1;
                }
            }
        }
        println!(
            "CAST_SCALAR_PADDING controls={controls} refusals={refusals} missing={}",
            missing.len()
        );
        assert!(
            missing.is_empty(),
            "padded scalar casts admitted: {missing:?}"
        );
        assert_eq!((controls, refusals), (2, 2));
    }
}
