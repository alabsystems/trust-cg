// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! Preserve the fallible constant-pointer contract across private API shapes.

use rustc_abi::HasDataLayout;
use rustc_middle::mir::interpret::{CtfeProvenance, Pointer, Scalar};

pub(super) fn checked<C: HasDataLayout>(
    cx: &C,
    scalar: Scalar,
) -> Option<Pointer<Option<CtfeProvenance>>> {
    // The direct API panics on a size mismatch. The older API reports an
    // interpreter error, which these consumers discard. Preserve that refusal.
    if scalar.size() != cx.data_layout().pointer_size() {
        return None;
    }
    #[cfg(rustc_scalar_direct_pointer)]
    {
        Some(scalar.to_pointer(cx))
    }
    #[cfg(not(rustc_scalar_direct_pointer))]
    {
        scalar.to_pointer(cx).discard_err()
    }
}

#[cfg(test)]
mod tests {
    use crate::constant_pointer;
    use rustc_abi::{HasDataLayout, Size, TargetDataLayout};
    use rustc_middle::mir::interpret::{AllocId, CtfeProvenance, Pointer, Scalar};
    use std::num::NonZeroU64;

    struct Dl(TargetDataLayout);
    impl HasDataLayout for Dl {
        fn data_layout(&self) -> &TargetDataLayout {
            &self.0
        }
    }
    fn dl(bits: u64) -> Dl {
        Dl(TargetDataLayout::parse_from_llvm_datalayout_string(
            &format!("e-p:{bits}:{bits}-i64:64-n8:16:32-S64"),
            rustc_abi::AddressSpace::ZERO,
        )
        .unwrap_or_else(|_| panic!("well-formed 32/64-bit model data layout")))
    }
    fn pointer(id: u64, offset: u64, flags: u8) -> Pointer {
        let provenance = CtfeProvenance::from(AllocId(NonZeroU64::new(id).unwrap()));
        let provenance = match flags {
            0 => provenance,
            1 => provenance.as_shared_ref(),
            2 => provenance.as_immutable(),
            _ => unreachable!(),
        };
        Pointer::new(provenance, Size::from_bytes(offset))
    }

    #[test]
    fn wrong_sizes_refuse_before_the_private_conversion() {
        let mut refused = 0;
        let mut controls = 0;
        for target in [32, 64] {
            let cx = dl(target);
            for bytes in [1, 2, 4, 8, 16] {
                let scalar = Scalar::from_uint(7_u128, Size::from_bytes(bytes));
                let result = constant_pointer::checked(&cx, scalar);
                if bytes * 8 == target {
                    assert!(result.is_some());
                    controls += 1;
                } else {
                    assert!(result.is_none(), "wrong-size integer must refuse");
                    refused += 1;
                }
            }
            let foreign = dl(if target == 32 { 64 } else { 32 });
            let scalar = Scalar::from_pointer(pointer(7, 17, 2), &foreign);
            assert!(constant_pointer::checked(&cx, scalar).is_none());
            refused += 1;
        }
        assert_eq!((controls, refused), (2, 10));
        println!("POINTER_SIZE controls={controls} refusals={refused}");
    }

    #[test]
    fn integer_addresses_do_not_acquire_allocation_provenance() {
        let mut cases = 0;
        for target in [32, 64] {
            let cx = dl(target);
            for address in [0, 1, u32::MAX as u64, u64::MAX] {
                if target == 32 && address > u32::MAX as u64 {
                    continue;
                }
                let scalar = Scalar::from_uint(address, cx.data_layout().pointer_size());
                let converted = constant_pointer::checked(&cx, scalar).unwrap();
                assert!(converted.provenance.is_none());
                assert_eq!(
                    converted.into_pointer_or_addr(),
                    Err(Size::from_bytes(address))
                );
                cases += 1;
            }
        }
        assert_eq!(cases, 7);
        println!("POINTER_ADDRESS cases={cases}");
    }

    #[test]
    fn allocation_identity_offset_and_flags_are_preserved() {
        let mut cases = 0;
        for target in [32, 64] {
            let cx = dl(target);
            for id in [1, 7] {
                for offset in [0, 1, 17] {
                    for flags in [0, 1, 2] {
                        let original = pointer(id, offset, flags);
                        let scalar = Scalar::from_pointer(original, &cx);
                        let converted = constant_pointer::checked(&cx, scalar).unwrap();
                        assert_eq!(converted.into_pointer_or_addr(), Ok(original));
                        cases += 1;
                    }
                }
            }
        }
        assert_eq!(cases, 36);
        println!("POINTER_PROVENANCE cases={cases}");
    }
}
