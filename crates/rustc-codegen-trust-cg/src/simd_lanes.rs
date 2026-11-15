// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! The exact fixed-vector lane count, read without changing its descriptor.

use rustc_abi::BackendRepr;

pub(super) fn count(repr: &BackendRepr) -> Option<u64> {
    let BackendRepr::SimdVector { element: _, count } = repr else {
        return None;
    };
    #[cfg(rustc_backend_lane_count)]
    {
        Some(count.as_u64())
    }
    #[cfg(not(rustc_backend_lane_count))]
    {
        Some(*count)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_abi::{Float, Integer, Primitive, Scalar, WrappingRange};

    fn elements() -> [Scalar; 3] {
        [
            Primitive::Int(Integer::I16, false),
            Primitive::Int(Integer::I16, true),
            Primitive::Float(Float::F16),
        ]
        .map(|value| Scalar::Initialized {
            value,
            valid_range: WrappingRange {
                start: 0,
                end: 65535,
            },
        })
    }

    fn vector(element: Scalar, lanes: u64) -> BackendRepr {
        #[cfg(rustc_backend_lane_count)]
        let lanes = rustc_abi::BackendLaneCount::new::<()>(lanes).expect("valid test count");
        BackendRepr::SimdVector {
            element,
            count: lanes,
        }
    }

    #[test]
    fn fixed_vector_counts_and_original_descriptors_remain_exact() {
        let mut cases = 0;
        for element in elements() {
            for lanes in [1, 2, 3, 4, 7, 8, 16, 128] {
                let repr = vector(element, lanes);
                let original = repr;
                assert_eq!(count(&repr), Some(lanes), "exact fixed-vector lane count");
                assert_eq!(repr, original, "original SIMD descriptor changed");
                let BackendRepr::SimdVector {
                    element: observed,
                    count: _,
                } = repr
                else {
                    panic!("vector fixture changed kind")
                };
                assert_eq!(observed, element, "element validity changed");
                cases += 1;
            }
        }
        assert_eq!(cases, 24);
        println!("SIMD_LANES_FIXED cases={cases}");
    }

    #[test]
    fn other_representations_do_not_acquire_a_fixed_lane_count() {
        for repr in [
            BackendRepr::Memory { sized: false },
            BackendRepr::Memory { sized: true },
            BackendRepr::Scalar(elements()[0]),
            BackendRepr::Scalar(elements()[2]),
        ] {
            let original = repr;
            assert_eq!(count(&repr), None, "non-vector acquired lane count");
            assert_eq!(repr, original, "non-vector descriptor changed");
        }
        println!("SIMD_LANES_OTHER cases=4");
    }

    #[test]
    fn full_legacy_width_and_modern_constructor_limits_are_preserved() {
        #[cfg(rustc_backend_lane_count)]
        {
            for lanes in [0, u64::MAX] {
                assert!(
                    rustc_abi::BackendLaneCount::new::<()>(lanes).is_err(),
                    "invalid modern lane count admitted"
                );
            }
            println!("SIMD_LANES_BOUNDARY cases=2");
        }
        #[cfg(not(rustc_backend_lane_count))]
        {
            for lanes in [0, u64::from(u32::MAX), u64::MAX] {
                assert_eq!(
                    count(&vector(elements()[0], lanes)),
                    Some(lanes),
                    "legacy lane count narrowed"
                );
            }
            println!("SIMD_LANES_BOUNDARY cases=3");
        }
    }
}
