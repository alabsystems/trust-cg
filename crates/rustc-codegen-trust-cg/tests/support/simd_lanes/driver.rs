#![feature(rustc_private)]
extern crate rustc_abi;
extern crate rustc_driver;

#[path = "../../../src/simd_lanes.rs"]
mod simd_lanes;

#[test]
fn real_checked_counts_above_one_byte_remain_exact() {
    use rustc_abi::{BackendRepr, Float, Primitive, Scalar, WrappingRange};
    for lanes in [256, 1024] {
        #[cfg(rustc_backend_lane_count)]
        let count = rustc_abi::BackendLaneCount::new::<()>(lanes).expect("valid wide count");
        #[cfg(not(rustc_backend_lane_count))]
        let count = lanes;
        let repr = BackendRepr::SimdVector {
            element: Scalar::Initialized {
                value: Primitive::Float(Float::F16),
                valid_range: WrappingRange {
                    start: 0,
                    end: 65535,
                },
            },
            count,
        };
        assert_eq!(
            simd_lanes::count(&repr),
            Some(lanes),
            "wide lane count narrowed"
        );
    }
    println!("SIMD_LANES_WIDE cases=2");
}
