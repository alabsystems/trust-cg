#![no_std]
extern crate linkage_base as base;

#[cfg_attr(left, unsafe(no_mangle))]
#[cfg_attr(right, unsafe(export_name = "RIGHT_CALLBACK"))]
pub static LEFT_CALLBACK: fn(u64) -> u64 = base::shared;

#[cfg_attr(left, unsafe(no_mangle))]
#[cfg_attr(right, unsafe(export_name = "RIGHT_CALLBACK_SLOT"))]
pub static LEFT_CALLBACK_SLOT: &'static fn(u64) -> u64 = &base::CALLBACK;

// Distinct Rust modules create independent CGUs under -Ccodegen-units=8.
// An upstream #[inline] helper is copied into the CGUs that reference it.
pub mod direct {
    #[cfg_attr(left, unsafe(export_name = "linkage_left"))]
    #[cfg_attr(right, unsafe(export_name = "linkage_right"))]
    pub fn call(x: u64) -> u64 {
        super::base::shared(x)
    }
}
pub mod indirect {
    #[cfg_attr(left, unsafe(export_name = "linkage_left_indirect"))]
    #[cfg_attr(right, unsafe(export_name = "linkage_right_indirect"))]
    pub fn call(x: u64) -> u64 {
        (super::LEFT_CALLBACK)(x) ^ (super::base::CALLBACK)(x.wrapping_add(3))
    }
}
pub mod dynamic {
    #[inline(never)]
    fn dispatch(item: &dyn super::base::Evaluate, x: u64) -> u64 {
        item.evaluate(x)
    }
    #[cfg_attr(left, unsafe(export_name = "linkage_left_dynamic"))]
    #[cfg_attr(right, unsafe(export_name = "linkage_right_dynamic"))]
    pub fn call(x: u64) -> u64 {
        let item = super::base::Item(x.wrapping_mul(7));
        dispatch(&item, x)
    }
}
