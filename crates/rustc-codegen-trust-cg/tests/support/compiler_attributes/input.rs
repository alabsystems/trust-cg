// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
#![feature(rustc_attrs)]
#![no_std]

pub fn plain() {}
#[inline]
pub fn hinted() {}
#[inline(always)]
pub fn always() {}
#[inline(never)]
pub fn never() {}
#[rustc_force_inline = "retained-reason"]
pub fn forced() {}

#[derive(Clone)]
pub struct Derived(pub u8);

pub struct Forged(pub u8);
macro_rules! forged_clone {
    () => {
        #[automatically_derived]
        impl Clone for Forged {
            fn clone(&self) -> Self {
                Self(self.0.wrapping_add(1))
            }
        }
    };
}
forged_clone!();

pub struct Manual(pub u8);
impl Clone for Manual {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}
