// The generic form of `exported_spread.rs`: `<Spread<u64> as Fn<_>>::call`,
// which this library instantiates in `use_here`. Under `-Zshare-generics` (on
// by default at O0 and O1) rustc EXPORTS that instance and a downstream crate
// links it rather than compiling its own; at O2 and O3 rustc gives the
// instance internal linkage and the downstream crate instantiates its own
// copy. While the bridge declared the tuple as one by-value parameter, with
// the callee-side comparison of `refuse_tupled_rust_call_shared_symbol`
// disabled (2026-10-04, AArch64 Linux), the bridge library compiled at O0 and
// O1 and an LLVM binary over it SIGSEGV'd. The bridge now declares the tuple's
// elements as rustc's `FnAbi` lists them, so every pairing must match LLVM.
#![feature(unboxed_closures, fn_traits)]
use std::hint::black_box as bb;

fn mx(h: u64, v: u64) -> u64 {
    (h ^ v).wrapping_mul(0x100000001b3).rotate_left(5)
}

pub type Args = (u64, u64, u64, u64, u64, u64, &'static str);

pub struct Spread<T>(pub T);

impl<T: Copy + Into<u64>> FnOnce<Args> for Spread<T> {
    type Output = u64;
    extern "rust-call" fn call_once(self, t: Args) -> u64 {
        self.call(t)
    }
}

impl<T: Copy + Into<u64>> FnMut<Args> for Spread<T> {
    extern "rust-call" fn call_mut(&mut self, t: Args) -> u64 {
        self.call(t)
    }
}

impl<T: Copy + Into<u64>> Fn<Args> for Spread<T> {
    extern "rust-call" fn call(&self, t: Args) -> u64 {
        let (a, b, c, d, e, f, s) = t;
        mx(
            mx(a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f, self.0.into()),
            s.len() as u64 * 256 + u64::from(s.as_bytes()[0]),
        )
    }
}

#[inline(never)]
pub fn use_here(k: u64) -> u64 {
    Spread(bb(7u64))(k, 2, 3, 4, 5, 6, bb("hello"))
}
