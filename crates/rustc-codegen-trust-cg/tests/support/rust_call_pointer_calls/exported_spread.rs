// A non-generic `extern "rust-call"` item a library DEFINES whose argument
// tuple does NOT place like one parameter: `<Spread as Fn<_>>::call` takes six
// `u64` and a `&str` after its receiver, which rustc passes untupled in x1-x7
// and on the stack. `#[inline(never)]` keeps it a reachable non-generic item,
// which rustc EXPORTS at every level and every other crate calls BY SYMBOL:
// directly, from its own generic, and from the vtable it builds. While the
// bridge declared the tuple as one by-value parameter, with the callee-side
// comparison of `refuse_tupled_rust_call_shared_symbol` disabled (2026-10-04,
// AArch64 Linux), the bridge library compiled and an LLVM binary over it
// SIGSEGV'd at O0-O3. The bridge now declares the tuple's elements as rustc's
// `FnAbi` lists them (`rust_call_spread`), so every library x binary pairing
// must compile and print LLVM's value at O0-O3.
#![feature(unboxed_closures, fn_traits)]

fn mx(h: u64, v: u64) -> u64 {
    (h ^ v).wrapping_mul(0x100000001b3).rotate_left(5)
}

pub type Args = (u64, u64, u64, u64, u64, u64, &'static str);

pub struct Spread(pub u64);

impl FnOnce<Args> for Spread {
    type Output = u64;
    extern "rust-call" fn call_once(self, t: Args) -> u64 {
        self.call(t)
    }
}

impl FnMut<Args> for Spread {
    extern "rust-call" fn call_mut(&mut self, t: Args) -> u64 {
        self.call(t)
    }
}

impl Fn<Args> for Spread {
    #[inline(never)]
    extern "rust-call" fn call(&self, t: Args) -> u64 {
        let (a, b, c, d, e, f, s) = t;
        mx(
            mx(a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f, self.0),
            s.len() as u64 * 256 + u64::from(s.as_bytes()[0]),
        )
    }
}
