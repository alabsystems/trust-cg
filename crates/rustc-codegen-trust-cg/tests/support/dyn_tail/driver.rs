#![feature(ptr_metadata)]
extern crate dyn_tail_types;
use core::ptr::DynMetadata;
use dyn_tail_types::*;

unsafe extern "Rust" {
    fn dyn_local(seed: u64, by: u64) -> (u8, u64, u64, u64);
    fn dyn_upcast(p: &Outer<dyn Payload>) -> &Outer<dyn Right>;
    fn dyn_right(p: &Outer<dyn Right>) -> u64;
    fn dyn_choose<'a>(
        a: &'a Outer<dyn Payload>,
        b: &'a Outer<dyn Payload>,
        take_a: bool,
    ) -> &'a Outer<dyn Payload>;

    fn dyn_identity(p: &mut Outer<dyn Payload>) -> &mut Outer<dyn Payload>;
    fn dyn_tail(p: &Outer<dyn Payload>) -> &dyn Payload;
    fn dyn_tail_mut(p: &mut Outer<dyn Payload>) -> &mut dyn Payload;
    fn dyn_inner(p: &mut Outer<dyn Payload>) -> &mut Inner<dyn Payload>;
    fn dyn_header(p: &mut Outer<dyn Payload>) -> &mut Header<dyn Payload>;
    fn dyn_prefix(p: &mut Outer<dyn Payload>) -> &mut u64;
    fn dyn_size(p: &Outer<dyn Payload>) -> usize;
    fn dyn_align(p: &Outer<dyn Payload>) -> usize;
    fn dyn_inner_size(p: &Inner<dyn Payload>) -> usize;
    fn dyn_inner_align(p: &Inner<dyn Payload>) -> usize;
    fn dyn_head(p: &Outer<dyn Payload>) -> u64;
    fn dyn_update(p: &mut Outer<dyn Payload>, value: u64) -> u64;
    fn dyn_unsize_small(p: &mut Outer<Small>) -> &mut Outer<dyn Payload>;
    fn dyn_unsize_word(p: &mut Outer<Word>) -> &mut Outer<dyn Payload>;
    fn dyn_unsize_wide(p: &mut Outer<Wide>) -> &mut Outer<dyn Payload>;
    fn dyn_unsize_empty(p: &mut Outer<Empty>) -> &mut Outer<dyn Payload>;
    fn dyn_transparent(p: &Transparent<dyn Payload>) -> (usize, usize, u64);
    fn dyn_rust(p: &RustHeader<dyn Payload>) -> (usize, usize, u128, u64);
    fn dyn_meta(p: *mut Outer<dyn Payload>) -> DynMetadata<dyn Payload>;
    fn dyn_parts(p: *mut (), meta: DynMetadata<dyn Payload>) -> *mut Outer<dyn Payload>;
    fn dyn_spill(
        a: u64,
        b: u64,
        c: u64,
        d: u64,
        e: u64,
        f: u64,
        g: u64,
        p: &Outer<dyn Payload>,
    ) -> u64;
}
fn address<T: ?Sized>(p: *const T) -> usize {
    p as *const () as usize
}
fn outer<T>(value: T, seed: u64) -> Outer<T> {
    Outer {
        lead: seed as u16,
        nested: Inner {
            prefix: [1, 2, seed as u8],
            node: Header {
                marker: (seed >> 8) as u8,
                epoch: seed & 0xffff,
                value,
            },
        },
    }
}
fn check<T: Payload + 'static>(
    make: impl Fn() -> T,
    unsize: unsafe extern "Rust" fn(&mut Outer<T>) -> &mut Outer<dyn Payload>,
    seed: u64,
) -> usize {
    let mut value = outer(make(), seed);
    let mut oracle = outer(make(), seed);
    let base = address(&value);
    let inner = address(&value.nested);
    let header = address(&value.nested.node);
    let payload = address(&value.nested.node.value);
    let prefix = address(&value.nested.node.epoch);
    let before = oracle.nested.node.value.read();
    let expected_head = oracle.lead as u64
        + oracle.nested.prefix[2] as u64
        + oracle.nested.node.marker as u64
        + oracle.nested.node.epoch;
    let mut checks = 0;
    macro_rules! eq {
        ($actual:expr, $expected:expr) => {{
            assert_eq!($actual, $expected, "{} seed={seed:x}", stringify!($actual));
            checks += 1;
        }};
    }
    unsafe {
        // LLVM constructs the inbound pointer; CG/LLVM returns reborrows to it.
        let p: &mut Outer<dyn Payload> = &mut value;
        eq!(address(dyn_identity(p)), base);
        eq!(address(dyn_inner(p)), inner);
        eq!(address(dyn_header(p)), header);
        eq!(address(dyn_tail(p)), payload);
        eq!(address(dyn_tail_mut(p)), payload);
        eq!(address(dyn_prefix(p)), prefix);
        eq!(dyn_size(p), core::mem::size_of::<Outer<T>>());
        eq!(dyn_align(p), core::mem::align_of::<Outer<T>>());
        eq!(
            dyn_inner_size(dyn_inner(p)),
            core::mem::size_of::<Inner<T>>()
        );
        eq!(
            dyn_inner_align(dyn_inner(p)),
            core::mem::align_of::<Inner<T>>()
        );
        eq!(dyn_head(p), expected_head);
        eq!(dyn_tail(p).read(), before);
        eq!(address(dyn_upcast(p)), base);
        eq!(dyn_right(dyn_upcast(p)), oracle.nested.node.value.right());
        eq!(
            dyn_spill(1, 2, 3, 4, 5, 6, 7, p),
            1 ^ 2 ^ 3 ^ 4 ^ 5 ^ 6 ^ 7 ^ before
        );
        eq!(dyn_meta(p), core::ptr::metadata(p));
        let raw = dyn_parts(base as *mut (), dyn_meta(p));
        eq!(address(raw), base);
        eq!(core::ptr::metadata(raw), core::ptr::metadata(p));
        eq!(dyn_tail(&*raw).read(), before);
        *dyn_prefix(p) ^= seed;
        oracle.nested.node.epoch ^= seed;
        let expected = oracle.nested.node.value.bump(seed);
        eq!(dyn_update(p, seed), expected);
        oracle.nested.node.epoch = oracle.nested.node.epoch.wrapping_add(seed);
        oracle.nested.prefix[2] ^= seed as u8;
        eq!(value.nested.node.epoch, oracle.nested.node.epoch);
        eq!(value.nested.prefix, oracle.nested.prefix);
        eq!(value.nested.node.marker, oracle.nested.node.marker);
        eq!(value.lead, oracle.lead);
        eq!(
            value.nested.node.value.read(),
            oracle.nested.node.value.read()
        );

        // The library constructs the outbound vtable for T's tail, while data
        // must still address the complete Outer<T> and preserve caller storage.
        let p = unsize(&mut value);
        eq!(address(p), base);
        eq!(dyn_size(p), core::mem::size_of::<Outer<T>>());
        eq!(dyn_align(p), core::mem::align_of::<Outer<T>>());
        eq!(address(dyn_tail(p)), payload);
        eq!(dyn_tail_mut(p).bump(13), oracle.nested.node.value.bump(13));
        eq!(
            value.nested.node.value.read(),
            oracle.nested.node.value.read()
        );

        let wrapped = Transparent(outer(make(), seed));
        eq!(
            dyn_transparent(&wrapped),
            (
                core::mem::size_of_val(&wrapped),
                core::mem::align_of_val(&wrapped),
                before
            )
        );
        let plain = RustHeader {
            marker: seed as u8,
            count: ((seed as u128) << 80) | 7,
            value: make(),
        };
        eq!(
            dyn_rust(&plain),
            (
                core::mem::size_of_val(&plain),
                core::mem::align_of_val(&plain),
                plain.count,
                before
            )
        );
    }
    checks
}
fn main() {
    let mut state = 0x217921fa589173ad_u64;
    let mut checks = 0;
    for _ in 0..256 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        checks += check(|| Small(state as u8), dyn_unsize_small, state);
        checks += check(|| Word(state), dyn_unsize_word, state);
        checks += check(
            || Wide([state, !state, state.rotate_left(19), 0x9ac13]),
            dyn_unsize_wide,
            state,
        );
        checks += check(|| Empty, dyn_unsize_empty, state);
        let by = state.rotate_left(23);
        let result = (!state).wrapping_add(by);
        assert_eq!(
            unsafe { dyn_local(state, by) },
            (state as u8, state ^ by, result, result)
        );
        checks += 1;
    }
    let a = outer(Word(0x72214), 33);
    let b = outer(Wide([11, 31, 77, 301]), 41);
    for flag in [true, false] {
        let expected: &Outer<dyn Payload> = if flag { &a } else { &b };
        let chosen = unsafe { dyn_choose(&a, &b, flag) };
        assert_eq!(address(chosen), address(expected));
        assert_eq!(
            unsafe { dyn_size(chosen) },
            core::mem::size_of_val(expected)
        );
        assert_eq!(
            unsafe { dyn_align(chosen) },
            core::mem::align_of_val(expected)
        );
        assert_eq!(
            unsafe { dyn_tail(chosen) }.read(),
            expected.nested.node.value.read()
        );
        checks += 4;
    }
    assert_eq!(checks, 34056);
    println!("PASS dyn_tail checks={checks}");
}
