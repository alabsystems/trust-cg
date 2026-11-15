// Guest program of `mir_families_aarch64` (ledger L06-P8): every
// `SetDiscriminant` shape rustc's runtime MIR can carry, written as custom MIR
// (ordinary Rust emits the statement only inside coroutine bodies), compiled by
// the bridge and by rustc's LLVM backend and compared.
//
// Layouts: a Direct tag (`Direct`), a Direct tag over a scalar payload
// (`Option<u32>`), Direct tags whose discriminants are not the variant index
// (`#[repr(i16)]` negative and wide, `#[repr(u8)]` above 127, each with
// payloads), fieldless enums whose whole value is the tag (`#[repr(u8)]` and
// `#[repr(i32)]` explicit discriminants, an implicit one), a niche in a
// `NonZeroU32` (to the niche variant: the niche value is written; to the
// untagged variant: nothing is written), a niche in a `bool` payload
// (`NicheB`), a niche in an explicit-discriminant enum's tag (`Option<R8>`),
// and a single-variant layout (no tag: a no-op).
// Places: through a reference, a field through a reference, a variant field
// through a reference, a field of a memory-backed local (built in place the way
// MIR builds an enum: payload field first, then the tag), a bare local.
//
// Every slot whose write stores a tag changes the variant the place holds, so
// a dropped or mis-valued tag write prints a different line; the writes that
// store nothing by design (the untagged niche variant, a single-variant
// layout) and a final control are the exceptions.
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features)]
use core::intrinsics::mir::*;
use std::hint::black_box;
use std::num::NonZeroU32;

#[derive(Clone, Copy, PartialEq)]
pub enum Direct {
    A(u32),
    B(u64, u8),
    C,
}

#[derive(Clone, Copy, PartialEq)]
pub enum NicheB {
    X(bool),
    Y,
    Z,
}

#[derive(Clone, Copy, PartialEq)]
pub enum Inner {
    I0,
    I1(u8),
    I2,
}

#[derive(Clone, Copy, PartialEq)]
pub enum Outer {
    O0(Inner),
    O1,
    O2(u32),
}

#[derive(Clone, Copy, PartialEq)]
pub enum Single {
    Only(u32),
}

#[derive(Clone, Copy, PartialEq)]
pub struct Holder {
    pub pad: u16,
    pub e: Direct,
    pub n: Option<NonZeroU32>,
}

#[derive(Clone, Copy, PartialEq)]
#[repr(i16)]
pub enum Wide {
    A(u8) = -1,
    B(u32) = -300,
    C = 7,
}

#[derive(Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum R8 {
    A(u8) = 10,
    B(u16) = 200,
    C = 3,
}

#[derive(Clone, Copy, PartialEq)]
#[repr(u8)]
pub enum F8 {
    A = 10,
    B = 200,
    C = 3,
}

#[derive(Clone, Copy, PartialEq)]
#[repr(i32)]
pub enum F32 {
    A = -5,
    B = 100_000,
    C = 0,
}

#[derive(Clone, Copy, PartialEq)]
pub enum P {
    A,
    B,
    C,
}

#[derive(Clone, Copy, PartialEq)]
pub struct WHolder {
    pub p: u8,
    pub w: Wide,
    pub f: F32,
    pub e: P,
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn set_direct_c(x: &mut Direct) {
    mir! {
        { SetDiscriminant(*x, 2); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn set_opt_some(x: &mut Option<u32>, v: u32) {
    mir! {
        {
            place!(Field(Variant(*x, 1), 0)) = v;
            SetDiscriminant(*x, 1);
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn set_nz_none(x: &mut Option<NonZeroU32>) {
    mir! {
        { SetDiscriminant(*x, 0); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn set_nz_some(x: &mut Option<NonZeroU32>) {
    mir! {
        { SetDiscriminant(*x, 1); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn set_nicheb_z(x: &mut NicheB) {
    mir! {
        { SetDiscriminant(*x, 2); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn set_field_c(x: &mut Holder) {
    mir! {
        { SetDiscriminant((*x).e, 2); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn set_field_niche_none(x: &mut Holder) {
    mir! {
        { SetDiscriminant((*x).n, 0); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn set_variant_field(x: &mut Outer) {
    mir! {
        { SetDiscriminant(Field::<Inner>(Variant(*x, 0), 0), 2); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn set_wide_b(x: &mut Wide, v: u32) {
    mir! {
        {
            place!(Field(Variant(*x, 1), 0)) = v;
            SetDiscriminant(*x, 1);
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn set_wide_field_c(x: &mut WHolder) {
    mir! {
        { SetDiscriminant((*x).w, 2); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn set_wide_field_a(x: &mut WHolder, v: u8) {
    mir! {
        {
            place!(Field(Variant((*x).w, 0), 0)) = v;
            SetDiscriminant((*x).w, 0);
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn set_r8_in_option(x: &mut Option<R8>, v: u16) {
    mir! {
        {
            place!(Field(Variant(Field::<R8>(Variant(*x, 1), 0), 1), 0)) = v;
            SetDiscriminant(Field::<R8>(Variant(*x, 1), 0), 1);
            SetDiscriminant(*x, 1);
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn set_f8_b(x: &mut F8) {
    mir! {
        { SetDiscriminant(*x, 1); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn set_fieldless_fields(x: &mut WHolder) {
    mir! {
        {
            SetDiscriminant((*x).f, 1);
            SetDiscriminant((*x).e, 2);
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn set_single(x: &mut Single) {
    mir! {
        { SetDiscriminant(*x, 0); Return() }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn local_roundtrip(v: u32) -> isize {
    mir! {
        let e: Direct;
        {
            e = Direct::A(v);
            SetDiscriminant(e, 2);
            RET = Discriminant(e);
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "optimized")]
#[inline(never)]
pub fn local_field_roundtrip(v: u32) -> u64 {
    mir! {
        let h: Holder;
        let e: Direct;
        let n: Option<NonZeroU32>;
        let r: &Holder;
        {
            e = Direct::C;
            n = Option::None;
            h = Holder { pad: 7, e: e, n: n };
            place!(Field(Variant(h.e, 0), 0)) = v;
            SetDiscriminant(h.e, 0);
            r = &h;
            Call(RET = holder_score(r), ReturnTo(done), UnwindUnreachable())
        }
        done = {
            Return()
        }
    }
}

#[inline(never)]
pub fn holder_score(h: &Holder) -> u64 {
    let e = match h.e {
        Direct::A(a) => 1000 + a as u64,
        Direct::B(a, b) => 2000 + a + b as u64,
        Direct::C => 3000,
    };
    let n = match h.n {
        Some(n) => n.get() as u64,
        None => 9,
    };
    e * 100 + n + h.pad as u64
}

#[inline(never)]
fn mk_direct(i: u32) -> Direct {
    match i {
        0 => Direct::A(5),
        1 => Direct::B(12, 4),
        _ => Direct::C,
    }
}

#[inline(never)]
fn mk_outer(i: u32) -> Outer {
    match i {
        0 => Outer::O0(Inner::I1(6)),
        1 => Outer::O1,
        _ => Outer::O2(i),
    }
}

#[inline(never)]
pub fn wide_code(w: Wide) -> u64 {
    match w {
        Wide::A(v) => 100 + v as u64,
        Wide::B(v) => 200 + v as u64,
        Wide::C => 300,
    }
}

#[inline(never)]
pub fn r8_code(r: Option<R8>) -> u64 {
    match r {
        Some(R8::A(v)) => 100 + v as u64,
        Some(R8::B(v)) => 200 + v as u64,
        Some(R8::C) => 300,
        None => 400,
    }
}

#[inline(never)]
pub fn wholder_code(h: &WHolder) -> u64 {
    let f = match h.f {
        F32::A => 1,
        F32::B => 2,
        F32::C => 3,
    };
    let e = match h.e {
        P::A => 1,
        P::B => 2,
        P::C => 3,
    };
    wide_code(h.w) * 1000 + f * 100 + e * 10 + h.p as u64
}

fn main() {
    let z = black_box(0u32);
    let mut out: [u64; 18] = [0; 18];

    // Direct, through a reference: A(5) -> C.
    let mut d = mk_direct(z);
    set_direct_c(&mut d);
    out[0] = (d == Direct::C) as u64;

    // Direct over a payload, built in place: None -> Some(9).
    let mut o: Option<u32> = if z == 0 { None } else { Some(1) };
    set_opt_some(&mut o, z + 9);
    out[1] = o.unwrap_or(0) as u64;

    // Niche (NonZeroU32): Some(7) -> None, None -> Some (nothing written).
    let mut n = NonZeroU32::new(z + 7);
    set_nz_none(&mut n);
    out[2] = n.is_none() as u64;

    let mut n2 = NonZeroU32::new(z + 8);
    set_nz_some(&mut n2);
    out[3] = n2.map(|v| v.get()).unwrap_or(0) as u64;

    // Niche (bool): X(true) -> Z.
    let mut nb = if z == 0 { NicheB::X(true) } else { NicheB::Y };
    set_nicheb_z(&mut nb);
    out[4] = (nb == NicheB::Z) as u64;

    // Direct field through a reference: B(12, 4) -> C; niche field -> None.
    let mut h = Holder { pad: 3, e: mk_direct(z + 1), n: NonZeroU32::new(z + 11) };
    set_field_c(&mut h);
    out[5] = holder_score(&h);
    set_field_niche_none(&mut h);
    out[6] = holder_score(&h);

    // Variant field through a reference: O0(I1(6)) -> O0(I2).
    let mut ou = mk_outer(z);
    set_variant_field(&mut ou);
    out[7] = match ou {
        Outer::O0(Inner::I2) => 42,
        Outer::O0(_) => 1,
        _ => 2,
    };

    // Single variant: no tag, a no-op.
    let mut s = Single::Only(z + 77);
    set_single(&mut s);
    out[8] = match s {
        Single::Only(v) => v as u64,
    };

    // Bare memory-backed local and a field of one.
    out[9] = local_roundtrip(z + 4) as u64;
    out[10] = local_field_roundtrip(z + 5);

    // Explicit negative / wide discriminants (repr(i16)): A(3) -> B(70000)
    // through a reference; C(..) never stored as the variant index.
    let mut w = if z == 0 { Wide::A(3) } else { Wide::C };
    set_wide_b(&mut w, z + 70_000);
    out[11] = wide_code(w);

    // ... as a field through a reference: B -> C, then built in place as A(9).
    let mut wh = WHolder { p: 4, w: Wide::B(z + 1), f: F32::A, e: P::A };
    set_wide_field_c(&mut wh);
    out[12] = wholder_code(&wh);
    set_wide_field_a(&mut wh, (z + 9) as u8);
    out[13] = wholder_code(&wh);

    // A niche in an explicit-discriminant tag (`Option<R8>`): None ->
    // Some(B(513)), writing R8's tag (200) and then the outer niche variant.
    let mut r = if z == 0 { None } else { Some(R8::C) };
    set_r8_in_option(&mut r, (z + 513) as u16);
    out[14] = r8_code(r);

    // Fieldless enums (the whole value is the tag): C -> B (200) through a
    // reference; F32::A (-5) -> B (100000) and P::A -> C as fields.
    let mut f8 = if z == 0 { F8::C } else { F8::A };
    set_f8_b(&mut f8);
    out[15] = f8 as u8 as u64;
    set_fieldless_fields(&mut wh);
    out[16] = wholder_code(&wh) * 10 + wh.f as i32 as u64 % 7;

    // Control: no SetDiscriminant.
    out[17] = (mk_direct(z + 2) == Direct::C) as u64;

    for value in out {
        print!("{value} ");
    }
    println!();
}
