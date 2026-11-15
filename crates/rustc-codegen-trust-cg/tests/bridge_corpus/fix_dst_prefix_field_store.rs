// CORPUS FIXTURE — a SCALAR STORE into the SIZED PREFIX of a slice-tail DST,
// addressed through the DST's own FAT reference.
//
// WHAT IT PINS. `lower_memory_slice_assign` used to refuse every projected
// destination that was not one of the two element STORES, by name:
// `memory slice assignment into projected place`. Measured 2026-09-26 at
// `-Copt-level=0`, that was 1 of `library/alloc`'s 37 failed roots —
// `PolymorphicIter::<[MaybeUninit<char>]>::next_back`, whose `self.alive.end`
// write is the statement
//
//     (((*_1).0: IndexRange).1: usize) = copy _8
//
// with `_1: &mut PolymorphicIter<[MaybeUninit<char>]>`. `Hdr<T>` below is that
// shape with a local name — a nested sized prefix (`Rng { start, end }`) ahead of
// an unsized `[u32]` tail — and `set_end` / `set_start` reproduce the refusal
// verbatim on the unpatched tree.
//
// WHY THE VALUES PROVE THE ADDRESS. Every write goes to the DST reference's DATA
// half plus the field chain's layout offset in the POINTEE, and the readback goes
// through the ORIGINAL sized value (`owned.r.start` / `owned.r.end` / `owned.n`),
// so a write at the wrong base or the wrong offset changes stdout rather than
// merely refusing. Two independent misdirections are covered:
//
//   * a write that addressed the fat POINTER's own slot instead of the pointee —
//     mutation-measured: making `memory_place_walk_base` return the slot address
//     for a DST reference makes this fixture exit 138 against LLVM's 0;
//   * a prefix write that landed on the TAIL, or a tail write that landed on the
//     prefix — `poke` writes `tail[2]` through the SAME fat reference and `n` is
//     never written at all, so `prefix 808 909 3` / `tail 4 11 77 44` pins the
//     whole 24-byte image, not just the two words this lane changed.
//
// The accessors are `#[inline(never)]` and every printed value is bound to a
// plain local first, because the format interception refused a placeholder whose
// value is a slice `.len()` (`[TCG-FMT-LEN]`, removed 2026-10-03) and refuses a
// projected borrow (`[TCG-FMT-ARGPLACE]`) — neither of which is this lane.
//
// SECOND SECTION — A PACKED PREFIX AT UNNATURAL OFFSETS. Every offset this arm
// uses comes from `tcx.layout_of`, never from a natural-alignment assumption, and
// `#[repr(packed)]` is what separates the two: `Pk`'s `r.start` / `r.end` sit at
// bytes 1 and 9, so a store that rounded either to 8 or 16 would print a
// different number or clobber the tail. Measured 2026-09-26: the section refuses
// on the unpatched tree with the SAME
// `memory slice assignment into projected place` and matches LLVM with the patch,
// prefix values and all four tail bytes intact.
//
// NOT PINNED HERE, ON PURPOSE. A SINGLE-level prefix write (`(*h).n = v`, the
// projection `[Deref, Field]`) still fails closed on this tree, and not in this
// function: nothing memory-backs the DST reference for a two-element chain, so the
// statement never reaches `lower_memory_slice_assign` at all and refuses earlier
// with `Ty::Adt multi-field struct …`. Adding `set_n` here would make this row
// INCOMPLETE for a reason that has nothing to do with the arm it is pinning.
#![allow(dead_code)]

struct Rng {
    start: usize,
    end: usize,
}

struct Hdr<T: ?Sized> {
    r: Rng,
    n: u32,
    tail: T,
}

#[inline(never)]
fn set_end(h: &mut Hdr<[u32]>, v: usize) {
    h.r.end = v;
}
#[inline(never)]
fn set_start(h: &mut Hdr<[u32]>, v: usize) {
    h.r.start = v;
}
#[inline(never)]
fn poke(h: &mut Hdr<[u32]>, i: usize, v: u32) {
    h.tail[i] = v;
}
#[inline(never)]
fn g_len(h: &Hdr<[u32]>) -> usize {
    h.tail.len()
}
#[inline(never)]
fn g_tail(h: &Hdr<[u32]>, i: usize) -> u32 {
    unsafe { *h.tail.as_ptr().add(i) }
}

// A PACKED slice-tail DST with a NESTED packed prefix: `start` at byte 1, `end`
// at byte 9, tail at byte 17 — every one an UNNATURAL offset. Built through a
// raw-pointer unsize (rustc rejects a generic `?Sized` last field on a packed
// struct, so the sized and unsized shapes are spelled separately and the DST
// pointer is made with `slice_from_raw_parts_mut`).
#[repr(packed)]
struct PkRng {
    start: u64,
    end: u64,
}
#[repr(packed)]
struct PkS {
    a: u8,
    r: PkRng,
    tail: [u8; 4],
}
#[repr(packed)]
struct PkD {
    a: u8,
    r: PkRng,
    tail: [u8],
}

#[inline(never)]
fn pk_set_end(h: &mut PkD, v: u64) {
    h.r.end = v;
}
#[inline(never)]
fn pk_set_start(h: &mut PkD, v: u64) {
    h.r.start = v;
}
#[inline(never)]
fn pk_len(h: &PkD) -> usize {
    h.tail.len()
}

fn main() {
    let mut owned: Hdr<[u32; 4]> = Hdr {
        r: Rng { start: 1, end: 4 },
        n: 3,
        tail: [11, 22, 33, 44],
    };
    let h: &mut Hdr<[u32]> = &mut owned;
    set_end(h, 909);
    set_start(h, 808);
    poke(h, 2, 77);
    let l = g_len(h);
    let t0 = g_tail(h, 0);
    let t2 = g_tail(h, 2);
    let t3 = g_tail(h, 3);
    println!("tail {} {} {} {}", l, t0, t2, t3);
    let ps = owned.r.start;
    let pe = owned.r.end;
    let pn = owned.n;
    println!("prefix {} {} {}", ps, pe, pn);

    let mut pk = PkS {
        a: 7,
        r: PkRng { start: 1, end: 2 },
        tail: [11, 22, 33, 44],
    };
    let pk_base: *mut PkS = &mut pk;
    let pk_dst: *mut PkD = core::ptr::slice_from_raw_parts_mut(pk_base as *mut u8, 4) as *mut PkD;
    let pk_l;
    unsafe {
        let ph: &mut PkD = &mut *pk_dst;
        pk_set_start(ph, 0x1122334455667788);
        pk_set_end(ph, 0x99aabbccddeeff01);
        pk_l = pk_len(ph);
    }
    let ka = pk.a;
    let ks = pk.r.start;
    let ke = pk.r.end;
    let k0 = pk.tail[0];
    let k3 = pk.tail[3];
    println!("packed {} {} {} {}", pk_l, ka, ks, ke);
    println!("packedtail {} {}", k0, k3);
}
