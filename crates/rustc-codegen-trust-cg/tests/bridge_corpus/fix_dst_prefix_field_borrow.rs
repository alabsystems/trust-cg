// FIXTURE: a borrow of a SIZED PREFIX FIELD of a SLICE-TAIL DST, reached through
// the DST's own `{ data, len }` WIDE pointer — in BOTH spellings rustc emits,
// `&raw mut (*p).f` (a `Rvalue::RawPtr`) and `&mut (*p).f` (a `Rvalue::Ref`).
//
// This is `alloc::rc::RcInner<[u8]>` / `alloc::sync::ArcInner<[u8]>`: a struct
// whose sized prefix is refcount words and whose tail is the payload slice.
// `Rc::try_allocate_for_layout` and `Arc::initialize_arcinner` write the two
// refcounts through `&raw mut ((*inner).0: Cell<usize>)`.
//
// WHY THE FIELD WIDTHS ARE UNEQUAL. `a: u8, b: u64, c: u16` under `repr(Rust)`
// gives rustc's layout no reason to match declaration order, so an addressing
// model that folds offsets in DECLARATION order disagrees with rustc's at every
// field. The tail bytes are printed too: a prefix write that overruns into the
// tail, or a base taken from the wide pointer's own SLOT ADDRESS instead of its
// DATA LANE, shows up as a different number here (or as a SIGSEGV).
//
// WHAT IT PINS, AND HOW IT FAILS IF THE LANE IS REVERTED (measured on this base,
// 2026-09-26, `-Copt-level=0`):
//   * `&raw mut (*p).f` — base COMPILED and SIGSEGV'd (the through-THIN-reference
//     `&raw` arm took the wide local's first ABI value as an address).
//   * `&mut (*p).f`     — base COMPILED and the store LANDED NOWHERE: LLVM
//     `a=165`, the bridge `a=0`, every other byte unchanged. A silent lost write.
// Either reversion is a HARD failure of this row, not an INCOMPLETE: the first
// exits via a signal, the second diverges in stdout.
//
// No `{:?}`, no slice indexing in the printed expressions, and every value is
// bound to a bare local before formatting: the bridge's `core::fmt` interception
// declines Debug placeholders and projected argument places, and those refusals
// are not what this fixture is about.

struct Hdr<T: ?Sized> {
    a: u8,
    b: u64,
    c: u16,
    tail: T,
}

/// The `Rvalue::RawPtr` spelling: three sized-prefix fields written through raw
/// pointers formed from a WIDE `*mut Hdr<[u8]>`.
#[inline(never)]
fn fill_raw(p: *mut Hdr<[u8]>) {
    unsafe {
        let pa: *mut u8 = &raw mut (*p).a;
        let pb: *mut u64 = &raw mut (*p).b;
        let pc: *mut u16 = &raw mut (*p).c;
        pa.write(0xA5);
        pb.write(0x1122_3344_5566_7788);
        pc.write(0xBEEF);
    }
}

/// The `Rvalue::Ref` spelling of the SAME three fields, through a WIDE
/// `&mut Hdr<[u8]>`. Must produce the identical addresses as `fill_raw`.
#[inline(never)]
fn fill_ref(p: &mut Hdr<[u8]>) {
    let pa: &mut u8 = &mut (*p).a;
    *pa = 0x5A;
    let pb: &mut u64 = &mut (*p).b;
    *pb = 0x0102_0304_0506_0708;
    let pc: &mut u16 = &mut (*p).c;
    *pc = 0xFEED;
}

/// A SHARED prefix borrow READ back through the wide pointer. Measured on the
/// unpatched base this returned `6101134192` where LLVM returns `777` — the READ
/// half of the same defect the two writers above cover, and the reason this
/// fixture carries both directions (fix a read path, ask what writes the same
/// bytes, and the reverse).
#[inline(never)]
fn read_ref(p: &Hdr<[u8]>) -> u64 {
    let rb: &u64 = &(*p).b;
    *rb
}

/// THE NON-INTERFERENCE ROWS. A borrow of the UNSIZED TAIL is a different thing
/// from a sized-prefix borrow: its result is FAT and keeps the DST's own metadata
/// verbatim. Both of these already worked on the base, and they must keep working
/// — if the prefix arm ever admitted the tail it would hand out a THIN address and
/// the length would be lost, which shows up here as a wrong `len` / `sum` (or a
/// trap inside the loop).
#[inline(never)]
fn tail_len(p: &Hdr<[u8]>) -> usize {
    let t: &[u8] = &(*p).tail;
    t.len()
}

#[inline(never)]
fn tail_sum(p: &Hdr<[u8]>) -> u64 {
    let t: &[u8] = &(*p).tail;
    let mut s: u64 = 0;
    let mut i: usize = 0;
    while i < t.len() {
        s = s.wrapping_add(t[i] as u64);
        i += 1;
    }
    s
}

fn main() {
    let mut h: Hdr<[u8; 5]> = Hdr {
        a: 0,
        b: 0,
        c: 0,
        tail: [11, 22, 33, 44, 55],
    };

    {
        let r: &mut Hdr<[u8]> = &mut h;
        let p: *mut Hdr<[u8]> = r;
        fill_raw(p);
    }
    let a1 = h.a as u64;
    let b1 = h.b;
    let c1 = h.c as u64;
    let t0 = h.tail[0] as u64;
    let t1 = h.tail[1] as u64;
    let t2 = h.tail[2] as u64;
    let t3 = h.tail[3] as u64;
    let t4 = h.tail[4] as u64;
    println!("raw a={} b={} c={}", a1, b1, c1);
    println!("raw tail={} {} {} {} {}", t0, t1, t2, t3, t4);

    {
        let r: &mut Hdr<[u8]> = &mut h;
        fill_ref(r);
    }
    let a2 = h.a as u64;
    let b2 = h.b;
    let c2 = h.c as u64;
    let u0 = h.tail[0] as u64;
    let u4 = h.tail[4] as u64;
    println!("ref a={} b={} c={}", a2, b2, c2);
    println!("ref tail0={} tail4={}", u0, u4);

    let b3;
    let tl;
    let ts;
    {
        let r: &Hdr<[u8]> = &h;
        b3 = read_ref(r);
        tl = tail_len(r);
        ts = tail_sum(r);
    }
    println!("read b={}", b3);
    println!("tail len={} sum={}", tl, ts);
}
