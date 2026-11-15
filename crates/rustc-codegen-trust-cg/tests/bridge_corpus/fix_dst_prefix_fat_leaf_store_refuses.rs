// [TCG-THIN-REF-DST] REGRESSION PIN — a WIDE (`{data,len}`) prefix field stored
// through a slice-tail DST's own FAT reference.
//
// # What this fixture is for
//
// `is_thin_pointer_ref_ty` used to decide thin-vs-fat by ENUMERATING the two
// builtin fat forms (`&[T]`/`&str`, `&dyn Trait`), which called `&mut H<'_, [u32]>`
// — a reference to a struct whose last field is the `[u32]` TAIL — THIN. On that
// answer `lower_memory_fat_leaf_store` took its `deref_leading &&
// is_thin_pointer_ref_ty` branch and addressed `h.i.s = v` through `h`'s single
// scalar binding instead of the DATA lane of `h`'s two-lane slot, so the 16-byte
// fat store was SILENTLY LOST. That branch now asks the real question for a
// deref BASE — is this pointer's one bound value the pointee's address
// (`deref_base_scalar_is_pointee_addr`: sized, or a vtable-tailed struct whose
// value is the data lane; never a slice-tail DST) — and this shape reaches its
// own named refusal instead.
//
// # Why the program is written this way
//
// The lost write leaves the OLD, LONGER length behind, so the length-driven read
// below walks off the end of the 2-byte `SMALL`: measured 2026-09-27, the bridge
// printed `oob len 64 sum 448` (62 bytes past the static) where LLVM printed
// `oob len 2 sum 3`. The sum is included precisely so the row cannot pass by
// accident — a dropped write changes THREE printed numbers, and reading past
// `SMALL` is the actual memory-safety event.
//
// `h.i.n = k` (the SCALAR prefix write) sits deliberately NEXT TO the wide one in
// the SAME body through the SAME reference: that scalar store is a shape the
// slice-tail-DST prefix arm ADMITS, and pairing them is what turned a
// whole-body refusal into a shipped lost write in the first place.
//
// # HOW THIS FAILS IF THE FIX IS REVERTED
//
// With the fix, trust-cg refuses this body by name — `[TCG-MIR-UNSUPPORTED] …
// DST prefix field store of non-scalar leaf Ptr` — so the row is an honest
// INCOMPLETE and the harness accepts it. Give that branch the old enumeration
// back (`matches!(ty, Ref|RawPtr) && !is_slice_or_str_fat_ptr_ty &&
// !is_trait_object_reference_ty`), or make `deref_base_scalar_is_pointee_addr`
// enumerate instead of asking sizedness, and the bridge COMPILES this instead,
// printing `oob len 64 sum 448 n 5`; the harness's
// `assert_eq!(bridge.stdout, oracle.stdout)` then fails with
// "STDOUT differs from LLVM". Both mutations measured 2026-09-27 at BOTH
// `-Copt-level=0` and `-Copt-level=2`.
#![allow(dead_code)]

struct In<'a> {
    s: &'a [u8],
    n: u64,
}
struct H<'a, T: ?Sized> {
    i: In<'a>,
    tail: T,
}

static BIG: [u8; 64] = [7u8; 64];
static SMALL: [u8; 2] = [1, 2];

// One SCALAR prefix store (admitted by the slice-tail-DST prefix arm) and one
// WIDE prefix store, through the SAME fat reference, in the SAME body.
#[inline(never)]
fn set_both<'a>(h: &mut H<'a, [u32]>, v: &'a [u8], k: u64) {
    h.i.n = k;
    h.i.s = v;
}

// A LENGTH-DRIVEN read: if the wide store was dropped, `l` is still 64 and this
// loop reads 62 bytes past the end of `SMALL`.
#[inline(never)]
fn sum_len(h: &H<'_, [u32; 2]>) -> (usize, u64) {
    let s: &[u8] = h.i.s;
    let l = s.len();
    let mut acc: u64 = 0;
    let mut i = 0usize;
    while i < l {
        acc = acc + unsafe { *s.as_ptr().add(i) } as u64;
        i = i + 1;
    }
    (l, acc)
}

fn main() {
    let mut h0: H<[u32; 2]> = H {
        i: In { s: &BIG, n: 0 },
        tail: [9, 9],
    };
    {
        let h: &mut H<[u32]> = &mut h0;
        set_both(h, &SMALL, 5);
    }
    let (l, acc) = sum_len(&h0);
    let n = h0.i.n;
    println!("oob len {} sum {} n {}", l, acc, n);
}
