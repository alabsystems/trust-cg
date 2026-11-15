// Corpus: a reference to a DYNAMICALLY-SIZED STRUCT whose tail is a `[T]` / `str`.
//
// `&ByteStr`, `&CStr`, `&Wtf8`, `&PolymorphicIter<[MaybeUninit<char>]>` are all
// this shape: a struct whose LAST field is unsized, so the reference is a FAT
// pointer `{ data, len }` — and neither `is_slice_or_str_fat_ptr_ty` (the pointee
// is a named struct, not `[T]`) nor `is_trait_object_reference_ty` (the metadata
// is a length, not a vtable) recognizes it. Typing such a reference THIN drops
// the length, which is miscompile class `3b9b89a8`: a fat leaf bound into one
// lane shifts every later field.
//
// WHAT EACH ROW WOULD CATCH, and why a wrong model is a WRONG NUMBER here rather
// than a refusal. Every printed value is returned from an `#[inline(never)]`
// function, so a lane confusion crosses a real ABI boundary before it is read:
//  * `probe_bytes` reads the METADATA half (the length) BESIDE two elements and
//    the LAST element. A thin model has no second lane at all; a model that reads
//    the wrong lane prints the data POINTER, not 5; a wrong length indexes off
//    the end of the wrong element.
//  * `probe_hdr` puts a SIZED PREFIX (`n: u32, m: u32`) in front of the tail, so
//    the tail's byte offset is a real layout question and the prefix fields are
//    read BESIDE the tail — the field-shift class.
//  * `pair_read` puts a `&Bytes` fat reference in a struct BETWEEN two scalars:
//    if the fat leaf occupies one lane instead of two, `after` reads `before`'s
//    neighbour.
//  * `tail_write` MUTATES through `&mut Bytes` and the caller reads the result
//    back out of its own array, so a wrong tail address is observable.
//  * `thin_control` is the CONTROL: an ordinary thin `&T` / `*const T`, which
//    must be unaffected.
#![allow(dead_code)]

#[repr(transparent)]
struct Bytes([u8]);

impl Bytes {
    #[inline(never)]
    fn new(b: &[u8]) -> &Bytes {
        // `*const [u8] -> *const Bytes`: a fat -> fat cast, both carrying a
        // LENGTH. This is `ByteStr::from_bytes` / `Wtf8::from_bytes_unchecked`.
        unsafe { &*(b as *const [u8] as *const Bytes) }
    }
    #[inline(never)]
    fn new_mut(b: &mut [u8]) -> &mut Bytes {
        unsafe { &mut *(b as *mut [u8] as *mut Bytes) }
    }
    #[inline(never)]
    fn as_bytes(&self) -> &[u8] {
        &self.0
    }
    #[inline(never)]
    fn count(&self) -> usize {
        self.0.len()
    }
}

#[inline(never)]
fn probe_bytes(b: &Bytes) -> (usize, u8, u8, u8) {
    let n = b.count();
    let s = b.as_bytes();
    (n, s[0], s[1], s[n - 1])
}

// A DST with a SIZED PREFIX — the `PolymorphicIter<[MaybeUninit<char>]>` shape.
#[repr(C)]
struct Hdr {
    n: u32,
    m: u32,
    tail: [u8],
}

#[inline(never)]
fn make_hdr(buf: &[u8], tail_len: usize) -> &Hdr {
    // The metadata of `&Hdr` IS the tail's element count.
    unsafe { &*(core::ptr::slice_from_raw_parts(buf.as_ptr(), tail_len) as *const Hdr) }
}

#[inline(never)]
fn probe_hdr(h: &Hdr) -> (u32, u32, usize, u8, u8) {
    let t: &[u8] = &h.tail;
    let k = t.len();
    (h.n, h.m, k, t[0], t[k - 1])
}

// A fat DST reference sitting BETWEEN two scalars inside an aggregate.
struct Pair<'a> {
    before: i64,
    r: &'a Bytes,
    after: i64,
}

#[inline(never)]
fn pair_read(p: &Pair<'_>) -> (i64, usize, u8, i64) {
    (p.before, p.r.count(), p.r.as_bytes()[1], p.after)
}

#[inline(never)]
fn tail_write(b: &mut Bytes, v: u8) {
    let s = &mut b.0;
    let n = s.len();
    s[n - 1] = v;
}

// The built-in UNSIZE of a reference to a struct whose last field is unsized:
// `&Wrap<[u8; 4]> -> &Wrap<[u8]>`. This is `array::IntoIter::unsize`. The data
// pointer is unchanged and the metadata is the source array's length, so a
// fabricated length shows up as a wrong `k` and a wrong last element.
struct Wrap<T: ?Sized> {
    head: u32,
    tail: T,
}

#[inline(never)]
fn wrap_unsize(w: &Wrap<[u8; 4]>) -> &Wrap<[u8]> {
    w
}

#[inline(never)]
fn probe_wrap(w: &Wrap<[u8]>) -> (u32, usize, u8, u8) {
    let k = w.tail.len();
    (w.head, k, w.tail[0], w.tail[k - 1])
}

#[inline(never)]
fn read4(a: &[u8; 4]) -> (u8, u8, u8, u8) {
    (a[0], a[1], a[2], a[3])
}

#[inline(never)]
fn thin_control(r: &i64, p: *const i64) -> (i64, i64) {
    unsafe { (*r, *p) }
}

fn main() {
    let a: [u8; 5] = [11, 22, 33, 44, 55];

    let b = Bytes::new(&a);
    let (n1, e0, e1, el) = probe_bytes(b);
    println!("d1 {} {} {} {}", n1, e0, e1, el);

    let b2 = Bytes::new(&a[2..]);
    let (n2, f0, f1, fl) = probe_bytes(b2);
    println!("d2 {} {} {} {}", n2, f0, f1, fl);

    // 8 bytes of prefix (`n`, `m`) then a 4-byte tail.
    let raw: [u8; 12] = [1, 0, 0, 0, 2, 0, 0, 0, 77, 88, 99, 111];
    let h = make_hdr(&raw, 4);
    let (hn, hm, hk, t0, tl) = probe_hdr(h);
    println!("d3 {} {} {} {} {}", hn, hm, hk, t0, tl);

    let p = Pair { before: 7, r: b, after: 9 };
    let (pb, pl, pe, pa) = pair_read(&p);
    println!("d4 {} {} {} {}", pb, pl, pe, pa);

    let mut w: [u8; 4] = [1, 2, 3, 4];
    {
        let wb = Bytes::new_mut(&mut w);
        tail_write(wb, 42);
    }
    let (r0, r1, r2, r3) = read4(&w);
    println!("d5 {} {} {} {}", r0, r1, r2, r3);

    let ws = Wrap { head: 5, tail: [60u8, 61, 62, 63] };
    let wd = wrap_unsize(&ws);
    let (wh, wk, w0, wl) = probe_wrap(wd);
    println!("d6 {} {} {} {}", wh, wk, w0, wl);

    let cv: i64 = 1234;
    let (c1, c2) = thin_control(&cv, &cv as *const i64);
    println!("d7 {} {}", c1, c2);
}
