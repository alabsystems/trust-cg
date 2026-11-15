// Lane places-promoted-refs-aggregates, program 4: a `&mut dyn Trait` fat
// pointer stored as a struct field at construction into a memory-backed
// (by-value return) slot — `Sink { out: w, n }`, the `Formatter { buf, .. }`
// shape. STATUS: the backend REFUSES `main` (out-of-lane `Ty::dyn`: a caller
// holding a `&dyn`-field struct as a memory-backed local has no slot layout),
// so this program documents the admitted construct-site store and is not a
// passing differential yet; it becomes one when the caller side lands.
#![allow(dead_code)]

trait Out {
    fn put(&mut self, s: &str);
}

struct Sink<'a> { out: &'a mut dyn Out, n: u32 }

struct Buf { bytes: [u8; 32], len: usize }
impl Out for Buf {
    fn put(&mut self, s: &str) {
        for b in s.bytes() {
            if self.len < 32 { self.bytes[self.len] = b; self.len += 1; }
        }
    }
}

#[inline(never)]
fn make_sink<'a>(w: &'a mut dyn Out, n: u32) -> Sink<'a> { Sink { out: w, n } }

#[inline(never)]
fn sink_n(s: &Sink<'_>) -> u32 { s.n }

fn main() {
    let mut buf = Buf { bytes: [0; 32], len: 0 };
    {
        let mut sk = make_sink(&mut buf, 5);
        let n = sink_n(&sk);
        sk.out.put(if n == 5 { "big!" } else { "small?" });
    }
    let bl = buf.len;
    let mut bsum = 0u32;
    for i in 0..bl { bsum = bsum * 7 + buf.bytes[i] as u32; }
    println!("len={} sum={}", bl, bsum);
}
