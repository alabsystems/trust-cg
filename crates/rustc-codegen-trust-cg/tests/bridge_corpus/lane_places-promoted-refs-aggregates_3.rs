// Lane places-promoted-refs-aggregates, program 3: whole-aggregate FIELD reads
// through `&self` into memory-backed locals (an enum field `self.res`, a union
// field, a nested struct field), a scalar-element ARRAY field read out of a
// by-ref struct into a scalarized array (the `&dyn Trait` fat
// pointer is program 4), and a reference to a struct whose field is itself a
// multi-field struct (`&Outer { r: Range2, .. }`).
#![allow(dead_code)]

#[derive(Clone, Copy)]
enum Res { Ok(u32), Err(u8), Nothing }

#[derive(Clone, Copy)]
union Bits { w: u32, b: [u8; 4] }

struct Range2 { lo: usize, hi: usize }
struct Outer { r: Range2, data: [u8; 6], tag: u16, res: Res, bits: Bits }


#[inline(never)]
fn read_res(o: &Outer) -> Res { o.res }

#[inline(never)]
fn read_bits(o: &Outer) -> Bits { o.bits }

#[inline(never)]
fn read_range(o: &Outer) -> Range2 { Range2 { lo: o.r.lo + 1, hi: o.r.hi } }

#[inline(never)]
fn read_data(o: &Outer) -> u32 {
    let d: [u8; 6] = o.data;
    d[0] as u32 * 10000 + d[3] as u32 * 100 + d[5] as u32
}

#[inline(never)]
fn span(o: &Outer) -> usize { o.r.hi - o.r.lo + o.tag as usize }

fn describe(r: Res) -> u32 { match r { Res::Ok(v) => v, Res::Err(e) => 1000 + e as u32, Res::Nothing => 7 } }

fn main() {
    let o = Outer { r: Range2 { lo: 3, hi: 11 }, data: [1, 2, 3, 4, 5, 6], tag: 40, res: Res::Err(9), bits: Bits { w: 0x0403_0201 } };
    let o2 = Outer { r: Range2 { lo: 5, hi: 6 }, data: [6, 5, 4, 3, 2, 1], tag: 1, res: Res::Ok(77), bits: Bits { b: [9, 8, 7, 6] } };
    let a = describe(read_res(&o)) + describe(read_res(&o2));
    let b = unsafe { read_bits(&o).b[2] as u32 + read_bits(&o2).w };
    let r = read_range(&o);
    let c = r.lo * 100 + r.hi;
    let d = read_data(&o) + read_data(&o2);
    let e = span(&o) + span(&o2);
    println!("a={} b={} c={} d={} e={}", a, b, c, d, e);
}
