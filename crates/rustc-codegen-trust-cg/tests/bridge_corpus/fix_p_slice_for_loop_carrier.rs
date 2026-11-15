// Corpus: `for b in s { }` over a `&[u8]` at `-O2` — a REGRESSION PIN for the
// fat-pointer carrier model.
//
// This is the most ordinary loop in Rust and it compiles today. It is here
// because at `-O2` rustc inlines `slice::Iter::new`, whose body is
// `NonNull::from_ref(slice).cast::<T>()` — it builds a `NonNull<[T]>` CARRIER of
// the slice fat pointer and immediately narrows it to a thin `NonNull<T>`. So
// the moment the carrier is modeled as two lanes (which is what closes the
// metadata-truncation channel), this loop needs the fat -> thin cast seam or it
// loses codegen entirely. Measured: with the `ty::Pat` peel and WITHOUT the
// seam, `sum` fails closed at `-O2` ("aggregate reference nested field is a fat
// pointer … pattern_type!(*const [u8] is !null)") while compiling fine at `-O0`
// — an opt-level-dependent refusal on a ubiquitous shape.
//
// The accumulator is order- and value-sensitive (`t*7 + b`), so a dropped
// element, a wrong start address or a wrong end bound changes stdout.
#[inline(never)]
fn sum(s: &[u8]) -> u64 {
    let mut t: u64 = 0;
    for b in s {
        t = t * 7 + (*b as u64);
    }
    t
}

#[inline(never)]
fn sum_rev(s: &[u8]) -> u64 {
    let mut t: u64 = 0;
    for b in s.iter().rev() {
        t = t * 7 + (*b as u64);
    }
    t
}

fn main() {
    let a: [u8; 6] = [1, 2, 3, 4, 5, 6];
    println!("s1 {}", sum(&a));
    println!("s2 {}", sum(&a[2..5]));
    println!("s3 {}", sum(&[]));
    println!("s4 {}", sum_rev(&a));
    println!("s5 {}", sum_rev(&a[1..4]));
}
