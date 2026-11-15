extern crate projected_aggregate_types;
use projected_aggregate_types::WithZst;
unsafe extern "Rust" {
    fn borrowed(v: WithZst, cb: fn(&mut WithZst)) -> u64;
}

fn keep(_: &mut WithZst) {}
fn bump(v: &mut WithZst) {
    v.a = v.a.wrapping_mul(0x9e37_79b9_7f4a_7c15).rotate_left(7);
    v.b = v.b.wrapping_add(0x1234);
}
fn swap(v: &mut WithZst) {
    let a = v.a;
    v.a = !(v.b as u64);
    v.b = a as u16 ^ 0xbeef;
}

fn main() {
    let mut checks = 0;
    let callbacks: [fn(&mut WithZst); 3] = [keep, bump, swap];
    for i in 0..4096u64 {
        let a = i.wrapping_mul(0xd6e8_feb8_6659_fd93) ^ (i << 51);
        let b = (i as u16).wrapping_mul(0x9e37);
        for cb in callbacks {
            // Oracle: the callback applied to a local copy, then the same read.
            let mut expected = WithZst {
                z: (),
                a,
                marker: (),
                b,
            };
            cb(&mut expected);
            let got = unsafe {
                borrowed(
                    WithZst {
                        z: (),
                        a,
                        marker: (),
                        b,
                    },
                    cb,
                )
            };
            assert_eq!(got, expected.a ^ (expected.b as u64), "{i} {a:#x} {b:#x}");
            checks += 1;
        }
    }
    println!("PASS zst_borrow checks={checks}");
}
