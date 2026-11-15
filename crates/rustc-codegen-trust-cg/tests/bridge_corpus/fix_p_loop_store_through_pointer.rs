// Corpus: a loop that writes THROUGH a pointer it carries.
//
// Thin pointers became loop-header phis (275e8973a), so a `&mut` live across a
// loop is threaded through the header as an identity phi. The back-edge
// faithfulness check in `patch_loop_header_edge` counted a store THROUGH that
// pointer (`(*_2) = Add(copy (*_2), ..)`) as a mutation OF the pointer, found
// its back-edge value equal to the phi parameter, and refused the function:
//
//     loop-carried local _2 is mutated inside the loop but its back-edge value
//     is the unchanged loop-header phi parameter
//
// although only the pointee changed. The completeness gate already skipped
// `Deref`-led stores; both now read one def-site map
// (`own_storage_assign_blocks`).
//
// WHAT EACH ROW WOULD CATCH. Every printed value is the pointee after the
// loop, so a store that really was dropped (the miscompile the check exists
// for) prints the entry value instead.
//  * `closure_store`: Trust run-make `trust-ir-cg-borrow-join-lanes`'s
//    `loop_store_nojoin`, a `u128` accumulated by a closure capturing `&mut`;
//    refused at -O2/-O3 where the closure inlines into the loop.
//  * `closure_store_u64`: the same shape over a `u64` with a non-idempotent
//    update, so a dropped or duplicated store changes the number.
//  * `ref_store`: a plain `let r = &mut value;` written in the loop; refused
//    at -O0, where the reference stays a local.
#[inline(never)]
fn count() -> u32 {
    std::hint::black_box(4)
}

#[inline(never)]
fn bump() -> u128 {
    std::hint::black_box(1)
}

#[inline(never)]
fn step() -> u64 {
    std::hint::black_box(5)
}

#[inline(never)]
fn closure_store() -> u128 {
    let mut value: u128 = 0;
    let mut ef = || {
        value += bump();
    };
    let n = count();
    let mut i = 0;
    while i < n {
        ef();
        i += 1;
    }
    value
}

#[inline(never)]
fn closure_store_u64() -> u64 {
    let mut value: u64 = 3;
    let mut ef = || {
        value = value * 2 + step();
    };
    let n = count();
    let mut i = 0;
    while i < n {
        ef();
        i += 1;
    }
    value
}

#[inline(never)]
fn ref_store(seed: u64) -> u64 {
    let mut value = seed;
    let r = &mut value;
    let n = count();
    let mut i = 0;
    while i < n {
        *r = *r * 3 + step();
        i += 1;
    }
    value
}

fn main() {
    println!("s1 {}", closure_store());
    println!("s2 {}", closure_store_u64());
    println!("s3 {}", ref_store(std::hint::black_box(2)));
}
