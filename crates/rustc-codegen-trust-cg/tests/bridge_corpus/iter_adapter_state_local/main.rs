// LLVM-compiled driver for `lib.rs` (see there). `main --list` prints the case
// names; `main <case>` runs one case and prints its result.
use std::hint::black_box as bb;

macro_rules! cases {
    ($($name:literal => $e:expr;)*) => {{
        let arg = std::env::args().nth(1).unwrap_or_default();
        if arg == "--list" {
            $(println!("{}", $name);)*
            return;
        }
        $(if arg == $name {
            println!("{:?}", $e);
            return;
        })*
        std::process::exit(2);
    }};
}

fn main() {
    let a = [1u32, 2, 3];
    let b = [10u32, 11, 12, 13];
    cases! {
        "chain_local_fold_a_none" => klib::chain_local_fold(bb(&a), bb(&b), bb(4));
        "chain_local_fold_ctl" => klib::chain_local_fold(bb(&a), bb(&b), bb(2));
        "chain_local_back_count_b_none" => klib::chain_local_back_count(bb(&a), bb(&b), bb(5));
        "chain_local_back_count_ctl" => klib::chain_local_back_count(bb(&a), bb(&b), bb(1));
    }
}
