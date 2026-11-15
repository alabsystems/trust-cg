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
    cases! {
        "ret_u32_take" => klib::ret_u32(bb(10)).take(8).collect::<Vec<_>>();
        "ret_u32_size_hint" => klib::ret_u32(bb(10)).size_hint();
        "ret_u32_len" => klib::ret_u32(bb(9)).len();
        "ret_u8_take" => klib::ret_u8(bb(200), bb(255)).take(4).collect::<Vec<_>>();
        "ret_u64_near_max" => klib::ret_u64_near_max().collect::<Vec<_>>();
        "ret_empty" => klib::ret_empty(bb(5)).take(6).collect::<Vec<_>>();
        "ret_i32_ctl" => klib::ret_i32(bb(10)).take(8).collect::<Vec<_>>();
        "ret_incl_i32" => klib::ret_incl_i32(bb(-5), bb(10)).take(8).collect::<Vec<_>>();
        "ret_incl_u8" => klib::ret_incl_u8(bb(250), bb(255)).collect::<Vec<_>>();
        "ret_chain" => klib::ret_chain(bb(5)).take(8).collect::<Vec<_>>();
        "arg_for_sum" => klib::for_sum(bb((0u32..10).step_by(3)));
        "arg_for_sum_advanced" => { let mut it = (0u32..20).step_by(3); it.next(); it.next(); klib::for_sum(bb(it)) };
        "arg_next_pair" => klib::next_pair(bb((5u64..40).step_by(6)));
        "arg_terminal_sum" => { let mut it = (0u32..20).step_by(3); it.next(); klib::terminal_sum(bb(it)) };
        "arg_terminal_collect" => klib::terminal_collect(bb((3usize..30).step_by(7)));
        "arg_terminal_incl_count" => { let mut it = (1u32..=10).step_by(3); it.next(); klib::terminal_incl_count(bb(it)) };
        "ret_u8_step_over_max" => { let mut it = klib::ret_u8_step_over_max(bb(3), bb(250)); (it.next(), it.next(), it.next()) };
        "ret_u128" => { let mut it = klib::ret_u128(bb(23)); (it.next(), it.collect::<Vec<_>>()) };
        "arg_terminal_incl_u64_sum" => { let mut it = (bb(1u64)..=20).step_by(4); it.next(); klib::terminal_incl_u64_sum(it) };
        "arg_terminal_usize_count" => { let mut it = (bb(1usize)..50).step_by(7); for _ in 0..3 { it.next(); } klib::terminal_usize_count(it) };
        "local_u16_sum_fresh" => klib::local_u16_sum(bb(40), bb(0));
        "local_u16_sum_advanced" => klib::local_u16_sum(bb(40), bb(3));
        "local_u16_count_advanced" => klib::local_u16_count(bb(40), bb(3));
        "local_u16_collect_advanced" => klib::local_u16_collect(bb(40), bb(3));
        "local_incl_sum" => klib::local_incl_sum(bb(30));
        "ref_any_exhausted_mid_skip" => { let mut it = (bb(1i32)..11).step_by(4); let found = klib::ref_any_i32(&mut it); (found, format!("{it:?}"), it.next()) };
        "ref_position_incl_exhausted" => { let mut it = (bb(1u64)..=12).step_by(5); it.next(); let found = klib::ref_position_incl(&mut it); (found, format!("{it:?}"), it.next()) };
        "shared_lib_loop" => klib::shared_u64(bb(30));
        "shared_driver_for" => { let mut v = Vec::new(); for x in (bb(5u64)..30).step_by(6) { v.push(x); } v };
        "shared_driver_next" => { let mut it = (bb(5u64)..30).step_by(6); (it.next(), it.next(), it.size_hint()) };
    }
}
