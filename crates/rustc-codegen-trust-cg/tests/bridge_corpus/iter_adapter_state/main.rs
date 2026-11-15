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
        // `a` exhausted and cleared by the 4th `next`; the control keeps it Some.
        "chain_slice_count_a_none" => { let mut c = bb(a.iter().chain(b.iter())); for _ in 0..4 { c.next(); } klib::chain_slice_count(c) };
        "chain_slice_count_ctl" => { let mut c = bb(a.iter().chain(b.iter())); for _ in 0..2 { c.next(); } klib::chain_slice_count(c) };
        "chain_slice_fold_a_none" => { let mut c = bb(a.iter().chain(b.iter())); for _ in 0..4 { c.next(); } klib::chain_slice_fold(c) };
        // `b` exhausted and cleared by `next_back`.
        "chain_slice_fold_b_none" => { let mut c = bb(a.iter().chain(b.iter())); for _ in 0..5 { c.next_back(); } klib::chain_slice_fold(c) };
        "chain_slice_collect_a_none" => { let mut c = bb(a.iter().chain(b.iter())); for _ in 0..4 { c.next(); } klib::chain_slice_collect(c) };
        "chain_range_count_a_none" => { let mut c = bb((bb(0u64)..3).chain(10..14)); for _ in 0..4 { c.next(); } klib::chain_range_count(c) };
        "chain_range_sum_a_none" => { let mut c = bb((bb(0u64)..3).chain(10..14)); for _ in 0..4 { c.next(); } klib::chain_range_sum(c) };
        "chain_range_sum_b_none" => { let mut c = bb((bb(0u64)..3).chain(10..14)); for _ in 0..5 { c.next_back(); } klib::chain_range_sum(c) };
        "chain_range_sum_ctl" => { let mut c = bb((bb(0u64)..3).chain(10..14)); c.next(); klib::chain_range_sum(c) };
        "take_while_first_none" => klib::take_while_first_none(bb(3), bb(12));
        "take_while_first_none_ctl" => klib::take_while_first_none(bb(0), bb(12));
        "take_while_drained_count" => klib::take_while_drained_count(bb(0), bb(12));
        "take_while_predicate_calls" => klib::take_while_predicate_calls(bb(3), bb(12));
        "take_while_predicate_calls_ctl" => klib::take_while_predicate_calls(bb(0), bb(12));
        "take_while_value_drained" => { let mut it = klib::take_while_make(bb(0), bb(10)); while it.next().is_some() {} klib::take_while_sum(it) };
        "take_while_value_ctl" => { let mut it = klib::take_while_make(bb(0), bb(10)); it.next(); klib::take_while_sum(it) };
        "flat_map_next" => klib::flat_map_u32(bb(4)).next();
        "flat_map_take" => klib::flat_map_u32(bb(4)).take(10).collect::<Vec<_>>();
        "flat_map_size_hint" => klib::flat_map_u32(bb(4)).size_hint();
        "flat_map_empty" => klib::flat_map_u32(bb(0)).take(10).collect::<Vec<_>>();
        "flat_map_usize_take" => klib::flat_map_usize(bb(4)).take(10).collect::<Vec<_>>();
        "flat_map_local_size_hint" => klib::flat_map_size_hint(bb(4));
        "flat_map_rev" => klib::flat_map_double_ended(bb(5)).rev().collect::<Vec<_>>();
        "flat_map_back_then_front" => { let mut it = klib::flat_map_double_ended(bb(5)); (it.next_back(), it.next(), it.size_hint()) };
        "flat_map_front_back_collect" => { let mut it = klib::flat_map_double_ended(bb(5)); it.next(); it.next(); it.next_back(); it.collect::<Vec<_>>() };
        "flat_map_clone" => { let it = klib::flat_map_double_ended(bb(4)); let c = it.clone(); (it.count(), c.collect::<Vec<_>>()) };
    }
}
