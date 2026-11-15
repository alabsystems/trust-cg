// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! The LLVM-compiled driver of `intercept_panic_replay_differential`.
//!
//! `driver --list` names the cases. `driver CASE` runs the case in a child
//! process and prints the child's stdout, its exit status or signal, and its
//! stderr lines, so a panic that aborts is observed rather than ended on. The
//! child's hook prints the payload's type and text and the full location, then
//! returns, so the panic runtime continues as it would without a hook.
use intercept_panic_callee as callee;
use std::hint::black_box as bb;
use std::io::Write;

const CASES: &[&str] = &[
    "controls",
    "swap_remove_u32",
    "swap_remove_pair",
    "remove_u32",
    "insert_u32",
    "split_off_len",
    "insert_mut_u32",
    "rotate_left_u32",
    "rotate_right_u8",
    "drain_from",
    "extend_within_end",
    "extend_within_start",
    "sum_u8",
    "product_u16",
    "slice_swap_first",
    "slice_swap_second",
    "vec_range_to",
    "vec_range_mut",
    "array_range",
    "array_range_mut",
    "str_range_order",
    "str_range_end",
    "str_range_boundary",
    "split_at_len",
    "str_split_at_end",
    "str_split_at_boundary",
    "str_split_at_mut",
    "windows_len",
    "chunks_len",
    "chunks_exact_len",
    "rchunks_len",
    "rchunks_exact_len",
    "c_panic_literal",
    "c_assert",
    "c_unreachable",
    "c_swap_remove",
    "c_split_at",
    "c_str_range",
    "c_str_split_at",
];

fn hook(info: &std::panic::PanicHookInfo<'_>) {
    let payload = info.payload();
    let (kind, text) = if let Some(text) = payload.downcast_ref::<&str>() {
        ("str", (*text).to_owned())
    } else if let Some(text) = payload.downcast_ref::<String>() {
        ("string", text.clone())
    } else {
        ("other", String::new())
    };
    let at = info.location().map_or_else(
        || "<no location>".to_owned(),
        |at| format!("{}:{}:{}", at.file(), at.line(), at.column()),
    );
    println!("HOOK {kind} {text:?} at {at}");
    std::io::stdout().flush().unwrap();
}

fn controls() {
    let mut v = bb(vec![1u32, 2, 3]);
    println!("swap_remove {}", callee::swap_remove_u32(&mut v, bb(0)));
    let mut p = bb(vec![
        callee::Pair { a: 1, b: 2 },
        callee::Pair { a: 3, b: 4 },
    ]);
    println!(
        "swap_remove_pair {:?}",
        callee::swap_remove_pair(&mut p, bb(0))
    );
    println!("remove {}", callee::remove_u32(&mut v, bb(0)));
    callee::insert_u32(&mut v, bb(1));
    println!("insert {v:?}");
    println!("split_off {} {v:?}", callee::split_off_len(&mut v, bb(1)));
    let mut r = bb(vec![1u32, 2, 3, 4]);
    callee::rotate_left_u32(&mut r, bb(1));
    let mut b = bb([1u8, 2, 3, 4]);
    callee::rotate_right_u8(&mut b, bb(3));
    println!("rotate {r:?} {b:?}");
    callee::drain_from(&mut r, bb(2));
    callee::extend_within(&mut r, bb(0), bb(2));
    println!("drain extend {r:?}");
    println!("sum {}", callee::sum_u8(bb(&[1u8, 2, 3])));
    println!("product {}", callee::product_u16(bb(&[2u16, 3])));
    let mut s = bb([1u32, 2, 3]);
    callee::slice_swap(&mut s, bb(0), bb(2));
    println!("swap {s:?}");
    println!(
        "vec_range_to {}",
        callee::vec_range_to(&bb(vec![1u32, 2, 3]), bb(2))
    );
    println!("array_range {}", callee::array_range(bb(1), bb(3)));
    let mut w = bb(vec![1u32, 2, 3]);
    println!(
        "full {} mut {} {} {}",
        callee::vec_range_full(&w),
        callee::vec_range_mut(&mut w, bb(1), bb(3)),
        callee::array_range_mut(bb(0), bb(4)),
        callee::str_range(bb("abc"), bb(1), bb(3))
    );
    println!("insert_mut {} {w:?}", callee::insert_mut_u32(&mut w, bb(3)));
    println!("str_range_to {}", callee::str_range_to(bb("abc"), bb(2)));
    println!(
        "split_at {}",
        callee::split_at_len(bb(&[1u32, 2, 3]), bb(1))
    );
    let mut text = String::from("t\u{e9}t");
    println!(
        "str_split_at {} {}",
        callee::str_split_at(bb("abc"), bb(3)),
        callee::str_split_at_mut(bb(text.as_mut_str()), bb(3))
    );
    println!("windows {}", callee::windows_len(bb(&[1u32, 2, 3]), bb(2)));
    println!("chunks {}", callee::chunks_len(bb(&[1u32, 2, 3]), bb(2)));
    println!(
        "chunks_exact {} rchunks {} rchunks_exact {}",
        callee::chunks_exact_len(bb(&[1u32, 2, 3]), bb(2)),
        callee::rchunks_len(bb(&[1u32, 2, 3]), bb(2)),
        callee::rchunks_exact_len(bb(&[1u32, 2, 3]), bb(2))
    );
    println!(
        "c {}",
        callee::c_panic_literal(bb(0)) + callee::c_assert(bb(1))
    );
    println!("c {}", callee::c_unreachable(bb(0)));
    println!("c {}", callee::c_swap_remove(&mut bb(vec![5u32, 6]), bb(1)));
    println!("c {}", callee::c_split_at(bb(&[1u32, 2]), bb(1)));
    println!("c {}", callee::c_str_range(bb("ab"), bb(1)));
    println!("c {}", callee::c_str_split_at(bb("ab"), bb(2)));
}

fn child(case: &str) {
    std::panic::set_hook(Box::new(hook));
    let value: u64 = match case {
        "controls" => {
            controls();
            0
        }
        "swap_remove_u32" => callee::swap_remove_u32(&mut bb(vec![1u32, 2, 3]), bb(7)).into(),
        "swap_remove_pair" => {
            callee::swap_remove_pair(&mut bb(vec![callee::Pair { a: 1, b: 2 }]), bb(1)).b
        }
        "remove_u32" => callee::remove_u32(&mut bb(vec![1u32, 2, 3]), bb(3)).into(),
        "insert_u32" => {
            callee::insert_u32(&mut bb(vec![1u32, 2, 3]), bb(4));
            0
        }
        "split_off_len" => callee::split_off_len(&mut bb(vec![1u32, 2, 3]), bb(5)) as u64,
        "insert_mut_u32" => callee::insert_mut_u32(&mut bb(vec![1u32]), bb(3)).into(),
        "rotate_left_u32" => {
            callee::rotate_left_u32(&mut bb(vec![1u32, 2, 3]), bb(7));
            0
        }
        "rotate_right_u8" => {
            callee::rotate_right_u8(&mut bb([1u8, 2, 3, 4]), bb(5));
            0
        }
        "drain_from" => {
            callee::drain_from(&mut bb(vec![1u32, 2, 3]), bb(5));
            0
        }
        "extend_within_end" => {
            callee::extend_within(&mut bb(vec![1u32, 2, 3]), bb(1), bb(5));
            0
        }
        "extend_within_start" => {
            callee::extend_within(&mut bb(vec![1u32, 2, 3]), bb(3), bb(2));
            0
        }
        "sum_u8" => callee::sum_u8(bb(&[200u8, 100, 7])).into(),
        "product_u16" => callee::product_u16(bb(&[300u16, 300])).into(),
        "slice_swap_first" => {
            callee::slice_swap(&mut bb([1u32, 2, 3]), bb(4), bb(9));
            0
        }
        "slice_swap_second" => {
            callee::slice_swap(&mut bb([1u32, 2, 3]), bb(0), bb(9));
            0
        }
        "vec_range_to" => callee::vec_range_to(&bb(vec![1u32, 2, 3]), bb(7)) as u64,
        "vec_range_mut" => callee::vec_range_mut(&mut bb(vec![1u32, 2, 3]), bb(1), bb(5)) as u64,
        "array_range" => callee::array_range(bb(1), bb(9)) as u64,
        "array_range_mut" => callee::array_range_mut(bb(3), bb(2)) as u64,
        "str_range_order" => callee::str_range(bb("abc"), bb(2), bb(1)) as u64,
        "str_range_end" => callee::str_range_to(bb("abc"), bb(7)) as u64,
        "str_range_boundary" => callee::str_range_to(bb("\u{e9}t\u{e9}"), bb(1)) as u64,
        "split_at_len" => callee::split_at_len(bb(&[1u32, 2, 3]), bb(4)) as u64,
        "str_split_at_end" => callee::str_split_at(bb("abc"), bb(4)) as u64,
        "str_split_at_boundary" => callee::str_split_at(bb("\u{e9}t"), bb(1)) as u64,
        "str_split_at_mut" => {
            let mut text = String::from("t\u{e9}");
            callee::str_split_at_mut(bb(text.as_mut_str()), bb(2)) as u64
        }
        "windows_len" => callee::windows_len(bb(&[1u32, 2, 3]), bb(0)) as u64,
        "chunks_len" => callee::chunks_len(bb(&[1u32, 2, 3]), bb(0)) as u64,
        "chunks_exact_len" => callee::chunks_exact_len(bb(&[1u32, 2, 3]), bb(0)) as u64,
        "rchunks_len" => callee::rchunks_len(bb(&[1u32, 2, 3]), bb(0)) as u64,
        "rchunks_exact_len" => callee::rchunks_exact_len(bb(&[1u32, 2, 3]), bb(0)) as u64,
        "c_panic_literal" => callee::c_panic_literal(bb(1)).into(),
        "c_assert" => callee::c_assert(bb(2)).into(),
        "c_unreachable" => callee::c_unreachable(bb(1)).into(),
        "c_swap_remove" => callee::c_swap_remove(&mut bb(vec![1u32, 2]), bb(2)).into(),
        "c_split_at" => callee::c_split_at(bb(&[1u32, 2]), bb(3)) as u64,
        "c_str_range" => callee::c_str_range(bb("ab"), bb(3)) as u64,
        "c_str_split_at" => callee::c_str_split_at(bb("\u{e9}"), bb(1)) as u64,
        other => panic!("unknown case {other}"),
    };
    println!("RETURNED {value}");
}

fn main() {
    let argument = std::env::args().nth(1).unwrap_or_default();
    if argument == "--list" {
        for case in CASES {
            println!("{case}");
        }
        return;
    }
    if let Some(case) = argument.strip_prefix('@') {
        child(case);
        return;
    }
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .arg(format!("@{argument}"))
        .env("RUST_BACKTRACE", "0")
        .output()
        .unwrap();
    use std::os::unix::process::ExitStatusExt;
    let status = match (output.status.code(), output.status.signal()) {
        (Some(code), _) => format!("exit {code}"),
        (None, Some(signal)) => format!("signal {signal}"),
        _ => "unknown".to_owned(),
    };
    print!("{}", String::from_utf8_lossy(&output.stdout));
    println!("STATUS {status}");
    for line in String::from_utf8_lossy(&output.stderr).lines() {
        if !line.starts_with(' ') && !line.starts_with("note:") {
            println!("STDERR {line}");
        }
    }
}
