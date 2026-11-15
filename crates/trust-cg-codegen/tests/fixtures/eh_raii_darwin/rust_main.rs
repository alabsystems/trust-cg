// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//
// AOT driver of the Rust-panic arm of the Darwin mixed-codegen
// exception/RAII campaign. Built twice by rustc: linked with the trust-cg
// object (the `tcgr_*` chains), and with `--cfg reference` as the Rust-only
// reference (no trust-cg code at all). The trace goes to stdout.

mod rust_arm;

#[cfg(not(reference))]
mod chains {
    use super::rust_arm::Table;

    unsafe extern "C-unwind" {
        fn tcgr_cleanup(x: u32) -> u32;
        fn tcgr_empty_cleanup(x: u32) -> u32;
        fn tcgr_plain(x: u32) -> u32;
        fn tcgr_nested(x: u32) -> u32;
        fn tcgr_through(x: u32) -> u32;
        fn tcgr_two_guards(x: u32) -> u32;
        fn tcgr_rust_mid(x: u32) -> u32;
        fn tcgr_cleanup_dyn(x: u32) -> u32;
        fn tcgr_empty_cleanup_dyn(x: u32) -> u32;
        fn tcgr_plain_dyn(x: u32) -> u32;
        fn tcgr_nested_dyn(x: u32) -> u32;
        fn tcgr_through_dyn(x: u32) -> u32;
        fn tcgr_two_guards_dyn(x: u32) -> u32;
        fn tcgr_rust_mid_dyn(x: u32) -> u32;
    }

    pub fn table() -> Table {
        [
            tcgr_cleanup,
            tcgr_empty_cleanup,
            tcgr_plain,
            tcgr_nested,
            tcgr_through,
            tcgr_two_guards,
            tcgr_rust_mid,
            tcgr_cleanup_dyn,
            tcgr_empty_cleanup_dyn,
            tcgr_plain_dyn,
            tcgr_nested_dyn,
            tcgr_through_dyn,
            tcgr_two_guards_dyn,
            tcgr_rust_mid_dyn,
        ]
    }
}

#[cfg(reference)]
mod chains {
    pub fn table() -> super::rust_arm::Table {
        super::rust_arm::reference_table()
    }
}

fn main() {
    rust_arm::install_quiet_hook();
    // Each line is printed (and, stdout being line-buffered, written) as soon
    // as its case has run: a case that crashes the process is the one after
    // the last line.
    rust_arm::run_matrix(&chains::table(), |line| println!("{line}"));
    std::process::exit(if rust_arm::errors() == 0 { 0 } else { 1 });
}
