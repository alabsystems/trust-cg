// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
// Actual compiler option values through the production adapter. No CG guest or
// proof credit. --parse-only observes real compiler argument parsing and exits
// from the configuration callback before session initialization or codegen.
#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_session;
#[cfg(rustc_structures_crate_type)]
extern crate rustc_structures;

#[path = "../../../src/compiler_options.rs"]
mod compiler_options;

use compiler_options::{
    CrateType, SAMPLE_PROFILE_OPTION, executable_only, rlib_only, sample_profile,
};
use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;
use std::path::PathBuf;

struct ParseOnly;

impl rustc_driver::Callbacks for ParseOnly {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        let expected = std::env::var_os("EXPECTED_SAMPLE_PROFILE").map(PathBuf::from);
        assert_eq!(sample_profile(&config.opts), expected.as_deref());
        assert_eq!(
            SAMPLE_PROFILE_OPTION,
            if cfg!(rustc_codegen_sample_profile) {
                "`-C profile-sample-use`"
            } else {
                "`-Z profile-sample-use`"
            }
        );
        println!(
            "PARSED_SAMPLE_PROFILE present={} option={SAMPLE_PROFILE_OPTION}",
            expected.is_some()
        );
        std::process::exit(0);
    }
}

fn main() {
    let mut args: Vec<String> = std::env::args().collect();
    if args.get(1).is_some_and(|arg| arg == "--parse-only") {
        args.remove(1);
        rustc_driver::run_compiler(&args, &mut ParseOnly);
        panic!("configuration callback did not run");
    }
    let kinds = [
        CrateType::Executable,
        CrateType::Dylib,
        CrateType::Rlib,
        CrateType::StaticLib,
        CrateType::Cdylib,
        CrateType::ProcMacro,
        CrateType::Sdylib,
    ];
    let mut cases = 0;
    for mask in 0u8..128 {
        let selected: Vec<_> = kinds
            .iter()
            .enumerate()
            .filter_map(|(i, kind)| (mask & (1 << i) != 0).then_some(*kind))
            .collect();
        let mut reverse = selected.clone();
        reverse.reverse();
        let repeated: Vec<_> = selected.iter().flat_map(|kind| [*kind, *kind]).collect();
        for input in [&selected, &reverse, &repeated] {
            assert_eq!(
                executable_only(input),
                mask <= 1,
                "executable policy mask={mask}"
            );
            assert_eq!(rlib_only(input), mask == 4, "rlib policy mask={mask}");
            cases += 1;
        }
    }
    assert_eq!(cases, 384);
    let mut non_utf8 = b"sample-".to_vec();
    non_utf8.push(0xff);
    let paths = [
        None,
        Some(PathBuf::new()),
        Some(PathBuf::from("profiles / kept.prof")),
        Some(PathBuf::from(OsString::from_vec(non_utf8))),
    ];
    for path in &paths {
        let mut opts = rustc_session::config::Options::default();
        #[cfg(rustc_codegen_sample_profile)]
        {
            opts.cg.profile_sample_use = path.clone();
        }
        #[cfg(not(rustc_codegen_sample_profile))]
        {
            opts.unstable_opts.profile_sample_use = path.clone();
        }
        assert_eq!(sample_profile(&opts), path.as_deref(), "profile path");
    }
    println!(
        "COMPILER_OPTIONS masks=128 orders=3 crate_cases={cases} kinds=7 profile_paths=4 option={SAMPLE_PROFILE_OPTION}"
    );
}
