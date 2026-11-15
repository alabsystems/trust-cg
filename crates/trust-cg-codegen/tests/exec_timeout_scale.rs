// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `TRUST_CG_TEST_TIMEOUT_SCALE`, the load multiplier for the budgets of
//! generated-binary executions: unset keeps every budget exactly, a valid
//! integer multiplies it, and anything else is refused loudly.

#[path = "common/rosetta.rs"]
mod process;

use std::ffi::OsStr;
use std::time::Duration;

const BASE: Duration = Duration::from_secs(5);

#[test]
fn unset_scale_keeps_the_hard_coded_budget() {
    assert_eq!(process::scale_exec_timeout(BASE, None), BASE);
}

#[test]
fn integer_scale_multiplies_the_budget() {
    for (raw, expected) in [("1", 5), ("6", 30), ("20", 100)] {
        assert_eq!(
            process::scale_exec_timeout(BASE, Some(OsStr::new(raw))),
            Duration::from_secs(expected),
            "scale {raw}"
        );
    }
}

#[test]
fn invalid_scale_panics_instead_of_defaulting() {
    for raw in ["", "0", "21", "-1", "1.5", "six", " 6"] {
        let Err(refused) =
            std::panic::catch_unwind(|| process::scale_exec_timeout(BASE, Some(OsStr::new(raw))))
        else {
            panic!("scale {raw:?} must be refused");
        };
        let message = refused
            .downcast_ref::<String>()
            .expect("the refusal is a formatted message");
        assert!(
            message.contains(process::EXEC_TIMEOUT_SCALE_ENV),
            "scale {raw:?}: {message}"
        );
    }
}

#[test]
fn exec_timeout_reads_the_environment() {
    let raw = std::env::var_os(process::EXEC_TIMEOUT_SCALE_ENV);
    assert_eq!(
        process::exec_timeout(BASE),
        process::scale_exec_timeout(BASE, raw.as_deref())
    );
}
