// Protocol fixture for the matrix parser, independent of Cargo and repo crates.

#[test]
fn executes_normally() {
    println!("ordinary successful test output");
}

#[test]
fn skips_missing_capability() {
    eprintln!("SKIP: required capability is unavailable");
    eprintln!("SKIP runtime half: another detail from the same test");
}

#[test]
fn diagnostics_are_not_suite_events() {
    println!("test result: ok. 999 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;");
    println!(r#"{{"type":"suite","event":"ok","passed":999}}"#);
    println!("Running fake binary from a captured diagnostic");
    println!("run_with_timeout: command exceeded 1500s: captured negative control");
}

#[test]
fn fails_after_partial_skip() {
    eprintln!("SKIP optional diagnostic: failure must still win");
    panic!("intentional protocol fixture failure");
}

#[test]
#[ignore = "intentional protocol fixture ignore"]
fn ignored_by_libtest() {}
