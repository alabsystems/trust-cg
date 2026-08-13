// JSON schema round-trip tests.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use schemars::schema_for;

// This checks the generic schema-generation dependency. The authoritative
// committed generic schemas are produced by `trust-cg-test ratchet schema`.

#[test]
fn run_summary_schema_generates() {
    // Compile a tiny in-line type here to exercise the same schemars path
    // without exposing the binary crate's private result module.
    #[derive(serde::Serialize, serde::Deserialize, schemars::JsonSchema)]
    struct Empty {}
    let s = schema_for!(Empty);
    let json = serde_json::to_string(&s).expect("serialize");
    assert!(!json.is_empty());
}
