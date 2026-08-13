// Minimal `main` program for the pinned rustc codegen-backend smoke test.
//
// The bridge compiles and links this file through
// `-Zcodegen-backend=<trust-cg-dylib>`. The resulting executable deliberately
// runs forever so the integration test can confirm execution under a bounded
// timeout without relying on additional Rust language features.
fn main() {
    loop {}
}
