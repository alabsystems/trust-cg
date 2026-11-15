// Supply only the compiler constant needed to compile the imported test helpers.
// These process contracts never run the imported compiler differentials.
fn main() {
    let compiler = std::env::var("RUSTC").expect("Cargo compiler");
    let output = std::path::PathBuf::from(std::env::var_os("OUT_DIR").unwrap());
    std::fs::write(
        output.join("test_build_compiler.rs"),
        format!("const BUILD_COMPILER: &str = {compiler:?};\n"),
    )
    .unwrap();
}
