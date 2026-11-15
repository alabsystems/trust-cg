from pathlib import Path
import hashlib, json, subprocess

r = Path('/home/ayates/trust-cg-soundness-20260914')
b = Path('/home/ayates/trust-cg-output-byte-binding-20260917')
c = Path('/home/ayates/trust-cg-output-source-capture-20260917')
head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=b, text=True).strip()
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=c, text=True).strip() == head
assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=c)
names = ['crates/rustc-codegen-trust-cg/Cargo.toml', 'crates/rustc-codegen-trust-cg/src/lib.rs', 'crates/trust-cg-verify/src/function_verifier.rs', 'crates/rustc-codegen-trust-cg/src/canonicalize_copies.rs']
before = {name:hashlib.sha256((c / name).read_bytes()).hexdigest() for name in names}
path = c / names[0]
text = path.read_text()
assert text.count('[dependencies]\n') == 1
path.write_text(text.replace('[dependencies]\n', '[dependencies]\nserde_json = "1.0"\n'))
path = c / names[1]
text = path.read_text()
needle = ') -> Result<CompiledModule, String> {\n    // Route object emission through the target-aware Trust Codegen `Compiler`'
assert text.count(needle) == 1
replacement = ''') -> Result<CompiledModule, String> {
    if module.functions.iter().any(|f| f.name.starts_with("aliased_") || f.name.starts_with("local_cell")) {
        eprintln!("OUTPUT_SOURCE_MODULE={}", serde_json::to_string(&module).map_err(|e| e.to_string())?);
    }
    // Route object emission through the target-aware Trust Codegen `Compiler`'''
path.write_text(text.replace(needle, replacement))
path = c / names[2]
text = path.read_text()
needle = '''        // TV-2: Enforce must not silently degrade to the source-less verifier'''
assert text.count(needle) == 1
replacement = '''        if func.name.starts_with("aliased_") || func.name.starts_with("local_cell") {
            eprintln!("CALL_FRAME_INPUT={}", serde_json::json!({
                "name": &func.name,
                "lir": lir_source,
                "machine_debug": format!("{func:#?}"),
                "xcheck": format!("{xcheck_mode:?}")
            }));
        }
        // TV-2: Enforce must not silently degrade to the source-less verifier'''
path.write_text(text.replace(needle, replacement))
(c / names[3]).write_bytes((b / names[3]).read_bytes())
subprocess.run(['git', 'add', '--', *names], cwd=c, check=True)
after = {name:hashlib.sha256((c / name).read_bytes()).hexdigest() for name in names}
(r / 'cg-call-frame-repaired-instrumentation.json').write_text(json.dumps(dict(source=head, before=before, after=after), indent=2) + '\n')
(r / 'cg-call-frame-repaired-instrumentation.patch').write_bytes(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=c))
print('Instrumented isolated checkout with exact Alloca pointer normalization repair.', flush=True)
