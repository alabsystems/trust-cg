#!/bin/zsh
# Append two TEMPORARY #[ignore] dump tests (never committed) to the codegen tests:
#  * e2e_x86_64_i128_div.rs: s20_dump_i128_div_objects - the e2e's four i128 division
#    modules and one richer module (four libcalls, values live across them) at O0..O3;
#  * x86_source_bound_body.rs: s20_dump_fixture_objects - the body e2e fixture module
#    (slices 1-15, the slice-11 and slice-14 functions among them) for both triples at O0..O3.
# Each writes object bytes into $S20_BYTES_DIR. Restore with git checkout of both files.
W=${1:?worktree}
cat >> $W/crates/trust-cg-codegen/tests/e2e_x86_64_i128_div.rs <<'RS'

fn s20_rich_module() -> trust_ir::Module {
    use trust_ir::Ty;
    let mut builder = trust_ir_build::ModuleBuilder::new("s20_libcall_rich");
    let ty = builder.add_func_type(
        vec![Ty::U128, Ty::U128, Ty::I128, Ty::U64],
        vec![Ty::U128],
    );
    let mut f = builder.function("_s20_rich", ty);
    let entry = f.create_block();
    let a = f.add_block_param(entry, Ty::U128);
    let b = f.add_block_param(entry, Ty::U128);
    let c = f.add_block_param(entry, Ty::I128);
    let k = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    let q = f.binop(BinOp::UDiv, Ty::U128, a, b);
    let r = f.binop(BinOp::URem, Ty::U128, a, b);
    let s = f.binop(BinOp::SDiv, Ty::I128, c, c);
    let t = f.binop(BinOp::SRem, Ty::I128, s, c);
    let kk = f.zext(Ty::U64, Ty::U128, k);
    let qr = f.add(Ty::U128, q, r);
    let t = f.cast(trust_ir::CastOp::Bitcast, Ty::I128, Ty::U128, t);
    let x = f.binop(BinOp::Xor, Ty::U128, qr, t);
    let y = f.add(Ty::U128, x, kk);
    f.ret(vec![y]);
    f.build();
    builder.build().expect("ModuleBuilder::build: s20 rich module")
}

#[test]
#[ignore]
fn s20_dump_i128_div_objects() {
    use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
    use trust_cg_codegen::pipeline::OptLevel;
    use trust_cg_codegen::target::Target;
    let dir = std::path::PathBuf::from(std::env::var_os("S20_BYTES_DIR").expect("S20_BYTES_DIR"));
    std::fs::create_dir_all(&dir).unwrap();
    let mut modules: Vec<(String, trust_ir::Module)> = [
        ("sdiv", BinOp::SDiv),
        ("udiv", BinOp::UDiv),
        ("srem", BinOp::SRem),
        ("urem", BinOp::URem),
    ]
    .into_iter()
    .map(|(name, op)| (name.to_string(), build_i128_binop_module(&format!("_i128_{name}"), op)))
    .collect();
    modules.push(("rich".to_string(), s20_rich_module()));
    for (name, module) in modules {
        for (k, level) in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3]
            .into_iter()
            .enumerate()
        {
            let compiler = Compiler::new(CompilerConfig {
                opt_level: level,
                target: Target::X86_64,
                ..CompilerConfig::default()
            })
            .with_codegen_license(
                trust_cg_lower::CodegenLicensePolicy::default()
                    .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit),
            );
            let result = compiler
                .compile(&module)
                .unwrap_or_else(|error| panic!("{name} O{k}: {error}"));
            std::fs::write(dir.join(format!("i128_{name}_O{k}.o")), &result.object_code).unwrap();
        }
    }
}
RS
cat >> $W/crates/trust-cg-codegen/tests/x86_source_bound_body.rs <<'RS'

#[test]
#[ignore]
fn s20_dump_fixture_objects() {
    let dir = std::path::PathBuf::from(std::env::var_os("S20_BYTES_DIR").expect("S20_BYTES_DIR"));
    std::fs::create_dir_all(&dir).unwrap();
    for triple in TRIPLES {
        for (k, level) in [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3]
            .into_iter()
            .enumerate()
        {
            let module = pinned_target::pinned(&module(triple), triple);
            let result = std::thread::Builder::new()
                .stack_size(64 * 1024 * 1024)
                .spawn(move || {
                    let spec = TargetSpec::parse(triple).expect("x86-64 triple");
                    Compiler::new_for_target_spec(
                        CompilerConfig {
                            opt_level: level,
                            target: Target::X86_64,
                            emit_proofs: false,
                            parallel: false,
                            ..CompilerConfig::default()
                        },
                        spec,
                    )
                    .with_codegen_license(permit_unlicensed())
                    .compile(&module)
                })
                .unwrap()
                .join()
                .unwrap()
                .unwrap_or_else(|error| panic!("{triple} O{k}: {error}"));
            std::fs::write(dir.join(format!("fixture_{triple}_O{k}.o")), &result.object_code)
                .unwrap();
        }
    }
}
RS
echo appended
