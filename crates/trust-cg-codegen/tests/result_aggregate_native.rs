// Copyright 2026 Andrew Yates. Apache-2.0.
//! Actual direct-THIR Result bodies through canonical Compiler::compile.
//! Native execution is engineering evidence, not source or kernel proof.
#![cfg(all(target_arch = "aarch64", target_os = "macos"))]
#[path = "common/rosetta.rs"]
mod process;
use std::{fs, path::PathBuf, process::Command};
use trust_cg_codegen::{Compiler, CompilerConfig, pipeline::OptLevel, target::TargetSpec};
use trust_cg_lower::{CodegenLicensePolicy, UnlicensedBodyPolicy};
use trust_ir::Module;
fn compile(m: &Module, opt: OptLevel) -> Result<Vec<u8>, String> {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: opt,
            emit_proofs: false,
            emit_debug: false,
            parallel: false,
            panic_unwind: false,
            ..CompilerConfig::default()
        },
        TargetSpec::parse("aarch64-apple-darwin").unwrap(),
    )
    .with_codegen_license(
        CodegenLicensePolicy::default()
            .with_recognized_authority("trust-direct-lane-structural")
            .with_unlicensed(UnlicensedBodyPolicy::Permit),
    )
    .compile(m)
    .map(|o| o.object_code)
    .map_err(|e| format!("{e:?}"))
}
fn execute(name: &str, json: &str, driver: &str) {
    execute_population(name, json, driver, 1);
}
fn execute_population(name: &str, json: &str, driver: &str, population: usize) {
    let module: Module = serde_json::from_str(json).unwrap();
    assert_eq!(
        module.functions.len(),
        population,
        "full actual function denominator"
    );
    let findings = trust_ir_build::validate::validate_module(&module);
    assert!(
        findings.is_empty(),
        "{name}: invalid native fixture: {findings:#?}"
    );
    let hold = tempfile::tempdir().unwrap();
    let root = std::env::var_os("TRUST_CG_RESULT_AGGREGATE_OUTPUT_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| hold.path().to_path_buf())
        .join(name);
    fs::create_dir_all(&root).unwrap();
    for (opt, label) in [(OptLevel::O0, "O0"), (OptLevel::O3, "O3")] {
        let dir = root.join(label);
        fs::create_dir(&dir).unwrap();
        fs::write(dir.join("input.json"), json).unwrap();
        let object = compile(&module, opt).unwrap_or_else(|e| panic!("{name} {label}: {e}"));
        fs::write(dir.join("module.o"), object).unwrap();
        fs::write(dir.join("driver.c"), driver).unwrap();
        let binary = dir.join("native");
        let link = process::command_output_with_timeout(
            Command::new("/usr/bin/cc")
                .args(["-O2", "-Wall", "-Wextra", "-Werror"])
                .arg(dir.join("driver.c"))
                .arg(dir.join("module.o"))
                .arg("-o")
                .arg(&binary),
            process::codegen_link_timeout(),
        )
        .unwrap();
        fs::write(dir.join("link.stderr"), &link.output.stderr).unwrap();
        assert!(
            !link.timed_out && link.output.status.success(),
            "{}",
            String::from_utf8_lossy(&link.output.stderr)
        );
        let run =
            process::run_executable_with_timeout(&binary, process::codegen_run_timeout()).unwrap();
        fs::write(dir.join("native.stdout"), &run.output.stdout).unwrap();
        fs::write(dir.join("native.stderr"), &run.output.stderr).unwrap();
        assert!(
            !run.timed_out && run.output.status.success(),
            "native {}: {}",
            run.output.status,
            String::from_utf8_lossy(&run.output.stderr)
        );
    }
}
const STRUCT_DRIVER: &str = r#"#include <stdint.h>
#include <stdio.h>
#include <string.h>
typedef struct { uint64_t tag; uintptr_t pointer; uint64_t code, metadata; } Image;
extern Image result_struct(Image);
int main(void){unsigned char cells[64];memset(cells,0x5a,sizeof cells);
 for(unsigned i=0;i<256;i++){
  Image in={1,(uintptr_t)&cells[i%64],0xabcdef0123450000ULL+i,0x1020304050600000ULL+i};
  Image saved=in,out=result_struct(in);
  if(out.tag!=1||out.pointer!=in.pointer||out.code!=in.code||out.metadata!=in.metadata||memcmp(&saved,&in,sizeof in))return 1;
  *(unsigned char*)out.pointer=(unsigned char)i;if(cells[i%64]!=(unsigned char)i)return 2;
  in.pointer=(uintptr_t)&in.code;out=result_struct(in);if(out.pointer!=(uintptr_t)&in.code||out.code!=in.code||out.metadata!=in.metadata)return 3;
 }
 Image ok={0,0,0,0},out=result_struct(ok);if(out.tag||out.pointer!=7)return 4;
 puts("256 complete pointer/code/metadata payloads + self-alias + success PASS");return 0;}
"#;
const ENUM_DRIVER: &str = r#"#include <stdint.h>
#include <stdio.h>
#include <string.h>
typedef struct { uint64_t tag; uintptr_t pointer; uint64_t code, metadata; } Image;
extern Image result_enum(Image);
int main(void){unsigned char cells[64];static const unsigned char text[512]="retained";memset(cells,0xa5,sizeof cells);
 for(unsigned variant=0;variant<3;variant++)for(unsigned i=0;i<256;i++){
  Image in={variant,(uintptr_t)&cells[i%64],0xabcdef0123450000ULL+i,0x1020304050600000ULL+i};
  if(variant==1){in.pointer=(uintptr_t)&text[i%64];in.code=i+1;} /* bounded static UTF-8 str */
  if(variant==2)in.pointer=0xdeadbeef12340000ULL+i;
  Image saved=in,out=result_enum(in);
  if(out.tag!=variant||out.pointer!=in.pointer||memcmp(&saved,&in,sizeof in))return 1;
  if(variant==0&&(out.code!=in.code||out.metadata!=in.metadata))return 2;
  if(variant==1&&out.code!=in.code)return 3;
  if(variant==0){*(unsigned char*)out.pointer=(unsigned char)i;if(cells[i%64]!=(unsigned char)i)return 4;}
 }
 Image ok={UINT64_MAX,0,0,0},out=result_enum(ok);if(out.tag!=UINT64_MAX||out.pointer!=11)return 5;
 puts("3 variants x256 complete active payloads + nested str metadata + success PASS");return 0;}
"#;
#[test]
fn actual_rich_struct_result_reaches_native() {
    execute(
        "rich-struct",
        include_str!("fixtures/result_residual/result_struct.json"),
        STRUCT_DRIVER,
    );
}
#[test]
fn actual_rich_enum_result_reaches_native() {
    execute(
        "rich-enum",
        include_str!("fixtures/result_residual/result_enum.json"),
        ENUM_DRIVER,
    );
}

/// Construct from an actual aggregate load, then store the new value through
/// a caller pointer. Equal/overlapping source and destination must preserve the
/// original payload: construction is a fresh value, never an in-place retag.
#[test]
fn runtime_enum_construction_has_value_semantics_under_aliasing() {
    use trust_ir::{Block, BlockId, FuncId, FuncTy, Function, Inst, InstrNode, Ty, ValueId};
    let mut module: Module =
        serde_json::from_str(include_str!("fixtures/result_residual/result_struct.json")).unwrap();
    let result = module.func_types[module.functions[0].ty.as_usize()].returns[0].clone();
    let payload = module
        .enums
        .iter()
        .find(|e| Ty::Enum(e.id) == result)
        .unwrap()
        .variants[1]
        .fields[0]
        .clone();
    let sig = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let v = ValueId::new;
    let mut block = Block::new(BlockId::new(0));
    block.params = vec![(v(0), Ty::Ptr), (v(1), Ty::Ptr)];
    block.body = vec![
        InstrNode::new(Inst::Load {
            ty: payload,
            ptr: v(1),
            volatile: false,
            align: None,
        })
        .with_result(v(2)),
        InstrNode::new(Inst::MakeAggregate {
            ty: result.clone(),
            variant: Some(1),
            fields: vec![v(2)],
        })
        .with_result(v(3)),
        InstrNode::new(Inst::Store {
            ty: result,
            ptr: v(0),
            value: v(3),
            volatile: false,
            align: None,
        }),
        InstrNode::new(Inst::Return { values: vec![] }),
    ];
    let mut function = Function::new(
        FuncId::new(1),
        "construct_result_store",
        sig,
        BlockId::new(0),
    );
    function.blocks = vec![block];
    module.try_add_function(function).unwrap();
    let wire = serde_json::to_string_pretty(&module).unwrap();
    execute_population(
        "aliasing",
        &wire,
        r#"#include <stdint.h>
#include <stdio.h>
#include <string.h>
extern void construct_result_store(void*,const void*);
int main(void){uint64_t words[16];unsigned char cells[8];memset(cells,0x9a,sizeof cells);
 for(unsigned mode=0;mode<3;mode++)for(unsigned i=0;i<256;i++){
  for(unsigned k=0;k<16;k++)words[k]=0x456789abcdef9876ULL;
  uint64_t *src=&words[2],*dst=mode==0?src:mode==1?&words[8]:src+1;
  uint64_t payload[3]={(uintptr_t)&cells[i%8],0x8123456700000000ULL+i,0xfedcba9800000000ULL+i};
  memcpy(src,payload,sizeof payload);construct_result_store(dst,src);
  if(dst[0]!=1||memcmp(dst+1,payload,sizeof payload)||words[0]!=0x456789abcdef9876ULL||words[15]!=0x456789abcdef9876ULL)return 1;
  if(mode==1&&memcmp(src,payload,sizeof payload))return 2;
 }
 puts("256 equal/disjoint/partially-overlapping stores preserve complete payload PASS");return 0;}
"#,
        2,
    );
}

#[test]
fn malformed_and_unbounded_niche_constructors_are_refused() {
    use trust_ir::{
        Block, BlockId, EnumDef, EnumId, EnumVariant, FuncId, FuncTy, Function, Inst, InstrNode,
        Ty, ValueId,
    };
    let original: Module =
        serde_json::from_str(include_str!("fixtures/result_residual/result_struct.json")).unwrap();
    for variant in [None, Some(99)] {
        let mut m = original.clone();
        let mut found = false;
        for f in &mut m.functions {
            for b in &mut f.blocks {
                for n in &mut b.body {
                    if let Inst::MakeAggregate { variant: v, .. } = &mut n.inst {
                        *v = variant;
                        found = true;
                    }
                }
            }
        }
        assert!(found);
        let error = compile(&m, OptLevel::O0).expect_err("invalid variant cannot emit bytes");
        assert!(error.contains("MakeAggregate"), "{error}");
    }
    let mut m = original.clone();
    for f in &mut m.functions {
        for b in &mut f.blocks {
            for n in &mut b.body {
                if let Inst::MakeAggregate { fields, .. } = &mut n.inst {
                    fields.clear();
                }
            }
        }
    }
    assert!(
        compile(&m, OptLevel::O0).is_err(),
        "missing full payload cannot emit bytes"
    );
    let mut m = original.clone();
    m.enums[0].layout.as_mut().unwrap().variant_field_offsets[1][0] = u64::MAX;
    assert!(
        compile(&m, OptLevel::O0).is_err(),
        "rebound/out-of-bounds payload layout cannot emit bytes"
    );
    let mut m = Module::new("unbounded_niche_constructor");
    let eid = EnumId::new(0);
    m.add_enum(EnumDef {
        origin: None,
        id: eid,
        name: "RawNiche".into(),
        variants: vec![
            EnumVariant {
                name: "Empty".into(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "Full".into(),
                fields: vec![Ty::Ptr],
                field_names: vec![],
            },
        ],
        discriminants: vec![],
        repr: None,
        layout: Some(trust_ir::ty::EnumLayoutDescriptor {
            encoding: trust_ir::ty::EnumTagEncoding::Niche {
                untagged_variant: 1,
                niche_variants_start: 0,
                niche_variants_end: 0,
                niche_start: 0,
                niche_offset: 0,
                niche_ty: trust_ir::ty::EnumTagRepr::U64,
            },
            size: 8,
            align: 8,
            variant_field_offsets: vec![vec![], vec![0]],
        }),
    });
    let ty = m
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::Enum(eid)],
            abi: None,
            is_vararg: false,
        })
        .unwrap();
    let mut f = Function::new(FuncId::new(0), "raw_niche", ty, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.params = vec![(ValueId::new(0), Ty::Ptr)];
    b.body = vec![
        InstrNode::new(Inst::MakeAggregate {
            ty: Ty::Enum(eid),
            variant: Some(1),
            fields: vec![ValueId::new(0)],
        })
        .with_result(ValueId::new(1)),
        InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        }),
    ];
    f.blocks = vec![b];
    m.try_add_function(f).unwrap();
    assert!(
        trust_ir_build::validate::validate_module(&m).is_empty(),
        "this is a type-correct but unbounded domain"
    );
    let err =
        compile(&m, OptLevel::O0).expect_err("raw pointer type cannot prove it avoids the niche");
    assert!(err.contains("no typed nonreserved"), "{err}");
}

#[test]
fn signed_discriminants_and_tagfree_constructor_encodings_execute() {
    use trust_ir::{
        Block, BlockId, EnumDef, EnumId, EnumTagRepr, EnumVariant, FuncId, FuncTy, Function, Inst,
        InstrNode, Ty, ValueId,
    };
    let mut m = Module::new("runtime_constructor_encoding_profiles");
    let variant = |name: &str, fields: Vec<Ty>| EnumVariant {
        name: name.into(),
        fields,
        field_names: vec![],
    };
    m.add_enum(EnumDef {
        origin: None,
        id: EnumId::new(0),
        name: "Signed".into(),
        variants: vec![
            variant("Negative", vec![Ty::U64]),
            variant("Hundred", vec![Ty::U64]),
            variant("SevenThousand", vec![Ty::U64]),
        ],
        discriminants: vec![Some(-9), Some(100), Some(7000)],
        repr: Some(EnumTagRepr::I16),
        layout: None,
    });
    m.add_enum(EnumDef {
        origin: None,
        id: EnumId::new(1),
        name: "Tagfree".into(),
        variants: vec![variant("Only", vec![Ty::U64])],
        discriminants: vec![Some(7)],
        repr: None,
        layout: Some(trust_ir::ty::EnumLayoutDescriptor {
            encoding: trust_ir::ty::EnumTagEncoding::Untagged,
            size: 8,
            align: 8,
            variant_field_offsets: vec![vec![0]],
        }),
    });
    m.add_enum(EnumDef {
        origin: None,
        id: EnumId::new(2),
        name: "BooleanNiche".into(),
        variants: vec![variant("Empty", vec![]), variant("Full", vec![Ty::Bool])],
        discriminants: vec![],
        repr: None,
        layout: Some(trust_ir::ty::EnumLayoutDescriptor {
            encoding: trust_ir::ty::EnumTagEncoding::Niche {
                untagged_variant: 1,
                niche_variants_start: 0,
                niche_variants_end: 0,
                niche_start: 2,
                niche_offset: 0,
                niche_ty: EnumTagRepr::U8,
            },
            size: 1,
            align: 1,
            variant_field_offsets: vec![vec![], vec![0]],
        }),
    });
    for (name, eid, index, args) in [
        ("construct_negative", 0, 0, vec![Ty::U64]),
        ("construct_hundred", 0, 1, vec![Ty::U64]),
        ("construct_seventhousand", 0, 2, vec![Ty::U64]),
        ("construct_untagged", 1, 0, vec![Ty::U64]),
        ("construct_boolean", 2, 1, vec![Ty::Bool]),
        ("construct_empty", 2, 0, vec![]),
    ] {
        let result = Ty::Enum(EnumId::new(eid));
        let sig = m
            .add_func_type(FuncTy {
                params: args.clone(),
                returns: vec![result.clone()],
                abi: None,
                is_vararg: false,
            })
            .unwrap();
        let values: Vec<_> = args
            .iter()
            .enumerate()
            .map(|(i, _)| ValueId::new(i as u32))
            .collect();
        let ret = ValueId::new(args.len() as u32);
        let mut b = Block::new(BlockId::new(0));
        b.params = values.iter().copied().zip(args).collect();
        b.body = vec![
            InstrNode::new(Inst::MakeAggregate {
                ty: result,
                variant: Some(index),
                fields: values,
            })
            .with_result(ret),
            InstrNode::new(Inst::Return { values: vec![ret] }),
        ];
        let mut f = Function::new(
            FuncId::new(m.functions.len() as u32),
            name,
            sig,
            BlockId::new(0),
        );
        f.blocks = vec![b];
        m.try_add_function(f).unwrap();
    }
    execute_population(
        "encodings",
        &serde_json::to_string_pretty(&m).unwrap(),
        r#"#include <stdint.h>
#include <stdio.h>
typedef struct{int16_t tag;uint64_t payload;} Signed;
typedef struct{uint64_t payload;} Word;typedef struct{uint8_t payload;} Byte;
extern Signed construct_negative(uint64_t),construct_hundred(uint64_t),construct_seventhousand(uint64_t);
extern Word construct_untagged(uint64_t);extern Byte construct_boolean(_Bool),construct_empty(void);
int main(void){for(unsigned i=0;i<256;i++){uint64_t x=0xabcdef0123450000ULL+i;Signed a=construct_negative(x),b=construct_hundred(x),c=construct_seventhousand(x);
 if(a.tag!=-9||b.tag!=100||c.tag!=7000||a.payload!=x||b.payload!=x||c.payload!=x)return 1;
 if(construct_untagged(x).payload!=x||construct_boolean(i&1).payload!=(i&1)||construct_empty().payload!=2)return 2;}
 puts("signed/nonsequential tags + untagged + typed Bool niche payload/reserved tag PASS");return 0;}
"#,
        6,
    );
    let mut overlap = m.clone();
    if let trust_ir::ty::EnumTagEncoding::Niche { niche_start, .. } =
        &mut overlap.enums[2].layout.as_mut().unwrap().encoding
    {
        *niche_start = 0;
    }
    assert!(
        compile(&overlap, OptLevel::O0).is_err(),
        "a reserved value cannot overlap valid Bool data"
    );
    let mut wrong = m.clone();
    if let trust_ir::ty::EnumTagEncoding::Niche {
        untagged_variant, ..
    } = &mut wrong.enums[2].layout.as_mut().unwrap().encoding
    {
        *untagged_variant = 0;
    }
    assert!(
        compile(&wrong, OptLevel::O0).is_err(),
        "cannot pick another/widest variant as the untagged carrier"
    );
}

#[test]
fn single_inhabited_enum_load_store_and_discriminants_execute() {
    use trust_ir::{
        Block, BlockId, EnumDef, EnumId, EnumLayoutDescriptor, EnumTagEncoding, EnumVariant,
        FuncId, FuncTy, Function, Inst, InstrNode, Ty, ValueId,
    };
    let mut module = Module::new("single_inhabited_native");
    let variant = |name: &str, fields| EnumVariant {
        name: name.into(),
        fields,
        field_names: vec![],
    };
    module
        .enums
        .push(EnumDef::new(EnumId::new(0), "Infallible", vec![]));
    for active in 0..2 {
        let eid = EnumId::new(1 + active as u32);
        let mut variants = vec![variant("Absent", vec![Ty::Enum(EnumId::new(0))]); 2];
        variants[active] = variant("Present", vec![Ty::U32]);
        let mut rows = vec![vec![]; 2];
        rows[active] = vec![0];
        let mut def = EnumDef::new(eid, format!("Selected{active}"), variants);
        def.discriminants = vec![Some(7), Some(23)];
        def.layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::SingleInhabited {
                variant: active as u32,
            },
            size: 4,
            align: 4,
            variant_field_offsets: rows,
        });
        module.enums.push(def);
        let ty = Ty::Enum(eid);
        let v = ValueId::new;
        for operation in 0..3 {
            let (name, params, returns, body) = match operation {
                0 => (
                    format!("store_selected{active}"),
                    vec![(v(0), Ty::Ptr), (v(1), Ty::U32)],
                    vec![],
                    vec![
                        InstrNode::new(Inst::MakeAggregate {
                            ty: ty.clone(),
                            variant: Some(active as u32),
                            fields: vec![v(1)],
                        })
                        .with_result(v(2)),
                        InstrNode::new(Inst::Store {
                            ty: ty.clone(),
                            ptr: v(0),
                            value: v(2),
                            volatile: false,
                            align: Some(4),
                        }),
                        InstrNode::new(Inst::Return { values: vec![] }),
                    ],
                ),
                _ => {
                    let discriminant = operation == 2;
                    (
                        format!(
                            "{}_selected{active}",
                            if discriminant { "disc" } else { "load" }
                        ),
                        vec![(v(0), Ty::Ptr)],
                        vec![if discriminant { Ty::U8 } else { Ty::U32 }],
                        vec![
                            InstrNode::new(Inst::Load {
                                ty: ty.clone(),
                                ptr: v(0),
                                volatile: false,
                                align: Some(4),
                            })
                            .with_result(v(1)),
                            InstrNode::new(Inst::ExtractField {
                                ty: if discriminant { Ty::U8 } else { Ty::U32 },
                                aggregate: v(1),
                                field: if discriminant { 0 } else { 1 },
                            })
                            .with_result(v(2)),
                            InstrNode::new(Inst::Return { values: vec![v(2)] }),
                        ],
                    )
                }
            };
            let signature = module
                .add_func_type(FuncTy {
                    params: params.iter().map(|(_, ty)| ty.clone()).collect(),
                    returns,
                    abi: None,
                    is_vararg: false,
                })
                .unwrap();
            let mut function = Function::new(
                FuncId::new(module.functions.len() as u32),
                name,
                signature,
                BlockId::new(0),
            );
            let mut block = Block::new(BlockId::new(0));
            block.params = params;
            block.body = body;
            function.blocks = vec![block];
            module.try_add_function(function).unwrap();
        }
    }
    let json = serde_json::to_string_pretty(&module).unwrap();
    execute_population(
        "single-inhabited",
        &json,
        r#"#include <stdint.h>
#include <stdio.h>
extern void store_selected0(uint32_t*,uint32_t), store_selected1(uint32_t*,uint32_t);
extern uint32_t load_selected0(const uint32_t*), load_selected1(const uint32_t*);
extern uint8_t disc_selected0(const uint32_t*), disc_selected1(const uint32_t*);
int main(void) {
 for(uint32_t i=0;i<1024;i++) {
  uint32_t image[3]={0x13579bdf,0,0x2468ace0};
  uint32_t x=i*0x9e3779b9u;
  store_selected0(&image[1],x);
  if(image[0]!=0x13579bdf||image[2]!=0x2468ace0||image[1]!=x||load_selected0(&image[1])!=x||disc_selected0(&image[1])!=7)return 1;
  store_selected1(&image[1],~x);
  if(image[0]!=0x13579bdf||image[2]!=0x2468ace0||image[1]!=~x||load_selected1(&image[1])!=~x||disc_selected1(&image[1])!=23)return 2;
 }
 puts("2 selectors x1024 payloads, bounded physical stores and exact discriminants PASS");return 0;
}
"#,
        6,
    );
}
