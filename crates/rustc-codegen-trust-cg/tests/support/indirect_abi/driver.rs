// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
// Actual FnABI queries and synthetic descriptor transport controls. Stop before
// input codegen: a transport/control success is not native ABI or proof credit.
#![feature(rustc_private)]
extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_target;
#[path = "../../../src/indirect_abi.rs"]
mod indirect_abi;
use indirect_abi::Kind;
use rustc_abi::{AddressSpace, Align, Size};
use rustc_driver::{Callbacks, Compilation};
use rustc_middle::ty::{self, TyCtxt};
use rustc_target::callconv::{ArgAttribute, ArgAttributes, ArgExtension, PassMode};

struct Audit;

fn check(
    mode: &PassMode,
    attrs: &ArgAttributes,
    meta: Option<&ArgAttributes>,
    space: Option<AddressSpace>,
    kind: Kind,
) {
    let view = indirect_abi::view(mode).expect("indirect descriptor must remain indirect");
    assert_eq!(view.attrs, attrs, "complete data-pointer attributes");
    assert!(
        std::ptr::eq(view.attrs, attrs),
        "borrow original data attributes"
    );
    assert_eq!(
        view.meta_attrs, meta,
        "complete metadata attributes and arity"
    );
    if let Some(meta) = meta {
        assert!(
            std::ptr::eq(view.meta_attrs.unwrap(), meta),
            "borrow original metadata attributes"
        );
    }
    assert_eq!(
        view.address_space, space,
        "retain exact address space including explicit zero"
    );
    assert_eq!(view.kind, kind, "retain exact indirect mode");
    assert_eq!(
        view.is_sized_pointer(),
        kind == Kind::Pointer && meta.is_none(),
        "sized pointer classification"
    );
    let nonzero = space.is_some_and(|s| s != AddressSpace::ZERO);
    #[cfg(rustc_indirect_modes)]
    let kernel = kind == Kind::AmdgpuKernelArg;
    #[cfg(not(rustc_indirect_modes))]
    let kernel = false;
    let invalid_stack = kind == Kind::OnStack && meta.is_some();
    let checked = indirect_abi::checked(mode);
    if nonzero || kernel || invalid_stack {
        let reason = checked.expect_err("unsupported descriptor must refuse");
        assert!(
            reason.contains(if nonzero {
                "address space"
            } else if kernel {
                "AmdgpuKernelArg"
            } else {
                "metadata"
            }),
            "{reason}"
        );
    } else {
        let checked = checked.unwrap().expect("supported descriptor retained");
        assert!(std::ptr::eq(checked.attrs, attrs), "checked data borrow");
        assert_eq!(checked.meta_attrs, meta, "checked metadata arity");
        assert_eq!(
            checked.address_space, space,
            "checked address-space transport"
        );
        assert_eq!(checked.kind, kind, "checked mode transport");
    }
}

fn inspect(mode: &PassMode) -> Option<bool> {
    match mode {
        #[cfg(rustc_indirect_modes)]
        PassMode::Indirect {
            attrs,
            address_space,
            mode: raw_kind,
        } => {
            use rustc_target::callconv::IndirectMode;
            let kind = match raw_kind {
                IndirectMode::Pointer => Kind::Pointer,
                IndirectMode::OnStack => Kind::OnStack,
                IndirectMode::AmdgpuKernelArg => Kind::AmdgpuKernelArg,
            };
            check(mode, attrs, None, *address_space, kind);
            Some(false)
        }
        #[cfg(rustc_indirect_modes)]
        PassMode::IndirectUnsized { attrs, meta_attrs } => {
            check(mode, attrs, Some(meta_attrs), None, Kind::Pointer);
            Some(true)
        }
        #[cfg(not(rustc_indirect_modes))]
        PassMode::Indirect {
            attrs,
            meta_attrs,
            on_stack,
        } => {
            check(
                mode,
                attrs,
                meta_attrs.as_ref(),
                None,
                if *on_stack {
                    Kind::OnStack
                } else {
                    Kind::Pointer
                },
            );
            Some(meta_attrs.is_some())
        }
        _ => {
            assert!(indirect_abi::view(mode).is_none(), "real nonindirect");
            assert!(
                indirect_abi::checked(mode).unwrap().is_none(),
                "checked nonindirect"
            );
            None
        }
    }
}

fn attributes() -> Vec<ArgAttributes> {
    let mut rich = ArgAttributes::new();
    rich.set(ArgAttribute::InReg)
        .set(ArgAttribute::NoAlias)
        .set(ArgAttribute::NonNull)
        .set(ArgAttribute::ReadOnly);
    rich.arg_ext = ArgExtension::Sext;
    rich.pointee_size = Size::from_bytes(17);
    rich.pointee_align = Some(Align::from_bytes(16).unwrap());
    let mut other = ArgAttributes::new();
    other.arg_ext = ArgExtension::Zext;
    other.pointee_size = Size::from_bytes(65535);
    other.pointee_align = Some(Align::from_bytes(64).unwrap());
    vec![ArgAttributes::new(), rich, other]
}

fn synthetic() -> usize {
    let mut count = 0;
    for attrs in attributes() {
        #[cfg(not(rustc_indirect_modes))]
        for meta in std::iter::once(None).chain(attributes().into_iter().map(Some)) {
            for on_stack in [false, true] {
                let mode = PassMode::Indirect {
                    attrs,
                    meta_attrs: meta,
                    on_stack,
                };
                inspect(&mode).unwrap();
                let raw = indirect_abi::view(&mode).unwrap();
                assert_eq!(*raw.attrs, attrs, "data constructor control");
                assert_eq!(
                    raw.meta_attrs.copied(),
                    meta,
                    "metadata constructor control"
                );
                count += 1;
            }
        }
        #[cfg(rustc_indirect_modes)]
        {
            use rustc_target::callconv::IndirectMode;
            for address_space in [
                None,
                Some(AddressSpace::ZERO),
                Some(AddressSpace(1)),
                Some(AddressSpace(3)),
                Some(AddressSpace(4)),
                Some(AddressSpace(u32::MAX)),
            ] {
                for mode in [
                    IndirectMode::Pointer,
                    IndirectMode::OnStack,
                    IndirectMode::AmdgpuKernelArg,
                ] {
                    let descriptor = PassMode::Indirect {
                        attrs,
                        address_space,
                        mode,
                    };
                    inspect(&descriptor).unwrap();
                    assert_eq!(
                        *indirect_abi::view(&descriptor).unwrap().attrs,
                        attrs,
                        "data constructor control"
                    );
                    count += 1;
                }
            }
            for meta_attrs in attributes() {
                let descriptor = PassMode::IndirectUnsized { attrs, meta_attrs };
                inspect(&descriptor).unwrap();
                let raw = indirect_abi::view(&descriptor).unwrap();
                assert_eq!(*raw.attrs, attrs, "unsized data constructor control");
                assert_eq!(
                    raw.meta_attrs.copied(),
                    Some(meta_attrs),
                    "unsized metadata constructor control"
                );
                count += 1;
            }
        }
    }
    for mode in [
        PassMode::Ignore,
        PassMode::Direct(ArgAttributes::new()),
        PassMode::Pair(ArgAttributes::new(), ArgAttributes::new()),
    ] {
        assert!(inspect(&mode).is_none());
    }
    assert_eq!(count, if cfg!(rustc_indirect_modes) { 63 } else { 24 });
    count
}

impl Callbacks for Audit {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        assert_eq!(tcx.data_layout.pointer_size().bytes(), 8);
        let env = ty::TypingEnv::fully_monomorphized();
        let (mut functions, mut modes, mut sized, mut unsized_modes) = (0, 0, 0, 0);
        for local in tcx.iter_local_def_id() {
            let did = local.to_def_id();
            if tcx.def_kind(did) != rustc_hir::def::DefKind::Fn
                || !tcx.item_name(did).as_str().starts_with("case_")
            {
                continue;
            }
            let abi = tcx
                .fn_abi_of_instance(
                    env.as_query_input((ty::Instance::mono(tcx, did), ty::List::empty())),
                )
                .unwrap();
            for arg in abi.args.iter().chain(std::iter::once(&abi.ret)) {
                if let Some(is_unsized) = inspect(&arg.mode) {
                    assert!(
                        indirect_abi::checked(&arg.mode).is_ok(),
                        "actual host indirect mode must remain representable: {:?}",
                        arg.mode
                    );
                    if is_unsized {
                        unsized_modes += 1;
                    } else {
                        sized += 1;
                    }
                }
                modes += 1;
            }
            functions += 1;
            println!(
                "REAL_INDIRECT_ABI function={} mode={:?}",
                tcx.item_name(did),
                abi
            );
        }
        assert_eq!(functions, 8);
        assert_eq!(modes, 15);
        assert!(sized >= 4);
        assert_eq!(unsized_modes, 3);
        let synthetic = synthetic();
        println!(
            "INDIRECT_ABI_QUERIES functions={functions} modes={modes} sized={sized} unsized={unsized_modes} synthetic={synthetic} mode_api={}",
            cfg!(rustc_indirect_modes)
        );
        Compilation::Stop
    }
}
fn main() {
    rustc_driver::run_compiler(&std::env::args().collect::<Vec<_>>(), &mut Audit);
}
