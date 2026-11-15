// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! `share_const_alloc_by_content` over hand-built modules: an allocation is
//! renamed to its content name, a second allocation of the same image is
//! given the first one's global and its own reservation removed, and the
//! two guards keep the per-allocation name: a global already under the
//! content name with another image (a hash collision), and an image, the
//! allocation's own included, that points at the reservation. The content names are a provisional surface
//! pending the owner's sign-off (docs/wasm32_perf_roadmap.md, "Pending owner
//! sign-off"); these tests follow them if they change.

use super::*;

fn reserved(name: &str) -> TrustIrGlobal {
    TrustIrGlobal {
        name: name.to_owned(),
        ty: TrustIrTy::Ptr,
        mutable: false,
        initializer: None,
        linkage: Linkage::Internal,
        tls: None,
        align: None,
        section: None,
        visibility: trust_ir::Visibility::Default,
        retained: false,
    }
}

fn flat(bytes: &[u8], pointer: Option<(&str, i64)>) -> Constant {
    let mut elements: Vec<Constant> = bytes
        .iter()
        .map(|b| Constant::Int(i128::from(*b)))
        .collect();
    if let Some((symbol, addend)) = pointer {
        elements.push(Constant::symbol_addr_with_addend(symbol, addend));
    }
    Constant::Aggregate(elements)
}

/// Reserve `name`, share it, and type the image under the name returned,
/// as `emit_const_alloc_global` does.
fn emit(module: &mut TrustIrModule, name: &str, image: &Constant, align: u64) -> String {
    module.globals.push(reserved(name));
    let symbol = match share_const_alloc_by_content(module, name, image, align) {
        ContentShare::Existing(shared) => return shared,
        ContentShare::Renamed(shared) => shared,
        ContentShare::Kept => name.to_owned(),
    };
    let typed = global_image::type_image(
        module,
        &symbol,
        image.clone(),
        match image {
            Constant::Aggregate(e) => e
                .iter()
                .map(|c| {
                    if matches!(c, Constant::SymbolAddr { .. }) {
                        session_pointer_bytes()
                    } else {
                        1
                    }
                })
                .sum(),
            _ => unreachable!(),
        },
        align,
    )
    .expect("image");
    let slot = module
        .globals
        .iter_mut()
        .find(|g| g.name == symbol)
        .expect("slot");
    slot.ty = typed.ty;
    slot.initializer = Some(typed.initializer);
    slot.align = Some(typed.align);
    symbol
}

#[test]
fn equal_images_share_one_global_and_others_keep_their_own() {
    let mut module = TrustIrModule::new("m");
    let a = emit(
        &mut module,
        "tcg.const.alloc1",
        &flat(b"hello, world", None),
        1,
    );
    assert!(a.starts_with("tcg.const.") && !a.contains("alloc"), "{a}");
    let b = emit(
        &mut module,
        "tcg.const.alloc2",
        &flat(b"hello, world", None),
        1,
    );
    assert_eq!(a, b, "an equal image shares the global");
    assert_eq!(module.globals.len(), 1, "the second reservation is removed");
    // Another alignment, other bytes, or a pointer: another global.
    let c = emit(
        &mut module,
        "tcg.const.alloc3",
        &flat(b"hello, world", None),
        4,
    );
    let d = emit(
        &mut module,
        "tcg.const.alloc4",
        &flat(b"hello, worle", None),
        1,
    );
    let e = emit(
        &mut module,
        "tcg.const.alloc5",
        &flat(b"loc", Some((&a, 2))),
        1,
    );
    let f = emit(
        &mut module,
        "tcg.const.alloc6",
        &flat(b"loc", Some((&a, 3))),
        1,
    );
    let names: std::collections::BTreeSet<&str> = [&a, &c, &d, &e, &f]
        .into_iter()
        .map(String::as_str)
        .collect();
    assert_eq!(names.len(), 5);
    assert_eq!(module.globals.len(), 5);
    let g = emit(
        &mut module,
        "tcg.const.alloc7",
        &flat(b"loc", Some((&a, 3))),
        1,
    );
    assert_eq!(g, f);
}

#[test]
fn a_different_image_under_the_content_name_keeps_the_allocation_name() {
    let mut module = TrustIrModule::new("m");
    let shared = emit(&mut module, "tcg.const.alloc1", &flat(b"abcd", None), 1);
    // Forge a collision: replace the shared global's bytes.
    let slot = module
        .globals
        .iter_mut()
        .find(|g| g.name == shared)
        .unwrap();
    slot.initializer = Some(Constant::Bytes {
        data: b"abce".to_vec(),
        utf8: false,
    });
    let again = emit(&mut module, "tcg.const.alloc2", &flat(b"abcd", None), 1);
    assert_eq!(again, "tcg.const.alloc2");
    assert_eq!(module.globals.len(), 2);
}

#[test]
fn an_image_pointing_at_the_reservation_keeps_the_allocation_name() {
    let mut module = TrustIrModule::new("m");
    // A nested allocation emitted while `alloc1` was reserved points at it.
    module.globals.push(reserved("tcg.const.alloc1"));
    let mut nested = reserved("tcg.const.alloc2");
    nested.initializer = Some(flat(b"", Some(("tcg.const.alloc1", 0))));
    module.globals.push(nested);
    let image = flat(b"xy", Some(("tcg.const.alloc2", 0)));
    assert!(matches!(
        share_const_alloc_by_content(&mut module, "tcg.const.alloc1", &image, 1),
        ContentShare::Kept
    ));
    assert!(module.globals.iter().any(|g| g.name == "tcg.const.alloc1"));
}

#[test]
fn an_image_pointing_at_itself_keeps_the_allocation_name() {
    let mut module = TrustIrModule::new("m");
    let image = flat(b"x", Some(("tcg.const.alloc1", 0)));
    assert_eq!(
        emit(&mut module, "tcg.const.alloc1", &image, 1),
        "tcg.const.alloc1"
    );
    assert_eq!(module.globals.len(), 1);
    let global = &module.globals[0];
    assert_eq!(global.name, "tcg.const.alloc1");
    assert!(constant_names_symbol(
        global.initializer.as_ref().unwrap(),
        "tcg.const.alloc1"
    ));
}

#[test]
fn flat_images_round_trip_the_typed_forms() {
    let mut module = TrustIrModule::new("m");
    for (bytes, pointer) in [
        (&b"aaaaaaaa"[..], None),
        (&b"q"[..], None),
        (&b"xyzzy"[..], Some(("t", 7))),
    ] {
        let image = flat(bytes, pointer);
        let name = emit(&mut module, "tcg.const.alloc9", &image, 2);
        let global = module.globals.iter().find(|g| g.name == name).unwrap();
        let Constant::Aggregate(elements) = &image else {
            unreachable!()
        };
        assert_eq!(
            flat_image(global.initializer.as_ref().unwrap()).as_ref(),
            Some(elements)
        );
    }
}

#[test]
fn content_sharing_refuses_changed_storage_metadata_and_malformed_type() {
    for mutation in 0..7 {
        let mut module = TrustIrModule::new("m");
        let shared = emit(&mut module, "tcg.const.alloc1", &flat(b"same", None), 1);
        let slot = module
            .globals
            .iter_mut()
            .find(|g| g.name == shared)
            .unwrap();
        match mutation {
            0 => slot.mutable = true,
            1 => slot.linkage = Linkage::External,
            2 => slot.tls = Some(trust_ir::TlsModel::GeneralDynamic),
            3 => slot.section = Some("custom".to_owned()),
            4 => slot.visibility = trust_ir::Visibility::Hidden,
            5 => slot.retained = true,
            6 => slot.ty = TrustIrTy::U64,
            _ => unreachable!(),
        }
        assert_eq!(
            emit(&mut module, "tcg.const.alloc2", &flat(b"same", None), 1),
            "tcg.const.alloc2"
        );
        assert_eq!(module.globals.len(), 2);
    }
}

#[test]
fn content_sharing_compares_uniform_empty_and_relocated_images_in_place() {
    for image in [
        flat(&[], None),
        flat(&[7; 64], None),
        flat(b"raw", Some(("target", -9))),
    ] {
        let mut module = TrustIrModule::new("m");
        let first = emit(&mut module, "tcg.const.alloc1", &image, 8);
        let second = emit(&mut module, "tcg.const.alloc2", &image, 8);
        assert_eq!(first, second);
        assert_eq!(module.globals.len(), 1);
    }
}

#[test]
fn content_sharing_refuses_other_width_even_when_flat_elements_match() {
    let mut module = TrustIrModule::new("m");
    let image = flat(b"raw", Some(("target", 9)));
    let shared = emit(&mut module, "tcg.const.alloc1", &image, 8);
    let Constant::Aggregate(elements) = &image else {
        unreachable!()
    };
    let other_width = if session_pointer_bytes() == 8 { 4 } else { 8 };
    let typed = trust_cg_lower::global_image::type_flat_image(
        &mut module,
        "other-width",
        elements.clone(),
        other_width,
    )
    .expect("typed");
    let slot = module
        .globals
        .iter_mut()
        .find(|g| g.name == shared)
        .unwrap();
    slot.ty = typed.ty;
    slot.initializer = Some(typed.initializer);
    assert_eq!(
        emit(&mut module, "tcg.const.alloc2", &image, 8),
        "tcg.const.alloc2"
    );
    assert_eq!(module.globals.len(), 2);
}
