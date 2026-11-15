// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Give a const-evaluated byte/relocation image canonical storage types.
//! Packed fields describe exact byte offsets; allocation alignment belongs to
//! the global, independently of those fields' alignment. No pointer validity
//! or lifetime is inferred from a relocation.

use trust_ir::{Constant, Module, Ty};

pub(crate) struct TypedImage {
    pub ty: Ty,
    pub initializer: Constant,
    pub align: u32,
}

/// Type the const-evaluated image of the allocation `name`
/// (`allocation_size` bytes, `allocation_align`-aligned) through the one
/// shared typer, [`trust_cg_lower::global_image::type_flat_image`], the LLVM
/// importer's too: adjacent bytes form one `[u8; n]` run in its one canonical
/// spelling, each relocation one `ptr` field of a packed struct. The size and
/// alignment are checked before any type table changes.
pub(crate) fn type_image(
    module: &mut Module,
    name: &str,
    image: Constant,
    allocation_size: u64,
    allocation_align: u64,
) -> Result<TypedImage, String> {
    let align = u32::try_from(allocation_align)
        .ok()
        .filter(|align| align.is_power_of_two())
        .ok_or_else(|| format!("global image `{name}` has invalid alignment {allocation_align}"))?;
    let Constant::Aggregate(elements) = image else {
        return Err(format!(
            "global image `{name}` is not a flat byte/relocation aggregate"
        ));
    };
    // Eight bytes per relocation on every native target, four on wasm32.
    let pointer_bytes = crate::session_pointer_bytes();
    let size = trust_cg_lower::global_image::flat_image_size(name, &elements, pointer_bytes)?;
    if size != allocation_size {
        return Err(format!(
            "global image `{name}` has {size} bytes, allocation has {allocation_size}"
        ));
    }
    let typed =
        trust_cg_lower::global_image::type_flat_image(module, name, elements, pointer_bytes)?;
    Ok(TypedImage {
        ty: typed.ty,
        initializer: typed.initializer,
        align,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use trust_ir::TyId;

    fn bytes(data: &[u8]) -> Vec<Constant> {
        data.iter().map(|b| Constant::Int(i128::from(*b))).collect()
    }

    /// trust-ir v50 §3.1: a uniform byte run is the one spelling
    /// `splat[ b; n ]`, never raw `Bytes`; a mixed or one-byte run stays raw.
    #[test]
    fn uniform_byte_runs_are_spelled_as_splats() {
        let mut module = Module::new("image");
        let zeros = type_image(
            &mut module,
            "Z",
            Constant::Aggregate(bytes(&[0; 64])),
            64,
            8,
        )
        .expect("a zero image");
        assert_eq!(zeros.ty, Ty::Array(TyId::new(0), 64));
        assert_eq!(zeros.initializer, Constant::splat(Constant::Int(0), 64));

        let mixed = type_image(
            &mut module,
            "M",
            Constant::Aggregate(bytes(&[1, 2, 2])),
            3,
            1,
        )
        .expect("a mixed image");
        assert_eq!(
            mixed.initializer,
            Constant::Bytes {
                data: vec![1, 2, 2],
                utf8: false
            }
        );

        let one = type_image(&mut module, "O", Constant::Aggregate(bytes(&[9])), 1, 1)
            .expect("a one-byte image");
        assert_eq!(
            one.initializer,
            Constant::Bytes {
                data: vec![9],
                utf8: false
            }
        );

        // Beside a relocation, each byte run is spelled on its own.
        let mut elements = bytes(&[0xAA; 3]);
        elements.push(Constant::symbol_addr("target"));
        elements.extend(bytes(&[1, 2]));
        let image = type_image(&mut module, "P", Constant::Aggregate(elements), 13, 8)
            .expect("a relocated image");
        let Constant::Aggregate(fields) = image.initializer else {
            panic!("a relocated image is a packed struct aggregate");
        };
        assert_eq!(fields[0], Constant::splat(Constant::Int(0xAA), 3));
        assert!(matches!(fields[1], Constant::SymbolAddr { .. }));
        assert_eq!(
            fields[2],
            Constant::Bytes {
                data: vec![1, 2],
                utf8: false
            }
        );
    }
}
