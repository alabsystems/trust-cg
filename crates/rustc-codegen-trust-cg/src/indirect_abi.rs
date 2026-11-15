// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! Retain the complete indirect ABI descriptor before deciding whether this
//! bridge can represent it. Unsized metadata is a second ABI value.

use rustc_abi::AddressSpace;
use rustc_target::callconv::{ArgAttributes, PassMode};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Kind {
    Pointer,
    OnStack,
    #[cfg(rustc_indirect_modes)]
    AmdgpuKernelArg,
}

#[derive(Clone, Copy, Debug)]
pub(super) struct Indirect<'a> {
    pub(super) attrs: &'a ArgAttributes,
    pub(super) meta_attrs: Option<&'a ArgAttributes>,
    pub(super) address_space: Option<AddressSpace>,
    pub(super) kind: Kind,
}

impl Indirect<'_> {
    pub(super) fn is_sized_pointer(self) -> bool {
        self.kind == Kind::Pointer && self.meta_attrs.is_none()
    }

    /// This checks descriptor transport restrictions, not the consumer's full
    /// layout, attribute or target contract. Keep those checks at each caller.
    fn supported(self) -> Result<Self, String> {
        // Both rustc LLVM implementations lower type_ptr() through ZERO;
        // an explicit ZERO has the same pointer ABI. Retain its raw presence.
        if let Some(space) = self
            .address_space
            .filter(|space| *space != AddressSpace::ZERO)
        {
            return Err(format!(
                "an indirect argument with nonzero address space {space:?}; the bridge does not model that pointer address space"
            ));
        }
        #[cfg(rustc_indirect_modes)]
        if self.kind == Kind::AmdgpuKernelArg {
            return Err("`IndirectMode::AmdgpuKernelArg` (a read-only kernel argument, not a by-value stack copy)".to_owned());
        }
        if self.kind == Kind::OnStack && self.meta_attrs.is_some() {
            return Err("an unsized indirect argument with `on_stack` set; metadata cannot be dropped into a by-value stack image".to_owned());
        }
        Ok(self)
    }
}

/// Borrow every payload component, including descriptors we must refuse.
pub(super) fn view(mode: &PassMode) -> Option<Indirect<'_>> {
    match mode {
        #[cfg(rustc_indirect_modes)]
        PassMode::Indirect {
            attrs,
            address_space,
            mode,
        } => {
            use rustc_target::callconv::IndirectMode;
            let kind = match mode {
                IndirectMode::Pointer => Kind::Pointer,
                IndirectMode::OnStack => Kind::OnStack,
                IndirectMode::AmdgpuKernelArg => Kind::AmdgpuKernelArg,
            };
            Some(Indirect {
                attrs,
                meta_attrs: None,
                address_space: *address_space,
                kind,
            })
        }
        #[cfg(rustc_indirect_modes)]
        PassMode::IndirectUnsized { attrs, meta_attrs } => Some(Indirect {
            attrs,
            meta_attrs: Some(meta_attrs),
            address_space: None,
            kind: Kind::Pointer,
        }),
        #[cfg(not(rustc_indirect_modes))]
        PassMode::Indirect {
            attrs,
            meta_attrs,
            on_stack,
        } => Some(Indirect {
            attrs,
            meta_attrs: meta_attrs.as_ref(),
            // The legacy descriptor has only the default pointer address space.
            address_space: None,
            kind: if *on_stack {
                Kind::OnStack
            } else {
                Kind::Pointer
            },
        }),
        _ => None,
    }
}

pub(super) fn checked(mode: &PassMode) -> Result<Option<Indirect<'_>>, String> {
    view(mode).map(Indirect::supported).transpose()
}

/// Existing tests describe the valid legacy pointer/stack geometry. This is
/// not a conversion that erases modern address spaces or kernel modes.
#[cfg(test)]
pub(super) fn fixture(
    attrs: ArgAttributes,
    meta_attrs: Option<ArgAttributes>,
    on_stack: bool,
) -> PassMode {
    #[cfg(rustc_indirect_modes)]
    {
        use rustc_target::callconv::IndirectMode;
        match meta_attrs {
            Some(meta_attrs) => {
                assert!(!on_stack, "unsized stack fixture is not a valid ABI mode");
                PassMode::IndirectUnsized { attrs, meta_attrs }
            }
            None => PassMode::Indirect {
                attrs,
                address_space: None,
                mode: if on_stack {
                    IndirectMode::OnStack
                } else {
                    IndirectMode::Pointer
                },
            },
        }
    }
    #[cfg(not(rustc_indirect_modes))]
    {
        PassMode::Indirect {
            attrs,
            meta_attrs,
            on_stack,
        }
    }
}
