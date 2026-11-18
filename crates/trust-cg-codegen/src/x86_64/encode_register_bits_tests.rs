// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Exhaustive byte checks of the actual encoder's shared Lean register fields.
use super::{ModRM, Sib, trust_cg_x86_low3};

#[test]
fn shared_rex_byte_preserves_every_flag_combination() {
    use super::RexPrefix;
    for flags in 0u8..16 {
        let prefix = RexPrefix {
            w: flags / 8 != 0,
            r: (flags / 4) % 2 != 0,
            x: (flags / 2) % 2 != 0,
            b: flags % 2 != 0,
        };
        assert_eq!(prefix.encode(), 64 + flags);
        assert_eq!(prefix.is_needed(), flags != 0);
    }
}

#[test]
fn shared_register_bits_cover_every_u8_carrier() {
    for raw in u8::MIN..=u8::MAX {
        assert_eq!(u16::from(trust_cg_x86_low3(raw)), u16::from(raw) % 8);
        assert_eq!(Sib::base_only(raw).encode(), 32 + raw % 8);
    }
}

#[test]
fn shared_register_bits_preserve_all_sib_and_modrm_bytes() {
    for base in u8::MIN..=u8::MAX {
        for index in u8::MIN..=u8::MAX {
            let base_field = u16::from(base) % 8;
            let index_field = u16::from(index) % 8;
            for (scale_bits, scale_factor) in [(0u8, 1), (1, 2), (2, 4), (3, 8)] {
                let expected = u16::from(scale_bits) * 64 + index_field * 8 + base_field;
                assert_eq!(
                    u16::from(Sib::scaled(base, index, scale_factor).encode()),
                    expected
                );
                assert_eq!(
                    u16::from(
                        Sib {
                            scale: scale_bits,
                            index,
                            base
                        }
                        .encode()
                    ),
                    expected
                );

                // Direct construction may set bits outside the documented
                // field widths. Preserve the observable byte for those inputs.
                let mode = scale_bits + 4;
                let raw = ModRM {
                    mode,
                    reg: index,
                    rm: base,
                };
                assert_eq!(raw.encode(), (mode << 6) | (index << 3) | base);
            }
            assert_eq!(
                u16::from(ModRM::reg_reg(index, base).encode()),
                192 + index_field * 8 + base_field
            );
            assert_eq!(
                u16::from(ModRM::indirect(index, base).encode()),
                index_field * 8 + base_field
            );
        }
    }
}

#[test]
fn shared_extended_flag_covers_every_carrier_and_actual_rex_registers() {
    use super::{X86Encoder, X86PReg, shared_x86_is_extended};
    for raw in u8::MIN..=u8::MAX {
        assert_eq!(shared_x86_is_extended(raw), u16::from(raw) / 8 != 0);
    }
    for reg in 0u16..80 {
        for rm in 0u16..80 {
            let reg = X86PReg::new(reg);
            let rm = X86PReg::new(rm);
            let r = u16::from(reg.hw_enc()) / 8 != 0;
            let b = u16::from(rm.hw_enc()) / 8 != 0;
            for wide in [false, true] {
                let actual = X86Encoder::rex_rr(reg, rm, wide);
                assert_eq!(
                    (actual.w, actual.r, actual.x, actual.b),
                    (wide, r, false, b)
                );
            }
            let actual = X86Encoder::rex_rr64(reg, rm);
            assert_eq!(
                (actual.w, actual.r, actual.x, actual.b),
                (true, r, false, b)
            );
        }
    }
}
