/- Shared REX.W C1 /5 prefixes. encode_shrRI_immediate covers every imm8. -/
import Trust.Model.Encoder
namespace Trust.Model.Encoder
theorem g_shrRI_rax_zero : encode (.shrRI .b64 .rax 0) = ([0x48, 0xC1, 0xE8, 0x00] : List UInt8) := by decide
theorem g_shrRI_rcx_zero : encode (.shrRI .b64 .rcx 0) = ([0x48, 0xC1, 0xE9, 0x00] : List UInt8) := by decide
theorem g_shrRI_rdx_zero : encode (.shrRI .b64 .rdx 0) = ([0x48, 0xC1, 0xEA, 0x00] : List UInt8) := by decide
theorem g_shrRI_rbx_zero : encode (.shrRI .b64 .rbx 0) = ([0x48, 0xC1, 0xEB, 0x00] : List UInt8) := by decide
theorem g_shrRI_rsp_zero : encode (.shrRI .b64 .rsp 0) = ([0x48, 0xC1, 0xEC, 0x00] : List UInt8) := by decide
theorem g_shrRI_rbp_zero : encode (.shrRI .b64 .rbp 0) = ([0x48, 0xC1, 0xED, 0x00] : List UInt8) := by decide
theorem g_shrRI_rsi_zero : encode (.shrRI .b64 .rsi 0) = ([0x48, 0xC1, 0xEE, 0x00] : List UInt8) := by decide
theorem g_shrRI_rdi_zero : encode (.shrRI .b64 .rdi 0) = ([0x48, 0xC1, 0xEF, 0x00] : List UInt8) := by decide
theorem g_shrRI_r8_zero : encode (.shrRI .b64 .r8 0) = ([0x49, 0xC1, 0xE8, 0x00] : List UInt8) := by decide
theorem g_shrRI_r9_zero : encode (.shrRI .b64 .r9 0) = ([0x49, 0xC1, 0xE9, 0x00] : List UInt8) := by decide
theorem g_shrRI_r10_zero : encode (.shrRI .b64 .r10 0) = ([0x49, 0xC1, 0xEA, 0x00] : List UInt8) := by decide
theorem g_shrRI_r11_zero : encode (.shrRI .b64 .r11 0) = ([0x49, 0xC1, 0xEB, 0x00] : List UInt8) := by decide
theorem g_shrRI_r12_zero : encode (.shrRI .b64 .r12 0) = ([0x49, 0xC1, 0xEC, 0x00] : List UInt8) := by decide
theorem g_shrRI_r13_zero : encode (.shrRI .b64 .r13 0) = ([0x49, 0xC1, 0xED, 0x00] : List UInt8) := by decide
theorem g_shrRI_r14_zero : encode (.shrRI .b64 .r14 0) = ([0x49, 0xC1, 0xEE, 0x00] : List UInt8) := by decide
theorem g_shrRI_r15_zero : encode (.shrRI .b64 .r15 0) = ([0x49, 0xC1, 0xEF, 0x00] : List UInt8) := by decide
end Trust.Model.Encoder
