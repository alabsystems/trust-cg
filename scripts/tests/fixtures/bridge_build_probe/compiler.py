#!/usr/bin/env python3
"""Controlled compiler process, NOT a Trust compiler or proof oracle.

An explicitly selected compiler checks rewritten ordinary-Rust stand-ins.
Private crate declarations, diagnostic file names, one reviewed old function
argument type spelling and fake sysroots are adapted. Original argv retains
actual build-script forwarding decisions; original diagnostic bytes are kept.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from sysroot_contract import metadata_sysroot, translate_probe_sysroot

args = sys.argv[1:]
mode = os.environ["PROBE_FIXTURE_MODE"]
# Transform only the failure-note of an otherwise genuine compiler diagnostic.
# The build script still checks its code, source span, summary and multiplicity.
note_mode = mode if mode.startswith("note-") else None
branded = mode.startswith("trust-") or note_mode is not None
if mode.startswith("trust-"):
    mode = mode.removeprefix("trust-")
if note_mode is not None:
    mode = "missing-mir"
root = Path(os.environ["PROBE_FIXTURE_ROOT"])
with (root / "argv.jsonl").open("a") as output:
    output.write(json.dumps(args) + "\n")
if args == ["-vV"]:
    print("rustc process fixture\nbinary: rustc\ncommit-hash: " + "1" * 40 +
          "\ncommit-date: 2026-09-12\nhost: aarch64-unknown-linux-gnu\nrelease: fixture")
    sys.exit(0)
try:
    sysroot = metadata_sysroot(args, root, os.environ["PROBE_FIXTURE_TARGET"])
except ValueError as error:
    print(f"error: {error}", file=sys.stderr)
    sys.exit(1)
if sysroot is not None:
    print(sysroot)
    sys.exit(0)
if "-Zhelp" in args:
    if mode in ("current-help", "current-help-no-tracked"):
        listing = Path(os.environ["PROBE_FIXTURE_HELP"]).read_text()
        if mode == "current-help-no-tracked":
            listing = "\n".join(line for line in listing.splitlines()
                                if not line.lstrip().startswith("-Z") or "trust-ir-cg-args=" not in line)
            listing += "\n        trust-ir-cg-args is mentioned in a description, not advertised as an option\n"
        print(listing)
        sys.exit(0)
    if mode == "help-failure":
        print("tool could not load its sysroot", file=sys.stderr)
        sys.exit(17)
    if mode == "help-ambiguous":
        print("unrecognized empty capability listing")
    else:
        print("Available fictional options:" if mode == "help-unknown-header" else "Available options:")
        if mode == "orphan-help-continuation":
            print("        description without a preceding option")
        print("    -Z codegen-backend=val -- select backend")
        if mode != "legacy-no-off":
            print("    -Z trust-verify=val -- select verification policy")
        if mode not in ("missing-field", "both-legacy"):
            print("    -Z trust-ir-cg-args=val -- tracked backend arguments")
        if mode == "duplicate-off":
            print("    -Z trust-verify=val -- duplicated policy")
        if mode == "duplicate-tracked":
            print("    -Z trust-ir-cg-args=val -- duplicated arguments")
        if mode == "duplicate-standard":
            print("    -Z codegen-backend=val -- duplicated backend")
        if mode == "malformed-help-row":
            print("    -Z trust-verify -- malformed row")
        if mode == "help-trailing-error":
            print("error: capability listing is incomplete")
        if mode == "help-indented-error":
            print("        error: capability listing is incomplete")
        if mode == "help-unindented-description":
            print("description without continuation indentation")
    sys.exit(0)

source_path = next(Path(arg) for arg in args if arg.endswith(".rs"))
name = source_path.stem
target = name == "probe_trust_ir_cg_args"
early_target = name == "probe_early_session"
hir_target = name == "probe_hir_lang_item"
memory_target = name == "probe_memory_lang_item"
attributes_target = name == "probe_hir_attributes"
common_target = name == "probe_common_linkage"
module_cache_target = name == "probe_compiled_module_cache_links"
crate_type_target = name == "probe_session_crate_type"
sample_profile_target = name == "probe_unstable_sample_profile"
scalar_pair_target = name == "probe_tuple_scalar_pair"
retained_pair_target = name == "probe_retained_scalar_pair"
cast_padding_target = name == "probe_boolean_cast_padding"
retained_cast_target = name == "probe_retained_cast_padding"
if early_target and mode in ("early-session-tool-failure", "early-session-missing-output", "early-session-malformed-json"):
    if mode == "early-session-malformed-json":
        print("{not-json", file=sys.stderr)
    sys.exit(0 if mode == "early-session-missing-output" else 31)
indirect_target = name == "probe_boolean_indirect_stack"
retained_indirect_target = name == "probe_retained_indirect_modes"
float_target = name == "probe_bfloat_primitive"
retained_float_target = name == "probe_retained_float_formats"
register_target = name == "probe_ppc_f128_register"
retained_register_target = name == "probe_retained_register_kinds"
format_probe = float_target or retained_float_target or register_target or retained_register_target
pointer_target = name == "probe_scalar_pointer_result"
retained_pointer_target = name == "probe_retained_scalar_pointer"
pointer_probe = pointer_target or retained_pointer_target
terminator_target = name == "probe_terminator_attributes"
retained_terminator_target = name == "probe_retained_terminator"
terminator_probe = terminator_target or retained_terminator_target
goto_target = name == "probe_goto_loop_hints"
retained_goto_target = name == "probe_retained_goto"
goto_probe = goto_target or retained_goto_target
lanes_target = name == "probe_backend_lane_count"
retained_lanes_target = name == "probe_retained_backend_lanes"
fn_args_target = name == "probe_bound_fn_args"
retained_fn_args_target = name == "probe_retained_fn_args"
# The alias probe compiles against the same function-item stand-in.
fn_args_probe = fn_args_target or retained_fn_args_target or name == "probe_generic_args_ref"
super_query_target = name == "probe_super_clauses_query"
retained_super_query_target = name == "probe_retained_super_clauses"
own_query_target = name == "probe_own_clauses_query"
retained_own_query_target = name == "probe_retained_own_clauses"
query_probe = super_query_target or retained_super_query_target or own_query_target or retained_own_query_target

off_flags = [arg for arg in args if arg.startswith("-Ztrust-verify=")]
if mode == "legacy-no-off" and off_flags:
    print("error: unknown unstable option: `trust-verify`", file=sys.stderr)
    sys.exit(1)
if mode == "strict-ambient" and (not off_flags or off_flags[-1] != "-Ztrust-verify=off"):
    print("error: Trust strict verification failed (controlled process fixture)", file=sys.stderr)
    sys.exit(1)
if mode == "verification-refusal" and target:
    print("error: Trust strict verification failed (controlled process fixture)", file=sys.stderr)
    sys.exit(1)
if mode == "tool-failure" and target:
    sys.exit(31)
if mode in ("missing-output", "missing-output-stale") and target:
    sys.exit(0)
if mode == "malformed-json" and target:
    print("{not-json", file=sys.stderr)
    sys.exit(1)
if mode == "scalar-pair-missing-output" and retained_pair_target:
    sys.exit(0)
if mode == "cast-padding-missing-output" and retained_cast_target:
    sys.exit(0)
if mode == "indirect-missing-output" and retained_indirect_target:
    sys.exit(0)
if mode == "float-formats-missing-output" and retained_float_target:
    sys.exit(0)
if mode == "register-kinds-missing-output" and retained_register_target:
    sys.exit(0)
if mode == "pointer-missing-output" and retained_pointer_target:
    sys.exit(0)
if mode == "terminator-missing-output" and retained_terminator_target:
    sys.exit(0)

if mode == "goto-missing-output" and retained_goto_target:
    sys.exit(0)
query_mode = mode
query_group = "super" if mode.startswith("query-super-") else "own" if mode.startswith("query-own-") else None
query_fault = mode.removeprefix("query-" + query_group + "-") if query_group else None
query_minimal_target = (query_group == "super" and super_query_target) or (query_group == "own" and own_query_target)
query_retained_target = (query_group == "super" and retained_super_query_target) or (query_group == "own" and retained_own_query_target)
if query_retained_target and query_fault in ("modern-missing-output", "legacy-missing-output"):
    sys.exit(0)

modern_super_query = mode.startswith(("query-super-modern", "query-both-modern"))
modern_own_query = mode.startswith(("query-own-modern", "query-both-modern"))
if mode.startswith("query-"):
    if mode.endswith("-all"):
        mode = "fn-args-modern-all"
    elif mode.endswith("-fn-args"):
        mode = "fn-args-modern"
    else:
        mode = "present"
fn_args_mode = mode
bound_fn_args = mode.startswith("fn-args-") and not mode.startswith("fn-args-legacy-")
if mode == "fn-args-missing-output" and retained_fn_args_target:
    sys.exit(0)
if mode.startswith("fn-args-"):
    if mode in ("fn-args-modern-all", "fn-args-legacy-all"):
        mode = "lanes-modern-all"
    elif mode in ("fn-args-modern-lanes", "fn-args-legacy-lanes"):
        mode = "lanes-modern"
    elif mode in ("fn-args-modern-goto", "fn-args-legacy-goto"):
        mode = "goto-modern"
    else:
        mode = "present"
lanes_mode = mode
wrapped_lanes = mode.startswith("lanes-") and not mode.startswith("lanes-legacy-")
if mode == "lanes-missing-output" and retained_lanes_target:
    sys.exit(0)
if mode.startswith("lanes-"):
    if mode in ("lanes-modern-all", "lanes-legacy-all"):
        mode = "goto-modern-all"
    elif mode in ("lanes-modern-goto", "lanes-legacy-goto"):
        mode = "goto-modern"
    elif mode in ("lanes-modern-pair", "lanes-legacy-pair"):
        mode = "scalar-pair-modern"
    else:
        mode = "present"
goto_mode = mode
goto_hints = mode.startswith("goto-") and not mode.startswith("goto-legacy-")
if mode.startswith("goto-"):
    if mode in ("goto-modern-all", "goto-legacy-all"):
        mode = "terminator-modern-all"
    elif mode in ("goto-modern-terminator", "goto-legacy-terminator"):
        mode = "terminator-modern"
    elif mode in ("goto-modern-pointer", "goto-legacy-pointer"):
        mode = "pointer-modern"
    else:
        mode = "present"
terminator_mode = mode
terminator_attributes = not (mode.startswith("terminator-") and not mode.startswith("terminator-legacy-"))
if mode in ("terminator-modern-all", "terminator-legacy-all"):
    mode = "pointer-modern-all"
elif mode in ("terminator-modern-pointer", "terminator-legacy-pointer"):
    mode = "pointer-modern"
pointer_mode = mode
modern_pointer = mode.startswith("pointer-") and not mode.startswith("pointer-legacy-")
if mode in ("pointer-modern-all", "pointer-legacy-all"):
    mode = "formats-modern-all"
elif mode == "pointer-modern-float":
    mode = "float-formats-modern"
elif mode == "pointer-modern-register":
    mode = "register-kinds-modern"
format_mode = mode
modern_float = ((mode.startswith("float-formats-") and not mode.startswith("float-formats-legacy-"))
                or mode in ("formats-modern", "formats-modern-all"))
modern_register = ((mode.startswith("register-kinds-") and not mode.startswith("register-kinds-legacy-"))
                   or mode in ("formats-modern", "formats-modern-all"))
if mode in ("float-formats-modern-all", "register-kinds-modern-all", "formats-modern-all"):
    mode = "indirect-modern-all"
float_names = ["F16", "F32", "F64", "F128"] + (["F16B", "PpcF128"] if modern_float else [])
if format_mode == "float-formats-missing-ppc":
    float_names.remove("PpcF128")
elif format_mode == "float-formats-missing-f16":
    float_names.remove("F16")
elif format_mode == "float-formats-legacy-missing-f128":
    float_names.remove("F128")
elif format_mode in ("float-formats-unknown-variant", "float-formats-legacy-unknown-variant"):
    float_names.append("OtherFloat")
elif format_mode == "float-formats-tuple-variant":
    float_names[float_names.index("F16B")] = "F16B(u8)"
elif format_mode == "float-formats-legacy-ppc-only":
    float_names.append("PpcF128")
vector_fields = {"hint_vector_elem": "Primitive"}
if format_mode in ("register-kinds-missing-hint", "register-kinds-legacy-missing-hint"):
    vector_fields.clear()
elif format_mode in ("register-kinds-wrong-hint-type", "register-kinds-legacy-wrong-hint-type"):
    vector_fields["hint_vector_elem"] = "Option<Primitive>"
elif format_mode in ("register-kinds-required-vector-field", "register-kinds-legacy-required-vector-field"):
    vector_fields["required"] = "bool"
register_names = ["Integer", "Float", "Vector { " + ",".join(k + ":" + v for k, v in vector_fields.items()) + " }"]
if modern_register:
    register_names.append("PpcF128")
if format_mode in ("register-kinds-unknown-variant", "register-kinds-legacy-unknown-variant"):
    register_names.append("OtherRegister")
elif format_mode == "register-kinds-missing-integer":
    register_names.remove("Integer")
elif format_mode == "register-kinds-tuple-variant":
    register_names[register_names.index("PpcF128")] = "PpcF128(u8)"
reg_import = "use super::Primitive; " if any("Primitive" in value for value in vector_fields.values()) else ""
kind_abi = ("#[derive(Clone, Copy)] pub struct Primitive; pub enum Float { " + ",".join(float_names) +
            " } mod reg { " + reg_import + "pub enum RegKind { " + ",".join(register_names) +
            " } } pub use reg::RegKind;")
layout_size_type = "u64" if pointer_mode.endswith("wrong-layout-size-type") else "Size"
layout_size_value = "0" if layout_size_type == "u64" else "Size(0)"
layout_size_method = ("" if pointer_mode.endswith("missing-layout-size") else
                      f"pub fn pointer_size(&self) -> {layout_size_type} {{ {layout_size_value} }}")
kind_abi += ("#[derive(Clone, Copy, PartialEq, Eq)] pub struct Size(pub u64);"
             "pub struct TargetDataLayout; impl TargetDataLayout { " + layout_size_method + " }"
             "pub trait HasDataLayout { fn data_layout(&self) -> &TargetDataLayout; }")
pointer_return = "Pointer<Option<CtfeProvenance>>" if modern_pointer else "PointerResult"
if pointer_mode.endswith("wrong-return"):
    pointer_return = "Option<Pointer<Option<CtfeProvenance>>>"
discard_return = ("Option<Pointer<CtfeProvenance>>" if pointer_mode == "pointer-legacy-wrong-discard"
                  else "Option<Pointer<Option<CtfeProvenance>>>")
scalar_pointer_method = ("" if pointer_mode == "pointer-missing-conversion" else
                         "pub fn to_pointer(self, _cx: &impl rustc_abi::HasDataLayout) -> " +
                         pointer_return + " { unimplemented!() }")
scalar_size_type = "u64" if pointer_mode.endswith("wrong-size-type") else "Size"
scalar_size_method = ("" if pointer_mode.endswith("missing-size") else
                      "pub fn size(self) -> " + scalar_size_type + " { unimplemented!() }")
address_split_method = ("" if pointer_mode.endswith("missing-address-split") else
                        "pub fn into_pointer_or_addr(self) -> Result<Pointer<CtfeProvenance>, Size> { unimplemented!() }")
relative_offset_type = "u64" if pointer_mode.endswith("wrong-relative-offset-type") else "Size"
relative_offset_method = ("" if pointer_mode.endswith("missing-relative-offset") else
                          "pub fn prov_and_relative_offset(self) -> (CtfeProvenance, " +
                          relative_offset_type + ") { unimplemented!() }")
terminator_name = "OtherTerminator" if terminator_mode.endswith("missing-type") else "Terminator"
source_info_name = "OtherSourceInfo" if terminator_mode.endswith("missing-source-type") else "SourceInfo"
source_info_derive = "" if terminator_mode.endswith("noncopy-source") else "#[derive(Clone, Copy)]"
source_info_field = "context" if terminator_mode.endswith("renamed-source") else "source_info"
source_info_type = "u64" if terminator_mode.endswith("wrong-source-type") else source_info_name
kind_field = "other_kind" if terminator_mode.endswith("renamed-kind") else "kind"
kind_type = "&'tcx ()" if terminator_mode.endswith("wrong-kind-type") else "TerminatorKind<'tcx>"
terminator_fields = f"pub {source_info_field}: {source_info_type}, pub {kind_field}: {kind_type},"
if terminator_attributes:
    visibility = "" if terminator_mode.endswith("private-attrs") else "pub "
    attribute_type = "u64" if terminator_mode.endswith("wrong-attrs-type") else "Vec<()>"
    # The intentionally private field must reach the consumer's privacy error,
    # rather than failing the ordinary dependency's own dead-code lint first.
    field_lint = "#[allow(dead_code)] " if not visibility else ""
    terminator_fields += field_lint + visibility + "attributes: " + attribute_type + ","
if terminator_mode.endswith("required-field"):
    terminator_fields += "pub required: bool,"
block_name = "OtherBasicBlock" if goto_mode.endswith("missing-block-type") else "BasicBlock"
block_derive = "" if goto_mode.endswith("noncopy-target") else "#[derive(Clone, Copy)]"
goto_name = "Jump" if goto_mode.endswith("missing-variant") else "Goto"
goto_target_name = "destination" if goto_mode.endswith("renamed-target") else "target"
goto_target_type = "bool" if goto_mode.endswith("wrong-target-type") else block_name
goto_fields = goto_target_name + ": " + goto_target_type + ","
if goto_hints:
    hint_type = ("u64" if goto_mode == "goto-wrong-hints-type" else
                 "std::collections::BTreeSet<()>" if goto_mode == "goto-wrong-hints-container" else "Vec<()>")
    goto_fields += "loop_hint_attrs: " + hint_type + ","
if goto_mode.endswith("required-field"):
    goto_fields += "required: bool,"
goto_variant = ("Goto(" + block_name + ")" if goto_mode == "goto-tuple-variant" else
                goto_name + " { " + goto_fields + " }")
goto_middle = block_derive + " pub struct " + block_name + "(pub u32);"
terminator_middle = (goto_middle + source_info_derive + " pub struct " + source_info_name + ";"
                     "pub enum TerminatorKind<'tcx> { Return, Marker(&'tcx ()), " + goto_variant + " }"
                     "pub struct " + terminator_name + "<'tcx> { " + terminator_fields + " }")
pointer_middle = ("extern crate rustc_abi; pub mod mir { pub mod interpret { use rustc_abi::Size;"
                  "pub struct CtfeProvenance; pub struct Pointer<Prov> { pub provenance: Prov, pub offset: Size }"
                  "#[derive(Clone, Copy)] pub struct Scalar; impl Scalar { " + scalar_size_method +
                  scalar_pointer_method + " } pub struct PointerResult; impl PointerResult { "
                  "pub fn discard_err(self) -> " + discard_return + " { None } }"
                  "impl Pointer<Option<CtfeProvenance>> { " + address_split_method + " }"
                  "impl Pointer<CtfeProvenance> { " + relative_offset_method + " } } " + terminator_middle + " }")

# Ordinary external types retain the compiler's missing-method diagnostic
# spelling. They are process-schema controls, not a binder semantics oracle.
fn_copy = "" if fn_args_mode == "fn-args-noncopy-binder" else "#[derive(Clone, Copy)]"
fn_method = "missing_no_bound_vars" if fn_args_mode == "fn-args-missing-method" else "no_bound_vars"
fn_read_result = "u64" if fn_args_mode == "fn-args-wrong-return-type" else "T"
fn_read_value = "0" if fn_args_mode == "fn-args-wrong-return-type" else "self.value"
fn_args_type = "Binder<'tcx, GenericArgsRef<'tcx>>" if bound_fn_args else "GenericArgsRef<'tcx>"
if fn_args_mode == "fn-args-legacy-wrong-args-type":
    fn_args_type = "u64"
fn_variant = "OtherFnDef" if fn_args_mode == "fn-args-missing-fndef" else "FnDef"
fn_extra = ", bool" if fn_args_mode in ("fn-args-required-field", "fn-args-legacy-required-field") else ""
fn_new_args = "GenericArgsRef<'tcx>" if fn_args_mode == "fn-args-wrong-constructor" else fn_args_type
fn_new_id = "u64" if fn_args_mode == "fn-args-wrong-def-id-type" else "u32"
fn_new_result = "u64" if fn_args_mode == "fn-args-wrong-new-result" else "Self"
fn_types = ("pub mod ty { use std::marker::PhantomData; "
            "pub mod list { pub struct RawList<H, T>(pub H, pub std::marker::PhantomData<T>); } "
            "pub struct GenericArg<'tcx>(pub &'tcx ()); "
            "pub type GenericArgsRef<'tcx> = &'tcx list::RawList<(), GenericArg<'tcx>>; "
            "pub type TyCtxt<'tcx> = &'tcx (); " + fn_copy +
            " pub struct Binder<'tcx, T> { pub value: T, pub marker: PhantomData<&'tcx ()> } "
            "impl<'tcx, T> Binder<'tcx, T> { pub fn dummy(value: T) -> Self { "
            "Self { value, marker: PhantomData } } pub fn " + fn_method +
            "(self) -> Option<" + fn_read_result + "> { Some(" + fn_read_value + ") } } " +
            fn_copy + " pub enum TyKind<'tcx> { " + fn_variant + "(u32, " + fn_args_type + fn_extra +
            "), Other(&'tcx ()) } pub use self::TyKind::*; "
            "pub struct Ty<'tcx>(pub &'tcx TyKind<'tcx>); "
            "impl<'tcx> Ty<'tcx> { pub fn kind(&self) -> &'tcx TyKind<'tcx> { self.0 } "
            "pub fn new_fn_def(_: TyCtxt<'tcx>, _: " + fn_new_id + ", _: " + fn_new_args +
            ") -> " + fn_new_result + " { unimplemented!() } } }")
pointer_middle += fn_types

indirect_mode = mode
modern_indirect = mode.startswith("indirect-") and not mode.startswith("indirect-legacy-")
if mode == "indirect-modern-all":
    mode = "cast-padding-modern-all"
padding_mode = mode
modern_padding = mode.startswith("cast-padding-") and not mode.startswith("cast-padding-legacy-")
if mode == "cast-padding-modern-all":
    mode = "scalar-pair-modern-all"
padding_field = "pad_i32_count" if modern_padding else "pad_i32"
padding_type = "u8" if modern_padding else "bool"
if padding_mode == "cast-padding-wrong-count-type":
    padding_type = "u16"
elif padding_mode == "cast-padding-legacy-wrong-count-type":
    padding_type = "u8"
padding_fields = {"cast": "Box<CastTarget>", padding_field: padding_type}
if padding_mode in ("cast-padding-missing-count", "cast-padding-legacy-missing-count"):
    del padding_fields[padding_field]
if padding_mode in ("cast-padding-wrong-target-type", "cast-padding-legacy-wrong-target-type"):
    padding_fields["cast"] = "Box<u8>"
if padding_mode == "cast-padding-missing-cast":
    del padding_fields["cast"]
if padding_mode == "cast-padding-required-variant-field":
    padding_fields["required"] = "bool"
cast_variant = "Cast { " + ",".join(key + ":" + value for key, value in padding_fields.items()) + " }"
if padding_mode == "cast-padding-tuple-shape":
    cast_variant = "Cast(Box<CastTarget>, u8)"
elif padding_mode == "cast-padding-missing-variant":
    cast_variant = "OtherCast { " + ",".join(key + ":" + value for key, value in padding_fields.items()) + " }"
target_fields = {"prefix": "Vec<u8>", "rest_offset": "Option<usize>", "rest": "usize", "attrs": "u8"}
if padding_mode == "cast-padding-missing-target-field":
    del target_fields["attrs"]
elif padding_mode == "cast-padding-required-target-field":
    target_fields["required"] = "bool"
attribute_fields = {"regular": "u8", "arg_ext": "u8", "pointee_size": "usize",
                    "pointee_align": "Option<usize>"}
if indirect_mode == "indirect-missing-attribute":
    del attribute_fields["arg_ext"]
elif indirect_mode == "indirect-required-attribute":
    attribute_fields["required"] = "bool"
indirect_fields = ({"attrs": "ArgAttributes", "address_space": "Option<super::AddressSpace>",
                    "mode": "IndirectMode"} if modern_indirect else
                   {"attrs": "ArgAttributes", "meta_attrs": "Option<ArgAttributes>", "on_stack": "bool"})
unsized_fields = {"attrs": "ArgAttributes", "meta_attrs": "ArgAttributes"}
for case, field in (("missing-address-space", "address_space"), ("missing-mode", "mode"),
                    ("missing-data-attrs", "attrs"), ("legacy-missing-meta", "meta_attrs")):
    if indirect_mode == "indirect-" + case:
        del indirect_fields[field]
for case, field, value in (("wrong-address-space", "address_space", "Option<u32>"),
                           ("wrong-mode", "mode", "u8"), ("wrong-data-attrs", "attrs", "u8"),
                           ("legacy-wrong-stack", "on_stack", "u8"),
                           ("legacy-wrong-meta", "meta_attrs", "ArgAttributes"),
                           ("required-field", "required", "bool"),
                           ("legacy-required-field", "required", "bool")):
    if indirect_mode == "indirect-" + case:
        indirect_fields[field] = value
for case, field in (("unsized-missing-meta", "meta_attrs"), ("unsized-missing-data", "attrs")):
    if indirect_mode == "indirect-" + case:
        del unsized_fields[field]
if indirect_mode == "indirect-unsized-wrong-meta":
    unsized_fields["meta_attrs"] = "Option<ArgAttributes>"
elif indirect_mode == "indirect-unsized-required-field":
    unsized_fields["required"] = "bool"
indirect_name = "OtherIndirect" if indirect_mode == "indirect-missing-variant" else "Indirect"
indirect_variant = indirect_name + " { " + ",".join(k + ":" + v for k, v in indirect_fields.items()) + " }"
if modern_indirect:
    unsized_name = "OtherUnsized" if indirect_mode == "indirect-unsized-missing-variant" else "IndirectUnsized"
    indirect_variant += "," + unsized_name + " { " + ",".join(k + ":" + v for k, v in unsized_fields.items()) + " }"
mode_variants = "Pointer, OnStack, AmdgpuKernelArg"
if indirect_mode == "indirect-unknown-mode":
    mode_variants += ", OtherMode"
zero = "" if indirect_mode == "indirect-missing-zero" else "impl AddressSpace { pub const ZERO: Self = Self(0); }"
callconv = ("pub mod rustc_target { #[derive(Clone, Copy, PartialEq, Eq)] pub struct AddressSpace(pub u32); " + zero +
            " pub mod callconv { #[derive(Clone, Copy)] pub enum IndirectMode { " + mode_variants + " } "
            "pub struct ArgAttributes { " + ",".join("pub " + k + ":" + v for k, v in attribute_fields.items()) +
            " } pub struct CastTarget { " +
            ",".join("pub " + key + ":" + value for key, value in target_fields.items()) +
            " } pub enum PassMode { Ignore, " + cast_variant + "," + indirect_variant + " } } }")

# This flag is independent of the seven earlier API capabilities. Both shapes
# are ordinary-Rust type controls; layout semantics use the real driver fixture.
modern_pair = mode.startswith("scalar-pair-") and not mode.startswith("scalar-pair-legacy-")
pair_mode = mode
if mode == "scalar-pair-modern-all":
    mode = "options-modern-all"
modern_pair_fields = "a: Scalar, b: Scalar, b_offset: Size"
if pair_mode == "scalar-pair-missing-offset":
    modern_pair_fields = "a: Scalar, b: Scalar"
elif pair_mode == "scalar-pair-wrong-offset-type":
    modern_pair_fields = "a: Scalar, b: Scalar, b_offset: u8"
elif pair_mode == "scalar-pair-wrong-component-type":
    modern_pair_fields = "a: Scalar, b: u8, b_offset: Size"
elif pair_mode == "scalar-pair-required-field":
    modern_pair_fields += ", required: bool"
pair_variant = ("ScalarPair { " + modern_pair_fields + " }" if modern_pair else
                "ScalarPair(Scalar, Scalar)")
if pair_mode == "scalar-pair-legacy-partial":
    pair_variant = "ScalarPair(Scalar, u8)"
elif pair_mode == "scalar-pair-legacy-third-field":
    pair_variant = "ScalarPair(Scalar, Scalar, Size)"
elif pair_mode == "scalar-pair-missing-variant":
    pair_variant = "OtherPair(Scalar, Scalar)"
offset_result = "u8" if pair_mode == "scalar-pair-legacy-wrong-offset-type" else "Size"
offset_value = "0" if offset_result == "u8" else "Size"
lane_name = "OtherVector" if lanes_mode == "lanes-missing-variant" else "SimdVector"
lane_target = "lanes" if lanes_mode == "lanes-renamed-count" else "count"
lane_element = "bool" if lanes_mode == "lanes-wrong-element-type" else "Scalar"
lane_type = "u32" if lanes_mode == "lanes-legacy-wrong-count-type" else "u64"
lane_wrapper = ""
if wrapped_lanes:
    lane_type = "BackendLaneCount"
    lane_result = "u32" if lanes_mode == "lanes-wrong-result-type" else "u64"
    lane_receiver = "self" if lanes_mode == "lanes-noncopy-consuming-count" else "&self"
    lane_derive = "" if lanes_mode == "lanes-noncopy-consuming-count" else "#[derive(Clone, Copy)]"
    lane_method = "other" if lanes_mode == "lanes-missing-method" else "as_u64"
    lane_result_value = "self.0 as " + lane_result
    lane_wrapper = (lane_derive + " pub struct BackendLaneCount(u64); impl BackendLaneCount { pub fn " +
                    lane_method + "(" + lane_receiver + ") -> " + lane_result + " { " + lane_result_value + " } } ")
lane_fields = "element: " + lane_element + ", " + lane_target + ": " + lane_type
if lanes_mode in ("lanes-required-field", "lanes-legacy-required-field"):
    lane_fields += ", required: bool"
lane_variant = lane_name + " { " + lane_fields + " }"
if lanes_mode == "lanes-tuple-variant":
    lane_variant = "SimdVector(Scalar, BackendLaneCount)"
abi = ("pub mod rustc_abi { #[derive(Clone, Copy)] pub struct Scalar; " + lane_wrapper +
       "pub struct Size; pub struct Aligns { pub abi: Size } pub trait HasDataLayout {} "
       "impl Scalar { pub fn size<C: HasDataLayout>(self, _: &C) -> Size { Size } "
       "pub fn default_align<C: HasDataLayout>(self, _: &C) -> Aligns { Aligns { abi: Size } } } "
       "impl Size { pub fn align_to(self, _: Size) -> " + offset_result + " { " + offset_value + " } } "
       "pub enum BackendRepr { " + pair_variant + ", " + lane_variant + ", Memory } }")
if indirect_target or retained_indirect_target:
    # Keep the two stand-in crates' address-space type identical, as in rustc.
    abi = abi.replace("pub mod rustc_abi {", "pub mod rustc_abi { pub use rustc_target::AddressSpace;")

macro = ("#[macro_export] macro_rules! fixture_find_attr { ($tcx:expr, $did:expr, $($tail:tt)*) => "
         "{{ let _ = ($tcx, $did); false }}; }")
modern_kind = mode.startswith("crate-type-") and mode != "crate-type-legacy-missing-kind"
modern_kind = modern_kind or mode == "options-modern-all"
kind_names = ["Executable", "Dylib", "Rlib", "StaticLib", "Cdylib", "ProcMacro", "Sdylib"]
if mode in ("crate-type-missing-kind", "crate-type-legacy-missing-kind"):
    kind_names.remove("Sdylib")
if mode == "crate-type-new-kind":
    kind_names.append("NewKind")
kind_definition = "pub mod fixture_crate_kinds { pub enum CrateType { " + ",".join(kind_names) + " } }"
source = source_path.read_text().replace("#![feature(rustc_private)]", macro + kind_definition)
missing_field = mode in ("missing-field", "both-legacy", "extra-error", "wrong-span", "field-option-mismatch", "current-help-no-tracked")
field = "legacy_field" if missing_field else "trust_ir_cg_args"
modern_sample = mode.startswith("sample-") and mode != "sample-old-wrong-type"
modern_sample = modern_sample or mode == "options-modern-all"
profile_type = "String" if mode in ("sample-old-wrong-type", "sample-new-wrong-type") else "std::path::PathBuf"
profile_field = "pub profile_sample_use: Option<" + profile_type + ">,"
old_profile = "" if modern_sample else profile_field
new_profile = profile_field if modern_sample and mode != "sample-missing-new" else ""
kind_import = ("use" if modern_kind else "pub use") + " crate::fixture_crate_kinds::CrateType;"
if mode == "crate-type-missing-old":
    kind_import = ""
elif modern_kind:
    if mode == "crate-type-private-import":
        kind_import += "pub fn fixture_kind() -> CrateType { CrateType::Executable }"
    else:
        # An in-crate private import diagnoses "enum import", unlike the real
        # cross-crate "enum" privacy boundary. Model the latter explicitly;
        # retain the former as an unknown-privacy refusal control.
        values = ",".join("CrateType::" + kind for kind in kind_names)
        kind_import = ("enum CrateType { " + ",".join(kind_names) +
                       " } pub fn fixture_kind() { let _ = [" + values + "]; }")
unstable_name = "OtherOptions" if mode == "sample-unknown-type" else "UnstableOptions"
session = ("pub mod rustc_session { pub mod config { " + kind_import +
           "pub struct Options { pub unstable_opts: UnstableOptions, pub cg: CodegenOptions } " +
           "pub struct CodegenOptions { " + new_profile + " } " +
           f"pub struct {unstable_name} {{ pub {field}: Vec<String>, " + old_profile + " }")
if unstable_name != "UnstableOptions":
    session += "pub type UnstableOptions = OtherOptions;"
session += " } " + ("pub struct EarlySession;" if mode == "early-session-present" else "") + " }"
structures = "pub mod rustc_structures { pub use crate::fixture_crate_kinds::CrateType; }"
query_type = "u8" if mode == "crate-type-query-wrong-type" else "crate::fixture_crate_kinds::CrateType"
kind_query = "" if mode == "crate-type-query-missing" else "pub fn crate_types(&self) -> &[" + query_type + "] { &[] }"
mono = "pub enum MonoItem<'tcx> { Item(&'tcx ()) }"
new_mono = "" if mode in ("missing-mir", "both-legacy", "missing-both-mono") else "pub mod mono { " + mono + " }"
old_mono = "" if mode == "missing-both-mono" else "pub mod mono { " + mono + " }"
canonical_fields = ("" if mode == "memory-canonical-missing-symbol" else "pub symbol: usize,")
canonical_fields += ("" if mode == "memory-canonical-missing-def-id" else "pub def_id: (),")
canonical_method = ("" if mode == "memory-canonical-missing" else
                    "pub fn all_canonical_symbols(&self, _: ()) -> &[Entry] { &[] }")
ty = ("pub mod ty { pub struct Context; pub type TyCtxt<'a> = &'a Context; "
      "pub struct LangItems; pub struct Entry { " + canonical_fields + " } "
      "impl Context { pub fn lang_items(&self) -> LangItems { LangItems } " + canonical_method + kind_query + " } "
      "impl LangItems { pub fn get<T>(&self, _: T) -> Option<()> { None } } }")
middle = "pub mod rustc_middle { pub mod mir { " + new_mono + " } " + old_mono + ty + " }"
if query_probe:
    super_method = "explicit_super_clauses_of" if modern_super_query else "explicit_super_predicates_of"
    own_method = "clauses_of" if modern_own_query else "predicates_of"
    own_carrier = "GenericClauses" if modern_own_query else "GenericPredicates"
    own_field = "clauses" if modern_own_query else "predicates"
    query_id = "u64" if query_fault in ("modern-wrong-id", "legacy-wrong-id") else "()"
    parent = "Option<u64>" if query_group == "own" and query_fault in ("modern-wrong-parent", "legacy-wrong-parent") else "Option<()>"
    clauses = "&'tcx [u64]" if query_group == "own" and query_fault in ("modern-wrong-clauses", "legacy-wrong-clauses") else "&'tcx [(Clause<'tcx>, ())]"
    parent_field = "" if query_group == "own" and query_fault in ("modern-missing-parent", "legacy-missing-parent") else "pub parent: " + parent + ", "
    required = "pub required: bool," if query_group == "own" and query_fault in ("modern-required-field", "legacy-required-field") else ""
    super_result = "u64" if query_group == "super" and query_fault in ("modern-wrong-result", "legacy-wrong-result") else "EarlyBinder<'tcx, &'tcx [(Clause<'tcx>, ())]>"
    own_result = "u64" if query_group == "own" and query_fault in ("modern-wrong-result", "legacy-wrong-result") else own_carrier + "<'tcx>"
    if query_group == "super" and query_fault in ("modern-missing-method", "legacy-missing-method"):
        super_method = "other_super_query"
    middle = ("pub mod rustc_middle { pub mod ty { "
              "pub struct Clause<'tcx>(pub &'tcx ()); "
              "pub struct EarlyBinder<'tcx, T> { pub value: T, pub marker: std::marker::PhantomData<&'tcx ()> } "
              "pub struct TyCtxt<'tcx>(pub &'tcx ()); "
              "pub struct " + own_carrier + "<'tcx> { " + parent_field + "pub " + own_field + ": " + clauses + "," + required + " } "
              "impl<'tcx> TyCtxt<'tcx> { pub fn " + super_method + "(self, _: " + (query_id if query_group == "super" else "()") + ") -> " + super_result + " { unimplemented!() } "
              "pub fn " + own_method + "(self, _: " + (query_id if query_group == "own" else "()") + ") -> " + own_result + " { unimplemented!() } } } }")

missing_hir_item = mode in (
    "missing-hir-lang-item", "missing-both-lang-items", "hir-lang-item-extra-error",
    "hir-lang-item-wrong-span", "hir-lang-item-denied-warning", "new-memory-and-lang-items",
    "new-attributes-new-lang-items",
    "module-modern-all", "options-modern-all",
)
missing_memory_item = mode in (
    "missing-memory-lang-items", "new-memory-and-lang-items", "memory-canonical-missing",
    "memory-canonical-missing-symbol", "memory-canonical-missing-def-id",
    "memory-extra-error", "memory-wrong-span", "memory-denied-warning",
    "module-modern-all", "options-modern-all",
)
memory_items = "" if missing_memory_item else (
    "MemCpy, MemSet," if mode == "memory-lang-item-partial" else "MemCpy, MemMove, MemSet,")
enum = "pub enum LangItem { Sized, " + memory_items + " }"
hir_item = "" if missing_hir_item else enum
missing_attributes = mode in (
    "missing-hir-attributes", "missing-both-attributes", "new-attributes-no-common",
    "new-attributes-new-lang-items", "attributes-extra-error", "attributes-wrong-span",
    "attributes-denied-warning",
    "module-modern-all", "options-modern-all", "module-legacy-new-attributes",
)
missing_common = mode in (
    "missing-common", "new-attributes-no-common", "common-extra-error",
    "common-wrong-span", "common-denied-warning",
    "module-modern-all", "options-modern-all", "module-legacy-new-attributes",
)
inline_variants = "None, Hint, Always, Never, Force { attr_span: (), reason: Option<()> },"
if mode == "attributes-partial-inline":
    inline_variants = "None, Hint, Never, Force { attr_span: (), reason: Option<()> },"
linkage_variants = ("AvailableExternally, ExternalWeak, External, Internal, "
                    "LinkOnceAny, LinkOnceODR, WeakAny, WeakODR,")
if mode == "attributes-partial-linkage":
    linkage_variants = "AvailableExternally, ExternalWeak, External, Internal, LinkOnceAny, LinkOnceODR, WeakAny,"
if not missing_common:
    linkage_variants += "Common,"
attributes = ("pub enum InlineAttr { " + inline_variants + " } pub enum Linkage { " + linkage_variants + " }")
# One physical line per extern replacement preserves the original probe spans.
macro_export = "" if mode == "attributes-missing-macro" else "pub use crate::fixture_find_attr as find_attr;"
hir_attributes = "" if missing_attributes else "pub mod attrs { " + attributes + " } "
hir = "pub mod rustc_hir { pub mod def_id { pub type DefId = (); } " + hir_item + hir_attributes + macro_export + " }"
attr_item = "" if mode == "missing-both-lang-items" else enum
modern_attributes = "" if mode == "missing-both-attributes" else attributes
attr_ir = "pub mod rustc_attr_ir { pub mod lang_items { " + attr_item + " } " + modern_attributes + macro_export + " }"
span = "pub mod rustc_span { pub struct Symbol; impl Symbol { pub fn intern(_: &str) -> usize { 0 } } }"
if query_probe:
    span_type = "u64" if query_group == "super" and query_fault in ("modern-wrong-span-type", "legacy-wrong-span-type") else "()"
    span = "pub mod rustc_span { pub type Span = " + span_type + "; }"
missing_module_cache = mode in (
    "module-cache-missing", "module-modern-all", "options-modern-all", "module-cache-extra-error",
    "module-cache-wrong-span", "module-cache-wrong-token", "module-cache-unrelated-field",
    "module-cache-denied-warning", "module-missing-llvm-ir", "module-unexpected-required",
    "module-cache-unknown-type",
)
module_fields = "pub name: String, pub kind: ModuleKind,"
for artifact in ("object", "global_asm_object", "dwarf_object", "bytecode", "assembly", "llvm_ir"):
    if (mode == "module-missing-object" and artifact == "object") or (
            mode == "module-missing-llvm-ir" and artifact == "llvm_ir"):
        continue
    value = "String" if mode == "module-object-wrong-type" and artifact == "object" else "std::path::PathBuf"
    module_fields += f"pub {artifact}: Option<{value}>,"
if not missing_module_cache:
    value = "Option<Vec<std::path::PathBuf>>" if mode == "module-cache-wrong-type" else "Vec<std::path::PathBuf>"
    module_fields += f"pub links_from_incr_cache: {value},"
if mode == "module-unexpected-required":
    module_fields += "pub new_required: bool,"
module_kind = "pub enum ModuleKind { Regular, Allocator }"
if mode == "module-missing-kind":
    module_kind = ""
    module_fields = module_fields.replace("pub kind: ModuleKind,", "pub kind: (),")
module_name = "OtherModule" if mode == "module-cache-unknown-type" else "CompiledModule"
ssa = "pub mod rustc_codegen_ssa { " + module_kind + f"pub struct {module_name} {{ " + module_fields + " }"
if module_name != "CompiledModule":
    ssa += "pub type CompiledModule = OtherModule;"
ssa += " }"
if query_minimal_target and query_fault == "legacy-missing-crate":
    source = source.replace("extern crate rustc_middle;", "extern crate fixture_absent_query_middle as rustc_middle;")
if mode not in ("missing-crate", "options-missing-session"):
    source = source.replace("extern crate rustc_session;", session)
if not (pointer_probe or terminator_probe or goto_probe or fn_args_probe):
    source = source.replace("extern crate rustc_middle;", middle)
if mode != "crate-type-missing-structures":
    source = source.replace("extern crate rustc_structures;", structures)
if mode != "hir-lang-item-missing-crate":
    source = source.replace("extern crate rustc_hir;", hir)
source = source.replace("extern crate rustc_attr_ir;", attr_ir)
source = source.replace("extern crate rustc_span;", span)
if mode != "module-missing-crate":
    source = source.replace("extern crate rustc_codegen_ssa;", ssa)
if pair_mode != "scalar-pair-missing-crate" and not (format_probe or pointer_probe or terminator_probe or goto_probe or fn_args_probe) and not (lanes_target and lanes_mode == "lanes-legacy-missing-crate"):
    source = source.replace("extern crate rustc_abi;", abi)
external_abi = format_probe or pointer_probe or terminator_probe or goto_probe or fn_args_probe
external_middle = pointer_probe or terminator_probe or goto_probe or fn_args_probe
if fn_args_target and fn_args_mode == "fn-args-legacy-missing-crate":
    source = source.replace("extern crate rustc_middle;", "extern crate fixture_absent_fn_middle as rustc_middle;")
    external_middle = False
if lanes_target and lanes_mode == "lanes-legacy-missing-crate":
    source = source.replace("extern crate rustc_abi;", "extern crate fixture_absent_lanes_abi as rustc_abi;")
if pointer_target and pointer_mode == "pointer-missing-crate":
    source = source.replace("extern crate rustc_middle;", "extern crate fixture_absent_pointer_middle as rustc_middle;")
    external_middle = False
if terminator_target and terminator_mode == "terminator-missing-crate":
    source = source.replace("extern crate rustc_middle;", "extern crate fixture_absent_terminator_middle as rustc_middle;")
    external_middle = False
if goto_target and goto_mode == "goto-legacy-missing-crate":
    source = source.replace("extern crate rustc_middle;", "extern crate fixture_absent_goto_middle as rustc_middle;")
    external_middle = False
if ((float_target and format_mode == "float-formats-missing-crate")
        or (register_target and format_mode == "register-kinds-missing-crate")):
    source = source.replace("extern crate rustc_abi;", "extern crate fixture_absent_abi_kinds as rustc_abi;")
    external_abi = False
external_target = "extern crate rustc_target;" in source and padding_mode not in (
    "cast-padding-missing-crate", "cast-padding-enum-qualified-message")
indirect_probe = indirect_target or retained_indirect_target
if indirect_probe and indirect_mode in ("indirect-missing-crate", "indirect-enum-qualified-message"):
    external_target = False
if padding_mode == "cast-padding-missing-crate":
    source = source.replace("extern crate rustc_target;", "extern crate fixture_absent_cast_target as rustc_target;")
elif indirect_probe and indirect_mode == "indirect-missing-crate":
    source = source.replace("extern crate rustc_target;", "extern crate fixture_absent_indirect_target as rustc_target;")
elif not external_target:
    source = source.replace("extern crate rustc_target;", callconv)
# Public extern control declarations must not leave a doubled visibility.
source = source.replace("pub pub mod", "pub mod")
if mode == "early-session-extra-error" and early_target:
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if mode == "early-session-unrelated-import" and early_target:
    source += "\nuse rustc_session::NoSuchItem;\n"
if mode == "early-session-denied-warning" and early_target:
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if mode == "extra-error" and target:
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if mode == "denied-warning" and target:
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if mode == "hir-lang-item-extra-error" and hir_target:
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if mode == "hir-lang-item-unrelated-import" and hir_target:
    source += "\nuse rustc_hir::NoSuchItem;\n"
if mode == "hir-lang-item-denied-warning" and hir_target:
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if mode == "memory-extra-error" and memory_target:
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if mode == "memory-unrelated-variant" and memory_target:
    source += "\npub fn unrelated_variant() -> LangItem { LangItem::NoSuchItem }\n"
if mode == "memory-denied-warning" and memory_target:
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if mode == "attributes-extra-error" and attributes_target:
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if mode == "attributes-unrelated-import" and attributes_target:
    source += "\nuse rustc_hir::NoSuchItem;\n"
if mode == "attributes-denied-warning" and attributes_target:
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if mode == "common-extra-error" and common_target:
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if mode == "common-unrelated-variant" and common_target:
    source += "\npub fn unrelated_variant() -> Linkage { Linkage::NoSuchItem }\n"
if mode == "common-denied-warning" and common_target:
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if mode == "module-cache-extra-error" and module_cache_target:
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if mode == "module-cache-denied-warning" and module_cache_target:
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if mode == "module-cache-unrelated-field" and module_cache_target:
    source = source.replace("module.links_from_incr_cache", "module.no_such_cache")
if ((mode == "crate-type-extra-error" and crate_type_target)
        or (mode == "sample-extra-error" and sample_profile_target)):
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if ((mode == "crate-type-denied-warning" and crate_type_target)
        or (mode == "sample-denied-warning" and sample_profile_target)):
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if mode == "sample-unrelated-field" and sample_profile_target:
    source = source.replace("opts.unstable_opts.profile_sample_use", "opts.unstable_opts.no_profile_field")
if pair_mode == "scalar-pair-extra-error" and scalar_pair_target:
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if pair_mode == "scalar-pair-denied-warning" and scalar_pair_target:
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if padding_mode == "cast-padding-extra-error" and cast_padding_target:
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if padding_mode == "cast-padding-denied-warning" and cast_padding_target:
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if indirect_mode == "indirect-extra-error" and indirect_target:
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if indirect_mode == "indirect-denied-warning" and indirect_target:
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if ((format_mode == "float-formats-legacy-extra-error" and float_target)
        or (format_mode == "register-kinds-legacy-extra-error" and register_target)):
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if ((format_mode == "float-formats-legacy-denied-warning" and float_target)
        or (format_mode == "register-kinds-legacy-denied-warning" and register_target)):
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if pointer_target and pointer_mode == "pointer-extra-error":
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if pointer_target and pointer_mode == "pointer-denied-warning":
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if goto_target and goto_mode == "goto-legacy-extra-error":
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if goto_target and goto_mode == "goto-legacy-denied-warning":
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if lanes_target and lanes_mode == "lanes-legacy-extra-error":
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if lanes_target and lanes_mode == "lanes-legacy-denied-warning":
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if fn_args_target and fn_args_mode == "fn-args-legacy-extra-error":
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if fn_args_target and fn_args_mode == "fn-args-legacy-denied-warning":
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if terminator_target and terminator_mode == "terminator-extra-error":
    source += "\npub fn unrelated_error() { missing_function(); }\n"
if terminator_target and terminator_mode == "terminator-denied-warning":
    source += "\n#[deprecated] pub fn old_api() {}\npub fn warning() { old_api(); }\n"
if query_minimal_target and query_fault == "legacy-extra-error":
    source += "\npub fn unrelated_query_error() { missing_function(); }\n"
if query_minimal_target and query_fault == "legacy-denied-warning":
    source += "\n#[deprecated] pub fn old_query_api() {}\npub fn query_warning() { old_query_api(); }\n"
translated = source_path.with_suffix(".ordinary.rs")
translated.write_text(source)
forwarded = [str(translated) if arg == str(source_path) else arg for arg in args
             if not arg.startswith("-Ztrust-verify=")]
try:
    forwarded = translate_probe_sysroot(forwarded, root, os.environ["PROBE_REAL_SYSROOT"])
except ValueError as error:
    print(f"error: {error}", file=sys.stderr)
    sys.exit(1)
# These ordinary-Rust stand-ins are explicitly not proof qualification. The
# fixture's original argv above still exposes the production policy ordering.
forwarded += ["-Ztrust-verify=off", "-Ztrust-policy=advisory"]
if external_abi:
    # Ordinary metadata models the real external enum's diagnostic spelling.
    # The complete source, command and artifact stay bound to this case.
    stub_source = root / "abi_kinds_standin.rs"
    stub_metadata = root / "librustc_abi_standin.rmeta"
    stub_receipt = root / "abi_kinds_standin.json"
    stub_command = list(forwarded)
    stub_command[stub_command.index(str(translated))] = str(stub_source)
    stub_command[stub_command.index("--crate-name") + 1] = "rustc_abi"
    stub_command[stub_command.index("-o") + 1] = str(stub_metadata)
    stub_command = [os.environ["PROBE_REAL_COMPILER"], *stub_command]
    stub_hash = hashlib.sha256(kind_abi.encode()).hexdigest()
    if stub_receipt.exists():
        retained = json.loads(stub_receipt.read_text())
        if (retained["source_sha256"] != stub_hash or retained["command"] != stub_command
                or not stub_source.is_file() or hashlib.sha256(stub_source.read_bytes()).hexdigest() != stub_hash
                or not stub_metadata.is_file()
                or hashlib.sha256(stub_metadata.read_bytes()).hexdigest() != retained["metadata_sha256"]):
            print("error: ordinary ABI-kind metadata cache does not match this process case", file=sys.stderr)
            sys.exit(1)
    else:
        stub_source.write_text(kind_abi)
        stub = subprocess.run(stub_command, capture_output=True, timeout=20)
        (root / "abi_kinds_standin.stdout").write_bytes(stub.stdout)
        (root / "abi_kinds_standin.stderr").write_bytes(stub.stderr)
        if stub.returncode or not stub_metadata.is_file():
            print("error: ordinary ABI-kind metadata dependency failed", file=sys.stderr)
            sys.exit(stub.returncode or 1)
        stub_receipt.write_text(json.dumps({"command": stub_command, "source_sha256": stub_hash,
                                           "metadata_sha256": hashlib.sha256(stub_metadata.read_bytes()).hexdigest(),
                                           "exit": 0, "scope": "ordinary-Rust type stand-in; no private-API/proof credit"}, indent=2) + "\n")
    forwarded += ["--extern", "rustc_abi=" + str(stub_metadata)]
if external_middle:
    # The external ordinary MIR stand-in retains the real missing-method
    # diagnostic spelling. Its ABI dependency, source and artifact are bound.
    stub_source = root / "pointer_middle_standin.rs"
    stub_metadata = root / "librustc_middle_standin.rmeta"
    stub_receipt = root / "pointer_middle_standin.json"
    stub_command = list(forwarded)
    stub_command[stub_command.index(str(translated))] = str(stub_source)
    stub_command[stub_command.index("--crate-name") + 1] = "rustc_middle"
    stub_command[stub_command.index("-o") + 1] = str(stub_metadata)
    stub_command += ["-Ldependency=" + str(root)]
    stub_command = [os.environ["PROBE_REAL_COMPILER"], *stub_command]
    stub_hash = hashlib.sha256(pointer_middle.encode()).hexdigest()
    dependency_hash = hashlib.sha256((root / "librustc_abi_standin.rmeta").read_bytes()).hexdigest()
    if stub_receipt.exists():
        retained = json.loads(stub_receipt.read_text())
        if (retained["source_sha256"] != stub_hash or retained["command"] != stub_command
                or retained["abi_metadata_sha256"] != dependency_hash
                or not stub_source.is_file() or hashlib.sha256(stub_source.read_bytes()).hexdigest() != stub_hash
                or not stub_metadata.is_file()
                or hashlib.sha256(stub_metadata.read_bytes()).hexdigest() != retained["metadata_sha256"]):
            print("error: ordinary pointer metadata cache does not match this process case", file=sys.stderr)
            sys.exit(1)
    else:
        stub_source.write_text(pointer_middle)
        stub = subprocess.run(stub_command, capture_output=True, timeout=20)
        (root / "pointer_middle_standin.stdout").write_bytes(stub.stdout)
        (root / "pointer_middle_standin.stderr").write_bytes(stub.stderr)
        if stub.returncode or not stub_metadata.is_file():
            print("error: ordinary pointer metadata dependency failed", file=sys.stderr)
            sys.exit(stub.returncode or 1)
        stub_receipt.write_text(json.dumps({"command": stub_command, "source_sha256": stub_hash,
                                           "abi_metadata_sha256": dependency_hash,
                                           "metadata_sha256": hashlib.sha256(stub_metadata.read_bytes()).hexdigest(),
                                           "exit": 0, "scope": "ordinary-Rust MIR/ABI stand-in; no private-API/proof credit"}, indent=2) + "\n")
    forwarded += ["--extern", "rustc_middle=" + str(stub_metadata), "-Ldependency=" + str(root)]
if external_target:
    # An external enum's E0026 names its variant, whereas an inline enum names
    # `PassMode::Variant`. Keep the real diagnostic boundary and model its crate
    # context with an ordinary-Rust metadata dependency. This is not a private
    # compiler crate or native/proof qualification.
    stub_source = root / "callconv_standin.rs"
    stub_metadata = root / "librustc_target_standin.rmeta"
    stub_receipt = root / "callconv_standin.json"
    stub_text = callconv.removeprefix("pub mod rustc_target { ").removesuffix(" }")
    stub_command = list(forwarded)
    stub_command[stub_command.index(str(translated))] = str(stub_source)
    stub_command[stub_command.index("--crate-name") + 1] = "rustc_target"
    stub_command[stub_command.index("-o") + 1] = str(stub_metadata)
    stub_command = [os.environ["PROBE_REAL_COMPILER"], *stub_command]
    stub_hash = hashlib.sha256(stub_text.encode()).hexdigest()
    if stub_receipt.exists():
        retained = json.loads(stub_receipt.read_text())
        if (retained["source_sha256"] != stub_hash or retained["command"] != stub_command
                or not stub_source.is_file() or hashlib.sha256(stub_source.read_bytes()).hexdigest() != stub_hash
                or not stub_metadata.is_file()
                or hashlib.sha256(stub_metadata.read_bytes()).hexdigest() != retained["metadata_sha256"]):
            print("error: ordinary call-convention metadata cache does not match this process case", file=sys.stderr)
            sys.exit(1)
    else:
        stub_source.write_text(stub_text)
        stub = subprocess.run(stub_command, capture_output=True, timeout=20)
        (root / "callconv_standin.stdout").write_bytes(stub.stdout)
        (root / "callconv_standin.stderr").write_bytes(stub.stderr)
        if stub.returncode or not stub_metadata.is_file():
            print("error: ordinary call-convention metadata dependency failed", file=sys.stderr)
            sys.exit(stub.returncode or 1)
        stub_receipt.write_text(json.dumps({"command": stub_command, "source_sha256": stub_hash,
                                           "metadata_sha256": hashlib.sha256(stub_metadata.read_bytes()).hexdigest(),
                                           "exit": 0, "scope": "ordinary-Rust type stand-in; no private-API/proof credit"}, indent=2) + "\n")
    forwarded += ["--extern", "rustc_target=" + str(stub_metadata)]
result = subprocess.run([os.environ["PROBE_REAL_COMPILER"], *forwarded],
                        capture_output=True, timeout=20)
if fn_args_probe or query_probe:
    (root / (name + ".ordinary.stderr")).write_bytes(result.stderr)
sys.stdout.buffer.write(result.stdout)
for line in result.stderr.decode("utf-8", errors="strict").splitlines(keepends=True):
    if line.startswith("{"):
        value = json.loads(line)
        if fn_args_target and (value.get("code") or {}).get("code") == "E0599":
            # The private compiler crate's diagnostic preserves its named
            # lifetime and qualified internal paths. This one exact ordinary
            # type has the same modeled shape but a shorter pretty spelling.
            # Translate only that spelling; retain original bytes above.
            ordinary = "no method named `no_bound_vars` found for reference `&RawList<(), GenericArg<'_>>` in the current scope"
            if value["message"] == ordinary:
                value["message"] = "no method named `no_bound_vars` found for reference `&'tcx ty::list::RawList<(), rustc_middle::ty::GenericArg<'tcx>>` in the current scope"
        def remap(node):
            if isinstance(node, dict):
                for key, child in node.items():
                    if key == "file_name" and child == str(translated):
                        wrong_span = (mode == "wrong-span" and target) or (
                            mode == "early-session-wrong-span" and early_target) or (
                            mode == "hir-lang-item-wrong-span" and hir_target) or (
                            mode == "memory-wrong-span" and memory_target) or (
                            mode == "attributes-wrong-span" and attributes_target) or (
                            mode == "common-wrong-span" and common_target) or (
                            mode == "module-cache-wrong-span" and module_cache_target) or (
                            mode == "crate-type-wrong-span" and crate_type_target) or (
                            mode == "sample-wrong-span" and sample_profile_target) or (
                            pair_mode == "scalar-pair-wrong-span" and scalar_pair_target) or (
                            padding_mode == "cast-padding-wrong-span" and cast_padding_target) or (
                            indirect_mode == "indirect-wrong-span" and indirect_target) or (
                            format_mode == "float-formats-legacy-wrong-span" and float_target) or (
                            format_mode == "register-kinds-legacy-wrong-span" and register_target) or (
                            pointer_mode == "pointer-wrong-span" and pointer_target) or (
                            terminator_mode == "terminator-wrong-span" and terminator_target) or (
                            goto_mode == "goto-legacy-wrong-span" and goto_target) or (
                            lanes_mode == "lanes-legacy-wrong-span" and lanes_target) or (
                            fn_args_mode == "fn-args-legacy-wrong-span" and fn_args_target)
                        node[key] = str(source_path) + (".foreign" if wrong_span else "")
                    else:
                        remap(child)
            elif isinstance(node, list):
                for child in node:
                    remap(child)
        remap(value)
        if ((mode == "early-session-wrong-token" and early_target)
                or (mode == "module-cache-wrong-token" and module_cache_target)
                or (mode == "crate-type-wrong-token" and crate_type_target)
                or (mode == "sample-wrong-token" and sample_profile_target)
                or (pair_mode == "scalar-pair-wrong-token" and scalar_pair_target)
                or (padding_mode == "cast-padding-wrong-token" and cast_padding_target)
                or (indirect_mode == "indirect-wrong-token" and indirect_target)
                or (format_mode == "float-formats-legacy-wrong-token" and float_target)
                or (format_mode == "register-kinds-legacy-wrong-token" and register_target)
                or (pointer_mode == "pointer-wrong-token" and pointer_target)
                or (terminator_mode == "terminator-wrong-token" and terminator_target)
                or (goto_mode == "goto-legacy-wrong-token" and goto_target)
                or (lanes_mode == "lanes-legacy-wrong-token" and lanes_target)
                or (fn_args_mode == "fn-args-legacy-wrong-token" and fn_args_target)):
            for span in value.get("spans", []):
                if span.get("is_primary"):
                    span["column_start"], span["column_end"] = 1, 2
                    for text in span.get("text", []):
                        text["highlight_start"], text["highlight_end"] = 1, 2
        if scalar_pair_target and (value.get("code") or {}).get("code") == "E0164":
            if pair_mode == "scalar-pair-wrong-message":
                value["message"] = "expected a different tuple variant"
            elif pair_mode == "scalar-pair-extra-primary":
                primary = next(span for span in value["spans"] if span.get("is_primary"))
                value["spans"].append(dict(primary))
        if early_target and (value.get("code") or {}).get("code") == "E0432":
            if mode == "early-session-wrong-code":
                value["code"]["code"] = "E0609"
            elif mode == "early-session-wrong-message":
                value["message"] = "unresolved import `rustc_session::OtherSession`"
            elif mode == "early-session-extra-primary":
                primary = next(span for span in value["spans"] if span.get("is_primary"))
                value["spans"].append(dict(primary))
        if cast_padding_target and (value.get("code") or {}).get("code") == "E0026":
            if padding_mode == "cast-padding-wrong-message":
                value["message"] = "variant `OtherCast` does not have a field named `pad_i32`"
            elif padding_mode == "cast-padding-wrong-code":
                value["code"]["code"] = "E0609"
            elif padding_mode == "cast-padding-extra-primary":
                primary = next(span for span in value["spans"] if span.get("is_primary"))
                value["spans"].append(dict(primary))
        if indirect_target and (value.get("code") or {}).get("code") == "E0026":
            if indirect_mode == "indirect-wrong-message":
                value["message"] = "variant `OtherIndirect` does not have a field named `on_stack`"
            elif indirect_mode == "indirect-wrong-code":
                value["code"]["code"] = "E0609"
            elif indirect_mode == "indirect-extra-primary":
                primary = next(span for span in value["spans"] if span.get("is_primary"))
                value["spans"].append(dict(primary))
        if (((float_target and format_mode.startswith("float-formats-"))
             or (register_target and format_mode.startswith("register-kinds-")))
                and (value.get("code") or {}).get("code") == "E0599"):
            if format_mode.endswith("legacy-wrong-message"):
                value["message"] = "unrelated missing variant"
            elif format_mode.endswith("legacy-wrong-code"):
                value["code"]["code"] = "E0609"
            elif format_mode.endswith("legacy-extra-primary"):
                primary = next(span for span in value["spans"] if span.get("is_primary"))
                value["spans"].append(dict(primary))
            elif format_mode.endswith("legacy-expanded-token"):
                for span in value["spans"]:
                    if span.get("is_primary"):
                        span["expansion"] = {"macro_decl_name": "unrelated_macro!"}
        if pointer_target and (value.get("code") or {}).get("code") == "E0599":
            if pointer_mode == "pointer-wrong-message":
                value["message"] = "no method named `unrelated` found"
            elif pointer_mode == "pointer-wrong-code":
                value["code"]["code"] = "E0609"
            elif pointer_mode == "pointer-extra-primary":
                primary = next(span for span in value["spans"] if span.get("is_primary"))
                value["spans"].append(dict(primary))
            elif pointer_mode == "pointer-expanded-token":
                for span in value["spans"]:
                    if span.get("is_primary"):
                        span["expansion"] = {"macro_decl_name": "unrelated_macro!"}
        if terminator_target and (value.get("code") or {}).get("code") == "E0609":
            if terminator_mode == "terminator-wrong-message":
                value["message"] = "no field `attributes` on type `OtherTerminator`"
            elif terminator_mode == "terminator-wrong-code":
                value["code"]["code"] = "E0599"
            elif terminator_mode == "terminator-extra-primary":
                primary = next(span for span in value["spans"] if span.get("is_primary"))
                value["spans"].append(dict(primary))
            elif terminator_mode == "terminator-expanded-token":
                for span in value["spans"]:
                    if span.get("is_primary"):
                        span["expansion"] = {"macro_decl_name": "unrelated_macro!"}
        if goto_target and (value.get("code") or {}).get("code") == "E0026":
            if goto_mode == "goto-legacy-wrong-message":
                value["message"] = "variant `OtherGoto` does not have a field named `loop_hint_attrs`"
            elif goto_mode == "goto-legacy-wrong-code":
                value["code"]["code"] = "E0609"
            elif goto_mode == "goto-legacy-extra-primary":
                primary = next(span for span in value["spans"] if span.get("is_primary"))
                value["spans"].append(dict(primary))
            elif goto_mode == "goto-legacy-expanded-token":
                for span in value["spans"]:
                    if span.get("is_primary"):
                        span["expansion"] = {"macro_decl_name": "unrelated_macro!"}
        if lanes_target and (value.get("code") or {}).get("code") == "E0599":
            if lanes_mode == "lanes-legacy-wrong-message":
                value["message"] = "no method named `as_u64` found for type `u32` in the current scope"
            elif lanes_mode == "lanes-legacy-wrong-code":
                value["code"]["code"] = "E0609"
            elif lanes_mode == "lanes-legacy-extra-primary":
                primary = next(span for span in value["spans"] if span.get("is_primary"))
                value["spans"].append(dict(primary))
            elif lanes_mode == "lanes-legacy-expanded-token":
                for span in value["spans"]:
                    if span.get("is_primary"):
                        span["expansion"] = {"macro_decl_name": "unrelated_macro!"}
        if fn_args_target and (value.get("code") or {}).get("code") == "E0599":
            if fn_args_mode == "fn-args-legacy-wrong-message":
                value["message"] = "no method named `no_bound_vars` found for type `u64` in the current scope"
            elif fn_args_mode == "fn-args-legacy-wrong-code":
                value["code"]["code"] = "E0609"
            elif fn_args_mode == "fn-args-legacy-extra-primary":
                primary = next(span for span in value["spans"] if span.get("is_primary"))
                value["spans"].append(dict(primary))
            elif fn_args_mode == "fn-args-legacy-expanded-token":
                for span in value["spans"]:
                    if span.get("is_primary"):
                        span["expansion"] = {"macro_decl_name": "unrelated_macro!"}
        if query_minimal_target and (value.get("code") or {}).get("code") == "E0599":
            if query_fault == "legacy-wrong-message":
                value["message"] = "unrelated query method is absent"
            elif query_fault == "legacy-wrong-code":
                value["code"]["code"] = "E0609"
            elif query_fault == "legacy-extra-primary":
                primary = next(span for span in value["spans"] if span.get("is_primary"))
                value["spans"].append(dict(primary))
            else:
                for span in value["spans"]:
                    if not span.get("is_primary"):
                        continue
                    if query_fault == "legacy-wrong-span":
                        span["file_name"] += ".foreign"
                    elif query_fault == "legacy-wrong-token":
                        span["column_end"] -= 1
                        span["text"][0]["highlight_end"] -= 1
                    elif query_fault == "legacy-expanded-token":
                        span["expansion"] = {"macro_decl_name": "unrelated_query_macro!"}
        if value.get("level") == "failure-note" and branded:
            value["message"] = value["message"].replace("`rustc --explain", "`trustc --explain")
            if note_mode == "note-wrong-code":
                value["message"] = value["message"].replace("E0432", "E0609")
            elif note_mode == "note-wrong-tool":
                value["message"] = value["message"].replace("trustc", "other-compiler")
            elif note_mode == "note-unrelated":
                value["message"] = "compiler verification refused"
            elif note_mode == "note-child":
                value["children"] = [{"level": "error", "message": "unrelated failure"}]
            if note_mode == "note-duplicate":
                sys.stderr.write(json.dumps(value) + "\n")
        sys.stderr.write(json.dumps(value) + "\n")
    else:
        sys.stderr.write(line)
sys.exit(result.returncode)
