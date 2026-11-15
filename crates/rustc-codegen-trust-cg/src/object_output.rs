//! Publish requested object bytes from the objects the backend actually emitted.
//!
//! Module names need not equal their sanitized temporary filenames. Publication
//! reads recorded paths, preserves live link inputs and does not reclassify any
//! code-generation or certificate verdict.

use std::collections::HashSet;
use std::fs::{self, File};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::Command;

use rustc_codegen_ssa::CompiledModules;
use rustc_codegen_ssa::back::link::linker_and_flavor;
use rustc_session::Session;
use rustc_session::config::{OutFileName, OutputFilenames, OutputType};
use rustc_target::spec::{Cc, LinkerFlavor, Lld};
use tempfile::{Builder, NamedTempFile};

pub(super) fn publish(
    sess: &Session,
    modules: &mut CompiledModules,
    outputs: &OutputFilenames,
) -> Result<(), String> {
    if !outputs.outputs.contains_key(&OutputType::Object) {
        return Ok(());
    }
    let objects: Vec<_> = modules
        .modules
        .iter()
        .flat_map(|module| [&module.object, &module.global_asm_object])
        .flatten()
        .cloned()
        .collect();
    let output = outputs.path(OutputType::Object);
    let object = objects.first().map_or(output.as_path(), PathBuf::as_path);
    if output.is_tty() {
        return Err("rustc_codegen_trust_cg: cannot publish a binary object to a terminal".into());
    }
    let published = if objects.is_empty() {
        // Only a genuinely empty compilation may synthesize empty bytes. A
        // carrier that lost an expected object must still fail publication.
        if !modules.modules.is_empty() || modules.allocator_module.is_some() {
            return Err(failure(
                object,
                "compiled modules contain no regular object",
            ));
        }
        empty(sess, outputs).map_err(|error| failure(object, error))?
    } else if objects.len() == 1 {
        snapshot(object, false).map_err(|error| failure(object, error))?
    } else {
        compose(sess, &objects)?
    };

    // The requested filename may name an input directly, through a symlink or
    // through a hard link. Preserve link inputs before writing through any of
    // those aliases; rustc's later link cleanup owns these private copies.
    let link_inputs = if outputs.outputs.should_link() {
        preserve_link_inputs(modules, outputs).map_err(|error| failure(object, error))?
    } else {
        Vec::new()
    };
    match &output {
        OutFileName::Real(path) => {
            fs::copy(published.path(), path).map_err(|error| failure(path, error))?;
        }
        OutFileName::Stdout => {
            let mut source =
                File::open(published.path()).map_err(|error| failure(published.path(), error))?;
            let mut stdout = io::stdout().lock();
            io::copy(&mut source, &mut stdout)
                .and_then(|_| stdout.flush())
                .map_err(|error| failure(output.as_path(), error))?;
        }
    }
    for input in link_inputs {
        input.keep();
    }
    if !sess.opts.cg.save_temps {
        for path in &objects {
            if !output_alias(path, &output) {
                fs::remove_file(path).map_err(|error| failure(path, error))?;
            }
        }
    }
    published.close().map_err(|error| failure(object, error))?;
    if sess.opts.json_artifact_notifications {
        sess.dcx()
            .emit_artifact_notification(output.as_path(), OutputType::Object.shorthand());
    }
    Ok(())
}

/// No instructions, data definitions or input objects exist in this case.
/// Use the existing target writer, then the same output delivery and cleanup
/// as a nonempty object. This does not compose or certify instruction bytes.
fn empty(sess: &Session, outputs: &OutputFilenames) -> Result<NamedTempFile, String> {
    use trust_cg_codegen::elf::{ElfMachine, ElfWriter};

    let bytes = match (
        sess.target.arch.desc(),
        sess.target.os.desc(),
        sess.target.pointer_width,
    ) {
        ("aarch64" | "x86_64", "linux", 64) if sess.target.endian == rustc_abi::Endian::Little => {
            let machine = if sess.target.arch.desc() == "aarch64" {
                ElfMachine::AArch64
            } else {
                ElfMachine::X86_64
            };
            let mut writer = ElfWriter::new(machine);
            writer.add_text_section(&[]);
            writer.add_note_gnu_stack();
            writer.write_checked().map_err(|error| error.to_string())?
        }
        ("wasm32", "unknown", 32) => {
            trust_cg_codegen::wasm::encode::WasmModule::new_object().finish()
        }
        _ => {
            return Err(format!(
                "empty object publication is not implemented for target {}",
                sess.target.llvm_target
            ));
        }
    };
    validate_composed_object(sess, &bytes)?;
    if sess.target.arch.desc() == "wasm32" {
        trust_cg_verify::wasm_internal_abi::check_object(&bytes)?;
    }
    let path = outputs.temp_path_for_cgu(OutputType::Object, "empty");
    let directory = path
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let mut staged = Builder::new()
        .prefix(".trust-cg-output-")
        .suffix(".tmp")
        .tempfile_in(directory)
        .map_err(|error| error.to_string())?;
    staged
        .write_all(&bytes)
        .and_then(|_| staged.flush())
        .map_err(|error| error.to_string())?;
    Ok(staged)
}

fn snapshot(path: &Path, link_input: bool) -> io::Result<NamedTempFile> {
    let directory = path
        .parent()
        .filter(|path| !path.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let suffix = if link_input { ".rcgu.o" } else { ".tmp" };
    let mut copy = Builder::new()
        .prefix(".trust-cg-output-")
        .suffix(suffix)
        .tempfile_in(directory)?;
    let mut source = File::open(path)?;
    io::copy(&mut source, copy.as_file_mut())?;
    copy.as_file_mut().flush()?;
    copy.as_file()
        .set_permissions(source.metadata()?.permissions())?;
    Ok(copy)
}

/// A partial link changes relocation sites and object layout. Per-input proof
/// bindings do not authorize those new bytes. Only explicitly unchecked
/// compilation may use the system linker as a trusted composition step.
fn compose(sess: &Session, objects: &[PathBuf]) -> Result<NamedTempFile, String> {
    if !crate::knobs::is_enabled(crate::knobs::NO_PROOF_CERTS) {
        return Err(
            "[TCG-OBJECT-COMPOSITION-PROOF] rustc_codegen_trust_cg: cannot compose multiple \
             objects while proof certificates are required; combined-byte proof binding \
             is not implemented"
                .into(),
        );
    }
    let (linker, flavor) = linker_and_flavor(sess);
    let mut command = Command::new(&linker);
    match flavor {
        LinkerFlavor::Gnu(Cc::Yes, lld) => {
            command.args(["-r", "-nostdlib", "-no-pie"]);
            if lld == Lld::Yes {
                command.arg("-fuse-ld=lld");
            }
        }
        LinkerFlavor::Darwin(Cc::Yes, lld) => {
            command.args(["-r", "-nostdlib"]);
            if lld == Lld::Yes {
                command.arg("-fuse-ld=lld");
            }
        }
        LinkerFlavor::WasmLld(Cc::Yes) => {
            command.args(["-r", "-nostdlib"]);
            command.arg(format!("--target={}", sess.target.llvm_target));
        }
        LinkerFlavor::Gnu(Cc::No, lld) | LinkerFlavor::Darwin(Cc::No, lld) => {
            if lld == Lld::Yes {
                command.args(["-flavor", flavor.lld_flavor().desc()]);
            }
            command.arg("-r");
        }
        LinkerFlavor::WasmLld(Cc::No) => {
            command.args(["-flavor", flavor.lld_flavor().desc(), "-r"]);
        }
        _ => {
            return Err(format!(
                "[TCG-OBJECT-COMPOSITION-LINKER] rustc_codegen_trust_cg: unsupported \
                 partial-linker flavor {flavor:?} for requested object publication"
            ));
        }
    }
    // Use the same tool search roots as rustc's linker, and pass each path as
    // one argument. Absolute inputs cannot be mistaken for linker switches.
    let mut search = sess.get_tools_search_paths(false);
    if let Some(path) = std::env::var_os("PATH") {
        search.extend(std::env::split_paths(&path));
    }
    command.env(
        "PATH",
        std::env::join_paths(search).map_err(|error| failure(&linker, error))?,
    );
    command.env("LC_ALL", "C");
    for object in objects {
        command.arg(fs::canonicalize(object).map_err(|error| failure(object, error))?);
    }
    let directory = objects[0].parent().unwrap_or(Path::new("."));
    let combined = Builder::new()
        .prefix(".trust-cg-output-")
        .suffix(".tmp")
        .tempfile_in(directory)
        .map_err(|error| failure(objects[0].as_path(), error))?;
    command.arg("-o").arg(combined.path());
    let result = command.output().map_err(|error| failure(&linker, error))?;
    if !result.status.success() {
        return Err(failure(
            &linker,
            format!(
                "partial link failed ({}): {}",
                result.status,
                String::from_utf8_lossy(&result.stderr)
            ),
        ));
    }
    let bytes = fs::read(combined.path()).map_err(|error| failure(combined.path(), error))?;
    validate_composed_object(sess, &bytes).map_err(|error| failure(combined.path(), error))?;
    Ok(combined)
}

/// Check framing, target architecture and relocatable kind. The linker and
/// these existing readers remain trusted; this is not a composition proof.
fn validate_composed_object(sess: &Session, bytes: &[u8]) -> Result<(), String> {
    if sess.target.arch.desc() == "wasm32" {
        let object = trust_cg_verify::wasm_internal_abi::decode_object(bytes)?;
        return object
            .linking
            .then_some(())
            .ok_or_else(|| "partial linker did not produce a relocatable Wasm object".into());
    }
    if sess.target.is_like_darwin {
        let object = trust_cg_codegen::macho::reparse::read_object_records(bytes)
            .map_err(|error| error.to_string())?;
        let expected = match sess.target.arch.desc() {
            "aarch64" => 0x0100_000c,
            "x86_64" => 0x0100_0007,
            arch => return Err(format!("unsupported Mach-O object architecture {arch}")),
        };
        if object.cputype != expected || bytes.get(12..16) != Some(&1u32.to_le_bytes()) {
            return Err("partial linker produced the wrong Mach-O object kind or CPU".into());
        }
    } else {
        let object = trust_cg_codegen::elf::reparse::read_object_records(bytes)
            .map_err(|error| error.to_string())?;
        let expected = match sess.target.arch.desc() {
            "aarch64" => 183,
            "x86_64" => 62,
            arch => return Err(format!("unsupported ELF object architecture {arch}")),
        };
        if object.machine != expected {
            return Err("partial linker produced an ELF object for the wrong CPU".into());
        }
    }
    Ok(())
}

struct LinkInput {
    path: PathBuf,
    keep: bool,
}

impl LinkInput {
    fn keep(mut self) {
        self.keep = true;
    }
}

impl Drop for LinkInput {
    fn drop(&mut self) {
        if !self.keep {
            let _ = fs::remove_file(&self.path);
        }
    }
}

fn preserve_link_inputs(
    modules: &mut CompiledModules,
    outputs: &OutputFilenames,
) -> io::Result<Vec<LinkInput>> {
    let sources: HashSet<_> = modules
        .modules
        .iter()
        .chain(modules.allocator_module.iter())
        .flat_map(|module| {
            [
                &module.object,
                &module.global_asm_object,
                &module.dwarf_object,
            ]
        })
        .flatten()
        .map(fs::canonicalize)
        .collect::<io::Result<_>>()?;
    let mut copies = Vec::new();
    for module in modules
        .modules
        .iter_mut()
        .chain(modules.allocator_module.iter_mut())
    {
        for path in [
            &mut module.object,
            &mut module.global_asm_object,
            &mut module.dwarf_object,
        ]
        .into_iter()
        .flatten()
        {
            loop {
                // Archive member names are observable: preserve their deterministic
                // order instead of serializing NamedTempFile's random name.
                let candidate = super::temp_object_path_in(
                    outputs,
                    &format!("trustcg.link-input.{}", copies.len()),
                );
                let requested = || {
                    outputs.outputs.keys().any(|kind| {
                        let output = outputs.path(*kind);
                        candidate == output.as_path() || output_alias(&candidate, &output)
                    })
                };
                if requested()
                    || fs::canonicalize(&candidate)
                        .ok()
                        .is_some_and(|path| sources.contains(&path))
                {
                    continue;
                }
                let copy = snapshot(path, true)?;
                copy.persist(&candidate).map_err(|error| error.error)?;
                let guarded = LinkInput {
                    path: candidate.clone(),
                    keep: false,
                };
                // A previously dangling requested symlink can resolve only after
                // this file exists. Never hand that alias back as a link input.
                if requested() {
                    continue;
                }
                *path = candidate;
                copies.push(guarded);
                break;
            }
        }
    }
    Ok(copies)
}

fn output_alias(path: &Path, output: &OutFileName) -> bool {
    let OutFileName::Real(output) = output else {
        return false;
    };
    fs::canonicalize(path)
        .ok()
        .zip(fs::canonicalize(output).ok())
        .is_some_and(|(left, right)| left == right)
}

fn failure(path: &Path, error: impl std::fmt::Display) -> String {
    format!(
        "rustc_codegen_trust_cg: object output publication failed for {}: {error}",
        path.display()
    )
}
