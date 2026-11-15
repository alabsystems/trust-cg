//! Objects emitted by a fixture's `--emit=obj -o <output>` invocation.

use std::io;
use std::path::{Path, PathBuf};

/// Collect regular CGU `.o` files and the exact requested output, which can
/// have any suffix. The caller supplies a private output directory and keeps
/// responsibility for symbol reachability and linkage checks.
///
/// Sorting and deduplication keep link order stable when the requested output
/// itself ends in `.o`. Directory errors must fail the fixture, not silently
/// drop objects from its evidence.
pub fn emitted_objects(output: &Path) -> io::Result<Vec<PathBuf>> {
    let name = output.file_name().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidInput,
            "object output needs a file name",
        )
    })?;
    let dir = output
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let requested = dir.join(name);
    let mut objects = Vec::new();
    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.extension().is_some_and(|suffix| suffix == "o") && entry.file_type()?.is_file() {
            objects.push(path);
        }
    }
    match std::fs::symlink_metadata(&requested) {
        Ok(metadata) if metadata.is_file() => objects.push(requested),
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }
    objects.sort();
    objects.dedup();
    Ok(objects)
}
