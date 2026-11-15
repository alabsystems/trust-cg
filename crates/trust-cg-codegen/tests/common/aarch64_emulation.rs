// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
//! Explicit Linux AArch64 test execution. Emulation never receives native credit.

use std::ffi::OsString;
use std::fs::File;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::process::Command;

pub const EMULATOR_ENV: &str = "TCG_TEST_AARCH64_EMULATOR";
pub const CPU_ENV: &str = "TCG_TEST_AARCH64_CPU";

#[derive(Debug)]
pub struct Emulation {
    emulator: PathBuf,
    cpu: String,
}

impl Emulation {
    pub fn new(emulator: &Path, cpu: &str) -> io::Result<Self> {
        if !emulator.is_absolute() || !matches!(cpu, "max" | "cortex-a53") {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "AArch64 emulation needs an absolute emulator and exact max/cortex-a53 CPU",
            ));
        }
        if !emulator.symlink_metadata()?.file_type().is_file() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "the recorded AArch64 emulator must be a regular file",
            ));
        }
        Ok(Self {
            emulator: emulator.to_owned(),
            cpu: cpu.to_owned(),
        })
    }

    pub fn from_values(
        emulator: Option<OsString>,
        cpu: Option<OsString>,
    ) -> io::Result<Option<Self>> {
        match (emulator, cpu) {
            (None, None) => Ok(None),
            (Some(emulator), Some(cpu)) => {
                let cpu = cpu.to_str().ok_or_else(|| {
                    io::Error::new(io::ErrorKind::InvalidInput, "non-UTF8 AArch64 CPU")
                })?;
                Self::new(Path::new(&emulator), cpu).map(Some)
            }
            _ => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "both AArch64 test execution controls must be supplied together",
            )),
        }
    }

    pub fn command(&self, program: &Path) -> io::Result<Command> {
        if !program.is_absolute() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "an emulated test executable must have an absolute path",
            ));
        }
        // Fail closed for scripts, other architectures and unsupported object
        // formats. A configured emulator must never fall back to native exec.
        let mut header = [0_u8; 20];
        File::open(program)?.read_exact(&mut header)?;
        if &header[..4] != b"\x7fELF"
            || header[4] != 2
            || header[5] != 1
            || u16::from_le_bytes([header[18], header[19]]) != 183
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "AArch64 emulation requires a little-endian ELF64 AArch64 executable",
            ));
        }
        let mut command = Command::new(&self.emulator);
        command.args(["-cpu", &self.cpu]).arg(program);
        Ok(command)
    }
}

pub fn configured_command(program: &Path) -> io::Result<Option<Command>> {
    Emulation::from_values(std::env::var_os(EMULATOR_ENV), std::env::var_os(CPU_ENV))?
        .map(|emulation| emulation.command(program))
        .transpose()
}
