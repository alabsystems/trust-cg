#![cfg(all(target_arch = "aarch64", target_os = "macos"))]

use std::{
    collections::HashMap,
    ffi::{c_int, c_void},
    process::Command,
    sync::atomic::{AtomicPtr, Ordering},
};

use serde_json::{Value, json};
use trust_cg_codegen::{
    ExecutableBuffer, JIT_CRASH_REPORT_SCHEMA, JitCompiler, JitConfig, JitCrashKind,
};
use trust_cg_ir::{AArch64Opcode, MachFunction, MachInst, Signature};

const CHILD_ENV: &str = "TRUST_CG_JIT_CRASH_REPLAY_CHILD";
const TEST_NAME: &str = "compiled_trap_artifact_derives_crash_json_from_signal_context";
const TRAP_RETURNED_EXIT: i32 = 77;
const SIGILL: c_int = 4;
const SIGTRAP: c_int = 5;
const SIGBUS: c_int = 10;
const SIGSEGV: c_int = 11;

static CRASH_BUFFER_PTR: AtomicPtr<ExecutableBuffer> = AtomicPtr::new(std::ptr::null_mut());

unsafe extern "C" {
    fn sigaction(signum: c_int, act: *const DarwinSigAction, oldact: *mut DarwinSigAction)
    -> c_int;
    fn write(fd: c_int, buf: *const u8, count: usize) -> isize;
    fn _exit(status: c_int) -> !;
}

#[repr(C)]
struct DarwinSigAction {
    sa_sigaction: usize,
    sa_mask: u32,
    sa_flags: c_int,
}

#[repr(C)]
struct DarwinStack {
    ss_sp: *mut c_void,
    ss_size: usize,
    ss_flags: c_int,
}

#[repr(C)]
struct DarwinUContext {
    uc_onstack: c_int,
    uc_sigmask: u32,
    uc_stack: DarwinStack,
    uc_link: *mut DarwinUContext,
    uc_mcsize: usize,
    uc_mcontext: *mut DarwinMContext64,
}

#[repr(C)]
struct DarwinMContext64 {
    __es: DarwinArmExceptionState64,
    __ss: DarwinArmThreadState64,
}

#[repr(C)]
struct DarwinArmExceptionState64 {
    __far: u64,
    __esr: u32,
    __exception: u32,
}

#[repr(C)]
struct DarwinArmThreadState64 {
    __x: [u64; 29],
    __opaque_fp: *mut c_void,
    __opaque_lr: *mut c_void,
    __opaque_sp: *mut c_void,
    __opaque_pc: *mut c_void,
    __cpsr: u32,
    __opaque_flags: u32,
}

fn trap_function() -> MachFunction {
    let mut func = MachFunction::new("trap_entry".to_string(), Signature::new(vec![], vec![]));
    let entry = func.entry;

    let trap = MachInst::new(AArch64Opcode::TrapDivZero, vec![]);
    let trap_id = func.push_inst(trap);
    func.append_inst(entry, trap_id);

    func
}

fn signal_name(signal: c_int) -> &'static str {
    match signal {
        SIGILL => "SIGILL",
        SIGTRAP => "SIGTRAP",
        SIGBUS => "SIGBUS",
        SIGSEGV => "SIGSEGV",
        _ => "UNKNOWN",
    }
}

unsafe fn signal_context_pc(context: *mut c_void) -> Option<u64> {
    let context = context.cast::<DarwinUContext>();
    if context.is_null() {
        return None;
    }
    let mcontext = unsafe { (*context).uc_mcontext };
    if mcontext.is_null() {
        return None;
    }
    Some(unsafe { (*mcontext).__ss.__opaque_pc as u64 })
}

extern "C" fn write_crash_json_and_exit(signal: c_int, _info: *mut c_void, context: *mut c_void) {
    let buffer = CRASH_BUFFER_PTR.load(Ordering::SeqCst);
    if !buffer.is_null() {
        let host_pc = unsafe { signal_context_pc(context) };
        let code_offset = host_pc.and_then(|pc| unsafe { (*buffer).code_offset_for_host_pc(pc) });
        let report = unsafe { &*buffer }
            .crash_report_metadata(JitCrashKind::NativeTrap, "execute", host_pc, code_offset)
            .with_signal(signal_name(signal))
            .with_message("BRK #1 trap replay")
            .to_pretty_json();
        unsafe {
            let _ = write(1, report.as_ptr(), report.len());
        }
    }
    unsafe { _exit(0) }
}

fn install_crash_json_signal_handlers(buffer: &ExecutableBuffer) {
    CRASH_BUFFER_PTR.store(std::ptr::from_ref(buffer).cast_mut(), Ordering::SeqCst);

    const SA_SIGINFO: c_int = 0x0040;
    let action = DarwinSigAction {
        sa_sigaction: write_crash_json_and_exit as *const () as usize,
        sa_mask: 0,
        sa_flags: SA_SIGINFO,
    };
    unsafe {
        let _ = sigaction(SIGILL, &action, std::ptr::null_mut());
        let _ = sigaction(SIGTRAP, &action, std::ptr::null_mut());
        let _ = sigaction(SIGBUS, &action, std::ptr::null_mut());
        let _ = sigaction(SIGSEGV, &action, std::ptr::null_mut());
    }
}

fn run_child() {
    let buffer = JitCompiler::new(JitConfig::default())
        .compile_raw(&[trap_function()], &HashMap::new())
        .expect("trap function should compile into executable memory");
    install_crash_json_signal_handlers(&buffer);

    let trap_entry = unsafe {
        buffer
            .get_fn_bound::<extern "C" fn()>("trap_entry")
            .expect("trap_entry symbol should be present")
    };
    (*trap_entry.as_ref())();
    std::process::exit(TRAP_RETURNED_EXIT);
}

fn extract_json(stdout: &[u8]) -> String {
    let stdout = String::from_utf8(stdout.to_vec()).expect("child output should be utf8");
    let start = stdout
        .find('{')
        .expect("child stdout should contain crash JSON start");
    let end = stdout
        .rfind('}')
        .expect("child stdout should contain crash JSON end")
        + 1;
    let mut json = stdout[start..end].to_owned();
    json.push('\n');
    json
}

#[test]
fn compiled_trap_artifact_derives_crash_json_from_signal_context() {
    if std::env::var_os(CHILD_ENV).is_some() {
        run_child();
        return;
    }

    let current_exe = std::env::current_exe().expect("current test binary");
    let output = Command::new(current_exe)
        .arg(TEST_NAME)
        .arg("--exact")
        .arg("--nocapture")
        .env(CHILD_ENV, "1")
        .output()
        .expect("run crash replay child");

    assert!(
        output.status.success(),
        "crash replay child should write JSON; status={:?}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let stdout = extract_json(&output.stdout);
    let parsed: Value = serde_json::from_str(&stdout).expect("child output should parse as JSON");
    assert_eq!(parsed["schema"], JIT_CRASH_REPORT_SCHEMA);
    assert_eq!(parsed["kind"], "native_trap");
    assert_eq!(parsed["status"], "native_trap");
    assert_eq!(parsed["component"], "jit-runtime");
    assert_eq!(parsed["stage"], "execute");
    assert_eq!(parsed["message"], "BRK #1 trap replay");
    assert!(
        parsed["signal"]
            .as_str()
            .is_some_and(|signal| matches!(signal, "SIGILL" | "SIGTRAP" | "SIGBUS" | "SIGSEGV")),
        "signal should come from the delivered crash context"
    );
    let host_pc = parsed["location"]["host_pc"]
        .as_u64()
        .expect("signal context should provide host pc");
    let code_offset = parsed["location"]["code_offset"]
        .as_u64()
        .expect("handler should derive code offset from live JIT mapping");
    assert_ne!(host_pc, 0);
    assert_eq!(code_offset % 4, 0);
    assert_eq!(parsed["location"]["symbol"], "trap_entry");
    assert_eq!(parsed["location"]["symbol_offset"], code_offset);
    assert_eq!(parsed["location"]["diagnostics"], json!([]));
    assert_eq!(parsed["replay_metadata"]["entry_symbol"], "trap_entry");
    assert_eq!(
        parsed["replay_metadata"]["statuses"][0]["kind"],
        "native_trap"
    );
    assert_eq!(
        parsed["replay_metadata"]["statuses"][0]["pc_offset"],
        code_offset
    );
    assert_eq!(
        parsed["replay_metadata"]["statuses"][0]["symbol"],
        "trap_entry"
    );

    let native_sha = parsed["replay_metadata"]["properties"]["native_payload_sha256"]
        .as_str()
        .expect("native payload sha should be present");
    assert!(
        native_sha.starts_with("sha256:") && native_sha.len() == "sha256:".len() + 64,
        "native payload sha should be a tagged sha256 digest, got {native_sha}"
    );

    let properties = &parsed["replay_metadata"]["properties"];
    assert!(
        properties["artifact_manifest_checksum"]
            .as_str()
            .is_some_and(|value| value.starts_with("trust-cg-stable128:")),
        "live replay metadata should carry an artifact manifest checksum"
    );
    assert!(
        properties["source_fingerprint"]
            .as_str()
            .is_some_and(|value| value.starts_with("sha256:")),
        "live replay metadata should carry source identity"
    );
    assert_eq!(properties["source_identity_kind"], "jit_live_symbol_layout");
    assert!(
        parsed["replay_metadata"]["artifact_id"]
            .as_str()
            .is_some_and(|value| value.starts_with("trust-cg-jit-live:sha256:")),
        "live replay metadata should carry an artifact id"
    );
}

#[test]
fn executable_buffer_crash_metadata_reports_unresolved_code_offset() {
    let buffer = JitCompiler::new(JitConfig::default())
        .compile_raw(&[trap_function()], &HashMap::new())
        .expect("trap function should compile into executable memory");
    let report = buffer
        .crash_report_metadata(
            JitCrashKind::HostSignal,
            "execute",
            Some(0x1000_0040),
            Some(64),
        )
        .with_signal("SIGSEGV")
        .to_json_value();

    assert_eq!(report["kind"], "host_signal");
    assert_eq!(report["status"], "host_signal");
    assert_eq!(report["signal"], "SIGSEGV");
    assert_eq!(report["location"]["host_pc"], 0x1000_0040_u64);
    assert_eq!(report["location"]["code_offset"], 64);
    assert_eq!(report["location"]["symbol"], Value::Null);
    assert_eq!(
        report["location"]["diagnostics"],
        json!(["missing_symbol_for_code_offset"])
    );
    assert_eq!(
        report["replay_metadata"]["statuses"][0]["kind"],
        "host_signal"
    );
    assert_eq!(report["replay_metadata"]["statuses"][0]["pc_offset"], 64);
    assert_eq!(
        report["replay_metadata"]["statuses"][0]["symbol"],
        Value::Null
    );
}

#[test]
fn executable_buffer_crash_metadata_reports_missing_code_offset() {
    let buffer = JitCompiler::new(JitConfig::default())
        .compile_raw(&[trap_function()], &HashMap::new())
        .expect("trap function should compile into executable memory");
    let report = buffer
        .crash_report_metadata(JitCrashKind::HostSignal, "execute", Some(0x1000_0040), None)
        .with_signal("SIGSEGV")
        .to_json_value();

    assert_eq!(report["kind"], "host_signal");
    assert_eq!(report["status"], "host_signal");
    assert_eq!(report["signal"], "SIGSEGV");
    assert_eq!(report["location"]["host_pc"], 0x1000_0040_u64);
    assert_eq!(report["location"]["code_offset"], Value::Null);
    assert_eq!(report["location"]["symbol"], Value::Null);
    assert_eq!(
        report["location"]["diagnostics"],
        json!(["missing_code_offset"])
    );
    assert_eq!(
        report["replay_metadata"]["statuses"][0]["kind"],
        "host_signal"
    );
    assert_eq!(
        report["replay_metadata"]["statuses"][0]["pc_offset"],
        Value::Null
    );
    assert_eq!(
        report["replay_metadata"]["statuses"][0]["symbol"],
        Value::Null
    );
}
