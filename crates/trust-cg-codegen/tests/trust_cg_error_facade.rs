use trust_cg_codegen::jit_contract::ArtifactContractError;
use trust_cg_codegen::macho::FixupError;
use trust_cg_codegen::macho::linker::LinkerError;
use trust_cg_codegen::{
    AsyncCompileService, AsyncCompileServiceConfig, AsyncCompileState, AsyncSubmitRejectCode,
    CodegenError, CompileError, CompileGeneration, CompileRequest, JitError, PipelineError,
    TrustCgError,
};

#[test]
fn public_reexport_is_the_facade_error_type() {
    fn assert_std_error<E: std::error::Error>() {}

    assert_std_error::<TrustCgError>();

    let err: TrustCgError =
        trust_cg_codegen::error::TrustCgError::from(JitError::UnresolvedSymbol("missing".into()));
    match err {
        TrustCgError::Jit(JitError::UnresolvedSymbol(symbol)) => {
            assert_eq!(symbol, "missing");
        }
        other => panic!("expected public TrustCgError::Jit, got {other:?}"),
    }
}

#[test]
fn typed_public_errors_convert_without_erasing_variants() {
    let err: TrustCgError =
        CodegenError::Pipeline(PipelineError::ISel("isel failed".into())).into();
    match err {
        TrustCgError::Codegen(CodegenError::Pipeline(PipelineError::ISel(message))) => {
            assert_eq!(message, "isel failed");
        }
        other => panic!("expected codegen pipeline error, got {other:?}"),
    }

    let err: TrustCgError = CompileError::EmptyModule.into();
    match err {
        TrustCgError::Compile(CompileError::EmptyModule) => {}
        other => panic!("expected compile error, got {other:?}"),
    }

    let err: TrustCgError = JitError::UnresolvedSymbol("callee".into()).into();
    match err {
        TrustCgError::Jit(JitError::UnresolvedSymbol(symbol)) => {
            assert_eq!(symbol, "callee");
        }
        other => panic!("expected JIT error, got {other:?}"),
    }

    let err: TrustCgError = PipelineError::RegAlloc("no register".into()).into();
    match err {
        TrustCgError::Pipeline(PipelineError::RegAlloc(message)) => {
            assert_eq!(message, "no register");
        }
        other => panic!("expected pipeline error, got {other:?}"),
    }

    let err: TrustCgError = FixupError::UnresolvedSymbol {
        name: "_extern".into(),
    }
    .into();
    match err {
        TrustCgError::MachOFixup(FixupError::UnresolvedSymbol { name }) => {
            assert_eq!(name, "_extern");
        }
        other => panic!("expected Mach-O fixup error, got {other:?}"),
    }

    let err: TrustCgError = LinkerError::UndefinedSymbol("_entry".into()).into();
    match err {
        TrustCgError::MachOLinker(LinkerError::UndefinedSymbol(symbol)) => {
            assert_eq!(symbol, "_entry");
        }
        other => panic!("expected Mach-O linker error, got {other:?}"),
    }

    let err: TrustCgError = ArtifactContractError::NullSymbolPointer {
        symbol: "entry".into(),
    }
    .into();
    match err {
        TrustCgError::ArtifactContract(ArtifactContractError::NullSymbolPointer { symbol }) => {
            assert_eq!(symbol, "entry");
        }
        other => panic!("expected artifact contract error, got {other:?}"),
    }
}

#[test]
fn typed_wrappers_expose_std_error_sources() {
    let err: TrustCgError = PipelineError::ISel("bad op".into()).into();
    let source = std::error::Error::source(&err).expect("pipeline source");

    assert_eq!(source.to_string(), "instruction selection failed: bad op");
}

#[test]
fn async_submit_rejection_converts_from_public_reject_data() {
    let mut service = AsyncCompileService::with_default_service(AsyncCompileServiceConfig {
        max_queued: 0,
        ..AsyncCompileServiceConfig::default()
    });
    let reject = service
        .submit(CompileRequest::new(
            "facade-async-reject",
            CompileGeneration::new(1),
        ))
        .expect_err("queue is configured full");

    let err: TrustCgError = reject.into();
    assert!(std::error::Error::source(&err).is_none());

    match err {
        TrustCgError::AsyncSubmitRejected {
            request_id,
            code,
            state,
        } => {
            assert_eq!(request_id.as_str(), "facade-async-reject");
            assert_eq!(code, AsyncSubmitRejectCode::QueueFull);
            assert_eq!(state, AsyncCompileState::Rejected);
        }
        other => panic!("expected async submit rejection, got {other:?}"),
    }
}
