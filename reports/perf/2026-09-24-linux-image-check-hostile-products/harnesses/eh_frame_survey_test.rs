    /// Survey (temporary, not committed): run the `.eh_frame` check over the
    /// ELF images listed one per line in `$TCG_EH_SURVEY_LIST` and write, per
    /// image, its FDE count, its wrapped-pointer count and its refusal tags
    /// to `$TCG_EH_SURVEY_OUT`.
    #[test]
    #[ignore = "host survey"]
    fn tmp_survey_wrap() {
        use std::io::Write as _;
        let list = std::fs::read_to_string(std::env::var("TCG_EH_SURVEY_LIST").unwrap()).unwrap();
        let mut out = std::fs::File::create(std::env::var("TCG_EH_SURVEY_OUT").unwrap()).unwrap();
        for path in list.lines().filter(|line| !line.is_empty()) {
            let Ok(bytes) = std::fs::read(path) else {
                continue;
            };
            let check = eh_frame_check(&bytes);
            let request = LinkRequest::executable(linux(), vec![], PathBuf::from(path));
            let diagnostics = eh_frame_diagnostics(&request, &Ok(bytes.into()));
            let tags: Vec<&str> = diagnostics
                .iter()
                .map(|d| {
                    if d.line.contains("hidden from an unwinder") { "OVERLAP" } else if d.line.contains("that begin together at") { "UNDECIDED" } else if d.line.contains("name the address their linker") {
                        "WRAP"
                    } else if d.line.contains("-UNPROVEN]") {
                        "UNPROVEN"
                    } else {
                        "WINDOW"
                    }
                })
                .collect();
            writeln!(
                out,
                "{path}\tfdes={}\twrapped={}\t{}\toverlapping={}\t{:?}",
                check.fdes,
                check.wrapped.len(),
                tags.join(","),
                check.overlapping.hidden.len() + check.overlapping.undecided.len(),
                (check.overlapping.hidden.first(), check.overlapping.undecided.first())
            )
            .unwrap();
        }
    }

