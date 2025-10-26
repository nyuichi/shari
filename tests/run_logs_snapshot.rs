use assert_cmd::Command;
use regex::Regex;
use std::sync::OnceLock;

#[test]
fn cargo_run_release_stderr_snapshot() {
    let mut cmd = Command::cargo_bin("shari").expect("binary exists");
    cmd.env("RUST_LOG", "info");
    cmd.env("RUST_LOG_STYLE", "never");

    let output = cmd.assert().success().get_output().clone();
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Normalize unstable timestamps and numeric suffixes so the snapshot only fails when structure changes.
    // TODO: change pretty printer to avoid this normalization.
    let without_timestamps = timestamp_re().replace_all(stderr.as_ref(), "<timestamp>");
    let normalized = digit_re().replace_all(without_timestamps.as_ref(), "<num>");

    insta::assert_snapshot!("cargo_run_release_stderr", normalized.as_ref());
}

fn timestamp_re() -> &'static Regex {
    static INSTANCE: OnceLock<Regex> = OnceLock::new();
    INSTANCE.get_or_init(|| {
        Regex::new(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?(?:Z|[+-]\d{2}:\d{2})")
            .expect("valid timestamp regex")
    })
}

fn digit_re() -> &'static Regex {
    static INSTANCE: OnceLock<Regex> = OnceLock::new();
    INSTANCE.get_or_init(|| Regex::new(r"\d+").expect("valid digit regex"))
}
