use assert_cmd::Command;
use regex::Regex;

#[test]
fn cargo_run_release_stderr_snapshot() {
    let mut cmd = Command::cargo_bin("shari").expect("binary exists");
    cmd.env("RUST_LOG", "info");
    cmd.env("RUST_LOG_STYLE", "never");

    let output = cmd.assert().success().get_output().clone();
    let stderr = String::from_utf8_lossy(&output.stderr);

    // Normalize unstable numeric suffixes so the snapshot only fails when structure changes.
    let digit_re = Regex::new(r"\d+").expect("valid regex");
    let normalized = digit_re.replace_all(&stderr, "<num>");

    insta::assert_snapshot!("cargo_run_release_stderr", normalized);
}
