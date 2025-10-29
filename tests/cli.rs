use assert_cmd::Command;

fn version_output() -> String {
    format!("shari {}\n", env!("CARGO_PKG_VERSION"))
}

#[test]
fn version_flag_prints_package_version() {
    let expected = version_output();
    Command::cargo_bin("shari")
        .expect("binary exists")
        .arg("--version")
        .assert()
        .success()
        .stdout(expected.clone())
        .stderr("");

    Command::cargo_bin("shari")
        .expect("binary exists")
        .arg("-v")
        .assert()
        .success()
        .stdout(expected)
        .stderr("");
}

#[test]
fn help_flag_prints_usage() {
    let output = Command::cargo_bin("shari")
        .expect("binary exists")
        .arg("--help")
        .output()
        .expect("help output");

    assert!(output.status.success());

    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.starts_with("Usage:"), "stdout was: {stdout}");
    assert!(
        stdout.contains("-v, --version"),
        "stdout was missing version flag: {stdout}"
    );
    assert!(output.stderr.is_empty(), "stderr was not empty");
}

#[test]
fn running_with_file_reads_from_disk() {
    Command::cargo_bin("shari")
        .expect("binary exists")
        .arg("src/main.shari")
        .assert()
        .success()
        .stdout("")
        .stderr("");
}

#[test]
fn running_with_missing_file_returns_error() {
    let output = Command::cargo_bin("shari")
        .expect("binary exists")
        .arg("tests/does-not-exist.shari")
        .assert()
        .failure()
        .get_output()
        .clone();

    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("failed to read `tests/does-not-exist.shari`"),
        "stderr was: {stderr}"
    );
}
