use std::{
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    sync::Arc,
};

fn format_error(err: &anyhow::Error) -> String {
    let mut lines = vec!["error chain:".to_string()];
    for cause in err.chain() {
        lines.push(format!("  - {cause}"));
    }
    lines.join("\n")
}

fn fixtures() -> Vec<PathBuf> {
    let dir = Path::new("tests/proof_successes");
    let entries = match fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(err) => panic!("failed to read {dir:?}: {err}"),
    };
    let mut files: Vec<PathBuf> = entries
        .filter_map(|entry| {
            entry.ok().and_then(|entry| {
                let path = entry.path();
                if path.extension() == Some(OsStr::new("shari")) {
                    Some(path)
                } else {
                    None
                }
            })
        })
        .collect();
    files.sort();
    files
}

#[test]
fn proof_success_snapshots() {
    let files = fixtures();
    assert!(
        !files.is_empty(),
        "no .shari fixtures found in tests/proof_successes"
    );
    for path in files {
        let input = fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
        let snapshot_name = path
            .file_stem()
            .expect("fixture without file_stem")
            .to_string_lossy()
            .replace('.', "_");
        let file = Arc::new(shari::File::new(path.display().to_string(), input));
        if let Err(err) = shari::process(file) {
            panic!(
                "expected {} to succeed\n{}",
                path.display(),
                format_error(&err)
            );
        }
        let formatted = format!("ok\nfixture: {}", path.display());
        insta::assert_snapshot!(snapshot_name, formatted);
    }
}
