use std::{
    fs,
    path::{Path, PathBuf},
};

const REQUIRED_DESIGN_HEADINGS: [&str; 5] = [
    "## Status",
    "## Summary",
    "## Decision",
    "## Impact",
    "## Update Triggers",
];

#[test]
fn agents_md_stays_a_short_entrypoint() {
    let agents = read("AGENTS.md");
    let line_count = agents.lines().count();
    assert!(
        line_count <= 80,
        "AGENTS.md should stay a short entrypoint, found {line_count} lines"
    );
    assert!(
        agents.contains("docs/README.md"),
        "AGENTS.md should point readers to docs/README.md"
    );
}

#[test]
fn docs_index_lists_operations_and_design_docs() {
    let index = read("docs/README.md");
    for path in operation_docs() {
        assert!(
            index.contains(path.to_str().expect("utf-8 path")),
            "docs/README.md should list {}",
            path.display()
        );
    }
    for path in design_docs() {
        assert!(
            index.contains(path.to_str().expect("utf-8 path")),
            "docs/README.md should list {}",
            path.display()
        );
    }
}

#[test]
fn operations_docs_exist() {
    for path in operation_docs() {
        assert!(path.exists(), "missing operations doc: {}", path.display());
    }
}

#[test]
fn design_docs_follow_the_template() {
    let docs = design_docs();
    assert!(!docs.is_empty(), "expected docs/design-docs/*.md");

    for path in docs {
        let text = read(&path);
        for heading in REQUIRED_DESIGN_HEADINGS {
            assert!(
                text.contains(heading),
                "{} is missing required heading `{heading}`",
                path.display()
            );
        }

        let status = section_value(&text, "## Status")
            .unwrap_or_else(|| panic!("{} is missing a status value", path.display()));
        assert!(
            matches!(status, "draft" | "proposed" | "implemented" | "superseded"),
            "{} has unsupported status `{status}`",
            path.display()
        );
        if status == "superseded" {
            assert!(
                text.contains("Replacement:"),
                "{} must link a replacement when status is superseded",
                path.display()
            );
        }
    }
}

#[test]
fn docs_do_not_contain_environment_specific_paths() {
    for path in markdown_docs() {
        let text = read(&path);
        assert!(
            !text.contains("/Users/"),
            "{} contains an environment-specific absolute path",
            path.display()
        );
        assert!(
            !text.contains("/worktrees/"),
            "{} contains an environment-specific worktree path",
            path.display()
        );
    }
}

#[test]
fn docs_internal_links_resolve() {
    for path in markdown_docs() {
        let text = read(&path);
        for target in markdown_links(&text) {
            if target.starts_with("http://")
                || target.starts_with("https://")
                || target.starts_with('#')
                || target.starts_with("mailto:")
            {
                continue;
            }

            // Strip any `#fragment` or `?query` suffix before resolving the
            // filesystem path — both are valid in markdown links but have no
            // meaning on disk.
            let path_part = target.find(['#', '?']).map_or(target, |i| &target[..i]);

            // If stripping left us with an empty string the link points only
            // to a fragment within the current file; nothing to check on disk.
            if path_part.is_empty() {
                continue;
            }

            let resolved = path
                .parent()
                .expect("parent directory")
                .join(path_part)
                .components()
                .collect::<PathBuf>();
            assert!(
                resolved.exists(),
                "{} links to missing path {}",
                path.display(),
                resolved.display()
            );
        }
    }
}

fn operation_docs() -> Vec<PathBuf> {
    vec![
        PathBuf::from("docs/operations/agent-docs-policy.md"),
        PathBuf::from("docs/operations/change-playbook.md"),
    ]
}

fn design_docs() -> Vec<PathBuf> {
    let dir = Path::new("docs/design-docs");
    let entries =
        fs::read_dir(dir).unwrap_or_else(|err| panic!("failed to read {}: {err}", dir.display()));
    let mut docs: Vec<PathBuf> = entries
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "md"))
        .collect();
    docs.sort();
    docs
}

fn markdown_docs() -> Vec<PathBuf> {
    let mut docs = vec![PathBuf::from("AGENTS.md")];
    docs.extend(walk_markdown_files(Path::new("docs")));
    docs.sort();
    docs
}

fn walk_markdown_files(dir: &Path) -> Vec<PathBuf> {
    let entries =
        fs::read_dir(dir).unwrap_or_else(|err| panic!("failed to read {}: {err}", dir.display()));
    let mut files = Vec::new();

    for entry in entries.filter_map(Result::ok) {
        let path = entry.path();
        if path.is_dir() {
            files.extend(walk_markdown_files(&path));
        } else if path.extension().is_some_and(|ext| ext == "md") {
            files.push(path);
        }
    }

    files
}

fn markdown_links(text: &str) -> Vec<&str> {
    let mut links = Vec::new();
    let mut rest = text;

    while let Some(start) = rest.find("](") {
        let tail = &rest[start + 2..];
        let Some(end) = tail.find(')') else {
            break;
        };
        links.push(&tail[..end]);
        rest = &tail[end + 1..];
    }

    links
}

fn section_value<'a>(text: &'a str, heading: &str) -> Option<&'a str> {
    let marker = text.find(heading)?;
    let rest = &text[marker + heading.len()..];
    rest.lines().map(str::trim).find(|line| !line.is_empty())
}

fn read(path: impl AsRef<Path>) -> String {
    let path = path.as_ref();
    fs::read_to_string(path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()))
}
