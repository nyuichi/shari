# Change Playbook

Use this file to decide which docs and artifacts must change together.

## Change Categories

| Change | Required updates |
| --- | --- |
| Grammar, keyword, or parser surface change | `docs/SHARI_LANGUAGE_GUIDE.md`, `editors/shari-vscode/syntaxes/shari.tmLanguage.json`, `shari-playground/public/index.html`, and any affected `docs/design-docs/*.md` |
| Elaboration or proof behavior change visible to `.shari` authors | `docs/SHARI_LANGUAGE_GUIDE.md` and the relevant design doc |
| Internal implementation strategy or accepted tradeoff change | Relevant file in `docs/design-docs/` |
| Agent workflow or documentation maintenance change | `docs/operations/agent-docs-policy.md`, this file, and `AGENTS.md` only if the entrypoint map changes |
| New long-lived feature area | Add or update a design doc and link it from `docs/README.md` |
| File move or doc rename inside `docs/` | Update `docs/README.md` and any relative links that point at the moved file |

## Required Review Pass

Before finishing a change:

1. Confirm the updated docs still match the code and command surface.
2. Confirm `docs/README.md` links to every current operations doc and design doc.
3. Confirm no doc contains environment-specific absolute paths.
4. Confirm `AGENTS.md` still works as a short entrypoint rather than a detailed manual.

## Local And CI Checks

- Run `cargo test --test docs_lint --locked` when touching documentation structure or policy.
- Run `cargo fmt --all --check`, `cargo clippy --all-targets --all-features`, and `cargo test --all --all-features --locked` before finishing the change.
