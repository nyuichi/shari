# Shari Agent Guide

Use this file as the entrypoint only. The durable project knowledge lives in [docs/README.md](docs/README.md).

## Non-negotiables

- Work in TDD order: add or update a failing test first, make it pass, then refactor.
- Do not introduce meaningless whitespace-only diffs such as CRLF churn.
- Run `cargo fmt`, `cargo clippy --all-targets --all-features`, and `cargo test --all --all-features --locked` after changes.
- After tests pass, review names, helper boundaries, and overall consistency with the rest of the codebase.
- This repository uses `cargo insta`; when a snapshot change is intentional, run `cargo insta accept`.

## Docs To Read

- [docs/README.md](docs/README.md): documentation index and reading order.
- [docs/operations/agent-docs-policy.md](docs/operations/agent-docs-policy.md): source-of-truth and doc maintenance rules.
- [docs/operations/change-playbook.md](docs/operations/change-playbook.md): which docs and artifacts to update for each kind of change.
- [docs/SHARI_LANGUAGE_GUIDE.md](docs/SHARI_LANGUAGE_GUIDE.md): language syntax and proof-writing reference for `.shari` files.

## Update Routing

- Agent workflow or documentation process changes belong in `docs/operations/*`, not as long prose here.
- Language grammar, keywords, or elaboration behavior changes must update `docs/SHARI_LANGUAGE_GUIDE.md`.
- Grammar or keyword changes must also update:
  - `editors/shari-vscode/syntaxes/shari.tmLanguage.json`
  - `shari-playground/public/index.html`
- Implementation design changes belong in the matching file under `docs/design-docs/`.
