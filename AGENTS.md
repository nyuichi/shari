# Shari

## Coding style

- Favor short, descriptive identifiers that match existing naming patterns. Spend a moment to choose names that communicate intent clearly.
- Prefer destructuring bindings when working with structs or enums. Avoid using `..` in patterns; instead, list fields explicitly and bind unused ones to `_` or `_name`.
- Place test code at the bottom of each source file.

## Testing

- This repository uses snapshot testing with `cargo insta`. When snapshot tests differ and the change is intentional, run `cargo insta accept` to refresh snapshots. You don't need to ask for permission to do this.

## Development Flow

- Always run `cargo fmt` after making changes.
- Keep `cargo clippy` warnings at zero.
- Ensure `cargo test` passes.
- After running `cargo test`, review your changes for consistency with the rest of the codebase and refactor when there is room for improvement.

## Shari language reference

- Before editing or creating `.shari` sources, read and follow the guidance in `docs/SHARI_LANGUAGE_GUIDE.md` so generated proofs respect the language grammar and features.
- When adding or changing Shari language features (syntax, commands, elaboration behavior), update `docs/SHARI_LANGUAGE_GUIDE.md` to keep the reference accurate.
- If the Shari grammar or keyword set changes, update the VS Code syntax (`editors/shari-vscode/syntaxes/shari.tmLanguage.json`) and the playground highlighter (`shari-playground/public/index.html`) accordingly.
