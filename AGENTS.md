# Shari

## Coding style

- Favor short, descriptive identifiers that match existing naming patterns. Spend a moment to choose names that communicate intent clearly.
- Prefer destructuring bindings when working with structs or enums. Avoid using `..` in patterns; instead, list fields explicitly and bind unused ones to `_` or `_name`.

## Testing

- This repository uses snapshot testing with `cargo insta`. When snapshot tests differ and the change is intentional, run `cargo insta review --accept` to refresh snapshots. You don't need to ask for permission to do this.

## Development Flow

- Always run `cargo fmt` after making changes.
- Keep `cargo clippy` warnings at zero.
- Ensure `cargo test` passes.
- After running `cargo test`, review your changes for consistency with the rest of the codebase and refactor when there is room for improvement.
