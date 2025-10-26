# Shari

## Coding style

- Favor short, descriptive identifiers that match existing naming patterns. Spend a moment to choose names that communicate intent clearly.

## Testing

- This repository uses snapshot testing with `cargo insta`. When snapshot tests differ and the change is intentional, run `cargo insta review --accept` to refresh snapshots. You don't need to ask for permission to do this.