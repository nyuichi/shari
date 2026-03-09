# Absolute Global Names

## Status

proposed

## Summary

Allow absolute global references such as `.foo.bar` while keeping declaration heads relative. The feature is intended to resolve names from the root namespace without changing AST shapes or lexer token kinds.

## Decision

- Accept absolute names at global reference parse sites, including term, type, proof, `namespace`, `use`, and operator target positions.
- Reject absolute names in declaration heads such as `def .foo := ...` and `const .bar : Prop`.
- Resolve relative names from `current_namespace` and absolute names from `Path::root()`.
- Keep local binder and self-reference behavior unchanged; absolute names bypass those local shortcuts.
- Make the resolution base explicit in parser helpers so reference and declaration parsing can share logic safely.

## Impact

- Parser tests should cover every accepted reference site and every rejected declaration-head site.
- Relative resolution semantics stay unchanged.
- The largest risk is acceptance drift between parse sites, so the implementation should keep the allowed and rejected entrypoints explicit.

## Update Triggers

- Update this doc if absolute-name syntax, accepted parse sites, or declaration-head restrictions change.
- Update [../SHARI_LANGUAGE_GUIDE.md](../SHARI_LANGUAGE_GUIDE.md) when the user-facing syntax lands or changes.
- If lexer or highlighting behavior for leading-dot names changes, update the VS Code syntax and playground highlighter in the same change.
