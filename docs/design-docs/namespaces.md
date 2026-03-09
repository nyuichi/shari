# Namespaces

## Status

implemented

## Summary

Shari uses lexical namespace blocks such as `namespace foo.bar { ... }` and canonicalizes global names during parsing. Alias resolution remains namespace-local through a per-namespace `use_table`.

## Decision

- Keep `current_namespace` and `namespace_table` in parser state and require the current namespace to exist at all times.
- Resolve names at parse time and store canonical qualified names in the AST.
- Treat `resolve` as a pure alias rewrite step; existence checks happen at the specific reference site afterward.
- Ensure `namespace` commands switch both parser and evaluator state and restore the previous namespace on success or failure.
- Allow namespace-relative declaration heads while keeping alias mappings scoped to the active namespace.

## Impact

- Parser tests should cover namespace block scoping, qualified declarations, alias rewrites, and unresolved-name errors after rewrite.
- The language guide must describe namespace blocks because they are part of the public command surface.
- Namespace behavior is coupled with `use`, so changes here often require updating the `use` design doc as well.

## Update Triggers

- Update this doc if namespace scoping, canonicalization timing, or alias rewrite rules change.
- Update [../SHARI_LANGUAGE_GUIDE.md](../SHARI_LANGUAGE_GUIDE.md) when namespace syntax or visible semantics change.
