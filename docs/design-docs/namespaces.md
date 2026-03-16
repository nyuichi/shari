# Namespaces

## Status

implemented

## Summary

Shari uses lexical namespace blocks such as `namespace foo.bar { ... }`. Parsing resolves namespace-relative references through per-namespace `use_table` entries, then stores resolved global entities as `GlobalId` values. Shared namespace state uses `Path`, while parser-only unresolved references stay in a private `QualifiedName`.

## Decision

- Keep `current_namespace` and `namespace_table` in parser state and require the current namespace to exist at all times.
- Represent resolved namespaces and `use` targets with `Path`, shared between parser and evaluator.
- Keep unresolved references in a parser-private `QualifiedName` that records `is_absolute` plus raw string segments, and convert resolved global references to `GlobalId` before storing them in the AST and evaluation tables.
- Treat `resolve` as a pure alias rewrite step; existence checks happen at the specific reference site afterward.
- Ensure `namespace` commands switch both parser and evaluator state and restore the previous namespace on success or failure.
- Allow namespace-relative declaration heads while keeping alias mappings scoped to the active namespace.

## Impact

- Parser tests should cover namespace block scoping, qualified declarations, alias rewrites, and unresolved-name errors after rewrite.
- The language guide must describe namespace blocks because they are part of the public command surface.
- Namespace behavior is coupled with `use`, so changes here often require updating the `use` design doc as well.

## Update Triggers

- Update this doc if namespace scoping, `Path`/parser-private `QualifiedName`/`GlobalId` responsibilities, canonicalization timing, or alias rewrite rules change.
- Update [../SHARI_LANGUAGE_GUIDE.md](../SHARI_LANGUAGE_GUIDE.md) when namespace syntax or visible semantics change.
