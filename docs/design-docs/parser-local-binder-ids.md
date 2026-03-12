# Parser Local Binder IDs

## Status

implemented

## Summary

The parser resolves local binders to fresh `Id`s as soon as they enter scope. Shadowing is therefore tracked by identity, not by written name, before elaboration or proof checking starts.

## Decision

- Term locals and type locals use a binding stack of `{ name, id }` pairs during parsing.
- Proof-expression binders and aliases stored in the AST carry the parser-generated `Id` directly.
- Parser desugarings such as `have`, `obtain`, `let`, `let structure`, and `obtain instance` must reuse those stored `Id`s instead of recomputing them from names later.
- Declaration labels such as constructor names, structure field names, and `use ... as ...` aliases remain `Name`-based because they are not local references.
- Top-level structure and instance field labels become visible to later fields only after the current field has been parsed, which keeps `def rep := rep` non-recursive and preserves outer bindings with the same written name.

## Impact

- Local shadowing like `take x, assume P x, take x` is parsed unambiguously.
- Proof and elaboration code must treat AST binder ids as authoritative and avoid `Id::from_name` for parser-introduced locals.
- Regression tests should cover aliases, `let`, `obtain`, local structures, and top-level instances that reuse written names.

## Update Triggers

- Update this doc if parser-local scope resolution changes, or if more declaration forms start carrying explicit local ids in the AST.
- Update [../SHARI_LANGUAGE_GUIDE.md](../SHARI_LANGUAGE_GUIDE.md) when user-visible shadowing or scoping behavior changes.
