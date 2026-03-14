# Parser Local Binder IDs

## Status

implemented

## Summary

The parser resolves local binders to fresh `Id`s as soon as they enter scope. Shadowing is therefore tracked by identity, not by written name, before elaboration or proof checking starts.

## Decision

- Term locals and type locals use a binding stack of `{ name, id }` pairs during parsing.
- Proof-expression binders and aliases stored in the AST carry the parser-generated `Id` directly.
- Parser desugarings such as `have`, `obtain`, `let`, `let structure`, and `obtain instance` must reuse those stored `Id`s instead of recomputing them from names later.
- Top-level `structure`, `class structure`, `instance`, and `class instance` const/def/lemma fields store an explicit `field_id` alongside their written `field_name`, and later parsing/elaboration stages must treat that id as authoritative.
- Parser-generated top-level helper declaration names such as constructor fully-qualified names and generated `ind` / `rec` / `abs` / `spec` names are stored in the command AST and later stages must treat those stored names as authoritative instead of rebuilding them from the declaration head.
- Declaration labels such as constructor names and `use ... as ...` aliases remain `Name`-based because they are not local references.
- Top-level structure and instance field labels become visible to later fields only after the current field has been parsed, which keeps `def rep := rep` non-recursive and preserves outer bindings with the same written name.

## Impact

- Local shadowing like `take x, assume P x, take x` is parsed unambiguously.
- Proof and elaboration code must treat AST binder ids and parser-generated helper declaration names as authoritative and avoid reconstructing them from written names later.
- Regression tests should cover aliases, `let`, `obtain`, local structures, and top-level instances that reuse written names.

## Update Triggers

- Update this doc if parser-local scope resolution changes, or if more declaration forms start carrying explicit local ids in the AST.
- Update [../SHARI_LANGUAGE_GUIDE.md](../SHARI_LANGUAGE_GUIDE.md) when user-visible shadowing or scoping behavior changes.
