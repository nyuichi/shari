# Use Command

## Status

implemented

## Summary

The `use` command provides parser-time aliases for qualified-name prefixes. It supports direct aliases, grouped imports, nested groups, and absolute groups while keeping alias resolution namespace-local.

## Decision

- Let `use` register prefix aliases in the current namespace table.
- Canonicalize `use` targets through existing aliases before storing them, so alias chains flatten eagerly.
- Allow grouped forms such as `use foo.{bar, baz}` and `use {foo as bar, baz.{hoge as piyo}}`.
- Allow unresolved targets at `use` time; reference sites remain responsible for reporting missing declarations.
- Apply alias lookup before global lookup for unqualified references in parser resolution.

## Impact

- Parser tests should cover direct aliases, grouped aliases, chained aliases, shadowing, and unresolved-target acceptance.
- Namespace behavior and `use` behavior evolve together because `use_table` is namespace-scoped.
- The language guide must stay aligned because `use` and `as` are part of the public command syntax.

## Update Triggers

- Update this doc if `use` syntax, alias shadowing policy, or canonicalization timing changes.
- Update [../SHARI_LANGUAGE_GUIDE.md](../SHARI_LANGUAGE_GUIDE.md) when the surface syntax or visible semantics change.
