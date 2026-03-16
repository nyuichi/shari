# Use Command

## Status

implemented

## Summary

The `use` command provides parser-time aliases for qualified-name prefixes. It supports direct aliases, grouped imports, nested groups, and absolute groups while keeping alias resolution namespace-local.

## Decision

- Let `use` register prefix aliases in the current namespace table.
- Resolve each `use` target in the parser against the alias table snapshot from the start of that `use` command, then store the resolved absolute `Path` in `CmdUse`.
- Allow grouped forms such as `use foo.{bar, baz}` and `use {foo as bar, baz.{hoge as piyo}}`.
- Allow unresolved targets at `use` time; reference sites remain responsible for reporting missing declarations.
- Apply alias lookup before global lookup for unqualified references in parser resolution.
- Keep unresolved `use` entries in the parser's private `QualifiedName` only until resolution; parser/evaluator boundaries expose only `Path`.
- Do not let earlier declarations inside the same grouped `use` affect later ones; `use {a as b, b as a}` reads both targets from the pre-command snapshot.
- Keep evaluator-side `use` handling as a plain install step with no additional alias canonicalization.

## Impact

- Parser tests should cover direct aliases, grouped aliases, snapshot semantics within a single `use`, shadowing, and unresolved-target acceptance.
- Namespace behavior and `use` behavior evolve together because `use_table` is namespace-scoped.
- The language guide must stay aligned because `use` and `as` are part of the public command syntax.

## Update Triggers

- Update this doc if `use` syntax, alias shadowing policy, or parser snapshot timing changes.
- Update [../SHARI_LANGUAGE_GUIDE.md](../SHARI_LANGUAGE_GUIDE.md) when the surface syntax or visible semantics change.
