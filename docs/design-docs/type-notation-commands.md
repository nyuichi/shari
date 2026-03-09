# Type Notation Commands

## Status
implemented

## Summary

Shari now supports `type infix`, `type infixl`, `type infixr`, `type prefix`, and `type nofix` as top-level commands for the type layer. These commands mirror term notation registration while keeping a separate parser/printer table for type syntax.

## Decision

- Keep term and type notation registration as separate command variants.
- Reuse the existing `Operator`/`Fixity` model, but store type notation in dedicated parser and pretty-printer maps.
- Preserve `→` as a built-in type operator because it is not backed by a type constructor.
- Remove the parser hard-codes for `×` and `ℕ`.
  - The prelude now declares `type infixr × : 35 := prod`.
  - The prelude now declares `type def ℕ := nat`.
- Validate type-notation target arity when commands are evaluated:
  - infix/infixl/infixr require arity 2
  - prefix requires arity 1
  - nofix requires arity 0

## Impact

- Type syntax can now use user-declared fixities with the same precedence/associativity model as terms.
- Pretty-printing of `Type` values reuses registered type notation, so logs and displayed declarations show `×`-style syntax when available.
- `ℕ` is no longer a parser special case; it behaves like any other `type def`.

## Update Triggers

- Update this doc when type-notation target validation, precedence handling, or printer round-tripping rules change.
- Update the language guide if the `type` notation command surface, prelude-provided aliases, or built-in type operators change.
