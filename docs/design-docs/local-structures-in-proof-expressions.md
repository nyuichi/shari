# Local Structures In Proof Expressions

## Status

implemented

## Summary

Proof expressions support `let structure Foo := { ... }, e` as a scoped theory extension. The generated type, fields, and axioms are visible only in the body expression and may reference term locals already in scope.

## Decision

- Support `let structure` inside proof expressions with no local type parameters.
- Reuse top-level structure field generation rules while keeping the scope local to the body expression.
- Allow local structure axioms to mention outer term locals from the definition site.
- Reject recursive or self-referential local structures and reject type escape from the body result.
- Keep the implementation separate from top-level `structure` expansion even when the generated pieces look similar.

## Impact

- The feature enables local structure reasoning without polluting global tables.
- Tests should cover visibility, shadowing, generated names, axiom scope, and type-escape rejection.
- Surface syntax and scoping rules are part of the user-facing language reference.

## Update Triggers

- Update this doc if `let structure` scoping, generated names, or type-escape rules change.
- Update [../SHARI_LANGUAGE_GUIDE.md](../SHARI_LANGUAGE_GUIDE.md) when the syntax or visible semantics change.
