# Expr `let` For Terms

## Status

implemented

## Summary

Proof expressions support local term binders with `let c := m, e` and `let c : t := m, e`. The binder introduces a local constant plus a local delta rule that participates in definitional equality inside the body.

## Decision

- Parse proof-expression `let` as a term-binding form distinct from `let structure`.
- Preserve the binder name as written instead of resolving it through namespace aliases.
- Keep the RHS non-recursive by parsing and elaborating it before the binder enters scope.
- Push both a local constant entry and a local delta entry while checking the body, then pop both afterward.
- Prioritize local term binders over global and alias-resolved constants during term lookup.

## Impact

- Definitional equality and `change` can use the local `let` expansion without adding a top-level command.
- Tests should cover typed and untyped binders, local shadowing, and recursive-RHS rejection.
- The feature is intentionally limited to proof expressions; there is no term-level `let ... in ...`.

## Update Triggers

- Update this doc if binder resolution, shadowing priority, or local-delta conversion behavior changes.
- Update [../SHARI_LANGUAGE_GUIDE.md](../SHARI_LANGUAGE_GUIDE.md) when the surface syntax or scoping rules change.
