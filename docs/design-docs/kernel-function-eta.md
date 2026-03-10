# Kernel Function Eta Equivalence

## Status

implemented

## Summary

The kernel's definitional equality now treats a function term `f` as judgmentally equal to its eta expansion `λ x, f x`. This change is intentionally limited to function eta and does not make product, unit, or structure eta judgmental.

## Decision

- Keep eta handling local to `tt::Env::equiv`; do not add a new reduction pass or new core syntax.
- When `equiv` compares an abstraction against a non-abstraction, first try the existing `δ/κ/local δ` head unfolding on the non-abstraction.
- If unfolding cannot expose an abstraction, compare the abstraction body opened with a fresh rigid local against the non-abstraction applied to that same local.
- Let repeated single-binder eta checks account for curried functions.
- Align elaborator metavariable solving with the same function-η principle for rigid-vs-`λ` comparison and flex-rigid projection/imitation candidates.

## Impact

- `change` and other proof-kernel conversion checks can use function eta without adding explicit propositional lemmas.
- Higher-order unification now uses the same function-η assumption for elaboration, although explicit search-space limits around polymorphic projection remain.
- Existing propositional lemmas such as product eta remain valid and are still needed where the surface language does not reduce them judgmentally.

## Update Triggers

- Update this doc if eta scope expands beyond functions or if kernel conversion stops using the current compare-on-demand strategy.
- Update [../SHARI_LANGUAGE_GUIDE.md](../SHARI_LANGUAGE_GUIDE.md) when user-visible conversion behavior changes again.
