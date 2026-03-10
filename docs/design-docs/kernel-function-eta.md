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
- Leave elaborator metavariable solving unchanged for now, even though some eta-shaped goals still require explicit guidance outside the kernel.

## Impact

- `change` and other proof-kernel conversion checks can use function eta without adding explicit propositional lemmas.
- Comments and guides must distinguish kernel conversion from elaborator/unifier behavior so users do not assume metavariable solving has the same eta coverage.
- Existing propositional lemmas such as product eta remain valid and are still needed where the surface language does not reduce them judgmentally.

## Update Triggers

- Update this doc if eta scope expands beyond functions or if kernel conversion stops using the current compare-on-demand strategy.
- Update [../SHARI_LANGUAGE_GUIDE.md](../SHARI_LANGUAGE_GUIDE.md) when user-visible conversion behavior changes again.
