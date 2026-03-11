# Polymorphic Higher-Order Unification

## Status

implemented

## Summary

Shari's elaborator keeps the existing higher-order imitation and projection search, adds one-step binder expansion when a projection candidate is blocked by a type metavariable, and explores those expansion branches with iterative deepening on the number of binder expansions used. Ground term constraints are also discharged with the kernel's definitional equality so the elaborator can benefit from the current `η` support without eagerly eta-expanding every candidate.

## Decision

- Preserve the existing `find_conflict_in_terms` lambda-opening rule for `?M ... =?= λ x, N` instead of adding a global eta-normalization pass.
- In `choice_fr`, keep the current rigid-head imitation and selector-like projection branches.
- Add a backtrackable type-substitution branch when a selected projection binder ends in a type hole; the branch instantiates that hole with one fresh arrow layer and retries the same flex-rigid constraint.
- Run DFS under a binder-expansion budget and increase that budget linearly (`0, 1, 2, ...`) from `solve()`, so finite-expansion solutions are not lost to one infinite DFS branch. Linear growth keeps the smallest-expansion solution order and only replays searches that actually used binder expansion; exponential growth is a possible future tuning if profiling shows many deep successful expansions.
- Treat kernel definitional equality as a simplification step only for ground term constraints.

## Impact

- Uses such as `eq.ap nat.zero.spec` can now elaborate when omitted proof instantiations must first make a hidden type argument into a function type.
- Binder-expansion-free problems finish in the first budget-`0` pass, so the common case keeps the old DFS behavior with only small bookkeeping overhead.
- Repeated one-step expansions are still possible, but iterative deepening makes the search fair across finite expansion depths instead of committing forever to one deep branch.
- Class-instance synthesis and method constraints are unchanged.

## Update Triggers

- Update this doc if flex-rigid branching changes again, especially if Shari adopts more of Hustadt's HPT transformation system.
- Update [../SHARI_LANGUAGE_GUIDE.md](../SHARI_LANGUAGE_GUIDE.md) when user-visible elaboration behavior for omitted proof arguments changes.
