# Structure Primitive Fields

## Status

proposed

## Summary

This proposal removes the generated `structure.rec` recursor and makes structure field projections primitive constants. Instance generation would provide per-field spec axioms instead of a single recursor-based specification axiom.

## Decision

- Stop generating `Foo.rec` for top-level structures.
- Keep `Foo.field` as primitive constants rather than delta definitions in terms of `Foo.rec`.
- Replace instance rec-spec axioms with per-field axioms such as `Bar.f.spec`.
- Leave inductive recursors, class structures, and the rest of the kernel unchanged.

## Impact

- Proofs that relied on definitional unfolding of structure fields would need explicit rewriting through per-field spec axioms.
- Snapshot output would change because `*.rec` declarations disappear.
- The proposal simplifies field behavior and reduces coupling between structures and delta reduction.

## Update Triggers

- Update this doc if structure field generation or instance spec naming changes.
- Update [../SHARI_LANGUAGE_GUIDE.md](../SHARI_LANGUAGE_GUIDE.md) when the proposal lands or any user-visible structure artifacts change.
