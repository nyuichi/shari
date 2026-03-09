# Structure Unique `abs`

## Status

proposed

## Summary

This proposal removes auto-generated `structure.ext` axioms and strengthens generated `structure.abs` axioms from ordinary existence to unique existence. Extensionality would then be derived as an ordinary lemma instead of being introduced axiomatically.

## Decision

- Generate `Foo.abs` with `uexists` for both top-level `structure` and local `let structure`.
- Stop auto-generating `Foo.ext`.
- Preserve call sites by providing explicit `Foo.ext` lemmas in library code when needed.
- Leave class structure behavior and kernel conversion rules unchanged.

## Impact

- Proof scripts that relied on generated `Foo.ext` would need replacement lemmas.
- Tests and snapshots would change because generated output and available names would differ.
- The language guide must be updated if this proposal is implemented because generated structure artifacts are user-visible.

## Update Triggers

- Update this doc if the generated `structure` axioms, compatibility plan, or helper-lemma strategy changes.
- Update [../SHARI_LANGUAGE_GUIDE.md](../SHARI_LANGUAGE_GUIDE.md) when the proposal lands or its visible semantics change.
