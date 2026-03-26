# Coherence-Checked Overlapping Class Instances

## Status

implemented

## Summary

`class instance` now allows overlap when the new instance is coherent with every overlapping previously registered instance. The checker enumerates critical pairs by first-order unification and requires prior top-level `N.coherence.*` axioms or lemmas for every non-definitional obligation.

## Decision

- Keep overlap checking in `run_class_instance_cmd`; the new instance is elaborated first and registered only after all obligations are discharged.
- Collect top-level coherence candidates in declaration order as `CoherenceProof` records and search them linearly with first-match semantics.
- Accept both top-level `axiom` and top-level `lemma` declarations as coherence candidates. Generated axioms from other commands are excluded.
- Generate one obligation per critical pair and field.
- For `const` fields, require an equality between the existing representative method and the specialized new field body.
- For `axiom` fields, require `iff old new` unless the old and new propositions are already definitionally equal.
- Auto-discharge obligations only when definitional equality succeeds; otherwise an explicit coherence candidate is required.

## Impact

- Overlapping class instances are now a user-visible part of elaboration behavior.
- Coherence candidates must appear before the overlapping `class instance` declaration they justify.
- Tests should cover exact overlap, generic-vs-specific overlap, multi-pair overlap, and missing-coherence failures.
- The language guide must document the `N.coherence.*` convention and the equality/`iff` obligation split.

## Update Triggers

- Update this doc if overlap eligibility, obligation generation, candidate search order, or auto-discharge rules change.
- Update [../SHARI_LANGUAGE_GUIDE.md](../SHARI_LANGUAGE_GUIDE.md) if the visible `class instance` behavior or coherence-proof convention changes.
