# Design: Remove auto-generated `structure.ext` and strengthen `structure.abs`

## Summary
Stop generating `Foo.ext` as an axiom for both top-level `structure` and local `let structure`.
At the same time, strengthen generated `Foo.abs` from existence (`exists`) to unique existence (`uexists`, i.e. `∃!`).

With this change, extensionality is no longer a primitive per-structure axiom. Instead, users prove `Foo.ext` as a lemma from `Foo.abs` (and field axioms when needed). In `src/main.shari`, we keep existing call sites unchanged by adding explicit lemmas named `Foo.ext`.

## Motivation
- `structure.ext` is currently introduced axiomatically even though it is derivable from a stronger abstraction principle.
- Replacing `exists` by `uexists` in `abs` makes the intended semantics more direct: structure objects are uniquely determined by their representation data.
- This reduces the number of primitive axioms introduced by `structure`/`let structure`.

## Goals
- Remove auto-generation of `Foo.ext` for top-level `structure`.
- Remove auto-generation of `Foo.ext` for local `let structure`.
- Change generated `Foo.abs` to use `uexists` (`∃!`) instead of `exists` (`∃`).
- Keep `src/main.shari` behavior by adding explicit `Foo.ext` lemmas where currently used.
- Add reusable generic lemmas to make deriving extensionality from abstraction straightforward.

## Non-goals
- No change to `class structure` / `class instance` behavior.
- No change to inductive definitions.
- No change to kernel conversion rules.

## Current behavior
For top-level `structure Foo := { ... }`:
- Generates `Foo` type constant.
- Generates field constants/axioms.
- Generates `Foo.abs` with existential conclusion:
  - `... -> exists (this : Foo ...), char(this, params)`
- Generates `Foo.ext` axiom:
  - equality of all const-field projections implies equality of objects.

For local `let structure Foo := { ... }, e` in expressions:
- Generates local `Foo`, `Foo.field`, `Foo.abs`, and `Foo.ext` with the same pattern.

## Proposed behavior

### 1) Generated `abs` uses unique existence
For both top-level and local structures, generate:
- `Foo.abs : ... -> uexists (this : Foo ...), char(this, params)`

where `char(this, params)` is the conjunction of const-field equalities, and guards from axiom fields are unchanged.

Concretely, for:
```
structure bool := {
  const rep : Prop
  axiom spec : rep = top or rep = bot
}
```
the generated abstraction principle becomes:
```
axiom bool.abs (rep : Prop) : rep = top or rep = bot -> uexists (this : bool), rep = bool.rep this
```

### 2) Do not auto-generate `ext`
- Remove generated `Foo.ext` from top-level `structure`.
- Remove generated local `Foo.ext` from `let structure`.

## Compatibility strategy (`src/main.shari`)
Existing code in `src/main.shari` currently calls names like `inhab.ext`, `bool.ext`, `monoid.ext`.
To keep those call sites unchanged:
- Add explicit lemmas named `Foo.ext` in `src/main.shari`.
- Each lemma is proved from `Foo.abs` (plus field axioms as needed).

## Generic helper lemmas
Add generic lemmas (in `src/main.shari`) for reusing the proof pattern.

Candidate API:
```
lemma abs.ext.{u, v} (rep : u -> v) (P : v -> Prop) :
  (forall (a : u), P (rep a)) ->
  (forall (x : v), P x -> uexists (a : u), rep a = x) ->
  (forall (a1 a2 : u), rep a1 = rep a2 -> a1 = a2)
```

Notes:
- The user-suggested shape without the first assumption is useful in some cases, but to derive full extensionality in general we need a way to discharge `P (rep a)` for representatives (typically from structure axiom fields).
- If needed, we can also provide a weaker variant that takes `P (rep a2)` as an explicit premise.

## Implementation plan

1) Top-level `structure` generation (`src/cmd.rs`)
- In `run_structure_cmd`:
  - Replace `exists` with `uexists` when building `abs`.
  - Remove generation of the `ext` axiom.
  - Remove `ext`-specific duplicate-name checks tied to auto-generation.

2) Local `let structure` generation (`src/elab.rs`)
- In `Elaborator::visit_expr` branch for `Expr::LetStructure`:
  - Replace local `abs` generation from `exists` to `uexists`.
  - Remove local `ext` axiom generation.

3) Library compatibility (`src/main.shari`)
- Add generic helper lemma(s) for deriving extensionality from unique abstraction.
- Add explicit `Foo.ext` lemmas for structures used by existing code paths so call sites remain unchanged.
- Update explanatory comments that currently say `structure` generates `Foo.ext`.

4) Tests and snapshots
- Update tests that currently reference generated `foo.ext` for local structures (e.g. `tests/proof_successes/local_structure_generated_axioms.shari`).
- Update snapshot expectations for run logs (removal of generated `*.ext`, and `abs` signature changes to `∃!`/`uexists`).

5) Documentation
- Update `docs/SHARI_LANGUAGE_GUIDE.md`:
  - `structure`/`let structure` now generate `abs` with unique existence.
  - `ext` is no longer auto-generated.

## Open questions
- `uexists` is assumed to be available in the environment when `structure` / `let structure` are elaborated.
- Should the name `ext` remain conventionally reserved in structure namespaces (for compatibility), even though it is no longer generated automatically?
- Do we want one helper lemma (`abs.ext`) or both strong/weak variants to cover common proof styles?
