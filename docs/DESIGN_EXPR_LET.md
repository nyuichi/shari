# Design: Term Local-Const Migration and Expr `let` Bindings

## Status
Proposed.

## Summary
This design has two phases.

1. Migrate existing local constants from `Term::Const` representation to a dedicated `Term::LocalConst`.
2. Introduce expression-level term let-bindings:
   - `let c := m, e`
   - `let c : t := m, e`

Where:
- `m` is a **term** (`Term`), not an expression.
- `c` may be a qualified name.
- Let-binding introduces a local constant and a local delta rule `c = m` inside `e`.

The immediate priority is **Phase 1** (local const migration of existing code).

## Goals
- Make local/global constants representation explicit and robust:
  - local constants => `Term::LocalConst`
  - global constants => `Term::Const`
- Preserve existing behavior while migrating current local-const paths (`let structure` etc.).
- Prepare a clean foundation for `let c := m, e`.

## Non-goals
- No term-level binder syntax like `let x := t in u` inside `term`.
- No top-level `let` command.
- No behavior change in class/kappa semantics except local-const interaction needed for correctness.

## Phase 1: Local-Const Migration (Priority)

### 1) Term layer changes (`src/tt.rs`)
- Add:
  - `Term::LocalConst(Arc<TermLocalConst>)`
  - `TermLocalConst { metadata, id: Id, name: QualifiedName }`
  - `mk_local_const(id: Id, name: QualifiedName) -> Term`
- Keep display as the original qualified name (`name`).

### 2) Term utility updates (`src/tt.rs`)
Update all `Term` traversal/matching utilities to handle `LocalConst`:
- `Display`
- `metadata`, `with_span`, `ptr_eq`
- `open`, `close`
- `replace_local`, `replace_hole`, `replace_type`, `replace_instance`
- `is_ground`, `is_type_ground`, `is_instance_ground`
- `alpha_eq`, `maybe_alpha_eq`
- `whnf`, `head`, `args`, `replace_head`, `replace_args`
- `contains_type_local`, `contains_local`, `is_pattern`, `is_quasi_pattern`

### 3) Local environment model (`src/tt.rs`)
- Extend `LocalEnv` with:
  - local const table keyed by id/name (for type lookup)
  - `local_deltas` for local definitional unfolding
- Existing local const entries currently used by `let structure` migrate to this model.

### 4) TT environment API replacement (`src/tt.rs`)
Change existing APIs to accept `local_env` (replace, do not add parallel versions):
- `unfold_head(&self, local_env: &LocalEnv, m: &Term) -> Option<Term>`
- `has_delta(&self, local_env: &LocalEnv, head: &Term) -> bool`
- `delta_height(&self, local_env: &LocalEnv, head: &Term) -> usize`
- `equiv(&self, local_env: &LocalEnv, m1: &Term, m2: &Term) -> bool`

Internal helpers (`delta_reduce`, kappa checks, height helpers) are updated accordingly.

### 5) Consumers (`src/elab.rs`, `src/proof.rs`, `src/cmd.rs`)
- Replace all call sites of the above APIs with local-env-aware calls.
- Update local constant resolution in elaborator/type checker to treat `Term::LocalConst` as local only.
- Ensure `change` in proof checker uses local-env-aware `equiv`.
- Update all `LocalEnv` initializations with new fields.

### 6) Parser mapping (`src/parse.rs`)
- Existing local constants (currently produced as `Term::Const`) should be emitted as `Term::LocalConst`.
- This includes current local-const-producing paths such as `let structure`.

### 7) Validation and tests
Add regression tests to confirm no behavior changes after migration:
- Existing `let structure` proof successes remain green.
- Snapshot changes are intentional only.
- Add focused tests for local/global const disambiguation and shadowing.

## Phase 2: Expr Let-Term Syntax

## Syntax
Extend expression grammar with:

```text
expr ::= ...
      | "let" qname ":=" term "," expr
      | "let" qname ":" type ":=" term "," expr
      | "let" "structure" ...
```

Where `qname` is a qualified name.

## AST (`src/proof.rs`)
- Add:
  - `Expr::LetTerm(Box<ExprLetTerm>)`
  - `ExprLetTerm { metadata, name: QualifiedName, ty: Option<Type>, value: Term, body: Expr }`

## Semantics
- Scope:
  - `name` is available only in `body`.
  - `value` is parsed/elaborated without `name` in scope (non-recursive RHS).
- Introduce into local environment for `body`:
  - local constant `name`
  - local delta `name = value`
- For typed let:
  - check `ty` is well-formed type
  - enforce `value : ty` via elaboration constraints.

## Parser behavior (`src/parse.rs`)
- `let` branch:
  - if next keyword is `structure`, keep existing flow.
  - else parse let-term form.
- Allow qualified binder names.

## Elaborator / Proof checker behavior
- Elaborator:
  - infer/check type of `value`
  - if `ty` is present, constrain `value` to `ty`
  - push local const + local delta while visiting `body`
- Proof checker:
  - mirror same scope discipline
  - use local-env-aware `equiv` for conversion checks.

## Risks
- `Term` variant addition touches many exhaustive matches; missed sites can cause silent behavior drift.
- Local delta integration in unifier/equiv can accidentally introduce loops; unfolding must detect no-progress cases.
- Shadowing interactions between local const / global const / class methods need targeted tests.

## Test strategy

### Phase 1 (migration) tests
- Existing proof success snapshots (especially local-structure tests) remain valid.
- New unit tests for:
  - local const type inference
  - local const shadowing
  - local vs global const precedence

### Phase 2 (let syntax) tests
Positive:
- `let_expr_term_basic.shari`
- `let_expr_term_typed_basic.shari`
- `let_expr_term_qualified_name.shari`
- `let_expr_term_shadowing.shari`
- `let_expr_term_change_delta.shari`

Negative:
- `let_expr_term_recursive_rhs.shari` (`let c := c, ...` fails)
- `let_expr_term_typed_mismatch.shari`
- `let_expr_term_bad_annotation.shari`

## Documentation updates
After implementation:
- Update `docs/SHARI_LANGUAGE_GUIDE.md` with:
  - `Term::LocalConst`-backed local-const semantics
  - new expression let syntax and scoping
- Keep this design doc as the canonical migration + feature design record.
