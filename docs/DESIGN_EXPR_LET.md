# Design: Expr `let` for Terms (Binder Non-`resolve`)

## Status
Implemented design target for proof-expression `let` with local delta conversion.

## Summary
Introduce proof-expression term binders:

- `let c := m, e`
- `let c : t := m, e`

Where:

- `m` is a term (`Term`), not a proof expression.
- `c` may be a qualified name.
- binder name `c` is preserved as written (non-resolved).
- RHS is non-recursive (`c` is not in scope while parsing/elaborating `m`).
- body `e` is checked with both:
  - a local constant entry (`c`), and
  - a local delta rule (`c = m`) used by definitional equality.

## AST
`src/proof.rs`

- `Expr::LetTerm(Box<ExprLetTerm>)`
- `ExprLetTerm { metadata, name: QualifiedName, ty: Option<Type>, value: Term, body: Expr }`
- constructor: `mk_expr_let_term(...)`

Display forms:

- `let c := m, e`
- `let c : t := m, e`

## Parser behavior
`src/parse.rs`

- `let` in proof expressions is split into:
  - `let structure ...` (existing path)
  - `let-term` (new path)
- Binder parsing for let-term:
  - parse as `QualifiedName`
  - do **not** call `resolve` on binder name
- Scope discipline:
  - parse `value` before introducing binder (non-recursive)
  - push binder into parser local const table only while parsing `body`

### Term name resolution order
`term_var` is fixed to prioritize local bindings:

1. term locals / self-reference
2. local consts (raw name comparison, before `resolve`)
3. global constant resolution after `resolve`

This guarantees local binder priority over global/use aliases.

## TT local environment and conversion
`src/tt.rs`

- `LocalEnv` includes:
  - `local_consts: Vec<(QualifiedName, LocalConst)>`
  - `local_deltas: Vec<(QualifiedName, LocalDelta)>`
- `LocalDelta { target: Term, height: usize }`

Definitional-equality API uses local environment:

- `unfold_head(&self, local_env: &LocalEnv, m: &Term) -> Option<Term>`
- `has_delta(&self, local_env: &LocalEnv, head: &Term) -> bool`
- `delta_height(&self, local_env: &LocalEnv, head: &Term) -> usize`
- `equiv(&self, local_env: &LocalEnv, m1: &Term, m2: &Term) -> bool`

Unfolding order for `Const` head:

1. local delta
2. global delta
3. kappa

For `LocalConst` head:

- resolve level -> local const name -> local delta lookup

## Elaborator / proof checker behavior
`src/elab.rs`, `src/proof.rs`

For `Expr::LetTerm`:

- If annotation exists:
  - check annotation is a well-formed type
  - constrain/check `value : ty`
- Without annotation:
  - infer binder type from `value`
- During body checking only:
  - push local const `(name, LocalConst { ty })`
  - push local delta `(name, LocalDelta { target: value, height })`
- Pop both entries after body

`change` conversion uses local-env-aware `equiv`, so local let delta participates in conversion.

## Scope and shadowing
- Binder is local to `body`.
- Binder shadows globals and alias-resolved names in term positions.
- Existing `let structure` behavior remains.

## Non-goals
- No term-level `let ... in ...` syntax.
- No top-level `let` command.
- No recursive let RHS.
