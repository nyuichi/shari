# Design: Local typedef (`let structure`) in proof expressions

## Summary
Add `let structure` inside `expr` to introduce a temporary structure type with no local type parameters. The name and derived constants/axioms are only visible in the body expression. Local structure axioms may reference any term locals in scope at the definition site. Semantics mirror top-level `structure` (with primitive field projections and no `rec`), but with lexical scope.

## Status
Implemented. This document reflects the current behavior.

## Goals
- Allow `let structure Foo := { ... }, e` inside proof expressions.
- Disallow local type parameters (`let structure Foo u := ...` is a parse error).
- Make `Foo` and `Foo.field`/`Foo.abs`/`Foo.ext` usable in `e`.
- Allow structure axiom targets to mention all in-scope term locals.
- Reuse the same generation rules as top-level `structure`.
- Keep scope limited to `e` and avoid global pollution.

## Non-goals
- No `class structure` local version in this iteration.
- No local `instance` or general `let def` in expressions.
- No recursive/self-referential local structures.

## Syntax
```
expr ::= ...
      | "let" "structure" ident ":=" "{" struct_fields "}" "," expr
struct_fields ::= ("const" ident ":" type | "axiom" ident ":" term)*
```

Example:
```
take (x : t),
let structure Foo := {
  axiom bar : x = x
},
...
```

Notes:
- Keep `let` as an identifier in the lexer; parse it in `expr`.
- `:=` is required (match top-level syntax and reduce ambiguity).

## Scoping and name resolution
- `Foo` and `Foo.*` are visible only in the body expression `e`.
- Inner `let structure` shadows outer/local/global names.
- `Foo` is not visible inside its own definition (same as top-level).
- `abs`/`ext` remain reserved in the generated namespace; field names that collide will error (same behavior as top-level, but can be made explicit earlier).
- Axiom targets may reference term locals that are in scope at the definition site; those locals remain free in the axiom target and must stay in scope wherever the axiom is used (which is guaranteed by lexical scoping).

## Semantics
- `let structure` is a *local theory extension* during checking of the body.
- The resulting proposition is exactly the body proposition.
- Generated definitions are identical to top-level `structure`:
  - Type constant `Foo` with arity = 0.
  - Constants `Foo.field` for const fields.
  - Axioms `Foo.field` for axiom fields.
  - Axioms `Foo.abs` and `Foo.ext`.
- Field projections are primitive constants (no delta expansion).
- Local structure axioms are elaborated under the current term local environment. Their targets may contain free locals and are **not** generalized over those locals (only the implicit `this` parameter is introduced, as in top-level `structure`).
- Definitional equality uses existing delta + beta machinery; `let structure` adds no new delta entries for fields.

Soundness note:
- This is a scoped extension with new axioms (abs/ext and axiom fields). It does not introduce a guarding implication like `assume`. This matches the existing `structure` design (axiomatic), but should be documented explicitly.

## Typing rule (sketch)
```
Gamma | Phi |- structdef OK
Gamma | Phi |- e : P   (under env extended with structdef)
-----------------------------------------------
Gamma | Phi |- let structure ... , e : P
```

## Implementation notes (implemented)

### 1) AST changes (proof.rs)
- Add `Expr::LetStructure(Box<ExprLetStructure>)`.
- New structs (kept in `proof.rs` to avoid cycles with `cmd.rs`):
  - `ExprLetStructure { metadata, name, fields, body }`
  - `LocalStructureField::{Const(LocalStructureConst), Axiom(LocalStructureAxiom)}`
- Update `Display`, `metadata()`, `with_span()`, `replace_hole()`, etc.

### 2) Parser changes (parse.rs)
- Add a `let structure` branch in `expr` parsing and reject local type parameters.
- Parse structure fields with the same rules as top-level `structure`.
- Maintain local definition stacks in the parser:
  - `local_consts: Vec<(QualifiedName, Const)>`
  - `local_axioms: Vec<(QualifiedName, Axiom)>`
  - `local_types: Vec<Name>`
- Name resolution checks locals before globals in `term_var`/`expr_const` via `get_const`/`get_axiom`.
- During `let structure` parsing:
  - Build `Foo`/`Foo.*` entries (arity = 0) including `abs`/`ext`.
  - Push local stacks while parsing the body, then pop/truncate.

### 3) Duplicate structure expansion logic
- Do **not** factor `cmd::run_structure_cmd` into a shared helper.
- Implement a separate expansion path for `let structure`, even if it duplicates code.
- Rationale: top-level `structure` and `let structure` are similar but not identical; explicit duplication keeps behaviors decoupled.

### 4) Elaboration and proof checking
- Handle `Expr::LetStructure` in `Elaborator::visit_expr`.
- Push a local frame into `tt_local_env.local_types` and `tt_local_env.local_consts`, and `local_axioms` for the body; pop afterward.
- Axiom targets are elaborated under the current term local environment, so they can reference in-scope locals.
- `Expr::Const` resolves local axioms before global axioms.
- Enforce an eigenvariable condition: the body result cannot mention the local structure type (type escape).

### 5) Tests
- Parsing:
  - `let structure` is accepted in `expr`.
  - `Foo` and `Foo.field` resolve in body.
  - Nested `let structure` and shadowing.
- Errors:
  - Undefined name in body.
  - Duplicate fields.
  - Self-reference in definition.
- Elaboration:
  - `Foo.abs`/`Foo.ext` usable.
  - Axiom target can refer to an outer `take`-bound local (e.g., `x = x`).
  - Type escape is rejected (eigenvariable condition).
  
Concrete tests:
- `tests/proof_successes/local_structure_generated_axioms.shari`
- `tests/proof_successes/local_structure_axiom_scope.shari`
- `tests/proof_errors/local_structure_type_escape.shari`

### 6) Documentation
- `docs/SHARI_LANGUAGE_GUIDE.md` documents the `let structure` syntax and scoping.

## Open questions / tradeoffs
- Allow optional `:=` omission?
- Add `class structure` local version?
