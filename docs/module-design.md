# Module and use Design Doc

Status: initial draft

## Purpose

- Provide logical grouping to avoid identifier collisions.
- Allow qualified references like `foo.bar` and short references via `use foo.bar`.
- Keep the design Lean-like while fitting Shari's existing syntax and implementation constraints.

## Non-goals

- A full module system or file-level import mechanism.
- Visibility controls like private/protected across modules.
- Scoped use variants like `use scoped` or attribute-like features.

## Terminology

- Module: a logical hierarchy for symbols.
- Qualified name: a full path like `foo.bar.baz`.
- Use: bringing a specific identifier into the current scope for shorter references.

## Syntax (proposal)

- Module definition: `module foo { ... }`
- Nested module: `module foo.bar { ... }`
- Qualified reference: `foo.bar`
- Use: `use foo.bar` (where `foo.bar` is a fully qualified identifier)
- Use alias: `use foo.bar as baz`

Note: `use foo` is only valid when `foo` resolves to a concrete declaration, not a module path.

Example:

```shari
module math {
  type const Nat : Type
  const zero : Nat
  const add : Nat → Nat → Nat
}

def f : math.Nat := math.add math.zero math.zero

use math.add
use math.zero

def g : math.Nat := add zero zero
```

## Scoping and name resolution (draft)

Resolution order for unqualified names:

1. Local bindings (function args, let, pattern binds).
2. Current module declarations.
3. Used identifiers.
4. Root module.

Rules:

- `use` is lexical and affects only later declarations in the same scope.
- Ambiguous names are errors. Use a qualified name to disambiguate.
- Inside `module foo { ... }`, unqualified `bar` resolves to `foo.bar` if present.
- `use` does not open a module; it only introduces the chosen identifier.

## AST and IR representation

- `ModuleDecl { path, items }` for `module` blocks.
- `UseDecl { target }` for `use` statements.
- Names stored internally as `Vec<Ident>` (fully qualified).
- Unqualified references resolved to fully qualified names during name resolution.

## Name resolution algorithm (sketch)

Environment fields:

- `current_module: QualifiedName` — the active module path for the current scope. Unqualified
  definitions declared in the scope are recorded under this path (for example, `module foo { def bar := ... }`
  records `foo.bar`). Nested `module` blocks push/pop this path lexically.
- `use_table: HashMap<QualifiedName, QualifiedName>` — maps an introduced name to its fully qualified
  target. A `use math.add` entry registers `math.add -> math.add`, while `use math.add as plus` registers
  `plus -> math.add`. Resolution first checks this map by the unqualified name (or alias) and, when present,
  substitutes the fully qualified target.

Algorithm:

1. If the reference is qualified, resolve directly.
2. If unqualified, try `current_module + name`.
3. If still unresolved, check `use_table` for `name` and, if present, resolve to the mapped qualified name.
4. If still unresolved, try `root + name`.
5. If no candidates, emit unknown identifier error.
6. If multiple candidates, emit ambiguity error.

Note: `use` order does not affect priority. This avoids subtle changes in meaning; the rule can be relaxed later if needed.

Kind handling:

- Name resolution is independent of entity kind and is driven by `current_module`, `use_table`, and the root
  namespace only.
- The resolver returns a qualified name; any kind validation is owned by the elaboration path that consumes it.

## Errors (examples)

- Unknown identifier: `unknown identifier 'add'`
- Ambiguous identifier: `ambiguous identifier 'add': candidates are math.add, list.add`
- Unknown use target: `unknown identifier 'math.add'`

## Desugaring

- `module foo.bar { ... }` desugars to `module foo { module bar { ... } }`.

## Examples

```shari
module list {
  type const List : Type
  const add : List → List → List
}

module math {
  type const Nat : Type
  const add : Nat → Nat → Nat
  const zero : Nat
}

use list.add
use math.add

def h : math.Nat := math.add math.zero math.zero
```

Ambiguity:

```shari
use list.add
use math.add

def x : math.Nat := add math.zero math.zero -- error: list.add vs math.add
```

## Implementation plan (rough)

1. Parser: add `module` and `use` constructs.
2. AST: add `ModuleDecl` and `UseDecl`.
3. Name resolution: track `current_module` and `use_table`.
4. Errors: add unknown/ambiguous diagnostics.
5. Tests: add examples and negative cases.

## Documentation updates

- Update `docs/SHARI_LANGUAGE_GUIDE.md` with syntax and rules.
- If keywords change, update `editors/shari-vscode/syntaxes/shari.tmLanguage.json`.
- If keywords change, update `shari-playground/public/index.html`.

## Risks and open questions

- Interactions with existing name resolution paths.
- Whether `use` should be order-sensitive in the future.
- Whether `use` is allowed at expression scope or only at declaration scope.
- Whether `module` should be allowed outside top-level.
- Whether visibility modifiers are out-of-scope for now.
- Whether the qualified-name separator should remain `.` or switch to `::`.
