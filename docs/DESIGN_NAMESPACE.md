# Namespace Design

Status: revised

## Goals

- Add lexical namespaces: `namespace foo.bar { ... }`.
- Resolve names at parse time and store canonical fully qualified names in AST.
- Keep alias resolution namespace-local (`use_table` per namespace).

## Core data model

```rust
struct Path(Option<Arc<PathInner>>);
struct PathInner {
    parent: Path,
    name: Name,
}

struct QualifiedName {
    path: Path,
    name: Name,
}

struct Namespace {
    use_table: HashMap<Name, QualifiedName>,
}
```

- `Path` represents namespace paths.
- `QualifiedName` is split into `path` and terminal `name`.
- `Path` and `QualifiedName` are interned.
- Root namespace is `Path::root()`.

## Parser state and invariants

- Parser holds:
  - `current_namespace: Path`
  - `namespace_table: HashMap<Path, Namespace>`
- `current_namespace` always exists in `namespace_table`.
- Root namespace entry is created before parsing starts.
- `Parser::new` does not hydrate from global symbol tables; caller provides consistent tables.

## Name resolution contract

`resolve(name: QualifiedName) -> QualifiedName`

- Input is by-value.
- Behavior is pure rewrite only:
  - If head segment is in `namespace_table[current_namespace].use_table`, rewrite head and keep tail.
  - Otherwise return input unchanged.
- `resolve` does not validate whether the rewritten target actually exists.

This keeps rewrite and validity checks separate.

## Canonicalization rules

- Declaration heads:
  - If alias head exists, canonical name is `resolve(name)`.
  - Otherwise canonical name is namespace-relative under `current_namespace`.
  - Ensure owner namespace path exists.
  - Register declaration alias in owner namespace: `name -> canonical`.
- Reference positions (term/type/expr/class):
  - Apply `resolve`.
  - Validate against locals/global tables at call site.
  - Unknowns fail with existing parse errors.
- `use` target and operator entities (`infix*`, `prefix`, `nofix`):
  - Canonicalize with `resolve` only.
  - Parse does not require rewritten target to exist.
  - Example: `use foo as bar; infix * : 50 := bar.baz` stores `foo.baz`.

## Namespace command semantics

- `Cmd::Namespace` stores `name: Path`.
- Parsing `namespace N { ... }`:
  - Canonicalize `N` to `Path`.
  - Ensure namespace path exists.
  - Switch `current_namespace`, parse inner commands, restore previous namespace.
  - Restore also on parse failure.

## Evaluator semantics

- Evaluator stores shared `namespace_table: HashMap<Path, Namespace>` and `current_namespace: Path`.
- `Cmd::Use` mutates only current namespace aliases.
- Alias mutations go through `Namespace::add(alias, target)` (no scattered `use_table.insert`).
- `Cmd::Namespace` executes inner commands under switched namespace and restores previous namespace on both success and error.

## Minimal tests to keep

- `namespace` is lexed as a keyword.
- Namespace block prefixes declaration names correctly.
- Qualified declarations create missing child namespaces.
- `resolve` rewrites alias heads without requiring target existence.
- Reference sites still reject unresolved names after rewrite.
