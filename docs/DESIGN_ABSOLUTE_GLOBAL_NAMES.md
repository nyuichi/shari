# Absolute Global Name Design (`.foo.bar`)

Status: draft

## Goals

- Add absolute global name syntax: `.foo.bar`.
- Resolve absolute names from top-level namespace, not `current_namespace`.
- Allow whitespace between field segments (`.foo .bar` is valid, same as `.foo.bar`).
- Apply support to all global-name parse points in `src/parse.rs`.
- Reject absolute paths in declaration heads (e.g. `const .foo : Prop`).

## Non-goals

- No lexer token-kind changes.
- No AST shape changes (`QualifiedName`, `Path`, command structs stay as-is).
- No change to local binder syntax (for example `let` binder names remain identifier-only).

## Current behavior summary

- Lexer already tokenizes `.foo` as `TokenKind::Field`.
- Parser global-name parsing (`qualified_name`) requires an identifier head, so leading-dot names are rejected today.
- Name resolution (`resolve`) always starts from `current_namespace`.

## Proposed syntax and semantics

### Syntax

- Relative global name: `foo.bar`
- Absolute global name: `.foo.bar`
- Absolute with whitespace between segments: `.foo .bar`

### Resolution

- Relative names: keep existing behavior (resolve from `current_namespace`).
- Absolute names: resolve from `Path::toplevel()`.
- Alias rewrite rules stay the same; only the starting namespace changes.

## Scope in `parse.rs`

### Accept absolute names

- Type references (`type_primary`)
- Class references (`class`)
- Term/global constant references (`term_var`)
- Proof/global axiom references (`expr_var`, including `@...`)
- `namespace` command target path (`namespace_cmd`)
- `use` target paths (`use_entry`)
- Operator entity paths (`infix_cmd`, `infixl_cmd`, `infixr_cmd`, `prefix_cmd`, `nofix_cmd`)

### Reject absolute names (declaration heads)

- `def` (`def_cmd`)
- `axiom` (`axiom_cmd`)
- `lemma` (`lemma_cmd`)
- `const` (`const_cmd`)
- `type const` (`type_const_cmd`)
- `type inductive` name and constructor names (`type_inductive_cmd`)
- `inductive` name and constructor names (`inductive_cmd`)
- `structure` (`structure_cmd`)
- `instance` (`instance_cmd`)
- `class structure` (`class_structure_cmd`)
- `class instance` (`class_instance_cmd`)

Error policy:

- Emit a parse error when a declaration head is absolute.
- Suggested message: `absolute path is not allowed in declaration head`.

## Parser design

### Pre-refactor (recommended)

This refactor is independently useful and reduces feature diff:

- Replace resolver signature with:
  - `resolve(base: Path, name: QualifiedName) -> QualifiedName`
- Update existing relative call sites to:
  - `self.resolve(self.current_namespace.clone(), name)`

Benefits:

- Removes duplicated resolution logic needed for absolute names.
- Makes resolution base explicit and testable.

## Parser helper model (no new types)

Keep parser APIs close to existing style:

- Keep `qualified_name(&Token) -> QualifiedName`, but allow head token to be either:
  - `TokenKind::Ident` (relative literal head)
  - `TokenKind::Field` (absolute literal head; strip leading `.`)
- Keep consuming trailing `TokenKind::Field` segments exactly as today.

Add only small helpers:

- `global_reference_name(head: &Token) -> QualifiedName`
  - Parse with `qualified_name(head)`.
  - If `head.kind == TokenKind::Field`, call `resolve(Path::toplevel(), name)`.
  - Otherwise call `resolve(self.current_namespace.clone(), name)`.
- `global_declaration_name() -> Result<QualifiedName, ParseError>`
  - Reject `TokenKind::Field` with `absolute path is not allowed in declaration head`.
  - Parse dotted tail with `qualified_name`.
  - Resolve by `self.resolve(self.current_namespace.clone(), name)`.

Parsing rules:

- `head.kind == Ident` => relative global name
- `head.kind == Field` => absolute global name (first segment from `head.as_str().strip_prefix('.')`)
- Consume trailing `TokenKind::Field` segments in both cases.

## Local/special lookup interaction

Relative-only checks remain relative-only:

- Local term/type binders
- Local structure-generated names
- Local proof aliases
- Self-reference stashes used by (type) inductive parsing

Absolute names bypass those relative/local checks and go straight to absolute global resolution.

For self-reference behavior in inductives:

- Keep existing relative-literal self-match behavior unchanged.
- Absolute names are treated as global references, not as literal self aliases.
- This preserves current anti-alias guarantees.

## TDD plan

Implement in red-green-refactor order:

1. Add failing parser tests for absolute global names:
   - `.foo.bar` parses as a global name.
   - `.foo .bar` equals `.foo.bar`.
2. Add failing tests for each absolute-allowed parse point:
   - type reference, term reference, expr reference (`@.foo`), namespace, use target, each fixity command entity.
3. Add failing tests for declaration-head rejection:
   - each declaration command listed above rejects leading-dot head.
4. Implement `resolve(base, name)` and switch existing `resolve(...)` call sites to explicit base passing.
5. Replace call sites in `parse.rs`.
6. Refactor duplicated declaration-head parsing through `global_declaration_name()`.
7. Keep/adjust existing tests for alias resolution and namespace behavior.

## Compatibility and risks

- Relative name behavior is unchanged.
- Main risk is accidental acceptance/rejection drift per call site; mitigated by per-command tests.
- Lexer already supports `Field`, so no lexical grammar risk.

## Documentation updates when implemented

- Update `docs/SHARI_LANGUAGE_GUIDE.md` with absolute global-name syntax and declaration-head restriction.
- Syntax highlighters likely need no keyword changes, but verify `.foo` examples render correctly in:
  - `editors/shari-vscode/syntaxes/shari.tmLanguage.json`
  - `shari-playground/public/index.html`
