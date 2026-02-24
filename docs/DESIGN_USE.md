# Use Command Design Doc

Status: initial draft

## Purpose

- Provide a small, explicit alias mechanism for qualified-name prefixes.
- Allow writing `use prod.fst` so later code can use `fst` and `fst.baz`.
- Allow chained alias declarations such as `use foo as bar; use bar as baz`.
- Keep this feature independent from any namespace block feature.

## Non-goals

- Introducing `namespace` syntax (`namespace foo { ... }`).
- Introducing open-namespace behavior (`use foo` as namespace import).
- Visibility control (private/protected).

## Terminology

- Qualified name: a dotted global name such as `prod.fst`.
- Prefix alias: a local head segment that points to one qualified prefix.
- Use table: mapping from alias head segment to qualified target prefix.

## Syntax (proposal)

- `use prod.fst`
- `use prod.fst as first`
- `use prod.{fst, snd}`
- `use bar as baz` (where `bar` is an existing alias)
- `use {foo as bar, baz.{hoge as piyo, fuga as piyopiyo}}`

Rules:

- `use` target can be a qualified global prefix or a path whose first segment is an existing alias.
- The parser resolves target head aliases before registering the new alias.
- If `as` is omitted, alias defaults to the last segment of the written target path.
- `use foo` is valid even if `foo` has no current global declaration; unresolved targets are allowed.
- Braced `use` trees contain comma-separated entries and nested `prefix.{...}` entries.
- `use` trees are expanded left-to-right into a flat sequence of leaf `use` entries.
- Comma-separated `use` targets are only valid inside `{...}`.
- `use prod.fst, prod.snd` is invalid; write `use prod.{fst, snd}`.

## Semantics

- `use` creates one prefix entry in `use_table`.
- `use prod.fst` registers `fst -> prod.fst`.
- `use prod.fst as first` registers `first -> prod.fst`.
- `use foo as bar; use bar as baz` registers `bar -> foo` then `baz -> foo`.

Prefix rewrite:

- If a reference starts with an alias key, replace that head with the mapped target prefix.
- `fst` rewrites to `prod.fst`.
- `fst.baz` rewrites to `prod.fst.baz`.
- `first.baz` rewrites to `prod.fst.baz` when `use prod.fst as first` is active.

Use-target canonicalization:

- Before inserting a `use` entry, the parser rewrites the target head using current `use_table`.
- The inserted mapping always points to a canonical qualified target, not to another alias.
- This flattening makes chained `use` declarations idempotent and avoids alias chains at lookup time.
- Canonicalization is left-to-right within one `use` command as well.
- Example: `use {hoge as fuga, fuga as piyo}` registers `fuga -> hoge` and `piyo -> hoge`.
- The parser does not require the canonicalized target to exist at `use` time.
- If an unresolved alias is later referenced as a term/type/proof constant, resolution fails at that reference site.

Use-tree expansion:

- `use {foo as bar, baz.{hoge as piyo, fuga as piyopiyo}}`
- expands to `use foo as bar; use baz.hoge as piyo; use baz.fuga as piyopiyo`
- each expanded leaf is then canonicalized and inserted by the normal rules.

Alias shadowing policy:

- Reusing an alias is always allowed.
- The latest `use` declaration wins and overwrites the previous mapping.
- This applies both across multiple `use` commands and within one braced `use` tree.

## AST and IR representation

- Parser-only node: `UseTree` (leaf path or nested `prefix.{...}` group).
- `UseDecl { target: QualifiedName, alias: Name }` for each expanded leaf.
- The parser desugars missing alias to an explicit alias during parsing.
- The parser expands `UseTree` to a flat ordered list of `UseDecl`.
- The parser maintains `use_table: HashMap<Name, QualifiedName>` as parse-state.
- The parser resolves `UseDecl.target` to a canonical qualified name before storing it in AST.
- The parser rewrites other name references to fully qualified names before they are stored in AST.

## Parser-side name resolution algorithm (sketch)

Resolution order for unqualified names:

1. Local bindings (function args, let, proof-local aliases).
2. `use_table` alias lookup.
3. Existing global lookup.

Rules:

- Qualified references (`foo.bar`) consult `use_table` on the first segment.
- `use` affects only declarations that appear after the `use` command in the same scope.
- If global lookup returns multiple candidates (cross-entity same name), report ambiguity.
- After a name is resolved, the parser stores only the resolved qualified name in AST.
- For `use` commands, `UseTree` expansion happens first, then target normalization, then alias insertion.
- `use` target existence checks are intentionally skipped.

## Errors (examples)

- Unknown identifier after rewrite: `unknown identifier 'fst.baz'`
- Ambiguous global name: `ambiguous identifier 'add': candidates are ...`
- Invalid use tree: `expected use entry after ','`
- Invalid multi-target use: `comma-separated targets require braces; use 'use prod.{fst, snd}'`

## Example

```shari
type const A : Type
type const B : Type
type const Prod : Type
const p : Prod
const prod.fst : Prod → A
const prod.snd : Prod → B
const prod.fst.default : Prod → A
const foo : A
const foo.child : A

use prod.fst

def x : A := fst p
def y : A := fst.default p

use foo as bar
use bar as baz

def z : A := baz
def w : A := baz.child

use {foo as bar2, prod.{fst as pfirst, snd as psnd}}

def u : A := bar2
def v : A := pfirst p
```

## Implementation plan (rough)

1. Parser: add top-level `use` command with optional `as` alias and braced `UseTree` grammar.
2. AST: add parser-only `UseTree`; keep `UseDecl { target, alias }` as normalized leaf form.
3. Parser expansion: flatten `UseTree` left-to-right into leaf `UseDecl`.
4. Parser state: maintain `use_table` with left-to-right shadowing semantics.
5. Parser rewrite: apply prefix rewrite using `use_table` for both unqualified and qualified references.
6. Parser normalization: resolve `use` targets through existing aliases before insertion.
7. Parser output: store fully qualified resolved names in AST so later stages do not re-resolve names.
8. Diagnostics: add unknown rewritten target and invalid-tree errors.
9. Tests: positive alias case, implicit alias case, `bar.baz` rewrite case, chained-use case, nested use-tree case, shadowing case, unresolved-use acceptance case.

## Documentation updates

- Update `/Users/yuichi/.codex/worktrees/3116/shari/docs/SHARI_LANGUAGE_GUIDE.md` when implementation lands.
- If `use`/`as` keywords are added or changed in grammar, update:
- `/Users/yuichi/.codex/worktrees/3116/shari/editors/shari-vscode/syntaxes/shari.tmLanguage.json`
- `/Users/yuichi/.codex/worktrees/3116/shari/shari-playground/public/index.html`

## Risks and open questions

- Scope boundary: top-level only vs nested scopes if future local command blocks are introduced.
- Alias shadowing against existing globals is allowed because alias lookup runs before global lookup.
- Whether `use` should allow non-qualified targets (`use fst`) in the future.
- Parser complexity increase from doing all name resolution at parse time.

## Future Directions (Not Implemented Yet)

- Option A: implicit alias registration from declarations.
- Example: `def foo := ...` automatically inserts `foo -> foo` into `use_table`.
- Expected benefit: reduces boilerplate `use` commands.
- Risks: shadowing interactions with existing aliases/globals and key policy for qualified definitions (`def prod.fst := ...`).

- Option B: replace `QualifiedName` references with global `Id`.
- Target model: `foo -> Id(X)` mapping, with `Const`/`ExprConst` and related TT/proof structures storing `Id` instead of `QualifiedName`.
- Required work: global symbol table design, parser/elaborator/printer migration, and reverse lookup for pretty-printing.
- Assessment: large refactor; best handled as incremental milestones rather than a single change.
