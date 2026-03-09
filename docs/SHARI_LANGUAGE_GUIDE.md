# Shari Language Guide for Coding Agents

This document summarizes the surface syntax, proof language, and namespace system of Shari. Coding agents must consult this guide before editing or adding `.shari` sources so that generated code respects the language.

## Lexical conventions
- **Whitespace and comments** – Lexing skips Unicode whitespace, line comments starting with `--`, and nested block comments delimited by `/-` … `-/`.
- **Tokens** – Tokens are classified as identifiers, fields, symbols, numeral literals, or keywords according to the rules in the lexer. Identifiers may contain Unicode letters, digits, underscores, and apostrophes. Dotted global names are parsed as a head token plus field segments (for example `foo.bar` as `foo` + `.bar`, and absolute `.foo.bar` as `.foo` + `.bar`). Symbols cover operators such as `:=`, `∃!`, `${`, `.{`, parentheses, and punctuation.
- **Keywords** – Reserved words recognized by the lexer are `infixr`, `infixl`, `infix`, `nofix`, `prefix`, `def`, `axiom`, `lemma`, `const`, `type`, `inductive`, `structure`, `instance`, `class`, `namespace`, `use`, and `as`. The bare glyphs `λ` and `_` are treated as symbols, not identifiers.

## Type grammar
- **Primary forms** – A type primary can be a local type variable, a registered type constant, a registered `type def` alias (expanded immediately during parsing), the numeral type `ℕ` (desugaring to `nat`), or a parenthesized type.
- **Arrow and product** – Types support right-associative arrows `→` with precedence 25 and right-associative products `×` at precedence 35.
- **Type application** – Any primary followed by additional primaries or parenthesized expressions applies like `F A`. Explicit type argument blocks `.{τ₁, …, τₙ}` are also parsed as applications.
- **Kinds** – `Type`, optionally repeated with `→ Type`, specifies the arity of type constants when declaring them.
- **Binders** – `(x y : T)` groups typed parameters, and `[C]` introduces local class constraints (see below).

## Term grammar
- **Binders** – Lambda abstractions use `λ` followed by parameters and a comma; binders `∀`, `∃`, and `∃!` require at least one parameter tuple before the comma. Each binder inserts the parameters into scope before parsing the body.
- **Set comprehension** – `{ x : T | e }` (or `{ x | e }`) produces a lambda with binder `x` and optional type annotation.
- **Variables and constants** – Global references support both relative (`foo.bar`) and absolute (`.foo.bar`) forms; whitespace before field segments is allowed (`.foo .bar`). Relative names resolve first against locals and then via the current namespace alias table, while absolute names resolve from the root namespace and bypass local/self-name lookup shortcuts. Explicit type arguments use `.{τ₁, …, τₙ}`; omitted arguments generate metavariables. Class constraints create implicit instance holes that elaboration fills later.
- **Pairs** – The Lean-style bracket syntax `⟨m, n⟩` is available as sugar for `pair m n`, with both components parsed as full terms. There are also projections `.0` and `.1`.
- **Applications and user operators** – Function application is implicit juxtaposition. Operator fixity, precedence, and entity resolution come from the token table populated by `infix`, `infixl`, `infixr`, `prefix`, and `nofix` commands.
- **Holes** – An underscore `_` introduces a fresh metavariable applied to the current local context, tracked for later synthesis.
- **Unsupported numerals** – Numerical literals currently raise a parse error when used as terms; write explicit constants such as `nat.zero` instead.

## Proof expressions
- **Atomic proof** – `«φ»` quotes a goal assumption; `assume φ, e` introduces an implication, and the variant `assume φ as h, e` binds the hypothesis under the alias `h`. Aliases act like local proofs and can be referenced directly by name inside their scope. `take (x : τ), e` and `change φ, e` correspond to universal introduction and definitional rewriting. Function application uses juxtaposition, and explicit instantiation `e[m₁, …, mₙ]` supplies arguments to universal hypotheses.
- **Automatic instantiation** – Referencing a lemma/axiom name auto-instantiates leading `∀` binders. The same auto-instantiation also applies to local proof aliases and local structure axioms (for example aliases from `assume ... as h` or names like `Foo.a` inside `let structure`). Prefixing a proof name with `@` suppresses this automatic instantiation when manual control is required.
- **Derived constructs** – `have φ := e₁, e₂` packages a lemma. Writing `have φ as h := e₁, e₂` additionally introduces an alias `h` scoped to `e₂`, allowing subsequent expressions to use `h` as a proof term. `obtain (x : τ), φ := e₁, e₂` performs existential elimination, and `obtain (x : τ), φ as h := e₁, e₂` likewise aliases the proof of `φ` within `e₂`. `calc` chains equalities via `have` and `eq.trans` expansions.
- **Expr `let` (term binder)** – `let c := m, e` and `let c : t := m, e` introduce a local term constant inside proof expressions. The binder must be a single identifier (`let foo.bar := ...` is a parse error). The RHS `m` is parsed/elaborated before introducing `c` (non-recursive), while `e` is parsed/elaborated with `c` in scope. Definitional equality uses a local delta rule `c = m` during checking.
- **Local structures** – `let structure Foo := { const f : τ ... axiom h : φ ... }, e` introduces a scoped structure type inside a proof expression. The structure name and generated constants/axioms (`Foo.f`, `Foo.abs`, etc.) are available only in `e`. `Foo.abs` uses unique existence (`∃!`). Local type parameters are not supported, and axiom targets may reference any term locals already in scope.

## Top-level commands
The `cmd` dispatcher recognizes the following keywords. Each command builds a structured object in `cmd.rs` that the elaborator consumes.

- **Declaration heads** – Declaration names for `def`, `axiom`, `lemma`, `const`, `type const`, `type def`, `type inductive` (including constructor names), `inductive` (including constructor names), `structure`, `instance`, `class structure`, and `class instance` must start with an identifier head. Absolute heads such as `.foo` are rejected in declaration positions.
- **Operator registration** – `infix`, `infixl`, `infixr`, `prefix`, and `nofix` map a symbol to an existing constant with a given precedence. Binary operators take precedence levels as natural numbers.
- **Definitions** – `def name.{tyvars} [class params] (args : τ) : σ := t` declares computable constants. Types are generalized over parameters before being stored.
- **Axioms and lemmas** – `axiom` and `lemma` share parameter syntax; lemmas additionally require a proof script and record any metavariable holes for later solving.
- **Constants** – `const` introduces noncomputable constants with optional local type/class parameters.
- **Type layer** – `type const` declares primitive type constructors, `type def name u₁ … uₙ := τ` declares parser-time type aliases that are expanded immediately when referenced, and `type inductive` declares inductive type families.
- **Inductive propositions** – `inductive` declares propositional inductives with parameters and constructor blocks separated by `|`. Constructor targets are automatically generalized over constructor parameters.
- **Structures and instances** – `structure` declares record-like bundles of constants and axioms; `instance` supplies implementations of those fields for a target type, including derived lemmas. Within a structure body, `const` and `axiom` fields may be freely interleaved. Within an `instance` body, later `def` fields may refer to earlier `def` fields by name, and later `lemma` fields may refer to earlier `lemma` fields by name in proof expressions.
- **Type classes** – `class structure` and `class instance` mirror structures/instances but live in the class namespace and accept class arguments on fields. Within a `class instance` body, later `def` fields may refer to earlier `def` fields by name, and later `lemma` fields may refer to earlier `lemma` fields by name in proof expressions.
- **Namespaces** – `namespace foo.bar { ... }` opens a scoped namespace block. Namespace targets also allow absolute form (`namespace .foo.bar { ... }`). Declarations inside are stored with fully qualified names; qualified declaration heads like `def qux.quux := ...` create missing child namespaces under the current namespace.
- **Use aliases** – `use` introduces parser-time alias mappings for qualified names in the current namespace table. Targets may be relative (`use foo.bar`) or absolute (`use .foo.bar`). Supported forms include `use foo.bar as baz`, grouped imports such as `use foo.{bar, baz}`, top-level absolute groups such as `use .{foo, bar}`, and nested groups such as `use {foo as bar, baz.{hoge as piyo}}`. Each leaf target is resolved during parsing against the alias-table snapshot from the start of that `use` command and stored as a resolved `QualifiedName` in AST, so earlier entries in the same grouped `use` do not affect later ones. Absolute entries are disallowed inside any use group (`use {.foo}`, `use foo.{.bar}` are invalid).

## Type classes and implicit arguments
- Class parameters `[C]` record constraints that become implicit instance arguments when using the resulting constants or lemmas.
- When invoking a constant or lemma, you may override implicit type arguments with `.{…}` or explicit instance arguments with `[ … ]`. Otherwise the elaborator synthesizes them using higher-order unification and κ-reduction.

## Working with holes and elaboration
- Every `_` in a term or proof registers a metavariable paired with the current local context. These are collected on the parser’s `holes` stack and emitted alongside `lemma` and `instance lemma` commands for the elaborator to solve.

## Using this guide
Before editing `.shari` files:
1. Review the lexical and grammar sections to ensure new syntax conforms to the parser.
2. Declare operators and type/class scaffolding via the documented commands rather than inventing new keywords.
3. Prefer explicit binders and instantiations when automation is insufficient, using `@` to disable auto instantiation on global or local proof names as needed.
4. Keep track of holes emitted by proof scripts and resolve or justify them during elaboration.

Following these rules will keep generated Shari code well-formed and compatible with the existing parser and elaborator.
