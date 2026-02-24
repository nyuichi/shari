# Shari Language Guide for Coding Agents

This document summarizes the surface syntax, proof language, and namespace system of Shari. Coding agents must consult this guide before editing or adding `.shari` sources so that generated code respects the language.

## Lexical conventions
- **Whitespace and comments** – Lexing skips Unicode whitespace, line comments starting with `--`, and nested block comments delimited by `/-` … `-/`.
- **Tokens** – Tokens are classified as identifiers, symbols, numeral literals, or keywords according to the rules in the lexer. Identifiers may contain Unicode letters, digits, underscores, apostrophes, and dot-separated namespaces. Symbols cover operators such as `:=`, `∃!`, `${`, `.{`, parentheses, and punctuation.
- **Keywords** – Reserved words recognized by the lexer are `infixr`, `infixl`, `infix`, `nofix`, `prefix`, `def`, `axiom`, `lemma`, `const`, `type`, `inductive`, `structure`, `instance`, `class`, `namespace`, `use`, and `as`. The bare glyphs `λ` and `_` are treated as symbols, not identifiers.

## Type grammar
- **Primary forms** – A type primary can be a local type variable, a registered type constant, the special keyword `sub` (expanding to an arrow into `Prop`), the numeral type `ℕ` (desugaring to `nat`), or a parenthesized type.
- **Arrow and product** – Types support right-associative arrows `→` with precedence 25 and right-associative products `×` at precedence 35.
- **Type application** – Any primary followed by additional primaries or parenthesized expressions applies like `F A`. Explicit type argument blocks `.{τ₁, …, τₙ}` are also parsed as applications.
- **Kinds** – `Type`, optionally repeated with `→ Type`, specifies the arity of type constants when declaring them.
- **Binders** – `(x y : T)` groups typed parameters, and `[C]` introduces local class constraints (see below).

## Term grammar
- **Binders** – Lambda abstractions use `λ` followed by parameters and a comma; binders `∀`, `∃`, and `∃!` require at least one parameter tuple before the comma. Each binder inserts the parameters into scope before parsing the body.
- **Set comprehension** – `{ x : T | e }` (or `{ x | e }`) produces a lambda with binder `x` and optional type annotation.
- **Variables and constants** – A bare identifier resolves first to locals, otherwise to registered constants. Explicit type arguments use `.{τ₁, …, τₙ}`; omitted arguments generate metavariables. Class constraints create implicit instance holes that elaboration fills later.
- **Pairs** – The Lean-style bracket syntax `⟨m, n⟩` is available as sugar for `pair m n`, with both components parsed as full terms. There are also projections `.0` and `.1`.
- **Applications and user operators** – Function application is implicit juxtaposition. Operator fixity, precedence, and entity resolution come from the token table populated by `infix`, `infixl`, `infixr`, `prefix`, and `nofix` commands.
- **Holes** – An underscore `_` introduces a fresh metavariable applied to the current local context, tracked for later synthesis.
- **Unsupported numerals** – Numerical literals currently raise a parse error when used as terms; write explicit constants such as `nat.zero` instead.

## Proof expressions
- **Atomic proof** – `«φ»` quotes a goal assumption; `assume φ, e` introduces an implication, and the variant `assume φ as h, e` binds the hypothesis under the alias `h`. Aliases act like local proofs and can be referenced directly by name inside their scope. `take (x : τ), e` and `change φ, e` correspond to universal introduction and definitional rewriting. Function application uses juxtaposition, and explicit instantiation `e[m₁, …, mₙ]` supplies arguments to universal hypotheses.
- **Constants** – Naming a lemma or axiom introduces it with implicit higher-order instantiation; prefixing the name with `@` suppresses automatic instantiation when manual control is required.
- **Derived constructs** – `have φ := e₁, e₂` packages a lemma. Writing `have φ as h := e₁, e₂` additionally introduces an alias `h` scoped to `e₂`, allowing subsequent expressions to use `h` as a proof term. `obtain (x : τ), φ := e₁, e₂` performs existential elimination, and `obtain (x : τ), φ as h := e₁, e₂` likewise aliases the proof of `φ` within `e₂`. `calc` chains equalities via `have` and `eq.trans` expansions.
- **Expr `let` (term binder)** – `let c := m, e` and `let c : t := m, e` introduce a local term constant inside proof expressions. The binder `c` may be qualified (for example `Foo.bar`) and is stored as written (not alias-resolved). The RHS `m` is parsed/elaborated before introducing `c` (non-recursive), while `e` is parsed/elaborated with `c` in scope. Definitional equality uses a local delta rule `c = m` during checking.
- **Local structures** – `let structure Foo := { const f : τ ... axiom h : φ ... }, e` introduces a scoped structure type inside a proof expression. The structure name and generated constants/axioms (`Foo.f`, `Foo.abs`, etc.) are available only in `e`. `Foo.abs` uses unique existence (`∃!`). Local type parameters are not supported, and axiom targets may reference any term locals already in scope.

## Top-level commands
The `cmd` dispatcher recognizes the following keywords. Each command builds a structured object in `cmd.rs` that the elaborator consumes.

- **Operator registration** – `infix`, `infixl`, `infixr`, `prefix`, and `nofix` map a symbol to an existing constant with a given precedence. Binary operators take precedence levels as natural numbers.
- **Definitions** – `def name.{tyvars} [class params] (args : τ) : σ := t` declares computable constants. Types are generalized over parameters before being stored.
- **Axioms and lemmas** – `axiom` and `lemma` share parameter syntax; lemmas additionally require a proof script and record any metavariable holes for later solving.
- **Constants** – `const` introduces noncomputable constants with optional local type/class parameters.
- **Type layer** – `type const` and `type inductive` manage type constructors and inductive type families.
- **Inductive propositions** – `inductive` declares propositional inductives with parameters and constructor blocks separated by `|`. Constructor targets are automatically generalized over constructor parameters.
- **Structures and instances** – `structure` declares record-like bundles of constants and axioms; `instance` supplies implementations of those fields for a target type, including derived lemmas. Within a structure body, `const` and `axiom` fields may be freely interleaved.
- **Type classes** – `class structure` and `class instance` mirror structures/instances but live in the class namespace and accept class arguments on fields.
- **Namespaces** – `namespace foo.bar { ... }` opens a scoped namespace block. Declarations inside are stored with fully qualified names; qualified declaration heads like `def qux.quux := ...` create missing child namespaces under the current namespace.
- **Use aliases** – `use` introduces parser-time alias mappings for qualified names in the current namespace table. Supported forms include `use foo.bar`, `use foo.bar as baz`, grouped imports such as `use foo.{bar, baz}`, and nested groups such as `use {foo as bar, baz.{hoge as piyo}}`. Alias expansion is resolved during parsing and stored as fully qualified names in AST.

## Type classes and implicit arguments
- Class parameters `[C]` record constraints that become implicit instance arguments when using the resulting constants or lemmas.
- When invoking a constant or lemma, you may override implicit type arguments with `.{…}` or explicit instance arguments with `[ … ]`. Otherwise the elaborator synthesizes them using higher-order unification and κ-reduction.

## Working with holes and elaboration
- Every `_` in a term or proof registers a metavariable paired with the current local context. These are collected on the parser’s `holes` stack and emitted alongside `lemma` and `instance lemma` commands for the elaborator to solve.

## Using this guide
Before editing `.shari` files:
1. Review the lexical and grammar sections to ensure new syntax conforms to the parser.
2. Declare operators and type/class scaffolding via the documented commands rather than inventing new keywords.
3. Prefer explicit binders and instantiations when automation is insufficient, using `@` to disable auto instantiation as needed.
4. Keep track of holes emitted by proof scripts and resolve or justify them during elaboration.

Following these rules will keep generated Shari code well-formed and compatible with the existing parser and elaborator.
