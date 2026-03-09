# Obtain Instance Syntax

## Status

implemented

## Summary

Proof expressions support `obtain instance c : S := { ... }, e` for local structure introduction. The parser desugars the form into nested local field bindings plus an `obtain` from `S.abs`, so no new proof AST or elaboration rule is needed.

## Decision

- Support only ordinary `structure` targets, not `class structure` targets.
- Parse `def` and `lemma` fields with the same field-parameter sugar as top-level `instance`.
- Allow later fields to refer to earlier fields by bare field name while parsing the local instance body.
- After desugaring, only `c` and `c.field` names are in scope in the trailing body expression.
- Build the existential characteristic from structure const fields only; axiom fields are supplied as proof arguments to `S.abs`.

## Impact

- The surface syntax is user-visible and must stay documented in the language guide.
- Parser tests should pin the desugared AST shape and prior-field name resolution.
- Integration tests should cover both single-field and multi-field structures.

## Update Triggers

- Update this doc if `obtain instance` scoping, supported targets, or desugaring strategy changes.
- Update [../SHARI_LANGUAGE_GUIDE.md](../SHARI_LANGUAGE_GUIDE.md) when the syntax or visible semantics change.
