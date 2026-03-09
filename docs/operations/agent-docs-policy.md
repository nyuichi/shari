# Agent Docs Policy

## Purpose

This document defines how agents should treat repository documentation so that `AGENTS.md` stays small and `docs/` remains the source of truth.

## Source Of Truth

- `AGENTS.md` is the entrypoint. Keep it short and route readers into `docs/`.
- `docs/README.md` is the index for durable documentation.
- `docs/SHARI_LANGUAGE_GUIDE.md` is the source of truth for Shari surface syntax, proof constructs, and command behavior.
- `docs/design-docs/*.md` record implementation decisions, constraints, and tradeoffs for specific features.
- `docs/operations/*.md` record maintenance workflow, update routing, and documentation policy.

## Naming And Placement

- Keep operational guidance under `docs/operations/`.
- Keep feature design records under `docs/design-docs/` with lowercase kebab-case filenames.
- Keep design doc titles descriptive and stable; rename files only when the topic changes materially.
- Do not store environment-specific absolute paths in docs.

## Design Doc Template

Every file in `docs/design-docs/` must include these top-level sections in this order:

1. `## Status`
2. `## Summary`
3. `## Decision`
4. `## Impact`
5. `## Update Triggers`

Allowed status values:

- `draft`
- `proposed`
- `implemented`
- `superseded`

If a design doc is superseded, keep the file and add a `Replacement:` line under `## Status` that links to the new source of truth.

## Update Triggers

- Update `AGENTS.md` only when the entrypoint rules or doc map change.
- Update `docs/operations/*.md` when maintenance workflow, ownership, or update routing changes.
- Update `docs/SHARI_LANGUAGE_GUIDE.md` when grammar, keywords, parser behavior, elaboration behavior visible to `.shari` authors, or proof-writing guidance changes.
- Update the matching design doc when implementation strategy, invariants, or accepted tradeoffs change.
- When grammar or keyword changes land, update the language guide, VS Code syntax, and playground highlighter in the same change.

## Stale Doc Rules

Treat documentation as stale when any of the following is true:

- Code changes invalidate a documented behavior and the relevant doc was not updated in the same change.
- A design doc describes a rejected or replaced approach but is not marked `superseded`.
- `AGENTS.md` carries detailed knowledge that belongs in `docs/`.
- `docs/README.md` does not point to a current operations doc or design doc.

## Archive Rules

- Prefer marking old design docs as `superseded` over deleting them when they explain historical reasoning that still informs the codebase.
- Delete a doc only when its content is fully duplicated elsewhere and no process or index links to it.
- When moving docs, update all internal links in the same change so the index remains complete.
