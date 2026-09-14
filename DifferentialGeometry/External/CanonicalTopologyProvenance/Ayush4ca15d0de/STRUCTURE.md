# Project structure

This file governs placement and dependency structure in `PoincareLean`.
`NAMING.md` governs declaration and module names, while `AGENTS.md` governs
workflow, soundness, dependency versions, and verification.

## Source layout

```text
Poincare/
  Analysis/       reusable analytic infrastructure not supplied upstream
  Geometry/       metric, curvature, and variation geometry
  Topology/       reusable topology and differential topology
  Toponogov/      the Appendix A comparison-geometry development
Poincare.lean     flat public-library aggregate
```

Put reusable mathematics in its natural subject directory. Keep
blueprint-specific assembly thin and do not copy source from the upstream
`DifferentialGeometry` dependency into this repository.

Use one file for one coherent mathematical development. Split a development
only at a genuine interface, such as definitions versus consequences, model
space versus transport, or local versus global theory. Use `Defs.lean` only
for the common definitions of a concept folder.

## Dependency direction

- Prefer precise leaf imports from Mathlib and `DifferentialGeometry`.
- Keep foundational topology independent of metric geometry.
- Keep foundational metric and curvature modules independent of high-level
  comparison arguments.
- Allow `Poincare/Toponogov/` to consume reusable analysis and geometry.
- Keep imports acyclic and register completed public leaves in
  `Poincare.lean`.

## Project records

- `PROJECT_CONTEXT.md` records pinned dependencies and the mathematical
  blueprint.
- `FORMALIZATION_STATUS.md` is the Appendix A completion ledger.
- Appendix-specific status files distinguish proved Lean results, proposed
  interfaces, imported classical inputs, and informal arguments.
