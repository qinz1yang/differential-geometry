# Shi cutoff data

## 2026-07-23: smooth and barrier interfaces

`ShiCutoffData` was moved unchanged from `BernsteinComplete.lean` into this
route-neutral data module.  The existing smooth Bernstein consumer therefore
keeps its public input and proof unchanged.

The Route B-prime interfaces are now checked:

- `ShiCutoffLowerSupportAt` stores a selected smooth lower support and only the
  local differential inequalities used at a positive cutoff contact point;
- `ShiBarrierCutoffData` requires a fixed compact support for each cutoff,
  exhaustion only at the selected center, compact-cylinder continuity, and
  local lower supports only where the cutoff is positive;
- `ShiCutoffData.toBarrierAt` turns every existing smooth cutoff family into
  barrier data at an arbitrary chosen center.

The consultation displayed `ShiCutoffLowerSupportAt` as a `Prop` structure.
That cannot carry the selected function `phi` in Lean, so the checked
interface is a data structure in `Type`.  Its separate pointwise spatial
differentiability field was omitted: the neighborhood field supplies it via
`Eventually.self_of_nhds`, giving a strictly weaker reusable input.

Focused and exact targeted verification passed with no local diagnostics.
These declarations are complete (100%).  They are only the Route B-prime data
boundary: the solution-generated Calabi barrier cutoff and the barrier
Bernstein capstone are both still unstated/unproved (0%).  Dedicated Route
B-prime machinery is about 15--20%; unconditional `compactnessSol` remains
theorem-level 0%, and whole-project HCG supporting machinery remains about
60%.
