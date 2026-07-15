# HamiltonCompactness

Source used: MSM135 Chapter 3 theorem "Compactness for solutions"; MSM135 Chapter 4 was checked to identify the true proof backend.

## Current canonical route (2026-07-09)

`compactnessSol_cond` is the canonical wrapper over `solutionComp_cond`.  It
consumes `MetricCompactnessInputs`, the concrete conditional Theorem 3.9
conclusion, and `FlowUpgradeData`; it calls neither unconditional
`metricCompactness` nor any exact-conclusion backend.

This conditional consumer body is checked infrastructure.  Its upstream
conditional Theorem 3.9 endpoint remains 0%, unconditional Theorem 3.10 remains
0%, and the whole-HCG endpoint remains 0%; whole-HCG machinery is still about
45%.  The Hamilton-specific adapter still needs a real common-window source
plus limit-slice completeness/topology producers.

The live Lean file now exports only `compactnessSol_cond`.  Focused verification
of `SolutionCompactnessInputs.lean`, `SolutionCompactness.lean`, and
`HamiltonCompactness.lean` passed, and the newly exported input module received
a successful targeted refresh.  The public `HCGCompactness.lean` umbrella also
passed focused verification after the Hamilton adapter refresh.

## Removed legacy route (superseded)

> **Superseded as current instructions.**  The former `compactnessSol`,
> `solutionCompactness`, and exact-conclusion input route were deleted on
> 2026-07-09.  They are not compatibility APIs and must not be restored or used
> as a resume point.

The deleted wrapper had carried `_hinj : InjInput` and an exact-conclusion
backend.  The canonical theorem instead exposes the real
`hflowInj : FlowBaseInjBound` and concrete `FlowUpgradeData`.

The zero-callsite `hamiltonCompactness` wrapper and its arbitrary numeric
`NoncollapseInput` were removed on 2026-07-09.  Volume noncollapse now reaches
the compactness route only through the explicit CGT frontier `flowInj_of_vol`
in `NoncollapseInjectivity.lean`.

The 2026-05-27/28 review notes about the pointed Riemannian rename,
`[I.Boundaryless]`, and `_hinj` are historical context for the deleted route,
not a live API or resume point.
