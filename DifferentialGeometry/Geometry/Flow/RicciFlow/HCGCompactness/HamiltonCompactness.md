# HamiltonCompactness

Source used: MSM135 Chapter 3 theorem "Compactness for solutions"; MSM135 Chapter 4 was checked to identify the true proof backend.

## Current canonical route (2026-07-17)

`compactnessSol_cond` is the canonical wrapper over `solutionComp_cond`.  It
consumes `MetricCompactnessInputs`, the concrete conditional Theorem 3.9
conclusion, and `FlowUpgradeData`; it calls neither unconditional
`metricCompactness` nor any exact-conclusion backend.

This conditional consumer body is checked infrastructure.  Conditional
Theorem 3.9 is now checked, while the P4 producer remains open.

The file now also states the genuine target `compactnessSol`.  Its time-domain
hypothesis is the literal book domain
`X.D = RealTimeInterval.openInterval α b 0 h0`; no endpoint/exhaustion
predicate is introduced.  Its remaining inputs are completeness, compact-time
curvature bounds, the genuine time-zero basepoint injectivity-radius bound, and
connectedness.  The compact-window curvature input is a locally uniform
strengthening of the book conclusion from a weaker hypothesis than one global
constant on the whole open interval.

The target conclusion now explicitly includes completeness of every limit
time-slice.  This strengthens only `compactnessSol`; the generic
`CompactnessConclusion` remains unchanged because it has existing consumers.
There were no `compactnessSol` call sites to migrate.  The proof body now
checks the first real reduction, `CompleteInput.at_time` at `t = 0`, before the
remaining explicit `sorry`.  This extraction is not yet an all-time limit
completeness proof: a checked bounded-curvature propagation/limit producer is
still required for the final `∀ t ∈ X.D.carrier` conclusion.  Theorem-level
completion remains 0%; dedicated P4
machinery is about 88% and whole-HCG machinery about 60%.  Focused verification
is green, with the expected warning at the one visible theorem-level `sorry`.

The generic carrier-capable `CompactnessConclusion` and conditional consumers
remain unchanged.  This is intentional: the Hamilton blow-up adapter separately
uses scalar convergence at the nonregular carrier endpoint `t = 0`.

## Removed legacy route (superseded)

> **Superseded as current instructions.**  The former exact-conclusion-backed
> `compactnessSol`/`solutionCompactness` route was deleted on 2026-07-09 and
> must not be restored.  The current `compactnessSol` reuses only the name: its
> statement is the honest open-interval MSM135 theorem and its unproved P4 body
> remains visible.

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
