# H0 fill log

2026-09-26. Brick H0 (class-free per-history scalar floor) delivered in the new file
`Surgery/Topology/HistoryScalarFloor.lean` (imports `ReducedVolumeTruncation`; nothing else edited).

- Barrier: `scalarLowerBarrier_le_on_slab` (`Extinction/Families/SlabScalarLowerBarrier.lean:95`) applied to
  the time-shifted flow `S.timeShift a` at base time 0. The slab wrappers `incomingSlab_/closedSlab_scalarLowerBarrier_le`
  need an initial floor of the form `-3/(2(a+c))`, unreachable when `a` is large and the stage floor
  very negative; the shift removes that. Closed end of `finalSlab` by `le_on_closure` + `scalarCont`.
- Stage floors: `exists_initialScalarBarrier_of_compact` per stage (empty carrier split), `b := 1 + Σ 3/(2cᵢ)`.
- Stated on every `stageDomain` (half-open incoming slabs, closed final slab, degenerate final point).
- Compile: `ReducedVolumeTruncation` has no olean; verified on a scratch concatenation (truncation file +
  this file) with `lake env lean`, 0 errors/warnings, also with the Mathlib standard linter set on.
- Axioms of all three history theorems: propext, Classical.choice, Quot.sound.
- Note for lead: `ObservedHistory.exists_stageMetric_scalar_lower_bound` (cutoff records) is now a
  special case of `ObservedHistory.exists_stageMetric_scalar_ge`; consider retiring it and the
  `_of_inCutoffClass` wrappers.
