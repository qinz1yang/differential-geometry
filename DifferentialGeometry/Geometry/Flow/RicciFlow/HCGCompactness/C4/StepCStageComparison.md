# StepCStageComparison.lean - local identification of the global stage map

## 2026-07-15 checked identification seam

`uniqueStage_of_fill` proves that a local `CenterInput` for any active-filled
version of the actual direct stage targets supplies
`HasUniqueStageCenter` for the original finite-stage energy.  The proof routes
through energy invariance at zero-weight slots, so every local implicit branch
is identified through the same global minimizer.  It never compares local limit
weights across overlapping source charts.

`stageCompare_eq_cm` completes the identification: on the controlled source
ball, the global `stageComparisonMap` equals the `centerOfMass` selected from
any such filled local input.  The equality follows from global minimizer
uniqueness and is independent of the proof object used by the map definition.

Focused verification and the exact stage-comparison target refresh passed.
This proof-choice-independence seam is complete
(100%).  It does not provide a smooth active-slot filler, a moving common-domain
implicit solver, or an all-pairs chart tail.  Those are the current analytic
frontiers; `StepB1RawInput` and textbook B1 remain theorem-level 0%.
