# StepCStageSeed

## 2026-07-16 radius-independent stage seed

`IsStableNet` names the existing pairwise `B`-intersection stability property.
`HasStageRefine` is the transparent existential payload for one construction
radius, ending at the already checked `HasStageJetData`.  `HasStageSeed`
chooses one stable net and retains a refinement procedure for every later
stable net over the same `MetricCompactnessInputs`.

The checked producer chooses the minimizing scale, the large construction
divisor, `MetricCompactnessInputs`, its proper metrics, and one stable `L0`
exactly once.  Its retained refinement works for every stable `L` over that
same input and every nonnegative radius, then returns the existing
`HasStageJetData` payload.  It reuses the fixed-input support, selected-center,
diagonal convergence, metric convergence, stage-jet, and exact-basepoint
producers; it adds no endpoint field or radius assumption.

The intended recursive-radius consumer uses `HasStageSeed.subseq`; stability
of each further strict refinement is supplied by the existing
`NetLimitData.stable_subseq`.  No master radius diagonal is asserted here.

At the 2026-07-16 pre-framed snapshot, focused verification and the exact
module refresh passed with no `sorry`; the current status is recorded below.
The seed theorem is complete (100%).  The recursive integer-radius master
diagonal remains a separate unstated/proof frontier (0%), and
`MetricCompactBase.exists_b1_raw` and the
textbook Step B1 endpoint remain unproved (0%); this file is dedicated
producer machinery, not endpoint completion.

## 2026-07-18 canonical framed migration focused and exact green

Inside `MetricCompactBase.exists_stage_seed`, the frozen-stage local chart
`chi` now uses `NormalCoordinates.framedChartAt`.  The two calls to the HCG
`normalTransition` API are deliberately unchanged: that canonical alias now
delegates to `framedTransition`.  The retained scale package already uses
`expRadiusGp`, so no radius conversion, compatibility wrapper, or new
assumption was introduced.

The one-line source migration and scoped diff review are complete.  After the
canonical `StepCStageComparison` and geodesic/injectivity artifacts were
refreshed, this file passes focused Lean verification with no local diagnostics.
Its own exact target refresh also completed successfully in the coordinated
Stage-DAG write chain.

The seed proof body is canonical-framed focused- and exact-green.
`MetricCompactBase.exists_b1_raw` likewise has a complete proof body but is not
yet fully validated through the framed chain.  The separately named textbook
B1 theorem and the unconditional compactness endpoint remain theorem-level 0%;
whole-HCG machinery remains about 60%.
