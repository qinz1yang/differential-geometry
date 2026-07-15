# StepCStageMap.lean - canonical finite-stage comparison map

## 2026-07-15 checked definition layer

`stageTarget` is the direct source-stage normal-chart readout interpreted in
the corresponding target-stage normal chart.  It is total because the partial
equivalence coercions are total; geometric claims are made only after the
normal-domain hypotheses are available.

`HasUniqueStageCenter` states that the actual normalized stage weights and
direct targets have one global target-manifold energy minimizer.
`stageComparisonMap` uses that minimizer on the existing closed source ball and
the target basepoint outside it or when uniqueness fails.  No
source chart selector or glued limit weight occurs in the definition.

`stageTarget_chart` records the direct source-transition/target-transition
formula.  `stageTarget_local` decodes that expression back to the same manifold
point once the existing target-chart source condition is supplied, and
`stageCompare_choose` exposes the selected minimizer on the controlled source
ball.  Focused verification and the exact downstream stage-comparison target
refresh passed.

The canonical definition/choice seam is complete (100%), but the all-pairs
chart-convergence theorem for this map is still unstated and 0%.  Consequently
the concrete `StepB1RawInput` producer and textbook B1 theorem remain 0%.
