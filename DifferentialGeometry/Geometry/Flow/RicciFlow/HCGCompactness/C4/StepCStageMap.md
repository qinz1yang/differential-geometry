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

## 2026-07-16 exact pointed-basepoint brick

`stageCompare_base` proves the exact identity
`stageComparisonMap ... O_k = O_l` under the existing finite-stage
`Item3GpScaleAt` hypothesis.  At the source basepoint, `seqWeights_base` makes
the actual normalized atom family the Kronecker delta at `baseIndex`;
`seqCenter_zero` and the normal-chart center/zero identities identify that
slot's direct target with the target basepoint.  The unique-center branch is
then pinned by global energy minimization.  The totalization branch already
returns the target basepoint, so the theorem does not assume existence of the
unique center.

Focused verification passed without local warnings.  The exact basepoint
producer itself is complete (100%).  The downstream common-tail packaging of
this identity is separate work.  Dedicated Step-B/B1 machinery is roughly
98%, Chapter-4 machinery roughly 90%, and whole-HCG machinery roughly 60%;
`StepB1RawInput`, textbook B1, and the final compactness endpoints remain
theorem-level 0%.

## 2026-07-16 exact subsequence stability

The map definition now has checked reindex readouts:

- `stageTarget_subseq` for direct target points;
- `uniqueCenter_subseq` for the actual global minimizing predicate;
- `stageCompare_default` for the harmless totalization branches; and
- `stageCompare_subseq` for the complete chart-independent comparison map.

The final equality does not assume definitional equality of dependent choices.
On the unique-center branch it proves that both selected points minimize the
same actual energy and invokes uniqueness; the other branches use the exact
basepoint totalization.  Focused verification and the exact module refresh
passed.

This closes the map-level persistence needed by the radius diagonal, but does
not itself prove an all-radius master subsequence.  `StepB1RawInput` and
textbook B1 remain theorem-level 0%; dedicated Step-B/B1 machinery is roughly
98%, Chapter-4 machinery roughly 90%, and whole-HCG machinery roughly 60%.

## 2026-07-18 framed stage-map migration

The canonical finite-stage map now uses the orthonormally framed normal charts
in its definition.  `stageTarget_chart` is stated with `framedTransition`,
`stageTarget_local` decodes with the framed partial-diffeomorphism inverse, and
`stageCompare_base` uses the exact framed center/origin identities.  No raw
`normalChartAt` or raw transition remains in this file, and no radius or
endpoint assumption was added.

Focused verification passed.  This restores the map-definition layer itself
to framed-green (100%).  It does not verify the downstream all-pairs chart
tail: the concrete framed `StepB1RawInput` producer and textbook B1 theorem
remain theorem-level 0%, while whole-HCG machinery remains about 60%.
