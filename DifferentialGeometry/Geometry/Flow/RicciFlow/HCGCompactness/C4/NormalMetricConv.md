# NormalMetricConv

## 2026-07-18 canonical framed-radius migration

The two phase-ball containment proofs in `exists_live_metric` and
`exists_slot_metric` now use `expRadiusGp`, its quarter-radius, and
`expRadiusGp_pos`.  This directly matches `phaseRadius_exp` and the live
`StepBLocalMetrics` convergence producers; no implication back to the old raw
`expMapC2Radius` was introduced.

Focused verification and the exact module refresh are green.  The
`NormalLiveConv`/SupportCapstone downstream validation remains the coordinated
next step.  `MetricCompactBase.exists_b1_raw` has a complete source proof body but
still awaits the full framed dependency validation.  The separately named
textbook B1 theorem and unconditional endpoints remain theorem-level 0%; the
rounded machinery estimates remain B1 95%, C4 87%, whole HCG 60%.

## 2026-07-16 slotwise phase-ball diagonal

`MetricCompactnessInputs.exists_slot_metric` extracts one strict subsequence
for the finite live-slot family even though each slot uses its own phase ball
`phaseRadius (rInf alpha + 1)`. It retains limit smoothness, two-sided metric
equivalence, and the all-stage center-distance bound on that same subsequence.

Focused verification and the targeted refresh passed. This is finite
subsequence packaging, not a new analytic assumption. `StepB1RawInput` and
textbook B1 remain theorem-level 0%.
