# SolutionCompactnessInputs

This file is the canonical conditional MSM135 Theorem 3.10 handoff.

`solutionComp_cond` imports the completed conditional Chapter 4 endpoint from
`MetricCompactnessEndpoint.lean`, applies
`MetricCompactnessInputs.metricCompactness` at time zero, and then consumes
`FlowUpgradeData` for that exact metric compactness conclusion.  It does not
call the unconditional `metricCompactness` frontier and does not consume the
legacy `SmoothFlowLimitInput.upgrade` field.

Focused verification passed after the endpoint-layer import move.  This
conditional wrapper is a 100% checked consumer.  Its Theorem 3.9 dependency is
now the 100%-checked explicit-input endpoint; the concrete P4 `FlowUpgradeData`
producer remains a separate input.  Unconditional Theorem 3.10 and
`ham3_cgh_limit` remain theorem-level 0%.

Accounting must stay separated: the conditional wrapper does not discharge the
unconditional CGT/Bishop--Gromov/[H6] inputs, and it does not turn the remaining
P4 producer into an unconditional Ricci-flow compactness theorem.  Current
rounded estimates are about 95% for Chapter 4 machinery and 60% for whole-HCG
machinery.
