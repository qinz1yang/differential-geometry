# EndpointMetricLimit

## Role

`exists_endMetric` is the G3 endpoint-metric producer for the direct BBS
endpoint route. It combines arbitrary-order fixed-reference tail bounds with
`metricPreconvFull`, then identifies the extracted smooth subsequential metric
with every scalar chart-Gram left limit using the Ricci-flow time equation.

## Current state

Focused verification passed. The theorem proves full left convergence of every
chart-Gram entry to one smooth endpoint metric. This completes G3 itself, but
does not by itself prove Ricci convergence at the endpoint (G4), construct
`CinftyLimitData`, or close the Hamilton maximal-flow endpoint.

Targeted export and a fresh axiom probe remain unavailable because the actively
modified Spectral module `GalerkinLimitUniformMass` has no exported object file.
This external cache blocker does not invalidate the earlier focused check, but
G3 is not yet certified axiom-clean on the live tree.

## Route

For each spatial derivative order, `covTailBoundSol` gives a bound on a
possibly order-dependent tail. `cov_bdd_of_eventual` absorbs the finite initial
part of a chosen time sequence. `metricPreconvFull` then extracts a smooth
subsequential limit. On a fixed inner tail, `movingShiBoundN` and pointwise
tensor Cauchy--Schwarz bound each chart-Gram time derivative. Hence every entry
has a full left limit, and uniqueness of limits identifies it with the smooth
subsequential metric.

## Honest accounting

`exists_endMetric` is a dedicated G3 producer: theorem 100%, dedicated G3
machinery 100%. G4 is now independently proved and axiom-clean.
`cinftyLimitData_of_allMBounds` remains 0% until the combined producer verifies.
