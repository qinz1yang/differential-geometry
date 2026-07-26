# MetricCovDerivMetric

## 2026-07-16

`metric_tower_conv` is proved and focused-green.  For two smooth
bilinear-form families converging to the same coercive limit metric, it proves
compact-open smooth convergence to zero of every finite `iterCovComp` tower of
their coefficient difference, using the first family's Levi--Civita
Christoffel coefficients.

The proof reuses the proof-independent `MetricKoszul.raisedKoszulOp_conv` and
`raisedOp_smooth`, projects the raised operator through one fixed basis, forms
the coefficient difference by pairing and a fixed continuous linear map, and
then calls `iter_comp_zero`.  It introduces no new geometric, radius, or
endpoint assumption and does not create a second Christoffel API.

This generic metric-to-component-tower bridge is complete.  The next frontier
is the C4 consumer that identifies the actual pullback coefficient field,
realizes these components as the intrinsic covariant-derivative tower, and
converts the finite component bounds to `tensor02CovDerivNormWith`.  That
consumer remains unstated here (0%).  `StepB1RawInput` and textbook Step B1
remain theorem-level 0%; the dedicated B/C machinery is approximately 98%,
while concrete raw-record field closure remains approximately 60%.
