# NormalMetricExtend

## Role

This file turns the named normal-coordinate smoothness ball into an honest
cross-model `C∞` partial diffeomorphism, realizes the pullback metric, and
extends it to a total model-space metric by a buffered cutoff.

## Current state

- `normalBall` is the ball of radius `expRadiusGp`.
- `normalExpPD` upgrades `framedExpDiffeo` and `framedChartAt` to a
  `PartialDiffeomorph … ∞` on that ball.
- `normalImage` is its open image.
- `normalBallDiffeo` packages that restriction using the general cross-model
  opens API.
- `normalMetric` pulls the ambient metric back to the ball, and
  `normalMetric_inner` identifies it with `normalCoordMetric`.
- `normalCut` is one on the quarter-radius ball and has topological support in
  the half-radius closed ball.
- `normalTotal` bump-extends `normalMetric` against the flat model metric.
- `normalTotal_inner` identifies the total metric with `normalCoordMetric` on
  the quarter-radius ball, leaving an open neighborhood suitable for later
  derivative and Koszul locality arguments.
- `normalTotal_eq` packages that equality at the coefficient-field level.
- `normal_cov_eq` consumes the neighborhood-local Levi--Civita/Koszul theorem
  and identifies constant-field covariant derivatives for `normalTotal` with
  the raised normal-coordinate Koszul vector.
- `normal_cov_eq_fderiv` gives the corresponding moving-field formula:
  Frechet derivative plus the raised normal-coordinate Koszul correction.

Focused verification and the framed exact module refresh passed. No new
`sorry` or `admit` was introduced.

## Frontier

The local pullback and total-extension producer is complete on the framed
radius.  The live migration frontier is downstream: refresh
`NormalMetricLocal`, then convert only the branch consumers whose public
statements still expose raw normal-coordinate maps.  Do not replace that work
with an endpoint radius assumption or a parallel connection hierarchy.

The positive-Hessian and `StrictDistInput` producers remain unstated and are
therefore each 0% complete.  Their selected-branch Hessian/Neumann/strict-IFT
support machinery is complete.  Step B/B1 machinery is approximately 90%,
Chapter 4 machinery approximately 83%, and the whole HCG compactness
infrastructure approximately 55%.  All textbook endpoint theorems remain 0%.
