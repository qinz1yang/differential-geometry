# NormalMetricExtend

## Role

This file turns the named normal-coordinate smoothness ball into an honest
cross-model `C∞` partial diffeomorphism, realizes the pullback metric, and
extends it to a total model-space metric by a buffered cutoff.

## Current state

- `normalBall` is the ball of radius `expMapC2Radius`.
- `normalExpPD` upgrades the restricted exponential and normal chart to a
  `PartialDiffeomorph … ∞`.
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

Focused verification of the complete file passed without local warnings after
the exact `MetricKoszul` artifact was refreshed. No new `sorry` or `admit` was
introduced.

## Frontier

The next brick is to identify the selected inverse tangent field with its
normal-coordinate moving-field germ, then transport the connection through
`normalBallDiffeo`.  The live API already supplies pullback-cross and open-
subtype restriction theorems; the smallest possible missing producer is
Levi--Civita locality under equality of metric germs.  Do not replace that
with an endpoint radius assumption or a parallel connection hierarchy.

The positive-Hessian and `StrictDistInput` producers remain unstated and are
therefore each 0% complete.  Their selected-branch Hessian/Neumann/strict-IFT
support machinery is complete.  Step B/B1 machinery is approximately 90%,
Chapter 4 machinery approximately 83%, and the whole HCG compactness
infrastructure approximately 55%.  All textbook endpoint theorems remain 0%.
