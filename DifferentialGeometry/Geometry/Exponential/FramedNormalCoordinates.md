# FramedNormalCoordinates

## Purpose

`FramedNormalCoordinates.lean` packages genuine Riemannian normal coordinates
at a fixed center. It first identifies the model space with the tangent space
through the chosen `g_p`-orthonormal `normalFrame`, then applies the exponential
map.

## Status

Focused verification and the targeted module build pass. The file is
sorry-free.

- `framedExpDiffeo` is the raw exponential local diffeomorphism conjugated by
  `normalFrame`.
- `framedExpMap` is the actual global map
  `z |-> exp_p (normalFrame g p z)`; it is used when a theorem must not depend
  on the arbitrary value of a partial equivalence outside its source.
- `framedChartAt` is its inverse coordinate map.
- `framed_norm_lt_iff` proves that a model Euclidean ball is exactly the
  corresponding `g_p` tangent ball under the frame.
- `framedExp_zero` and `framedChart_centre` identify the chart center.
- `framedTransition` is the canonical overlap map
  `framedChart_q o framedExp_p`.
- `framedExp_eq_expMap` exposes the underlying exponential map.
- `mfderiv_framedExp` identifies the chart differential as the raw exponential
  differential composed with `normalFrame`.

The construction is pointwise in the center. It intentionally makes no claim
that the classically chosen frames vary smoothly with the center; the current
HCG use chooses charts at finite or discrete center families.

The Gauss-dependent source-membership bridge intentionally does not live in
this file: importing the Gauss radius layer here would create the cycle
`GaussLemmaPullback -> InjectivityRadius -> FramedNormalCoordinates`. Consumers
derive source membership from `normalFrame_sqrt` and the existing Gauss radius
lemmas at the layer that already imports both APIs.

## Next Consumer

The generic injectivity radius now uses `framedExpMap`; the remaining consumers
are `ExpBallDiffeo` and the Chapter-4 normal-coordinate input/transition layer.
Their canonical H6-facing semantics must use the same framed chart.
