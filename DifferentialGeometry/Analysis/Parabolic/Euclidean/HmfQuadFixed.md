# HmfQuadFixed status

## Source theorem

`quad_fixed` feeds the exact three-arm state-dependent quadratic source into
the clean `HmfCoreData` Banach theorem.  The realized nonlinear equation keeps
the actual coefficient `Q z (path u z)`; it is not replaced by a prescribed
coefficient.

With base bound `K / 2`, the two gradient-difference arms cost `K * R`.  The
state-difference contributions cost `3 * L * R^2`, so the exact total rate is

`4 * eps + K * R + 3 * L * R^2`.

The conclusion gives a unique fixed point in the closed rough ball, zero
trace, the untruncated Duhamel equation, and the path, weighted-gradient, and
gradient-Carleson bounds.

## Dependency boundary

This file imports only `HmfFixedCore` and `HmfStateQuad`.  It does not import
`HmfRoughMap` or `HmfRoughFixedPoint` and therefore does not reuse the older
prescribed-quadratic realization.

## Verification

The source is complete with no placeholder.  Focused Lean verification and
the named exported-module build are GREEN with no local warning.  The build
replays only two pre-existing style warnings from `RoughCarleson.lean`.  This
is analytic machinery only:
the geometric coefficient realization, rough heat-potential producer, and
`ricci_flow_forward_unique` remain unproved, so that endpoint is still 0%.

Honest accounting: this abstract fixed-point package is 100% proved and
Lean-verified; both analytic endpoint theorems remain theorem-level 0%.
