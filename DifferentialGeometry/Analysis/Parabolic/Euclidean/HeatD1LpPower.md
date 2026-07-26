# HeatD1LpPower

## Purpose

This file provides the real-power spatial mass and exact parabolic scaling of
the first heat-derivative majorant used in the late Koch--Lamm flux estimate.

## Source content

- `baseD1Maj_sq_int` and `baseD1Maj_rpow` prove integrability for
  `1 ≤ p ≤ 2` without assuming a non-existent closed formula for a fractional
  Gaussian moment.
- `heatD1MajPow_int` evaluates the scaled mass by dilation.
- `heatD1Pow_scale`, `heatD1Pow_int_eq`, and `heatD1Pow_shift` isolate the
  exact time exponent `((n(1-p)-p)/2)`.

Focused verification passes with no local warning.  The source contains no
`sorry`, `admit`, axiom, or opaque replacement.  This is analytic machinery
for one heat-map arm; the forward Ricci-flow uniqueness endpoint remains 0%.
