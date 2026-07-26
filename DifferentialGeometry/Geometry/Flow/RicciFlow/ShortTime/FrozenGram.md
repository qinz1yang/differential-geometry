# FrozenGram

## Purpose

This is the concrete bridge from `IsLowRegCoeff.elliptic` to the frozen
Euclidean heat kernel.  At each active chart point it constructs the positive
square-root continuous linear equivalence of the chart inverse-Gram matrix.

## Source-level facts implemented

- the inverse-Gram matrix is positive definite, proved directly from the
  existing positive lower ellipticity constant;
- the double-sum ellipticity inequalities are rewritten as Euclidean inner
  product inequalities;
- applying the frozen equivalence twice gives the inverse-Gram matrix action;
- all forward maps have norm at most `√D.ellMax`;
- all inverse maps have norm at most `(√D.ellMin)⁻¹`.

Thus the anisotropic cancellation constants depend only on the uniform family
coefficient package, not on the metric index or frozen point.

## Verification state

Source-only implementation.  It has not been focused-checked because a
concurrent named build owns the shared Lean build lane.  Once that lane is
available, check `HeatKernelSPD.lean` first and this file second.

The next geometric producer must supply a nested outer cutoff equal to one on
a uniform neighbourhood of each active POU support.  Gaussian convolution is
not compactly supported, so chart reconstruction cannot use bare zero
extension; the outer cutoff is required before pulling the smoothed component
back with the existing `secModelPull`/`tensorChartBasisElement` pattern.
