# NormalFrame

## Purpose

`NormalFrame.lean` supplies the pointwise linear normalization implicit in
Riemannian normal coordinates. At each center `x`, `normalFrame g x` maps the
fixed model inner-product space to a chosen `g_x`-orthonormal tangent basis.

## Status

Focused verification passes without warnings. The file is sorry-free.

- `normalBasis_inner` proves the chosen tangent basis is `g_x`-orthonormal.
- `normalFrame_basis` identifies the image of the fixed orthonormal basis.
- `frameMetric_eq` proves the full pulled-back bilinear form is `innerSL Real`.
- `normalFrame_inner` is the pointwise isometry formula consumed by H6.
- `normalFrame_normSq` and `normalFrame_sqrt` identify the Riemannian radial
  norm with the fixed model norm exactly.

The construction uses the existing `tangentMetricData_gen` metric-core bridge
and does not add an assumption or a new typeclass instance. No smooth dependence
on the center is claimed or needed for the HCG finite/discrete center families.

## Lean Notes

`LinearEquiv.toContinuousLinearEquiv` is available because both spaces are
finite-dimensional. Equality of the pulled-back bilinear forms is proved by
extensionality on `stdOrthonormalBasis`; direct rewriting first has to expose
the underlying `LinearMap` coercions.

## Consumer Status

`FramedNormalCoordinates.lean` now conjugates the exponential chart and inverse
chart by this same frame and proves the exact radial-ball correspondence. The
remaining HCG work is to migrate the shared injectivity-radius and normal-metric
consumer interfaces to those framed coordinates. Using `normalFrame` only in
the metric estimate while retaining raw chart coordinates would be
inconsistent.
