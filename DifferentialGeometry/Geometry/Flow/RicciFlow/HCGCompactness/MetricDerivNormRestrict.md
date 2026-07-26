# MetricDerivNormRestrict

## 2026-07-16 constant-frame component restriction

The generic theorem `iterCovComp_restrict` now identifies a constant-frame
component tower on an open subtype of the model space with the ambient tower
at the underlying point.  The only analytic premise is pointwise
differentiability of each ambient running component, exactly what an existing
smooth tower supplies; no metric, normal-coordinate, or branch-specific
assumption enters the restriction layer.  The successor step uses
`extDerivFun_restrictOpen`, while the Christoffel and lower-level correction
terms reduce by the induction hypothesis.

Focused verification passed without warnings.

## 2026-07-13 short-time alignment

The pointwise difference-tower restriction proof now evaluates subtraction
with the public `Tensor0SSpace.sub_apply` theorem instead of rewriting the
underlying multilinear-map representation.  Its public statement is unchanged,
and focused verification passed without warnings.

## 2026-06-21

This file isolates the open-subtype restriction bridge needed between fixed-window
P3 convergence and the source-domain seminorms for the P4 upgrade.

What is verified:

- `metricCovDeriv_zero_restrictOpen_apply` proves the order-zero tower base.
  At order zero the covariant tower is just the metric tensor field, so metric
  restriction closes directly.
- `metricCovDeriv_restrictOpen_apply` proves all-order open-subtype naturality
  for `metricCovDeriv`.  The successor step uses the section-slot evaluation
  formula from `MetricCovDerivLinear.lean`, the scalar restriction derivative
  from `OpenSubtypeNaturality.lean`, and the open-subtype Levi-Civita
  global-section bridge from `OpenSubtypeNaturality.lean`.
- `metricDiffCovDerivAt_restrictOpen_apply` packages the all-order result for
  the pointwise tensor difference.
- `normSq0S_restrictOpen_apply` proves tensor-norm invariance by choosing an
  ambient `g`-orthonormal tangent basis via `exists_gOrthonormalBasis`; the
  same basis is orthonormal for `g.restrictOpen U`, and both sides reduce to
  the same finite component sum with `normSq0S_identity_eq_sum_sq`.
- `metricDerivNorm_restrictOpen` is proved from the tensor-difference and norm
  bridges.

Verification passed.  The public endpoint and the main producer lemmas are
axiom-clean with only the standard `[propext, Classical.choice, Quot.sound]`
dependencies.
