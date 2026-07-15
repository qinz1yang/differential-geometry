# OpenSubtype

2026-06-17: Added the open-subtype restriction backend for smooth Riemannian
metrics.

What landed:

- `hasMFDerivAt_subtype_val`, `mfderiv_subtype_val`, and
  `mfderiv_subtype_val_apply`: the inclusion `Subtype.val : U -> M` for an open
  subtype has identity manifold derivative on the model tangent fiber.
- `SmoothRiemannianMetric.restrictOpenInner`: the restricted pointwise inner
  product on an open subtype, using the project convention that tangent fibers
  are model-space fibers.
- `SmoothRiemannianMetric.restrictOpen`: a smooth Riemannian metric on the open
  subtype, assuming the finite-dimensional and `SigmaCompactSpace`/`T2Space`
  instances required by the existing smooth Hom-section backend.
- `SmoothRiemannianMetric.restrictOpen_inner`: the direct inner-product formula
  `(g.restrictOpen U).inner x v w = g.inner (x : M) v w`.

This resolves the metric-layer theorem needed before using
`Diffeomorph.pullbackMetric` on comparison-map target open domains.  The HCG
consumer now uses this through `SourceDomainMetricData.ofRestrictPullback`,
combining:

- `restrictOpen` on the source limit/reference metrics;
- `restrictOpen` on the target sequence metric;
- `sourceTargetDiff` plus `Diffeomorph.pullbackMetric`;
- the `mfderiv_subtype_val_apply` formula and `sourceTargetDiff_apply` to match
  the `SourceDomainMetricData` inner-product fields.

Verification: passed for this file.

## 2026-07-10: flat nested restriction

Added `mfderiv_opens_incl` and
`SmoothRiemannianMetric.restrictOpenOfSubset` for restricting a metric on an
open carrier `U` to a smaller ambient open carrier `V ≤ U` without introducing
the nested subtype `↥(Subtype.val ⁻¹' V)`.  The evaluation theorem
`restrictSubset_inner` identifies its inner product with the one on `U` at the
open inclusion.

`restrictOpen_flat` proves that restricting an ambient metric first to `U` and
then flatly to `V` agrees with direct restriction to `V`.  Focused verification
and the explicitly named module refresh passed without warnings.  These are the
metric-level producers for restricting Step D's large-stage limit metrics and
sequence metrics to the same shrunk tail carriers.
