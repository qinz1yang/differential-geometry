# MetricCovDerivPullbackCross

## 2026-07-24: cross-model curvature scalar invariants

The source-realization seam now has a checked, model-independent curvature
scalar API for `Diffeomorph.pullbackMetricCross`:

- `ricciTensor_cross` transports the canonical Ricci bilinear form;
- `metricRicci_cross` packages the same result for the canonical bundled
  `(0,2)` Ricci tensor;
- `metricScalar_cross` proves scalar-curvature invariance;
- `ricciNormSq_cross` combines evaluated Ricci transport with
  `normSq0S_pullbackCross_eval_of_orthonormal`;
- `tfRicNormSq_cross` combines the preceding two scalar equalities for the
  canonical pointwise trace-free Ricci norm-square formula.

The Ricci proof traces `metricRm04Std_pullbackCross` in an orthonormal basis.
Because the two manifold models may have different definitionally presented
dimensions, the pushed basis is reindexed by the finite-dimensional linear
equivalence supplied by the diffeomorphism derivative; no dimension equality,
coordinate frame, or new consumer assumption is exposed in the public
statements.

Focused verification and the targeted producer refresh pass without local
warnings or `sorry`.  This cross-model invariant bridge and its dedicated
machinery are **100%**.  The actual theorem producing `LimitTfDecayAt L 0` from
retained CGH metric-jet convergence remains theorem-level **0%**; its dedicated
machinery is now about **70%**, with the concrete
C2-jet-to-pulled-back-Ricci convergence producer still open.  Consequently
`ham3_cgh_limit` remains theorem-level **0%**, and whole-project HCG
infrastructure remains conservatively about **60%**.

## 2026-07-16: cross-model metric tower and norm naturality

The cross-model B/C intrinsic seam is now supplied at the metric-only layer.
The checked public API consists of:

- `metricCovDeriv_pullbackCross`, transporting the full background
  metric-covariant derivative tower through a diffeomorphism between different
  manifold models;
- `metricDiffCovDerivAt_pullbackCross`, transporting the difference of two
  metric towers;
- `normSq0S_pullbackCross_eval_of_orthonormal`, transporting the pointwise
  squared norm of any already-related covariant tensor;
- `metricDerivNorm_pullbackCross`, combining the preceding results into the
  pointwise metric-difference seminorm equality.

The tower proof is the metric-valued cross-model sibling of the established
same-model induction.  Its connection-correction terms use
`metricCov_pullbackCross`; its scalar derivative term uses a private
cross-model chain-rule specialization, since the existing public scalar helper
is same-model only.  No arbitrary-base tensor naturality API and no new
endpoint assumptions were introduced.

Focused verification and the targeted producer refresh passed without local
warnings or `sorry`.
