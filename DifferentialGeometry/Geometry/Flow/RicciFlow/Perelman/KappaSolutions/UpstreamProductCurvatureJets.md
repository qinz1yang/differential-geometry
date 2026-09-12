# UpstreamProductCurvatureJets

Three explicitly deferred general curvature-jet identities (`sorry`), in the style of
`UpstreamRiemannianProduct.lean`. They are the only admitted statements of the
rank-one terminal branch written in this batch.

- `curvDerivNorm_pullbackMetricCross` — naturality of `curvDerivNorm` under a global
  cross-model diffeomorphism.
- `curvDerivNorm_le_product_real_of_inner_eq` — the curvature jets of a Riemannian
  product `h + b ds²` on `M × ℝ` dominate those of the factor `h`. The constant line
  scale `b > 0` is carried explicitly: the consumer applies it with `b = R(q)` after
  rescaling the three-dimensional metric, which scales the line factor as well. Using
  the `b = 1` shape would have forced a rescaling diffeomorphism of the `ℝ` factor.
- `curvDerivNorm_liftedMetric` — invariance of `curvDerivNorm` under the native
  universal covering `UniversalCover.proj`.

## Why deferred

Searched before stating (2026-09-11): the tree has **no** naturality statement for
`HCGCompactness.curvCovDeriv` at any order. `curvCovDeriv` occurs only in
`Compactness/CheegerGromov/Pointed/BoundedGeometry.lean` (its definition),
`Connection/LeviCivita/Curvature/Sections.lean`, `Curvature/Bianchi.lean`,
`Curvature/CurvatureOperator/{CovariantDerivativeTower,DifferentiatedPalatini,
PointwiseCurvatureDerivative}.lean`, `Flow/RicciFlow/Compactness/Bounds/*` and
`Perelman/CanonicalNeighborhood/Chapter25Theorems.lean`; none of these is a pullback,
product or covering identity. What exists is only order zero, plus the *metric*-jet
tower:

- `Geometry/Metric/Convergence/PullbackCross.lean`: `metricCovDeriv_pullbackCross`,
  `metricDerivNorm_pullbackCross`, `metricScalar_cross`,
  `normSq0S_pullbackCross_eval_of_orthonormal` (metric jets and order-zero curvature).
- `Geometry/Curvature/PullbackNaturalityCross.lean`: `metricRm04Std_pullbackCross`.
- `Geometry/Metric/UniversalCover/Curvature.lean`: `UniversalCover.metricRm_lifted`
  (order zero, proved through chart curvature coefficients); the lane wrappers
  `UniversalCoverCurvatureNorm.metricRm04_lifted_apply`, `metricRmNormSq_lifted`.
- `UpstreamRiemannianProduct.metricRm04At_product_real_of_inner_eq` — the order-zero
  product identity, itself an admitted `sorry` in the tree.

So the product statement is deferred a fortiori (its order-zero case is deferred), and
the two naturality statements would each need a fresh induction over `totalNabla0S`
for the curvature tower, in the covering case for a *local* diffeomorphism, for which
the tree has no framework at all. This is outside a bounded job, hence the owner's
interface rule applies.

## If they are proved later

`curvDerivNorm_pullbackMetricCross` is the closest to feasible: mirror the induction of
`metricCovDeriv_pullbackCross` with the reference connection `metricCov g` in place of
`lcConn gRef`, base case `metricRm04Std_pullbackCross`, and finish the norms with
`normSq0S_pullbackCross_eval_of_orthonormal` exactly as `metricDerivNorm_pullbackCross`
does. `curvDerivNorm_liftedMetric` additionally needs the local-isometry version of that
induction (the covering projection has `mfderiv = id` by
`UniversalCover.hasMFDerivAt_proj`, and `liftedMetric g |>.inner x' = g.inner (proj x')`
by `rfl`). The product statement should follow the eventual proof of the order-zero
`UpstreamRiemannianProduct` identity.
