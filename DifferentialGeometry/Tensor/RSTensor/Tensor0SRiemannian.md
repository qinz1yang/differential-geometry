# Tensor0SRiemannian

## 2026-05-12: Heartbeat audit

- Removed the local `maxHeartbeats` bump from `coordInner0S_succ_eq`.
- The proof checks at the default heartbeat budget.
- Verification passed.

## 2026-05-12: Linear trace coordinate formula

- Added `linearMap_trace_eq_sum_inv_inner_apply`.
- The theorem expresses `LinearMap.trace A` as the double contraction
  `sum_i sum_j gInv i j * g(A e_i, e_j)`.
- This is the algebraic trace bridge needed by `Operators/HessianTrace.lean`.

## 2026-05-12: Trace nonnegativity

- Added `linearMap_trace_nonneg_of_metric_inner_apply_self_nonneg`.
- This is the finite-dimensional metric linear algebra needed by
  `Operators/LaplacianMinimum.lean`: if the metric quadratic form
  `g(A v, v)` is nonnegative for every tangent vector, then
  `LinearMap.trace A` is nonnegative.
- The proof installs the inner-product structure induced by
  `tangentMetricData g x`, rewrites trace as the orthonormal-basis inner sum,
  and applies termwise nonnegativity.
# Tensor0SRiemannian

## 2026-05-15 namespace qualification for tensor metric frontier

Worked:

- Planned the dependency repair for the tensor metric compatibility frontier by
  qualifying the DifferentialGeometry metric type and using the existing
  `Tensor0SBundle.TotalNabla0SRealizes` namespace.

Verification passed for the focused file check and targeted tensor module
build; this pass only unblocked imports and did not attempt the `sorry`
frontier.

## 2026-05-15 namespace blocker cleared

- Replaced the stale `TensorLieDeriv.TotalNabla0SRealizes` references with the
  root-level `TotalNabla0SRealizes` API exposed by the higher-order nabla file.
- Verification passed with the existing intentional theorem frontier still
  reported as a `sorry`.

## 2026-05-15 induced tensor metric compatibility frontier

- Added `Tensor0SBundle.inner0S_two_metricCompatible_extDerivFun`, the precise
  lower-layer statement needed by the `(0,2)` Bochner norm product rule.
- Verification passed for `Tensor0SRiemannian.lean`, with this theorem left as
  the single explicit frontier.
- The remaining proof is the induced tensor-metric compatibility bridge:
  tangent metric compatibility plus `TotalNabla0SRealizes` should imply
  compatibility of `inner0S g x 2` with total covariant derivatives. This is a
  missing tensor metric/nabla API lemma, medium-hard, and still expected to be
  solvable without user intervention.

## 2026-05-15 cotangent compatibility blocker

- Rechecked the induced tensor metric frontier and sharpened the obstruction.
- The natural proof starts with the cotangent identity
  `X <alpha, beta> = <nabla_X alpha, beta> + <alpha, nabla_X beta>`.
- The available `Connection.metric_compatible_apply` only applies to tangent
  vector fields.  To use it for one-forms, the proof must first know that
  `fun y => cotangentSharp g y (alpha y)` is differentiable/smooth as a tangent
  field, and then identify its covariant derivative with the sharp of
  `nablaAlpha`.
- No existing DifferentialGeometry API exposes that sharp-field differentiability or the
  induced cotangent compatibility theorem.
- Verification passed with the same single Lean frontier still visible.
- Frontier assessment: missing induced cotangent metric-compatibility API.  This
  is medium-hard local tensor/connection infrastructure, not Bochner algebra or
  Ricci-flow geometry. It should be solvable without user intervention, but it
  needs a real cotangent-sharp smoothness/duality bridge first.

## 2026-05-15 cotangent sharp commutation partial closure

- Added a point-vector evaluation helper for `TotalNabla0SRealizes`, local to
  this file, by extending the tangent vector to a smooth section.
- Proved `cotangentSharp_cov_eq_sharp_curry_of_mdiffAt`: under differentiability
  of the sharped one-form field, metric compatibility implies
  `nabla_X (alpha#) = (nabla_X alpha)#`.
- Proved `cotangentInner_metricCompatible_extDerivFun_of_sharp_mdiffAt`: under
  differentiability of both sharped one-form fields, the cotangent inner product
  satisfies the expected product rule.
- Verification passed for `Tensor0SRiemannian.lean`, with the existing
  `inner0S_two_metricCompatible_extDerivFun` frontier still visible.
- The remaining blocker is now sharply isolated: prove that a smooth one-form
  field has a differentiable sharp tangent field under a smooth metric, then use
  the cotangent product rule to lift through the `(0,2)` recursive tensor metric.
  This is a missing local cotangent-sharp smoothness API. It looks medium-hard
  but still likely solvable without user intervention; it is not a Bochner or
  finite-sum problem.

## 2026-05-15 component route reassessment

- The mathematical identity is a pure finite-sum computation:
  differentiate the inverse-metric contraction formula for the `(0,2)` tensor
  inner product, use metric compatibility to get `nabla gInv = 0`, and the
  remaining terms are exactly `<nabla A, B> + <A, nabla B>`.
- A direct curried Hom-metric conversion is not the right local proof shape:
  the required `ContinuousLinearMap` additive/topological/module instances are
  installed inside the recursive tensor metric step, so using that expression
  as an external theorem statement causes typeclass synthesis failures.
- The better next frontier is a DifferentialGeometry-local component API for
  `nabla gInv = 0` outside the Ricci-flow evolution layer, followed by a
  component derivative theorem for `inner0S_two_eq_coord`.
- Frontier assessment: missing component tensor-metric compatibility API. This
  is routine but medium-sized finite-sum and local-frame plumbing, and still
  expected to be solvable without user intervention.

## 2026-05-16 existing API check for component expansion

- Existing usable pieces:
  `inner0S_two_eq_coord`, `Coordinates.nabla0SFun_two_eval_coordFrame`, and the
  Ricci-flow-local `inverseMetricCovDerivCompInFrame_eq_zero` proof.
- The current APIs do not plug together directly for
  `inner0S_two_metricCompatible_extDerivFun`: the inverse-metric covariant
  derivative theorem is in the Ricci-flow evolution layer, depends on
  `SolutionOn`/time-indexed metric components, and uses private scalar
  `extDerivFun` sum/product helpers.  The tensor metric layer needs the same
  result for an arbitrary smooth metric and local frame.
- The smallest next implementation step is to lower/generalize
  `metricCompInFrame_extDerivFun_eq_christoffel` and
  `inverseMetricCovDerivCompInFrame_eq_zero` into a DifferentialGeometry coordinate or
  tensor component layer with `g : SmoothRiemannianMetric I M` and
  `gInv : M -> Idx -> Idx -> Real`, then use them in the four-index derivative
  calculation.
- Frontier assessment: missing API placement, not a mathematical obstruction.
  Expected hardness is medium; it should be solvable locally without user
  intervention, but not by a one-line rewrite with the current exports.

## 2026-05-16 finite-sum reindexing pass

- Added checked private five-index swap lemmas and the four checked correction
  reindexing lemmas needed for the `(0,2)` inner-product compatibility
  coordinate computation.
- Verification passed for `Tensor0SRiemannian.lean`, with the original
  `inner0S_two_metricCompatible_extDerivFun` theorem still the only Lean
  frontier in this file.
- The failed next step was the assembled private algebra theorem: after using
  `nabla gInv = 0`, a broad final `ring_nf` over all four indices ran too long.
  This is a performance/proof-control issue, not a mathematical obstruction.
- Smallest next lemma: split the assembled algebra theorem into two scalar
  normalizers, one for substituting `DU = -Γ*U - Γ*U` and one for combining the
  four already-checked correction reindexing lemmas.  Expected hardness is
  routine local finite-sum proof work and should not need user intervention.

## 2026-05-16 coordinate algebra closure

- Closed the finite-sum computation that had previously timed out:
  `inner0S_two_metricCompatible_coord_algebra` now checks by splitting the
  inverse-metric derivative substitutions and tensor-slot correction sums into
  small private lemmas.
- Also added the reusable coordinate input in
  `Coordinates/MetricCompatibility.lean`: inverse-metric compatibility along
  an arbitrary smooth direction, expressed with `christoffelAlongInFrame`.
- Verification passed for this file, `Bochner.lean`, and `RicciFlow/Basic.lean`.
  The tensor theorem `inner0S_two_metricCompatible_extDerivFun` still has its
  original `sorry`.
- Remaining blocker: component-to-invariant assembly. The next missing API is
  a localized fixed-chart inverse-metric component construction for the
  coordinate-frame neighborhood, not more finite-sum algebra. Expected hardness
  is medium local-coordinate infrastructure and should be solvable without user
  intervention.

## 2026-05-16 fixed-chart API pass

- `Coordinates/MetricCompatibility.lean` now exposes the fixed-chart inverse
  metric component construction and center `MetricInverseInBasis` theorem.
- Verification still passes for `Tensor0SRiemannian.lean`; the public theorem
  `inner0S_two_metricCompatible_extDerivFun` remains the only visible frontier
  in this file.
- Exact blocker: the public theorem needs the derivative of the coordinate
  four-index inner-product formula in a neighborhood of `x`. The fixed-chart
  inverse components are now available at the center, but the assembly needs a
  localized theorem saying these components satisfy `MetricInverseInBasis` on
  the coordinate-frame base set and therefore satisfy localized
  `nabla gInv = 0` along `X`.
- Frontier assessment: missing localized coordinate inverse-metric API, not a
  mathematical obstruction and not Bochner/Ricci-flow algebra. This looks like
  routine but medium local-frame plumbing; I expect it can be solved without
  user intervention.
