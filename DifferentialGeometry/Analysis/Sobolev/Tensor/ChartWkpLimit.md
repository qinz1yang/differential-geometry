# ChartWkpLimit

## Status

This is a source-written producer. No Lean/Lake process was started in this
lane because another named build owns verification. The claims below must
therefore be read as source-complete but not yet elaboration-verified.

## Proved in source

- `wkpNorm_secComp_le` bounds one scalar chart-component `wkpNorm` by the
  total tensor chart norm.
- `secComp_cauchy` turns total-norm Cauchy control into `wkpNorm` Cauchy
  control for every fixed chart and pair of tensor indices.
- `exists_secComp_lim` applies the existing Euclidean theorem
  `MemWkp.exists_limit_of_wkpNorm_cauchy`. Its limit is an actual scalar
  function in `MemWkp k p`, not a formal or smooth placeholder.
- `secCompLimit_mem` and `secCompLimit_tendsto` expose membership and norm
  convergence for the chosen component limit.
- `secModelLimit` reconstructs a model-fibre tensor from the scalar limits
  through `tensorChartBasisElement`; `secModelLimit_proj` proves that the
  canonical component projection recovers the original scalar limit.
- `secModelPull` moves an arbitrary model-fibre field into the genuine
  dependent fibre through the inverse bundle trivialization and extends it by
  zero outside the chart source.
- `tensorLimitSec` is consequently a genuine raw tensor section, assembled as
  the finite `chartAtlasPOU_finset` sum of those pulled-back model fields.

None of these definitions asserts smoothness of a weak Sobolev limit. No
tensor `Hom` implementation was unfolded, and no new global class, instance,
notation, axiom, opaque producer, `sorry`, or `admit` was introduced.

## Exact next analytic theorem

The remaining completeness obstruction is no longer the existence of a
dependent tensor-section candidate or a pre-imposed compatibility condition
between arbitrary component arrays. Finite POU pullback assembly produces
the candidate directly. The smallest missing theorem is a tensor-valued
cross-chart Sobolev transport estimate:

```lean
theorem modelPull_wkp
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (β γ : M)
    (v : EuclN → TensorRSModel r s ℝ E)
    (hv : ∀ Idx Jdx,
      MemWkp k p (fun y =>
        tensorChartComponentProjection r s Idx Jdx (v y))
        (chartTargetEuclid β))
    (hv_support : each component is a.e. supported in the fixed compact
      Euclidean image of the β-POU kernel) :
    ∀ Idx Jdx,
      MemWkp k p
        (secChartComp r s (secModelPull r s β v) γ Idx Jdx)
        (chartTargetEuclid γ)
```

A quantitative version must also bound the target norm by a finite sum of
source component norms. The intended proof ingredients already exist:

1. `transitionCoeff` and
   `tensorChartComponentRaw_eq_transitionCoeff_sum` give the finite tensor
   transition formula;
2. smoothness and compact-support bounds for the transition coefficients are
   already proved in `TensorChartTransition.lean`;
3. `crossChartAeJoint` / `crossChartJointK` transfer scalar weak Sobolev
   functions through the chart-transition diffeomorphism;
4. the arbitrary-order smooth-multiplier lemmas control the finite coefficient
   products.

The tensor transition identity is currently stated for `SmoothCcTensor`, even
though its core proof is fibrewise algebra. The next implementation should
first generalize that identity to `RSTensorSection` or directly to
`secModelPull`; it must not assume the weak limit is smooth.

Once this estimate is available, finite sums give
`MemWkpTensor g k p tensorLimitSec`; applying the quantitative bound to the
componentwise convergence proves total-norm convergence and hence the desired
`wkpTensor_limit` producer.

## Failed or rejected routes

- Treating independently chosen chart-component limits as the final tensor
  object was rejected: that changes the carrier and loses the geometric
  section required by Ricci--DeTurck.
- Reusing `tensorBundleSectionOfChartComponents` was rejected because that
  constructor requires smooth components; Sobolev completeness produces only
  weakly differentiable limits.
- Requiring a transition-compatibility axiom before constructing the limit was
  unnecessary: the finite POU pullback construction creates a genuine section
  directly. Compatibility is replaced by the concrete transport estimate
  needed to prove its chart regularity and convergence.

## Honest progress

- Per-chart/per-component Cauchy-limit producer: 100% source-written, 0% Lean
  verified in this lane.
- Genuine weak tensor-section candidate and model-component recovery: 100%
  source-written, 0% Lean verified in this lane.
- Tensor cross-chart `W^{k,p}` transport estimate: 0%; exact next theorem is
  `modelPull_wkp` above.
- Full `wkpTensor_limit`: 25% machinery, 0% exact theorem.
- Exact `ricci_flow_unif_existence`: 0%; this file removes neither the
  maximal-regularity solver nor same-horizon smoothing obligations.

## Superseding implementation update

The former `modelPull_wkp` frontier described above has now been implemented
source-side, split along abstraction boundaries:

- `ChartWkpSupport.lean` proves support inheritance and supplies compact weak
  representatives;
- `ChartWkpBound.lean` proves the quantitative `W^{2,p}` term transport;
- `ChartWkpCompat.lean` proves the exact finite transition identities and
  eliminates both cutoff factors by explicit support/zero branches;
- `ChartWkpComplete.lean` assembles `tensorLimit_mem`, total-norm convergence,
  `wkpTensor_limit`, and quotient-norm convergence.

This update supersedes the earlier “exact next theorem” and progress figures
in this note. The chain is still 0% Lean-verified in this lane because a
different named build owns verification.
