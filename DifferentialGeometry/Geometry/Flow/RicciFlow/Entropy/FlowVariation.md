# FlowVariation

## Purpose

This module supplies the two pointwise geometric time derivatives needed before
assembling Perelman's entropy variation along the reversed Ricci flow.

## Proven producers

- `revGram_smooth` supplies the jointly smooth reverse-time chart Gram entries
  required by interval-local moving-volume differentiation.  It is a scalar
  local-frame statement obtained by precomposing
  `MetricFamilySmoothOn.frameCompSmooth` with `r ↦ T - r`.
- `revTrace_eq` identifies the reverse metric volume trace with `2 R(T-s)`.
  The proof differentiates the metric after applying it to two tangent vectors
  and then uses the existing scalar-trace bridge; it does not compare whole
  tensor or Hom objects.
- `revScalar_time` differentiates `R(T-s)` using the genuine scalar-curvature
  evolution of `IsSolutionOn`.  Its conclusion is expressed with the
  `reverseFamily` Laplacian and metric norm, and therefore needs no coordinate
  or supplied-component data.
- `revGradSq_time` differentiates the reverse-metric squared gradient norm of
  the reconstructed Perelman potential.  The reverse metric equation is used
  with `Q = -Ric(T-s)`, `normGradSq_time` supplies the invariant norm
  derivative, and `potential_df_time` supplies the actual derivative of the
  spatial differential.

The positivity input has exactly the producer-facing shape used by
`potential_df_time`: positivity on `Dr.regular ∩ Ioi 0`.  No chart-selection
hypothesis, whole-Hom equality, or additional consumer-side regularity package
is introduced.

## Proof-normal-form lessons

- Upgrade the original scalar and metric equations from within-derivatives at
  regular times, then compose with the scalar path `s ↦ T - s`.
- Keep the Laplacian in the realized `reverseFamily` normal form; unfolding only
  `laplacianAt` and the two realized-family constructors closes the definitional
  comparison.
- For the metric sign change, evaluate `Q = -Ric` on the two slots first.  The
  canonical `Tensor0SSpace.neg_apply` lemma is the stable scalar normal form;
  no equality of tensor objects is needed.
- Keep the inner-product model context local to `revTrace_eq`.  The other
  reverse-flow producers retain their weaker normed-space assumptions, while
  the chart-basis inverse used by the trace proof consumes the same
  finite-dimensional inner-product context as the original private proof.

## Remaining assembly frontier

The reverse metric chart regularity and volume trace are public producer API,
and `NormGradSqTime.gradSq_joint` supplies the joint spacetime smoothness of the
moving scalar `|grad_{g(s)} f(s)|^2`.  `WVariation.w_rev_hasDerivAt` now uses
these facts in the checked interval-local raw `W` first variation.  The next
separate frontier is weighted Hessian square completion, not another
regularity assumption for the `W` consumer.

## Verification and project accounting

Focused verification passed without local warnings.  All four public producers
are proved without `sorry` or `admit`.

- `revGram_smooth`: 100%.
- `revTrace_eq`: 100%.
- `revScalar_time`: 100%.
- `revGradSq_time`: 100%.
- This pointwise reverse-flow variation sublayer: 100%.
- Dedicated raw first-variation machinery: 100%.
- Broader entropy/noncollapse machinery: approximately 67%.
- The final W-monotonicity theorem: not yet stated and proved here, 0%.
- Perelman noncollapsing endpoint theorem: 0%; this file supplies machinery only.
