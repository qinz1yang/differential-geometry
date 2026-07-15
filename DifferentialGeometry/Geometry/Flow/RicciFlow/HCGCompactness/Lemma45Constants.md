# Lemma45 algebra notes

## 2026-06-02 first-pass name map

MSM135 Lemma 4.5 lives above the checked approximate-isometry layer, but this
pass intentionally stays geometry-free.

Existing geometric names to be consumed later:

- map-level approximate isometry:
  `PreApproxIsometryData`, `BookApproxIsometryData`;
- same-domain supplied-metric comparison:
  `IsApproxIsometryOn`, `IsTwoSidedApproxIsometryOn`;
- pullback metric tensor data:
  `PullbackMetricTensorData`;
- metric derivative norm vocabulary:
  `metricCovDeriv`, `metricCovDerivNorm`,
  `metricCovDerivNormWith`;
- tensor norms:
  `Tensor0SBundle.normSq0S`, `Tensor0SBundle.normSqRS`;
- connection-difference zero-order target:
  `ConnDiffEpsBoundOn`, `ConnDiffEpsBoundsBelow`.

New first-pass algebra names:

- `oneStepConst`;
- `lemma45Const`;
- finite range-sum helpers in `SumLemmas.lean`;
- `main_step_algebra`, the pure induction-step inequality.
- `main_step_to_lemma45Const`, the same induction-step inequality with the
  recursive Lemma 4.5 constant already absorbed.
- `main_step_to_lemma45Const_of_partials`, the absorbed induction-step
  inequality in the natural geometric form where lower `G k` estimates only
  have partial sums up to `k`.

The remaining frontier after this algebra pass is the covariant `(0,s)`
connection-difference action and its iterated Leibniz estimate.  That later
work should consume these constants rather than expanding Christoffel symbols
inside Lemma 4.5.

## 2026-06-02 verification

`Lemma45Constants.lean` and `SumLemmas.lean` both verified.  The checked
content is only the constants, positivity/monotonicity facts, range-sum
comparison lemmas, and the pure algebraic induction-step inequality.  No
geometric pullback, connection, or tensor derivative statement was added in
this pass.

## 2026-06-02 continuation

Added and verified `main_step_to_lemma45Const`, a pure algebra endpoint for the
`r = p + 1` induction case.  The existing RicciFlower theorem
`Tensor0SBundle.nabla0SFun_sub_cov` is the checked first-order covariant
connection-change identity for `(0,s)` tensors, while
`Tensor0SBundle.componentRS_nablaRSFun_sub` is the checked mixed component
version.  The next missing producer is therefore not the first derivative
identity itself, but the iterated `H`-Leibniz estimate for repeated derivatives
of the connection-difference action.

Also added `main_step_to_lemma45Const_of_partials`, so the later one-step
geometric theorem can produce the natural partial sums and leave the sum
enlargement to algebra.

## 2026-06-02 scalar one-step endpoint

Added `oneStep_from_leibniz` in `SumLemmas.lean`.  This is the pure scalar
collapse of the Leibniz expansion: once the tensor layer proves a sum of terms
`|nabla_H^a A| * |nabla_H^(k-a) T|`, the bounds
`|nabla_H^a A| <= eps * B a` and the full partial-sum bound for the `T` terms
produce the `eps * oneStepConst B k s` coefficient.

The remaining frontier is still geometric: the project needs an iterated
covariant product/Leibniz estimate for repeated `H`-derivatives of the
connection-difference action.  Existing product smoothness and product norm
splitting do not by themselves expose that theorem.

## 2026-06-02 composition constant

Added `compApproxConst` in `Lemma45Constants.lean` for MSM135 Chapter 4,
Proposition "Composition of approximate isometries, I".  It is a deliberately
larger natural-power constant depending on the Corollary 4.6 constants.  This
keeps the future composition proof algebraic and avoids introducing a separate
real-power bookkeeping frontier.

The constant layer verified.  The remaining frontier is still the geometric
composition theorem itself, which must consume the completed Corollary 4.6
derivative-comparison endpoint.
