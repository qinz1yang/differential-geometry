# ComparisonComposition

Book label: `lem:scn-good-point-buffered-canonical` (`master05b.tex`, the passage that
pulls back a compact buffered core of the model neck and concludes the buffered
`2 * alpha`-neck from the strict reserves).

## What the file does

Composes two `Chapter25.MetricComparisonOn` records along a composite map and feeds the
result into `StrongNeck` / `SpatialNeck`.

Underlying identity:

```
(F ∘ G)^* g - h  =  G^* (F^* g - k)  +  (G^* k - h)
```

with `h` the cylinder family, `k` the model family, `g` the (rescaled) source family.
The second summand is the given `cyl ≈ model` error tower (`c₁.jet`, bounded by
`alpha`); the first is the pullback by `G` of the `model ≈ source` error tower
(`c₂.jet`, bounded by `eps`), whose covariant jets *measured in `h`* are packaged as
`TransportedErrorTower` with the explicit factor `K`.

## Public declarations

| name | role |
| --- | --- |
| `derivWithin_add_of_eq` | sum rule for `derivWithin` that also covers the degenerate case (`¬ UniqueDiffWithinAt`), so a `times = {0}` comparison needs no differentiability input |
| `tensor02CovDeriv_add` | additivity of the covariant tower in the tensor slot |
| `tensor02CovDerivNormWith_add_le` | triangle inequality for the native spatial jet norms at fixed order/connection/norm metric |
| `MetricComparisonOn.mono` | restrict comparison set, lower the order, raise the tolerance (time set fixed) |
| `TransportedErrorTower` | the transported `model ≈ source` error tower on the cylinder side: zeroth identity, genuine time recursion, transported bound `K * eps` |
| `TransportedErrorTower.ofPullbackCross` | **constructs** that tower from `pullbackTensor02FieldCross` when `G` is a global diffeomorphism; only the change-of-background factor `K` is left as a hypothesis |
| `MetricComparisonOn.trans` | the composition, tolerance `alpha + K * eps` |
| `partialDiffeomorphTransMixed`, `coe_partialDiffeomorphTransMixed`, `source_partialDiffeomorphTransMixed` | composition of two partial diffeomorphisms with *different* models (the tree's `HCGCompactness.PartialDiffeomorph.trans` is single-model) |
| `neck_window_subset` | `univ ×ˢ Ioo (-(2α)⁻¹) (2α)⁻¹ ⊆ univ ×ˢ Ioo (-α⁻¹) α⁻¹` |
| `StrongNeck.transport` | model `alpha`-neck + model comparison ⇒ source `2 * alpha`-neck, chart `Fmap ∘ nk.map` |
| `SpatialNeck.transport` | single-slice version; needs no time-differentiability hypothesis at all |

## Proof mechanism

* `pullback_eq`: `mfderiv_comp_apply` (chain rule) plus `c₁.pullback_eq`, `c₂.jet_zero`
  and `c₂.pullback_eq` at `G y ∈ V`.  `c₂.pullback_eq` is available **only on `V`**,
  hence the hypothesis `hGV`.
* `jet b s := c₁.jet b s + T.tower b s`; `jet_zero` is global and purely algebraic.
* `jet_succ`: `derivWithin_add_of_eq`.  Mathlib's `derivWithin_fun_add` still needs
  `DifferentiableWithinAt`; that is required here only under
  `UniqueDiffWithinAt ℝ times s`, because without unique differentiability every
  `derivWithin` is `0` and the recursion is degenerate on both sides.  This is what makes
  the `times = {0}` (spatial) case hypothesis-free.
* `close`: `tensor02CovDerivNormWith_add_le` + `c₁.close` + `T.close`.
* `equivalence`: **not** proved from the two metric sandwiches (that would force
  `K ≥ 1 + alpha`); instead it is read off from the composed `close` bound at
  `a = b = 0` via `quadratic_comparison_of_error_norm`.  So `trans` imposes no relation
  between `alpha`, `eps` and `K`.
* `ofPullbackCross`: `pullbackTensor02FieldCross` (global smooth section — this is the
  structural reason a *global* diffeomorphism is needed), `pullbackTensor02FieldCross_apply`
  for `zero_eq`/`succ_eq`/`differentiableWithinAt`, and the exact naturality
  `tensor02CovDerivNormWith_pullbackTensor02FieldCross` (no tolerance loss) for `close`.
* Neck consumers: `mono` down to the `2α`-window and order `⌈(2α)⁻¹⌉₊` first (so the
  transported bound is only needed on the smaller core), then `trans`, then `mono` again
  with `alpha + K * eps ≤ 2 * alpha`.

## Real dependencies

`Chapter25Geometry` (`MetricComparisonOn`, `StrongNeck`, `CylinderReference`),
`Chapter25Extension` (`SpatialNeck`), `WitnessNormalizedTimeJets`
(`quadratic_comparison_of_error_norm`), `ModelWitness` (`inner_self_nonneg`,
`rescaledMetric`), `PullbackCovariantNaturality` (`tensor02_eq_covDOF`),
`CovariantDerivativeAlgebra` (`covDerivOfField_add`), `Tensor0SMetricIneq`
(`_root_.Tensor0SBundle.sqrt_normSq0S_add_le`), `KappaSolutions.CrossModelTensorPullback`
(`pullbackTensor02FieldCross`, `..._apply`, `tensor02CovDerivNormWith_pullbackTensor02FieldCross`),
`Geometry/Metric/PullbackCross` (`Diffeomorph.pullbackMetricCross`).

## Pitfalls found

* `MetricComparisonOn.pullback`/`jet` are **globally smooth sections**; the pullback
  identity holds on `U` only.  A composed comparison therefore cannot be built by
  pulling back along a bare `PartialDiffeomorph` — there is no global smooth
  representative.  That is exactly why `TransportedErrorTower` exists as data, and why
  `ofPullbackCross` needs a `Diffeomorph`, not a `PartialDiffeomorph`.
* The time set of a comparison **cannot be shrunk**: `jet_succ` is a `derivWithin` along
  it.  `mono` therefore keeps `times` fixed.  By contrast `c₂`'s time set and order are
  unconstrained in `trans` (it is used only through `pullback_eq` and `jet_zero`);
  `ofPullbackCross` does need `c`'s time set to be the composed one.
* The tree's `HCGCompactness.PartialDiffeomorph.trans` is single-model
  (`PartialDiffeomorph I I …`) and same-universe; the neck chart is
  `PartialDiffeomorph IC I3 Cylinder _`, so a mixed-model composition had to be
  reproved here (`partialDiffeomorphTransMixed`).  **Upstream candidate**: generalise
  `PullbackTowerBounds.PartialDiffeomorph.trans` to three models and drop the
  `[SigmaCompactSpace] [T2Space]` section variables.
* `tensor02CovDerivNormWith_add_le` and `tensor02CovDeriv_add` are general-purpose.
  **Upstream candidates** for `Geometry/Metric/Convergence/CovariantDerivativeAlgebra` or
  `ApproximateIsometry/MetricApproximationDefs`.  Note the name clash: the tree already
  has `HCGCompactness.sqrt_normSq0S_add_le` (basis form) beside
  `_root_.Tensor0SBundle.sqrt_normSq0S_add_le` (basis-free); the latter is the one used.
* `linarith` does not see structure projections: `nk.eps_pos` must be pulled into a
  `have ha : (0:ℝ) < alpha` before any `linarith`/`inv_anti₀` step.
* Shared-checkout hazard observed while verifying: a concurrent build kept replacing
  unrelated `.olean` files, producing transient
  `error: failed to read file '….olean'` at line 1 with no other diagnostics.  Retrying
  the same `lake env lean` invocation succeeds; this is **not** a proof failure.

## Verification

```
LEAN_NUM_THREADS=2 lake env lean \
  DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/ComparisonComposition.lean
```
exit code 0, empty output, 30 s (repeat runs 25–30 s).  No `sorry`, no `nolint`, no
`maxHeartbeats`/`maxRecDepth`/`skipKernelTC`/`set_option backward.*`.  Not registered in
`DifferentialGeometry.lean` (reviewer's job); axiom audit pending an artifact refresh —
expected `propext`, `Classical.choice`, `Quot.sound` for all 13 publics.

## Remaining obligation / next step

One analytic input, isolated as `TransportedErrorTower.ofPullbackCross`'s `hback`:

> the covariant jet of a fixed two-tensor measured in the cylinder background `h s` is at
> most `K` times the same jet measured in `Phi^* (k s)`,

for the orders `a + 2b ≤ order` actually used.  This is the change-of-background estimate
the lane already has in the strong-neck special case
(`KappaSolutions.strongNeckBackground_backward_forward_covNorm_le`, constant
`sqrt (3 ^ (a + 2))`, via `sqrt_normSq0S_le_of_metric_equiv`) — but there the two
backgrounds share a connection.  Here the connections differ by the Christoffel
difference of two `alpha`-equivalent metrics, so the general statement needs a Leibniz
expansion of `metricCovDerivStep` against that difference tensor.  Next step: prove

```
tensor02CovDerivNormWith a A g₁ g₁ y ≤ K a alpha * tensor02CovDerivNormWith a A g₂ g₂ y
```

for `alpha`-equivalent `g₁, g₂` whose mutual covariant jets are `alpha`-small, with `K`
depending only on `a` and `alpha` (and `K → 1` as `alpha → 0`), then instantiate
`ofPullbackCross` with it.  The second, softer hypothesis is `hdiff`
(time-differentiability of the model-to-source error jets on the window); it is free for
`times = {0}` and is exactly the "genuine tower" property that
`metricComparisonOnOfGenuineTimeTowers` already produces on the construction side.
