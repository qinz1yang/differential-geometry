# NeckTransportDecoupled — model tolerance chosen after the target tolerance

Lane `CanonicalNeighborhood/`, book `ch:scn` (`master05b.tex`), namespace
`DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.Chapter25`.
Consumers/producers used: `ComparisonComposition.lean` (`MetricComparisonOn.mono`,
`MetricComparisonOn.trans`, `TransportedErrorTower`, `partialDiffeomorphTransMixed`,
`neck_window_subset`) and `BackgroundJetTransfer.lean` (`backgroundJetBudget`,
`backgroundJetSmallness`, `backgroundJetConstant`,
`TransportedErrorTower.ofPullbackCross_of_close`).  Neither file was edited; this module only
imports `BackgroundJetTransfer.lean`.

## The defect this module repairs

`StrongNeck.transport_of_comparisons` and `SpatialNeck.transport_of_comparisons` produce a
`2 * alpha`-neck of the source from an `alpha`-neck of the model under

```
halpha' : alpha ≤ backgroundJetSmallness (EuclideanSpace ℝ (Fin 2) × ℝ) ⌈(2 * alpha)⁻¹⌉₊
```

which ties the tolerance of the *model* neck to the derivative order of the *produced* neck.
The plan recorded as open whether this is satisfiable for small `alpha`, pending a growth bound
on `metricCovariantDerivativeComparisonConstant`.  It is **not**, and no growth bound is needed,
because the comparison constant only enlarges the budget and therefore only lowers the
threshold:

* `sqrt_add_two_le_backgroundJetBudget`:
  `√((3/2) ^ (2 + order)) + 2 ≤ backgroundJetBudget E' order` (the factor `1 + C * order` is
  at least `1`, and the additive `2` of the budget is kept);
* `backgroundJetSmallness_le_inv_sqrt`:
  `backgroundJetSmallness E' order ≤ (√((3/2) ^ (2 + order)))⁻¹`, i.e. the threshold decays like
  `(3/2) ^ (-(2 + order)/2)`;
* `backgroundJetSmallness_lt_of_inv_le` / `backgroundJetSmallness_ceil_lt_self`:
  `backgroundJetSmallness E' ⌈(2 * alpha)⁻¹⌉₊ < alpha` for `0 < alpha < 1/32`, and
  `not_le_backgroundJetSmallness_ceil` is the `¬ alpha ≤ …` form.

Arithmetic of the threshold lemma, with `n := ⌈(2 * alpha)⁻¹⌉₊`: `alpha < 1/32` gives
`16 ≤ (2 * alpha)⁻¹ ≤ n`; `two_mul_sq_le_three_halves_pow` gives `2 * n ^ 2 ≤ (3/2) ^ n` (base
case `512 ≤ (3/2) ^ 16 = 43046721/65536`, step `4 * n + 2 ≤ n ^ 2`), hence
`(2 * n) ^ 2 ≤ (9/4) * (3/2) ^ n = (3/2) ^ (2 + n)` and `2 * n ≤ √((3/2) ^ (2 + n))`; with
`1 ≤ 2 * alpha * n` this gives `1 < alpha * backgroundJetBudget E' n`, i.e.
`backgroundJetSmallness E' n ≤ (backgroundJetBudget E' n)⁻¹ < alpha`.

The threshold `1/32` is explicit, not sharp; the neck admissibility window is `alpha < 1/22`
(from `2 * alpha < 1/11`), and the same computation with the sharper inequality
`(3/2) ^ (2 + n) > (2 * n - 2) ^ 2` only reaches `alpha < 1/28`.  Nothing in the lane needs a
sharper threshold: the point is that the coupled hypothesis has to be abandoned, not located.

## The repair

The book chooses the model tolerance *after* the target tolerance ("apply the model canonical
neighborhood theorem at tolerance `alpha/4`"), which Kleiner–Lott permits for any smaller
tolerance.  The decoupled transports take a model neck of an independent tolerance
`beta ≤ alpha`.  Three inequalities change relative to the coupled versions and nothing else:

1. **Window.**  `neck_window_subset_of_le`:
   `univ ×ˢ Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹ ⊆ univ ×ˢ Ioo (-beta⁻¹) beta⁻¹`, because
   `beta ≤ alpha ≤ 2 * alpha` gives `(2 * alpha)⁻¹ ≤ beta⁻¹`.  (`neck_window_subset` is the
   case `beta = alpha`; it is not usable here.)
2. **Order.**  `⌈(2 * alpha)⁻¹⌉₊ ≤ ⌈beta⁻¹⌉₊` by `Nat.ceil_mono` on the same inverse
   inequality, so `nk.comparison` (order `⌈beta⁻¹⌉₊`, tolerance `beta`) restricts by
   `MetricComparisonOn.mono` to the produced window at the produced order, still at tolerance
   `beta`.
3. **Tolerance.**  `MetricComparisonOn.trans` gives `beta + K * eps`, and
   `beta ≤ alpha`, `K * eps ≤ alpha` give `beta + K * eps ≤ 2 * alpha`.

The transported error tower is built by `TransportedErrorTower.ofPullbackCross_of_close` at the
model tolerance `beta` (its `halpha'` becomes `beta ≤ backgroundJetSmallness _ ⌈(2α)⁻¹⌉₊`) and
at the **target** order `⌈(2 * alpha)⁻¹⌉₊`, so its constant is
`backgroundJetConstant _ ⌈(2α)⁻¹⌉₊ * (⌈(2α)⁻¹⌉₊ + 1)` and the demand on the model-to-source
tolerance stays `K * eps ≤ alpha` at that order.  This is why the transport is re-proved here
instead of instantiating `StrongNeck.transport_of_comparisons` at `alpha := beta` and relaxing
afterwards: that route would force the order `⌈(2 * beta)⁻¹⌉₊ ≥ ⌈(2 * alpha)⁻¹⌉₊` and hence a
strictly stronger (and, as `beta` shrinks, arbitrarily stronger) demand on `eps`.  The proofs
are the proofs of `StrongNeck.transport` / `SpatialNeck.transport` and
`…transport_of_comparisons` with those three inequalities adjusted; no analytic step is
repeated.

## Admissible tolerances

`neckModelTolerance alpha := min alpha (backgroundJetSmallness _ ⌈(2 * alpha)⁻¹⌉₊)` and
`neckSourceTolerance alpha := alpha / (backgroundJetConstant _ ⌈(2 * alpha)⁻¹⌉₊ *
(⌈(2 * alpha)⁻¹⌉₊ + 1))` are explicit, positive for `0 < alpha`, and depend only on `alpha`.
`exists_model_tolerance` and `exists_source_tolerance` are their existence forms;
`StrongNeck.transport_of_comparisons_of_tolerances` and
`SpatialNeck.transport_of_comparisons_of_tolerances` are the transports instantiated at them,
which is the form the book's argument uses: choose `alpha`, then `beta`, then the accuracy of
the model-to-source comparison.

`exists_model_tolerance` also returns `beta < 1/11` (from `hsmall : 2 * alpha < 1/11`), because
a `StrongNeck Sm beta p 0` only exists for an admissible neck tolerance; this is the one place
where the statement is stronger than the shape requested in the task brief, and it is what makes
`hsmall` load-bearing there.

## Redundant hypothesis kept

`StrongNeck.transport_of_comparisons'` and `SpatialNeck.transport_of_comparisons'` take
`hbeta_pos : 0 < beta` although `nk.eps_pos` already provides it (the coupled versions derive
`0 < alpha` from `nk.eps_pos`).  It is kept because the brief specifies it and because it makes
the two smallness hypotheses readable side by side; it is used as the `halpha` argument of
`ofPullbackCross_of_close`, so no linter warning arises.  `StrongNeck.transport'` and
`SpatialNeck.transport'` do not take it.

## Verification

```
LEAN_NUM_THREADS=1 lake env lean \
  DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/NeckTransportDecoupled.lean
```
empty output, 34.0 s (2026-09-11, one `lean.exe`, quiet host).  Wrong-proof control: the same
file with `two_mul_sq_le_three_halves_pow` weakened to `15 ≤ n` is rejected
(`unsolved goals … ⊢ False` in the base case, `2 * 15 ^ 2 = 450 > (3/2) ^ 15`), confirming the
base case is not vacuous and the file is really elaborated.

Axiom audit: `#print axioms` appended to a scratch copy of the same source (no artifact refresh
needed, the declarations are elaborated in that file) — all 22 public declarations depend on
`propext, Classical.choice, Quot.sound` only.  **No inherited admission**: the whole chain
through `ComparisonComposition`, `BackgroundJetTransfer` and the native
`iterated_covariant_derivative_norm_comparison_bound` is `sorry`-free, and none of the
`Chapter25Extension` `Upstream` admissions is reachable from these declarations.

## Remaining obligations of the transport (unchanged by this module)

* The neck chart must agree with a **global** diffeomorphism `Phi : Cylinder ≃ₘ⟮IC, I3⟯ P`
  (`hPhi`), inherited from `TransportedErrorTower.ofPullbackCross`; a genuinely partial model
  chart is not covered.
* `hdiff` (time differentiability of the pulled-back model-to-source jets) and `hjet` (time
  differentiability of the model neck's own jets) on `Icc (-1) 0`, inherited from
  `ofPullbackCross` and `MetricComparisonOn.trans`.  The spatial versions have neither.
* The model-to-source comparison `cmp` itself, its window hypotheses `hcore`, `hVsource`,
  `horder`, `hbase`, and `htime` for the strong neck.
* The producer of the model `beta`-neck at the freely chosen `beta = neckModelTolerance alpha`
  is the Chapter 24 model canonical-neighborhood input (`Upstream.kappa_canonical_neighborhood`,
  still `sorry` in `Chapter25Extension.lean`); this module only shows that such a `beta` exists
  and transports correctly.
