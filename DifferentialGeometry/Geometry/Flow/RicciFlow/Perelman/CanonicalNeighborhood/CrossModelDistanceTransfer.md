# CrossModelDistanceTransfer

Book label: `eq:scn-good-distance-transfer`, inside the proof of
`lem:scn-good-point-buffered-canonical` (`master05b.tex`, the paragraph at L4700–4735 of
the L4616–4770 block).

Namespace: `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.Chapter25`.
Imports: `CrossModelBallCapture`, `CollarMetricControl` (which pulls in
`Chapter25Geometry` and `Geometry/Comparison/DistanceHessianLocal`).

## What is proved

For a partial diffeomorphism `F : PartialDiffeomorph J I N M ∞` carrying a two-sided
differential metric equivalence with error `eps` on the *compact* closed reference ball
`riemannianClosedBallOf h p R`, every pair `a, b` of the much smaller closed ball
`riemannianClosedBallOf h p rho` satisfies

```
√(1-eps) · d_h(a,b) ≤ d_g(F a, F b) ≤ √(1+eps) · d_h(a,b)
```

both as an `ℝ≥0∞` statement (`crossModel_edist_transfer`) and, after `toReal`, as a real
statement (`crossModel_toReal_transfer`, and `crossModel_metricDistance_transfer` in the
`metricDistance` phrasing of `Chapter25Geometry.lean`).

The only numerical reserve is the single explicit inequality

```
hroom : Real.sqrt (1 + eps) * (3 * rho) < Real.sqrt (1 - eps) * R
```

`crossModel_room_of_book_constants` checks that the book's instance
`rho = 3 * L₊ / √(1-eps)`, `R = ε^{-1/2}` with `ε^{-1/2} > 10 L₊ + 10` satisfies it.

## Proof mechanism

Upper half (`crossModel_edist_le_of_metric_upper`, needs no compactness, no `T2Space`, no
`FiniteDimensional`): for every real `r` with `d_h(a,b) < ofReal r` and `rho + r ≤ R`, take a
`C¹` reference path of `h`-length `< ofReal r` from `exists_lt_of_edistOf_lt`. Every point
of it is within `d_h(p,a) + r ≤ rho + r ≤ R` of `p` by the triangle inequality, hence the
whole path is inside the reference ball; push it forward with
`Chapter25.metricPathELength_map_le` (`L = √(1+eps)`) and use
`edistOf_le_metricPathELength`. Then `d_h(a,b) ≤ ofReal (rho + rho)` is finite, so writing
`d_h(a,b) = ofReal D` the statement follows from `ENNReal.le_of_forall_pos_le_add` with the
choice `r = D + min (R - 3ρ) (η/L)`; the strict `3 * rho < R` is what supplies the room for
`δ → 0`.

Lower half (`crossModel_edist_ge_of_metric_equiv`): apply the upper half twice first, to
get `d_g(F p, F a) ≤ ofReal (√(1+eps) ρ)` and `d_g(F a, F b) ≤ ofReal (√(1+eps) · 2ρ)` (the
latter also gives the finiteness used at the end). For every real `r` with
`d_g(F a, F b) < ofReal r` and `√(1+eps) ρ + r < √(1-eps) R`, take a `C¹` ambient path from
`F a` to `F b` of `g`-length `< ofReal r`. Each of its points `z` satisfies
`d_g(F p, z) ≤ d_g(F p, F a) + r < √(1-eps) R = R / L` with `L = (√(1-eps))⁻¹`, so
`ball_subset_image_of_metric_lower_crossModel` (the first-exit theorem) puts the whole path
inside `F '' riemannianClosedBallOf h p R`. Pull it back by `F.symm` — `C¹` because the path
stays in `F.target` — bound the `h`-length from below with
`Chapter25.metricPathELength_map_ge` (`L = √(1-eps)`) applied to `F ∘ (F.symm ∘ γ)`, and
identify that composite with `γ` by `Manifold.pathELength_congr`. Finally
`ENNReal.le_of_forall_pos_le_add` with `r = D_g + min ((√(1-eps)R - √(1+eps)·3ρ)/2) η`.

## Public declarations

* `crossModel_edist_le_of_metric_upper`
* `crossModel_edist_ge_of_metric_equiv`
* `crossModel_edist_transfer`
* `crossModel_toReal_transfer`
* `crossModel_metricDistance_transfer`
* `crossModel_edist_transfer_of_comparison`
* `crossModel_room_of_book_constants`

All are unconditional (no `sorry`, no extra axiom-like hypothesis); everything is stated
from explicit hypotheses on `h`, `g`, `F`, `p`, `R`, `eps`, `rho`.

## Real dependencies

* `CrossModelBallCapture.ball_subset_image_of_metric_lower_crossModel` (first exit).
* `Chapter25.metricPathELength_map_le` / `metricPathELength_map_ge` (`CollarMetricControl`).
* `DistanceHessianLocal`: `exists_lt_of_edistOf_lt`, `edistOf_le_metricPathELength`,
  `metricPathELength_mono`, `metricPathELength`.
* `ModelWitness`: `riemannianClosedBallOf`, `riemannianBallOf`,
  `riemannianClosedBallOf_mono`; `DistanceScaling`: `riemannianEDistOf`,
  `riemannianEDistOf_self`.
* `Chapter25Geometry`: `metricDistance`, `MetricComparisonOn`, `I3`, `ThreeSpace`.
* Mathlib: `Manifold.riemannianEDist_triangle`, `Manifold.riemannianEDist_comm`,
  `Manifold.pathELength_congr`, `ENNReal.le_of_forall_pos_le_add`.

## Private helpers and upstream candidates

Four private lemmas are proved locally rather than editing existing files:

* `edistOf_triangle` — upstream candidate `riemannianEDistOf_triangle` in
  `Geometry/Metric/DistanceScaling.lean`.
* `edistOf_comm` — upstream candidate `riemannianEDistOf_comm` in the same file (a private
  copy already exists in `Extinction/Width/Loops.lean`, so a public version would remove two
  duplicates).
* `metricPathELength_congr_curve` — upstream candidate next to `metricPathELength_congr` in
  `Geometry/Comparison/DistanceHessianLocal.lean` (that one varies the *metric*; this one
  varies the *curve*).
* `edistOf_le_of_mem_closedBall` — two points of one closed ball are `2ρ` apart.

## Pitfalls hit while writing this file

* The `Bundle`-scoped instance `RiemannianBundle → NormedAddCommGroup (E b)` is what supplies
  `∀ x, ENorm (TangentSpace I x)`. Without `open Bundle` the three private lemmas fail with
  `failed to synthesize (x : M) → ENorm (TangentSpace I x)` even though the local
  `letI : RiemannianBundle …` is present.
* `(F.symm : M → N) y` elaborates to `↑F.symm.toPartialEquiv y` while `F.left_inv'` /
  `F.right_inv'` produce `F.invFun y`. They are defeq, so `exact` works but `rw` does not:
  state a `have hleft : (F.symm : M → N) ((F : N → M) y) = y := F.left_inv' …` first and
  rewrite with that, exactly as `CrossModelBallCapture` does.
* In this toolchain `mul_le_mul_left'` is not available; use `mul_le_mul' le_rfl h`.
  `add_le_add_left` has the "right" argument convention here; use `add_le_add le_rfl h`.
* `ENNReal.ofReal_coe_nnreal` takes its `ℝ≥0` argument implicitly; apply it as a `calc` step,
  not as `ofReal_coe_nnreal eta`.
* `open scoped Topology` inside this namespace triggers the `ambiguousOpen` linter
  (`DifferentialGeometry.Topology` shadows `_root_.Topology`); the file does not need it.
* `MetricComparisonOn.pullback_eq` holds only on the comparison set `U`, hence the hypothesis
  `riemannianClosedBallOf h p R ⊆ U` in `crossModel_edist_transfer_of_comparison`.

## Deviations from the brief

`hrho` is `0 ≤ rho` rather than `0 < rho` (the proof never needs strict positivity), and
`crossModel_room_of_book_constants` does not need `eps < 1`: `Real.sqrt eps⁻¹ > 10 L₊ + 10`
already forces `eps ≤ 1/100`.

## Verification

```
LEAN_NUM_THREADS=2 lake env lean \
  DifferentialGeometry/Geometry/Flow/RicciFlow/Perelman/CanonicalNeighborhood/CrossModelDistanceTransfer.lean
```
Empty output, ~23 s (2026-09-11). The module is not registered in `DifferentialGeometry.lean`
(reviewer's job), so the `#print axioms` audit of the seven public declarations above is still
outstanding; expected axioms are `propext`, `Classical.choice`, `Quot.sound`.

## Next step

Feed `crossModel_edist_transfer_of_comparison` to the buffered-canonical consumer in the
`lem:scn-good-point-buffered-canonical` chain: it is the step that converts the `C⁰` part of
a `WindowedModelWitness`/`StrongNeck` comparison into an honest bi-Lipschitz statement about
`metricDistance`, which the ball-sandwich bookkeeping of `CanonicalMetricSandwich` then uses.
