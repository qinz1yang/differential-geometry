# SegmentDensity.lean — L2 of the A0′ lane (the density identity past the cut locus)

Verification: **PASS** (focused check + targeted module build `+…Volume.SegmentDensity`,
sorry-free, grep-clean of `sorry`/`admit`, no new axioms/classes/instances/notation).

## Result

`exp_density_curve` (deliverable L2): for a base point `x`, launch vector `v`, and a
chart center `y₀` whose chart contains `expMapIntrinsic x v`,
```
chartDensity g y₀ (expMapIntrinsic x v) · |det D(extChartAt y₀ ∘ expMapIntrinsic x)_v|
  = curveDensity g (intrinsicGeodesic x v) (fun i t ↦ intrinsicJacobi x v (chartModelBasis E i) t) 1.
```
LHS is exactly the `MeasureTheory.image_lintegral_le` integrand
(`chartDensity`-weight × Euclidean `|det fderiv|`) with `f = extChartAt y₀ ∘ exp_x`.
RHS is the intrinsic Riemannian Jacobian = `curveDensity` of the endpoint Jacobi frame.

## Route chosen: **Route C (diffeo-free port)** — and WHY

The route-decider scout established the decisive fact: the
`paramDensity_eq_abs_det_mul_chartDensity` chain
(`ParamEvaluation.lean:162→239→293→334→354`) is **invertibility-free** — it touches
`Ψ` only through `hw ∈ Ψ.source ⟹ MDifferentiableAt Ψ w` and `hx ∈ baseSet` (chart
validity); the trivialization equiv `T₀.continuousLinearEquivAt` is Ψ-independent
(always invertible).  So the identity needs **no local diffeomorphism, no manifold
IFT, no nonconjugacy** — only `MDifferentiableAt`, which `intrinsicFiber_smooth`
supplies for `expMapIntrinsic` everywhere.

Routes rejected:
- **Route A (local `PartialDiffeomorph` at nonconjugate `v` + reuse the param
  lemmas).**  The forward manifold IFT exists (`contMDiffAt_isLocalDiffeomorphAt` /
  `hlocAt_infty'`, `Coordinates/LocalDiffeoIFT.lean`), but its input is chart-level
  `fderiv` invertibility, which needs an **un-built** bridge `¬IsConjVec ⟹
  (fderiv (writtenInExtChartAt … exp) v).IsInvertible` plus `EventuallyEq` transfer
  of `mfderiv`/`fderiv` from the IFT-produced Φ back to `exp` — strictly more work
  for a strictly weaker (nonconjugate-only) result.
- **Route B (duplicate the whole param layer as general-map defs).**  ~10 new
  defs/lemmas; unnecessary since only one lemma (`paramDeriv_chartBasis_eq_sum`)
  touches differentiability.

Because Route C is invertibility-free, the stated identity **drops the nonconjugacy
hypothesis** and holds for **all** `v` (at a conjugate `v` both sides are `0`:
`det J = 0` ⇒ LHS `= 0`, and `det curveGram = (det J)²·det chartGram = 0` ⇒ RHS `= 0`).
This is strictly stronger than the plan's "conjugate-free directions" scope.

## What was ported / built (reusable, general-map)

1. `mfderiv_chartBasis` (public) — diffeo-free port of `paramDeriv_chartBasis_eq_sum`:
   for any `MDifferentiableAt f w` with `f w` in the `y₀`-chart,
   `mfderiv f w (bᵢ) = ∑ k, (LinearMap.toMatrix cmb cmb (fderiv (extChartAt y₀ ∘ f) w)) k i • chartBasisVecFiber y₀ k (f w)`.
   Verbatim port with `Ψ w → f w`, `hΨdiff → hf`; the trivialization/chart machinery is unchanged.
2. `gramDiff_det` (public) — diffeo-free port of `paramGramMatrix_det_pullback`:
   `det (Matrix.of fun i j ↦ g.inner (f w) (mfderiv f w bᵢ) (mfderiv f w bⱼ))
      = (fderiv (extChartAt y₀ ∘ f) w).det ^ 2 · (chartGramMatrix g y₀ (f w)).det`
   for every differentiable `f : E → M`.  (Gram `= Jᵀ·chartGram·J` entrywise via
   bilinearity + `mfderiv_chartBasis`, then `det_mul`/`det_transpose`/`det_toMatrix`.)
   This is the reusable "Riemannian area Jacobian" lemma — a candidate to promote to
   `Analysis/Integration/Measure/` later (kept here to avoid editing the settled
   `ParamEvaluation.lean`; scope-locked to the brick).
3. `exp_density_curve` (public, the L2 endpoint) — instantiates `gramDiff_det` at
   `f = fun b ↦ expMapIntrinsic x b` (differentiable via `intrinsicFiber_smooth`),
   identifies the differential columns with the endpoint Jacobi frame via
   `intrinsic_jacobi_one` (so `curveGram … 1 = ` the differential-column Gram), and
   finishes with `√(det) = |det J|·chartDensity` (`Real.sqrt_mul`, `sqrt_sq_eq_abs`).

## Key ingredients reused (all sorry-free, past the cut locus)

- `intrinsic_jacobi_one` (`JacobiVariation.lean:257`): `mfderiv(exp_x) v w = intrinsicJacobi x v w 1`, un-capped.
- `intrinsicFiber_smooth` (`IntrinsicVelocity.lean:191`): global C∞ of `exp_x` in `v` (= L1).
- `curveGram`/`curveDensity` (`Variation/JacobiGram.lean`); `chartGramMatrix`/`chartModelBasis`/`chartBasisVecFiber` (`Metric/ChartGram.lean`); `chartDensity` (`ChartDensity.lean`).

## What B5c can consume

`exp_density_curve` turns the `image_lintegral_le` integrand into `curveDensity` of
the intrinsic Jacobi frame; B5c then does the polar decomposition (Gauss lemma:
radial × transverse) and applies the `(β)` bound `intrDens_le_hyp`/`exists_intrRatio`
(a transverse `(n-1)`-frame `curveDensity ≤ N·hypDensity`) to reach the model
`hypRadVol`, discharging `SegmentPolar.lean`'s `segBall_vol_le`/`segBall_vol_rel`.
Note the frame here is the **full** `chartModelBasis`-generated frame (`n` columns);
the radial/transverse split is B5c's step, not L2's.

## Lean notes

- `intrinsicJacobi` lives in `Exponential/EndpointShape.lean`, NOT transitively
  imported by `JacobiVariation` — needs an explicit `import`.
- `intrinsicJacobi (I := I) …` fails ("Invalid argument name I"); drop `(I := I)`,
  `g` pins `I`.  `curveDensity`/`intrinsicGeodesic` accept `(I := I)`.
- `intrinsic_jacobi_one`'s LHS is defeq to `intrinsicJacobi … 1` (the `show
  TangentSpace I x from …` coercion around the `+`/`•` is the identity), so the
  column identification closes by `exact intrinsic_jacobi_one …`.
- Per-theorem `attribute [-instance] Tensor0SBundle.tangentSpace_normed*` needed on
  the `g.inner`-using lemmas (`gramDiff_det`, `exp_density_curve`); `mfderiv_chartBasis`
  does not use `g` and does not need it.
