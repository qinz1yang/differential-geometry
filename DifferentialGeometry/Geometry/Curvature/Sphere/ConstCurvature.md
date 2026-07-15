# ConstCurvature.lean — notes

Plan: `plan-on-taking-a-spicy-kitten.md`, step 5. The round sphere has constant
positive sectional curvature, via one-point computation + O(n+1) homogeneity.

## State: 5A DONE (sorry-free); 5B (one-point computation) + capstone NOT started

`metricRm04_round_invariant` (Step 5A) — VERIFIED GREEN, sorry-free: the metric
`(0,4)` Riemann tensor of the round metric is invariant under `sphereDiffeo e`:
`metricRm04StdAt roundMetric x X Y Z W = metricRm04StdAt roundMetric (φx)(dφ X)(dφ Y)(dφ Z)(dφ W)`.
Proof: `have h := metricRm04Std_pullback roundMetric (sphereDiffeo e) x X Y Z W;
rwa [pullbackMetric_round_eq] at h`.

Gotchas:
- Needs `[NeZero n]` in the variable block (the sphere's dimension), then
  `haveI : NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n))) := by rw [finrank_euclideanSpace_fin]; infer_instance`
  — `metricRm04Std_pullback` requires `[NeZero (finrank ℝ model)]`.
- The heavier `metricRm04Std_pullback` instances on the sphere:
  `haveI : IsManifold (𝓡 n) 1 (sphere 0 1) := EuclideanSpace.instIsManifoldSphere.of_le le_top`
  and the `(∞+1)` analogue; `SigmaCompactSpace`/`T2Space`/`BoundarylessManifold` auto.
- `CoordRm04Bridge` import was dropped for now (only needed for 5B); re-add it for the
  one-point computation.

## Remaining: 5B + capstone — ROUTE PIVOTED to GAUSS / shape-operator (user choice 2026-06-29)

The stereographic-chart 2-jet route below is SUPERSEDED. `metricRm04_round_invariant` (5A) and the
chart-Gram lemmas in `RoundChartGram.lean` are NOT used by the Gauss route (kept, harmless). The
Gauss route gives the curvature at EVERY point directly (no homogeneity / point-transitivity needed).

- **5B-A DONE (verified sorry-free):** `Geometry/Metric/Sphere/RoundProjConn.lean` — `projConnCD`,
  the tangential-projection connection as a bundled `CovariantDerivative`, with `dIncl_projConn`
  characterization + `ambDeriv`. See `RoundProjConn.md`.
- **5B-B (`RoundProjConnLC.lean`):** `projConn ≐ metricCov roundMetric` on differentiable sections via
  Koszul uniqueness (`koszul_levi_civita_unique_of_torsionFree_metricCompatible`). Needs the ambient
  bracket identity `dIncl x (mlieBracket X Y x) = ambDeriv Y x (X x) − ambDeriv X x (Y x)` (B1,
  RHS tangent ⇒ projection fixes it) + the ambient inner-product product rule (B2, reduce to
  `HasFDerivAt.inner`; do NOT reuse the Levi-Civita metric-compat lemmas — circular).
- **5B-C (`RoundShape.lean`):** normal = position `x`; Gauss formula `D_X Y = ∇_X Y − ⟪X,Y⟫·x`
  (so `⟪ambDeriv Y x v, x⟫ = −roundInner x (Y x) v`); expand `riemannCurvatureAux (metricCov g)`,
  substitute projConn via 5B-B (only on the differentiable sections that occur — Koszul gives
  pointwise eq on `MDiffAt` inputs only), Gauss ⇒ `Rm04 X Y Y X = ⟪X,X⟫⟪Y,Y⟫ − ⟪X,Y⟫²`. Sign:
  with `S = −Dν` the shape operator is `−Id` (don't mislabel it `Id`), but the Gauss equation still
  gives `+Gram`, c = 1. (Pro-review-confirmed 2026-06-29.)
- **Capstone `roundMetric_constPosSec : ConstPosSecMetric roundMetric`** (extend this file, ~10 lines):
  `⟨1, one_pos, fun x X Y => by rw [metricRm04StdAt_apply, riemannCurvature04At_apply_const, 5B-C]; ring⟩`.
