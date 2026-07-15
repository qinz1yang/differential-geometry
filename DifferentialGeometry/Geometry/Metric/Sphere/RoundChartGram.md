# RoundChartGram.lean — notes

Plan: `plan-on-taking-a-spicy-kitten.md`, Step 5B, sub-goal P1. The round metric's
chart Gram matrix in the stereographic chart (toward the one-point curvature).

## State: project-side plumbing DONE (sorry-free, verified green); stereographic part = frontier

Two lemmas verified (`lake env lean`, exit 0, no sorry):

- **`extChartAt_symm_zero_sphere`** : `(extChartAt (𝓡 n) x₀).symm 0 = x₀` (the chart centre
  fact). Route that worked: `(extChartAt (𝓡 n) x₀).symm 0 = (stereographic' n (-x₀)).symm 0`
  (`rfl`!), then `apply Subtype.ext`, `simp only [stereographic'_symm_apply]`, a separate
  `hz : (↑(repr.symm 0) : E) = 0` proven by `rw [map_zero]; rfl`, `rw [hz]`, then `simp only`
  the zeros + `coe_neg_sphere` + `module`.
- **`chartGramOnE_roundMetric`** : `chartGramOnE roundMetric x₀ i j y =
  ⟪dIncl p (chartBasisVecFiber x₀ i p), dIncl p (chartBasisVecFiber x₀ j p)⟫`,
  `p = (extChartAt (𝓡 n) x₀).symm y`. Proof: `rw [chartGramOnE_def, chartGramMatrix_apply,
  roundMetric_inner]` (one line — the project-side reduction).

## Gotchas hit

- `chartGramOnE` lives in `DifferentialGeometry.Integral.DivergenceTheorem` (Hessian.lean,
  must `import` it); `chartBasisVecFiber`/`chartGramMatrix` in `…Integral.Measure` (ChartGram.lean).
- Needs `[NeZero n]` + a LOCAL instance `NeZero (finrank ℝ (EuclideanSpace ℝ (Fin n)))` (via
  `finrank_euclideanSpace_fin`) — `chartModelBasis` in the chart machinery requires it. The
  center fact does NOT need `[NeZero n]` → `omit [NeZero n] in` before it (omit goes BEFORE the
  docstring).
- `map_zero` would NOT fire via `simp` on `repr.symm 0` (LinearIsometryEquiv) — only `rw [map_zero]`
  worked. `stereographic_neg_apply` likewise mis-matched on the hidden norm proof `⋯`.

## The remaining frontier (the stereographic computation)

The 0-jet `chartGramOnE roundMetric x₀ i j 0 = δ i j` needs: the dIncl-pushed chart frame at the
centre is ambient-orthonormal, i.e.
`⟪dIncl x₀ (chartBasisVecFiber x₀ i x₀), dIncl x₀ (chartBasisVecFiber x₀ j x₀)⟫ = δ i j`.
This is the genuinely deep part and is BLOCKED on two interface lemmas:
1. **chart-frame ↔ `eᵢ`**: `mfderiv (extChartAt I α) x (chartBasisVecFiber α i x) = chartModelBasis E i`
   — exists but `private` (POUReduction.lean:131, also Gradient.lean). Reprove (~20 lines via
   `trivializationAt` + `TangentBundle.continuousLinearMapAt_trivializationAt` +
   `Trivialization.continuousLinearMapAt_symmL`) or de-privatize.
2. **explicit `mfderiv ι x₀`**: Mathlib's `range_mfderiv_coe_sphere` gives only the RANGE
   `(ℝ∙x₀)ᗮ`, not the exact map. Re-derive `mfderiv ι x₀ = subtypeL ∘ U.symm ∘ (chart deriv)` (an
   isometry at the centre) from `hasFDerivAt_stereoInvFunAux` (= `id` at 0) + the chain rule, then
   `⟪U.symm eᵢ, U.symm eⱼ⟫ = δ` (U a `LinearIsometryEquiv`).
Then P2 (the 2-jet ∂²g(0), away from the centre) and P3 (Christoffel/Riemann) follow. This is the
major remaining computation — a focused effort, Pro-consult candidate for the explicit `mfderiv ι`.
