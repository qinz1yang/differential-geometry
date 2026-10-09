import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Defs
import DifferentialGeometry.LinearAlgebra.Matrix.LoewnerDeterminant
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Comparison of parametric densities with a bilinear form

For a map `Ψ : E → M` into a Riemannian manifold modelled on `E`, the Gram matrix
`paramGramMatrix g Ψ w` is the matrix, in the basis `chartModelBasis E`, of the pull-back bilinear
form `(x, y) ↦ g(dΨ x, dΨ y)` (`paramGramMatrix_eq_toMatrix`). If a symmetric positive
semidefinite bilinear form `B` on `E` satisfies `c B ≤ Ψ*g` (resp. `Ψ*g ≤ c B`) on the diagonal, then
the determinant monotonicity in the Loewner order gives

* `rpow_mul_sqrt_det_le_paramDensity`: `c^{n/2} √det B ≤ paramDensity g Ψ w`;
* `paramDensity_le_rpow_mul_sqrt_det`: `paramDensity g Ψ w ≤ c^{n/2} √det B`,

with `n = dim E` and `det B` the Gram determinant of `B` in `chartModelBasis E`. No second metric
is needed: `B` is an arbitrary bilinear form (used for finite-order comparisons, statement V.1).
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The parametric Gram matrix is the Gram matrix of the pull-back bilinear form. -/
theorem paramGramMatrix_eq_toMatrix (g : SmoothRiemannianMetric I M) (Ψ : E → M) (w : E) :
    paramGramMatrix g Ψ w = LinearMap.BilinForm.toMatrix (chartModelBasis E)
      ((g.inner (Ψ w)).toLinearMap₁₂.compl₁₂ (mfderiv 𝓘(ℝ, E) I Ψ w).toLinearMap
        (mfderiv 𝓘(ℝ, E) I Ψ w).toLinearMap) := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, paramGramMatrix_apply]
  rfl

theorem sqrt_pow_eq_rpow {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    Real.sqrt (c ^ n) = c ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hc]
  ring_nf

theorem det_toMatrix_smul (B : LinearMap.BilinForm ℝ E) (c : ℝ) :
    (LinearMap.BilinForm.toMatrix (chartModelBasis E) (c • B)).det =
      c ^ Module.finrank ℝ E * (LinearMap.BilinForm.toMatrix (chartModelBasis E) B).det := by
  rw [LinearEquiv.map_smul, Matrix.det_smul, Fintype.card_fin]

/-- **Lower density comparison.** If `c B ≤ Ψ*g` on the diagonal (`B` symmetric, positive
semidefinite, `c ≥ 0`), then `c^{n/2} √det B ≤ paramDensity g Ψ w`. -/
theorem rpow_mul_sqrt_det_le_paramDensity (g : SmoothRiemannianMetric I M) (Ψ : E → M) (w : E)
    {B : LinearMap.BilinForm ℝ E} (hsymm : ∀ x y, B x y = B y x) (hpos : ∀ x, 0 ≤ B x x)
    {c : ℝ} (hc : 0 ≤ c)
    (hle : ∀ x : E, c * B x x ≤
      g.inner (Ψ w) (mfderiv 𝓘(ℝ, E) I Ψ w x) (mfderiv 𝓘(ℝ, E) I Ψ w x)) :
    c ^ ((Module.finrank ℝ E : ℝ) / 2) *
        Real.sqrt (LinearMap.BilinForm.toMatrix (chartModelBasis E) B).det ≤
      paramDensity g Ψ w := by
  have hdet := LinearMap.BilinForm.det_toMatrix_le_det_toMatrix (chartModelBasis E)
    (B₁ := c • B) (B₂ := (g.inner (Ψ w)).toLinearMap₁₂.compl₁₂ (mfderiv 𝓘(ℝ, E) I Ψ w).toLinearMap
        (mfderiv 𝓘(ℝ, E) I Ψ w).toLinearMap)
    (fun x y => by
      simp only [LinearMap.smul_apply]
      rw [hsymm x y])
    (fun x y => g.symm (Ψ w) _ _)
    (fun x => mul_nonneg hc (hpos x)) hle
  rw [det_toMatrix_smul, ← paramGramMatrix_eq_toMatrix] at hdet
  rw [paramDensity_apply, ← sqrt_pow_eq_rpow hc, ← Real.sqrt_mul (pow_nonneg hc _)]
  exact Real.sqrt_le_sqrt hdet

/-- **Upper density comparison.** If `Ψ*g ≤ c B` on the diagonal (`B` symmetric, `c ≥ 0`), then
`paramDensity g Ψ w ≤ c^{n/2} √det B`. -/
theorem paramDensity_le_rpow_mul_sqrt_det (g : SmoothRiemannianMetric I M) (Ψ : E → M) (w : E)
    {B : LinearMap.BilinForm ℝ E} (hsymm : ∀ x y, B x y = B y x)
    {c : ℝ} (hc : 0 ≤ c)
    (hle : ∀ x : E,
      g.inner (Ψ w) (mfderiv 𝓘(ℝ, E) I Ψ w x) (mfderiv 𝓘(ℝ, E) I Ψ w x) ≤ c * B x x) :
    paramDensity g Ψ w ≤ c ^ ((Module.finrank ℝ E : ℝ) / 2) *
        Real.sqrt (LinearMap.BilinForm.toMatrix (chartModelBasis E) B).det := by
  have hdet := LinearMap.BilinForm.det_toMatrix_le_det_toMatrix (chartModelBasis E)
    (B₁ := (g.inner (Ψ w)).toLinearMap₁₂.compl₁₂ (mfderiv 𝓘(ℝ, E) I Ψ w).toLinearMap
        (mfderiv 𝓘(ℝ, E) I Ψ w).toLinearMap) (B₂ := c • B)
    (fun x y => g.symm (Ψ w) _ _)
    (fun x y => by
      simp only [LinearMap.smul_apply]
      rw [hsymm x y])
    (fun x => metric_inner_self_nonneg g (Ψ w) _) hle
  rw [det_toMatrix_smul, ← paramGramMatrix_eq_toMatrix] at hdet
  rw [paramDensity_apply, ← sqrt_pow_eq_rpow hc, ← Real.sqrt_mul (pow_nonneg hc _)]
  exact Real.sqrt_le_sqrt hdet

end DifferentialGeometry.Integral.Measure
