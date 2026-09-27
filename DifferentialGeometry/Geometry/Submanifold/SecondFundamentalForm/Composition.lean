import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise

noncomputable section

open Function Manifold
open scoped ContDiff Manifold
namespace DifferentialGeometry.Geometry

variable {E₁ E₂ E₃ H₁ H₂ H₃ M₁ M₂ M₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [FiniteDimensional ℝ E₃]
  [TopologicalSpace H₃] {I₃ : ModelWithCorners ℝ E₃ H₃}
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃] [IsManifold I₃ ∞ M₃]

theorem secondFundamentalFormDiagonalAlongCurve_comp
    (g₁ : SmoothRiemannianMetric I₁ M₁) (g₂ : SmoothRiemannianMetric I₂ M₂)
    (g₃ : SmoothRiemannianMetric I₃ M₃) {f : M₁ → M₂} {j : M₂ → M₃}
    (hf : ContMDiff I₁ I₂ ∞ f) (hj : ContMDiff I₂ I₃ ∞ j)
    (γ : ℝ → M₁) (t : ℝ) :
    secondFundamentalFormDiagonalAlongCurve g₁ g₃ (j ∘ f) γ t =
      secondFundamentalFormDiagonalAlongCurve g₂ g₃ j (fun s => f (γ s)) t +
        mfderiv I₂ I₃ j (f (γ t))
          (secondFundamentalFormDiagonalAlongCurve g₁ g₂ f γ t) := by
  rw [secondFundamentalFormDiagonalAlongCurve_def,
    secondFundamentalFormDiagonalAlongCurve_def,
    secondFundamentalFormDiagonalAlongCurve_def,
    mfderiv_comp (γ t) (hj.mdifferentiable (by simp) _) (hf.mdifferentiable (by simp) _)]
  change _ - _ = (_ - _) + _
  rw [map_sub]
  abel

theorem hasVanishingSecondFundamentalFormAlongCurves_of_comp_of_inner_map
    [I₂.Boundaryless] [I₃.Boundaryless]
    {g₁ : SmoothRiemannianMetric I₁ M₁} {g₂ : SmoothRiemannianMetric I₂ M₂}
    {g₃ : SmoothRiemannianMetric I₃ M₃} {f : M₁ → M₂} {j : M₂ → M₃}
    (hj : ContMDiff I₂ I₃ ∞ j)
    (hmetric : ∀ (x : M₂) (u v : TangentSpace I₂ x),
      g₃.inner (j x) (mfderiv I₂ I₃ j x u) (mfderiv I₂ I₃ j x v) = g₂.inner x u v)
    (hf : ContMDiff I₁ I₂ ∞ f)
    (hc : hasVanishingSecondFundamentalFormAlongCurves g₁ g₃ (j ∘ f)) :
    hasVanishingSecondFundamentalFormAlongCurves g₁ g₂ f := by
  intro γ t hγ
  let B := secondFundamentalFormDiagonalAlongCurve g₁ g₂ f γ t
  let C := secondFundamentalFormDiagonalAlongCurve g₂ g₃ j (fun s => f (γ s)) t
  let J := mfderiv I₂ I₃ j (f (γ t))
  have hsum : C + J B = 0 := by
    rw [← secondFundamentalFormDiagonalAlongCurve_comp g₁ g₂ g₃ hf hj]
    exact hc γ t hγ
  have hC : g₃.inner (j (f (γ t))) C (J B) = 0 := by
    have hd := secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero_of_inner_map hj hmetric
      (f (γ t)) (mfderiv 𝓘(ℝ, ℝ) I₂ (fun s => f (γ s)) t 1)
      (mfderiv 𝓘(ℝ, ℝ) I₂ (fun s => f (γ s)) t 1) B
    rw [secondFundamentalFormAmbientAt_diagonal_along_curve g₂ g₃ hj
      (fun s => f (γ s)) (hf.comp hγ) t] at hd
    exact hd
  have hinner : g₃.inner (j (f (γ t))) (J B) (J B) = 0 := by
    have hz := congrArg (fun v => g₃.inner (j (f (γ t))) v (J B)) hsum
    rw [map_add, add_apply, hC, zero_add, map_zero, zero_apply] at hz
    exact hz
  have hB : B = 0 := by
    by_contra hne
    exact (ne_of_gt (g₂.pos (f (γ t)) B hne)) ((hmetric (f (γ t)) B B).symm.trans hinner)
  exact hB

namespace IsRiemannianIsometricImmersion

theorem hasVanishingSecondFundamentalFormAlongCurves_of_comp
    [I₂.Boundaryless] [I₃.Boundaryless]
    {g₁ : SmoothRiemannianMetric I₁ M₁} {g₂ : SmoothRiemannianMetric I₂ M₂}
    {g₃ : SmoothRiemannianMetric I₃ M₃} {f : M₁ → M₂} {j : M₂ → M₃}
    (hj : IsRiemannianIsometricImmersion g₂ g₃ j)
    (hf : ContMDiff I₁ I₂ ∞ f)
    (hc : hasVanishingSecondFundamentalFormAlongCurves g₁ g₃ (j ∘ f)) :
    hasVanishingSecondFundamentalFormAlongCurves g₁ g₂ f :=
  hasVanishingSecondFundamentalFormAlongCurves_of_comp_of_inner_map hj.contMDiff hj.inner_map hf hc

end IsRiemannianIsometricImmersion
end DifferentialGeometry.Geometry
