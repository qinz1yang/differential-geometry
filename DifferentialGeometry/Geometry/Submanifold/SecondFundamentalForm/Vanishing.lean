import DifferentialGeometry.Topology.Manifold.CurveExtension
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise

noncomputable section

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

variable {E₁ E₂ H₁ H₂ M₁ M₂ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [I₁.Boundaryless]
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]

theorem secondFundamentalFormAmbientAt_eq_zero_of_along_curves
    {g₁ : SmoothRiemannianMetric I₁ M₁} {g₂ : SmoothRiemannianMetric I₂ M₂}
    {f : M₁ → M₂} (hf : ContMDiff I₁ I₂ ∞ f)
    (hc : hasVanishingSecondFundamentalFormAlongCurves g₁ g₂ f) (x : M₁) :
    secondFundamentalFormAmbientAt g₁ g₂ f x = 0 := by
  have hdiag (v : TangentSpace I₁ x) :
      secondFundamentalFormAmbientAt g₁ g₂ f x v v = 0 := by
    obtain ⟨γ, hγ, _, hv⟩ := exists_contMDiff_curve_with_velocity_range_subset
      (I := I₁) BoundarylessManifold.isInteriorPoint v (Filter.univ_mem : Set.univ ∈ 𝓝 x)
    have heq := congrArg
      (fun q : TangentBundle I₁ M₁ =>
        (secondFundamentalFormAmbientAt g₁ g₂ f q.1 q.2 q.2 : E₂)) hv
    have hz := hc γ 0 hγ
    rw [← secondFundamentalFormAmbientAt_diagonal_along_curve g₁ g₂ hf γ hγ 0] at hz
    exact heq.symm.trans hz
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have hsum := hdiag (u + v)
  simp only [map_add, add_apply, hdiag u, hdiag v, zero_add, add_zero] at hsum
  rw [secondFundamentalFormAmbientAt_symmetric g₁ g₂
    (hf.contMDiffAt.of_le (by decide : (2 : ℕ∞ω) ≤ ∞)) v u] at hsum
  have htwo : (2 : ℝ) • secondFundamentalFormAmbientAt g₁ g₂ f x u v = 0 := by
    simpa only [two_smul] using hsum
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem hasVanishingSecondFundamentalFormAlongCurves_iff
    {g₁ : SmoothRiemannianMetric I₁ M₁} {g₂ : SmoothRiemannianMetric I₂ M₂}
    {f : M₁ → M₂} (hf : ContMDiff I₁ I₂ ∞ f) :
    hasVanishingSecondFundamentalFormAlongCurves g₁ g₂ f ↔
      ∀ x, secondFundamentalFormAmbientAt g₁ g₂ f x = 0 := by
  refine ⟨fun hc x => secondFundamentalFormAmbientAt_eq_zero_of_along_curves hf hc x, ?_⟩
  intro hzero γ t hγ
  rw [← secondFundamentalFormAmbientAt_diagonal_along_curve g₁ g₂ hf γ hγ t, hzero (γ t)]
  rfl

end DifferentialGeometry.Geometry
