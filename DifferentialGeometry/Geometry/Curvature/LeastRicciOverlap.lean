import DifferentialGeometry.Geometry.Curvature.RicciEigenpairUniqueness

noncomputable section
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Curvature

theorem least_ricci_eigenpair_eq_of_signed_covector_error
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [BoundarylessManifold I M]
    (g : SmoothRiemannianMetric I M) (x : M)
    (ℓ₀ ℓ₁ : TangentSpace I x →ₗ[ℝ] ℝ)
    (μ ν : ℝ) (v w : TangentSpace I x)
    (hv : g.inner x v v = 1) (hw : g.inner x w w = 1)
    (hev : ricciSharp g x v = μ • v) (hew : ricciSharp g x w = ν • w)
    (hminv : ∀ z : TangentSpace I x, g.inner x z z = 1 → μ ≤ ricciTensor g x z z)
    (hminw : ∀ z : TangentSpace I x, g.inner x z z = 1 → ν ≤ ricciTensor g x z z)
    (hsimple : Module.End.eigenspace (ricciSharp g x).toLinearMap ν = Submodule.span ℝ {w})
    (σ η₀ η₁ δ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (h₀ : |ℓ₀ v - 1| ≤ η₀) (h₁ : |ℓ₁ w - 1| ≤ η₁)
    (hη₀ : η₀ < 1) (herror : η₁ + δ < 1)
    (hoverlap : ∀ z : TangentSpace I x,
      |ℓ₀ z - σ * ℓ₁ z| ≤ δ * Real.sqrt (g.inner x z z)) :
    μ = ν ∧ v = σ • w ∧ |ℓ₀ (σ • w) - 1| ≤ η₁ + δ := by
  have hσsq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσne : σ ≠ 0 := by intro h; rw [h, zero_mul] at hσsq; norm_num at hσsq
  have hun : g.inner x (σ • w) (σ • w) = 1 := by
    simp only [map_smul, smul_apply, smul_eq_mul, hw, mul_one, hσsq]
  have he : ricciSharp g x (σ • w) = ν • (σ • w) := by rw [map_smul, hew, smul_comm]
  have hs : Module.End.eigenspace (ricciSharp g x).toLinearMap ν = Submodule.span ℝ {σ • w} := by
    rw [Submodule.span_singleton_smul_eq hσne.isUnit, hsimple]
  have hcross : |ℓ₀ (σ • w) - ℓ₁ w| ≤ δ := by
    have h := hoverlap w
    rw [hw, Real.sqrt_one, mul_one] at h
    rcases hσ with rfl | rfl
    · simpa only [one_smul, one_mul] using h
    · have heq : ℓ₀ ((-1 : ℝ) • w) - ℓ₁ w = -(ℓ₀ w + ℓ₁ w) := by
        rw [neg_one_smul, map_neg]
        ring
      rw [heq, abs_neg]
      simpa only [neg_one_mul, sub_neg_eq_add] using h
  have hb : |ℓ₀ (σ • w) - 1| ≤ η₁ + δ := by
    have ht := abs_add_le (ℓ₀ (σ • w) - ℓ₁ w) (ℓ₁ w - 1)
    rw [sub_add_sub_cancel] at ht
    linarith only [ht, hcross, h₁]
  have hpv : 0 < ℓ₀ v := by have h := (abs_le.mp h₀).1; linarith only [h, hη₀]
  have hpw : 0 < ℓ₀ (σ • w) := by have h := (abs_le.mp hb).1; linarith only [h, herror]
  obtain ⟨hμ, hvw⟩ := least_ricci_eigenpair_eq_of_positive_functional g x ℓ₀ μ ν v (σ • w)
    hv hun hev he hminv hminw hs hpv hpw
  exact ⟨hμ, hvw, hb⟩

end DifferentialGeometry.Geometry.Curvature
