import DifferentialGeometry.Analysis.Spectral.FiniteDimensional.TransverseSpectralGap

noncomputable section
open scoped InnerProductSpace

namespace DifferentialGeometry.Analysis

theorem is_least_eigenvalue_of_axis_error
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (v : E) {κ ε μ : ℝ}
    (herror : ∀ x : E, ‖A x - κ • (x - ⟪v, x⟫_ℝ • v)‖ ≤ ε * ‖x‖)
    (w : E) (hw : ‖w‖ = 1) (heigen : A w = μ • w) (hμ : μ < κ - ε) :
    ∀ x : E, ‖x‖ = 1 → μ ≤ ⟪A x, x⟫_ℝ := by
  have hlower (x : E) (hx : ⟪v, x⟫_ℝ = 0) :
      (κ - ε) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ := by
    have herr := herror x
    rw [hx, zero_smul, sub_zero] at herr
    have hb := (abs_real_inner_le_norm (A x - κ • x) x).trans
      (mul_le_mul_of_nonneg_right herr (norm_nonneg x))
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hb
    have hh := (abs_le.mp hb).1
    nlinarith
  have hwne : w ≠ 0 := fun hz ↦ by simp [hz] at hw
  let : Nontrivial E := nontrivial_of_ne w 0 hwne
  obtain ⟨ν, u, hu, heu, hmin⟩ := exists_unit_least_eigenvector A hA
  have hν : ν ≤ μ := by
    have h := hmin w hw
    simpa [heigen, real_inner_smul_left, real_inner_self_eq_norm_sq, hw] using h
  have heq := eigenvalue_eq_of_lt_transverse_lower_bound A hA.isSymmetric v (κ - ε)
    hlower u w hu hw heu heigen (hν.trans_lt hμ) hμ
  exact heq ▸ hmin

end DifferentialGeometry.Analysis
