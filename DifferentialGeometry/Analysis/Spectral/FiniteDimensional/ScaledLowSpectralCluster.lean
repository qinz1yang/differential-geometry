import DifferentialGeometry.Analysis.Spectral.FiniteDimensional.LowSpectralCluster

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
namespace DifferentialGeometry.Analysis
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem iInf_rayleigh_ge_scaled_relative_low_cluster
    (A B : E3 →L[ℝ] E3) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {v : E3} (hv : ‖v‖ = 1) {δ ε : ℝ}
    (hcloseA : ∀ x : E3,
      ‖(A - InnerProductSpace.rankOne ℝ v v) x‖ ≤ δ * ‖x‖)
    (hcloseB : ∀ x : E3,
      ‖(B - InnerProductSpace.rankOne ℝ v v) x‖ ≤ ε * ‖x‖)
    {t α η : ℝ} (ht : 1 ≤ t) (hα : 0 ≤ α)
    (hincrement : ∀ x : E3,
      α * (‖x‖ ^ 2 - ⟪v, x⟫_ℝ ^ 2) - η * ‖x‖ ^ 2 ≤
        ⟪(B - t • A) x, x⟫_ℝ) :
    (⨅ x : {x : E3 // x ≠ 0}, A.rayleighQuotient x) +
        α * (1 - 2 * ε) - η - (t - 1) * δ ≤
      (⨅ x : {x : E3 // x ≠ 0}, B.rayleighQuotient x) := by
  obtain ⟨_, _, _, hleastA, _, _⟩ :=
    exists_unit_least_eigenvector_low_cluster A hA hv hcloseA
  have hscale := mul_le_mul_of_nonneg_left (abs_le.mp hleastA).1 (sub_nonneg.mpr ht)
  have hgain := iInf_rayleigh_ge_relative_low_cluster A B hA hB hv hcloseB
    (le_trans zero_le_one ht) hα hincrement
  nlinarith

end DifferentialGeometry.Analysis
