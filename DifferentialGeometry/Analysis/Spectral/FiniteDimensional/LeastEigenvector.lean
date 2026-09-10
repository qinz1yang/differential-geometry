import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Module.RCLike.Real

noncomputable section
open Set Metric
open scoped InnerProductSpace

namespace Poincare.Analysis

theorem exists_unit_least_eigenvector
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) :
    ∃ (μ : ℝ) (w : E), ‖w‖ = 1 ∧ A w = μ • w ∧
      ∀ x : E, ‖x‖ = 1 → μ ≤ ⟪A x, x⟫_ℝ := by
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) A.reApplyInnerSelf_continuous.continuousOn
  have hnorm : ‖w‖ = 1 := by simpa only [mem_sphere_zero_iff_norm] using hw
  have heigen := hA.eq_smul_self_of_isLocalExtrOn_real
    (show IsLocalExtrOn A.reApplyInnerSelf (sphere (0 : E) ‖w‖) w from
      hnorm ▸ Or.inl hmin.localize)
  refine ⟨⟪A w, w⟫_ℝ, w, hnorm, ?_, ?_⟩
  · simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      hnorm] using heigen
  · intro x hx
    exact hmin (mem_sphere_zero_iff_norm.mpr hx)

end Poincare.Analysis
