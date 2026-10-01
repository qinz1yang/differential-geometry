import DifferentialGeometry.Analysis.InnerProductSpace.Complexification
import DifferentialGeometry.LinearAlgebra.TensorProduct.BaseChange
import Mathlib.Analysis.InnerProductSpace.Spectrum

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace LinearMap.IsSymmetric

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem iSup_eigenspace_complexify {A : H →L[ℝ] H}
    (hA : A.toLinearMap.IsSymmetric) (S : Set ℂ) :
    (⨆ μ ∈ S, Module.End.eigenspace A.complexify.toLinearMap μ) =
      (⨆ r : ℝ, ⨆ (_ : (r : ℂ) ∈ S), Module.End.eigenspace A.toLinearMap r).baseChange ℂ := by
  simp only [Submodule.baseChange_iSup]
  apply le_antisymm
  · apply iSup_le
    intro μ
    apply iSup_le
    intro hμ
    by_cases hbot : Module.End.eigenspace A.complexify.toLinearMap μ = ⊥
    · rw [hbot]
      exact bot_le
    · obtain ⟨r, rfl⟩ := RCLike.conj_eq_iff_real.mp
        (hA.complexify.conj_eigenvalue_eq_self hbot)
      change Module.End.eigenspace (A.toLinearMap.baseChange ℂ) (algebraMap ℝ ℂ r) ≤ _
      rw [Module.End.eigenspace_baseChange]
      exact le_iSup_of_le r (le_iSup_of_le hμ le_rfl)
  · apply iSup_le
    intro r
    apply iSup_le
    intro hr
    rw [← Module.End.eigenspace_baseChange]
    exact le_iSup_of_le (r : ℂ) (le_iSup_of_le hr le_rfl)

theorem iSup_eigenspace_ball_complexify {A : H →L[ℝ] H}
    (hA : A.toLinearMap.IsSymmetric) (c r : ℝ) :
    (⨆ μ ∈ Metric.ball (c : ℂ) r, Module.End.eigenspace A.complexify.toLinearMap μ) =
      (⨆ μ ∈ Metric.ball c r, Module.End.eigenspace A.toLinearMap μ).baseChange ℂ := by
  rw [hA.iSup_eigenspace_complexify]
  congr 1
  apply iSup_congr
  intro μ
  have hmem : (μ : ℂ) ∈ Metric.ball (c : ℂ) r ↔ μ ∈ Metric.ball c r := by
    simp only [Metric.mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real]
  simp only [hmem]

theorem starProjection_eigenspace_ball_complexify [FiniteDimensional ℝ H]
    {A : H →L[ℝ] H} (hA : A.toLinearMap.IsSymmetric) (c r : ℝ) :
    (⨆ μ ∈ Metric.ball c r, Module.End.eigenspace A.toLinearMap μ).starProjection.complexify =
      (⨆ μ ∈ Metric.ball (c : ℂ) r,
        Module.End.eigenspace A.complexify.toLinearMap μ).starProjection := by
  rw [hA.iSup_eigenspace_ball_complexify, Submodule.complexify_starProjection]

end LinearMap.IsSymmetric
