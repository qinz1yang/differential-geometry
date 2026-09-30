import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionResolvent
import Mathlib.Analysis.Complex.Norm

set_option autoImplicit false

noncomputable section

open ContinuousLinearMap Submodule

namespace ProjectionSpectrumApplications

private def μ : ℂ := 1 + Complex.I / 8
private def A : ℂ →L[ℂ] ℂ := μ • ContinuousLinearMap.id ℂ ℂ

private theorem close : ‖A - (⊤ : Submodule ℂ ℂ).starProjection‖ ≤ (1 / 8 : ℝ) := by
  have h : A - (⊤ : Submodule ℂ ℂ).starProjection =
      (Complex.I / 8) • ContinuousLinearMap.id ℂ ℂ := by
    rw [Submodule.starProjection_top]
    simp only [A, μ, add_smul, one_smul, add_sub_cancel_left]
  rw [h, norm_smul, norm_id]
  norm_num [norm_div]

private theorem eigen : Module.End.HasEigenvalue A.toLinearMap μ := by
  have hv : Module.End.HasEigenvector A.toLinearMap μ (1 : ℂ) := by
    refine ⟨?_, one_ne_zero⟩
    rw [Module.End.mem_eigenspace_iff]
    rfl
  exact Module.End.hasEigenvalue_of_hasEigenvector hv

private theorem mem_spectrum : μ ∈ spectrum ℂ A := by
  rw [ContinuousLinearMap.spectrum_eq]
  exact eigen.mem_spectrum

example : ‖μ‖ ≤ (1 / 8 : ℝ) ∨ ‖μ - 1‖ ≤ (1 / 8 : ℝ) :=
  norm_eigenvalue_or_sub_one_le_of_norm_sub_starProjection_le A ⊤ close eigen

example : spectrum ℂ A ⊆ Metric.closedBall 0 (1 / 8 : ℝ) ∪ Metric.closedBall 1 (1 / 8 : ℝ) :=
  spectrum_subset_closedBall_union_of_norm_sub_starProjection_le A ⊤ close

example : (3 / 8 : ℝ) ≤ ‖(3 / 2 : ℂ) - μ‖ := by
  have h := norm_sub_spectrum_ge_of_norm_sub_starProjection_le A ⊤ close
    (ζ := (3 / 2 : ℂ)) (r := 1 / 2) (by norm_num) mem_spectrum
  norm_num at h ⊢
  exact h

example : ‖μ - 1‖ ≤ (1 / 8 : ℝ) := by
  have h := eigenvector_projection_error_bounds A ⊤ close (v := (1 : ℂ)) (μ := μ) rfl
  simpa [Submodule.starProjection_top] using h.1

example :
    spectrum ℂ ((Complex.I / 8) • ContinuousLinearMap.id ℂ ℂ) ⊆
      Metric.closedBall 0 (1 / 8 : ℝ) ∪ Metric.closedBall 1 (1 / 8 : ℝ) := by
  apply spectrum_subset_closedBall_union_of_norm_sub_starProjection_le _ ⊥
  rw [Submodule.starProjection_bot, sub_zero, norm_smul, norm_id]
  norm_num [norm_div]

example (ζ : ℂ) (hζ : ‖ζ - 1‖ = (1 / 2 : ℝ)) : ‖resolvent A ζ‖ ≤ 4 := by
  have hζnorm := norm_sub_norm_le (1 : ℂ) ζ
  rw [norm_one, norm_sub_rev, hζ] at hζnorm
  have hmin : (1 / 2 : ℝ) ≤ min ‖ζ‖ ‖ζ - 1‖ := le_min (by linarith) hζ.ge
  have hgap : (1 / 4 : ℝ) < min ‖ζ‖ ‖ζ - 1‖ := by linarith
  have h := norm_resolvent_le_of_norm_sub_starProjection_le A ⊤
    (ε := (1 / 4 : ℝ)) (close.trans (by norm_num)) hgap
  exact h.trans ((div_le_iff₀ (sub_pos.mpr hgap)).mpr (by linarith))

end ProjectionSpectrumApplications
