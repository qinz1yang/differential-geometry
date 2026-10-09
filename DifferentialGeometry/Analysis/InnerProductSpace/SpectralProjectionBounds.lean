import DifferentialGeometry.Analysis.InnerProductSpace.SpectralProjection
import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionRankStability
import DifferentialGeometry.Analysis.InnerProductSpace.ProjectionResolvent
import DifferentialGeometry.Analysis.Integration.Integral.Resolvent

set_option autoImplicit false

noncomputable section

open Complex Metric
open scoped NNReal

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

theorem norm_starProjection_eigenspace_ball_sub_le (A : H →L[ℂ] H)
    (hA : A.toLinearMap.IsSymmetric) (P : Submodule ℂ H)
    (hclose : ‖A - P.starProjection‖ ≤ 1 / 4) :
    ‖(⨆ μ ∈ ball (1 : ℂ) (1 / 2), Module.End.eigenspace A.toLinearMap μ).starProjection -
      P.starProjection‖ ≤ 4 * ‖A - P.starProjection‖ := by
  let : CompleteSpace H := FiniteDimensional.complete ℂ H
  have hg {z : ℂ} (hz : z ∈ sphere (1 : ℂ) (1 / 2)) : 1 / 2 ≤ min ‖z‖ ‖z - 1‖ := by
    rw [Metric.mem_sphere, dist_eq_norm] at hz
    have hn := norm_sub_norm_le (1 : ℂ) z
    rw [norm_one, norm_sub_rev, hz] at hn
    exact le_min (by linarith) hz.ge
  have ha : sphere (1 : ℂ) (1 / 2) ⊆ resolventSet ℂ A := by
    intro z hz
    apply mem_resolventSet_of_norm_sub_starProjection_lt A P
    exact hclose.trans_lt (lt_of_lt_of_le (by norm_num) (hg hz))
  have hb : sphere (1 : ℂ) (1 / 2) ⊆ resolventSet ℂ P.starProjection := by
    intro z hz
    apply mem_resolventSet_of_norm_sub_starProjection_lt P.starProjection P
    simpa only [sub_self, norm_zero] using lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hg hz)
  have hK (z : ℂ) (hz : z ∈ sphere (1 : ℂ) (1 / 2)) : ‖resolvent A z‖ ≤ (4 : ℝ≥0) := by
    have hgap : (1 : ℝ) / 4 < min ‖z‖ ‖z - 1‖ := lt_of_lt_of_le (by norm_num) (hg hz)
    apply (norm_resolvent_le_of_norm_sub_starProjection_le A P hclose hgap).trans
    apply (div_le_iff₀ (sub_pos.mpr hgap)).mpr
    have hh := hg hz
    norm_num only [NNReal.coe_ofNat, sub_zero]
    linarith
  have hL (z : ℂ) (hz : z ∈ sphere (1 : ℂ) (1 / 2)) :
      ‖resolvent P.starProjection z‖ ≤ (2 : ℝ≥0) := by
    have hgap : (0 : ℝ) < min ‖z‖ ‖z - 1‖ := lt_of_lt_of_le (by norm_num) (hg hz)
    apply (norm_resolvent_le_of_norm_sub_starProjection_le P.starProjection P
      (by simp : ‖P.starProjection - P.starProjection‖ ≤ (0 : ℝ)) hgap).trans
    apply (div_le_iff₀ (sub_pos.mpr hgap)).mpr
    have hh := hg hz
    norm_num only [NNReal.coe_ofNat, sub_zero]
    linarith
  have hsel := P.iSup_eigenspace_starProjection_eq (ball (1 : ℂ) (1 / 2))
    (by norm_num [Metric.mem_ball, dist_eq_norm])
    (by norm_num [Metric.mem_ball, dist_eq_norm])
  have hQA := circleIntegral_resolvent_eq_starProjection A hA (by norm_num : (0 : ℝ) ≤ 1 / 2) ha
  have hQP := circleIntegral_resolvent_eq_starProjection P.starProjection P.starProjection_isSymmetric
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hb
  rw [hsel] at hQP
  have hbound := spectrum.norm_normalized_circleIntegral_resolvent_sub_le A P.starProjection
    (by norm_num : (0 : ℝ) ≤ 1 / 2) ha hb 4 2 hK hL
  rw [hQA, hQP] at hbound
  calc
    _ ≤ (1 / 2 : ℝ) * ((4 : ℝ≥0) * ‖A - P.starProjection‖ * (2 : ℝ≥0)) :=
      hbound
    _ = 4 * ‖A - P.starProjection‖ := by norm_num; ring

theorem finrank_eigenspace_ball_eq_of_norm_sub_starProjection_lt (A : H →L[ℂ] H)
    (hA : A.toLinearMap.IsSymmetric) (P : Submodule ℂ H)
    (hclose : ‖A - P.starProjection‖ < 1 / 4) :
    Module.finrank ℂ (⨆ μ ∈ ball (1 : ℂ) (1 / 2), Module.End.eigenspace A.toLinearMap μ : Submodule ℂ H) =
      Module.finrank ℂ P := by
  apply Submodule.finrank_eq_of_norm_starProjection_sub_lt_one
  have hbound := norm_starProjection_eigenspace_ball_sub_le A hA P hclose.le
  linarith

end ContinuousLinearMap
