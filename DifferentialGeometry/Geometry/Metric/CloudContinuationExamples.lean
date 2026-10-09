import DifferentialGeometry.Geometry.Metric.CloudPerturbedInputBindings
import DifferentialGeometry.Geometry.Metric.CloudCoordinateLocalityBindings
import DifferentialGeometry.Geometry.Metric.OriginalPacketScaleBindings
import DifferentialGeometry.Analysis.Calculus.Cutoff.Ball

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators
namespace GC.MetricGeometry.CloudContinuationExamples

theorem affine_perturbed_displacement (y : ℝ) (hy : y ∈ ball (0 : ℝ) 2) :
    ‖2 * y - y‖ ≤ (5 / 3 : ℝ) * 2 + 2 * ‖y‖ := by
  have hh := nearest_displacement_at_perturbed_input (fun q : ℝ => 2 * q)
    (ContinuousLinearMap.id ℝ ℝ) 0 y (r := 2) (ρ := 1) (σ := 2) (ε := 1)
    (E := ‖y‖) (by norm_num) (by norm_num) (mem_ball_self (by norm_num)) hy
    (fun z hz => (differentiableAt_const 2).mul differentiableAt_id)
    (by simp) (by
      intro z hz
      have hd : fderiv ℝ (fun q : ℝ => 2 * q) z =
          (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ := ((hasFDerivAt_id z).const_mul 2).fderiv
      rw [hd]
      have he : (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ - ContinuousLinearMap.id ℝ ℝ =
          ContinuousLinearMap.id ℝ ℝ := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, add_smul, one_smul, add_sub_cancel_right]
      rw [he]
      exact ContinuousLinearMap.norm_id_le)
    (by norm_num) (by simp)
  simpa only [mul_one, one_mul, zero_add, sub_zero, show (1 + 1 : ℝ) = 2 by norm_num] using hh

theorem original_cutoff_full_marker :
    let U := ball (0 : ℝ) (200 * (1 : ℝ))
    let marker : ℝ → ℝ := (Subtype.val : U → ℝ).extend
      (fun p => ballCutoff (0 : ℝ) 1 2 p.val) 0
    ∀ p ∈ ball (0 : ℝ) 1, marker p = 1 := by
  dsimp only
  have hh := original_packet_marker_scale_binding (I := Unit) (f := id)
    (ρ := fun _ : ℝ => 1) (Λ := 0) (LipschitzWith.const 1)
    (fun _ => 0) (fun _ => 200) 1 (by norm_num)
    (fun _ => Or.inl rfl) (by norm_num) (fun _ => by norm_num)
    (fun _ p => ballCutoff (0 : ℝ) 1 2 p.val)
    (fun _ => (Subtype.val : ball (0 : ℝ) (200 * (1 : ℝ)) → ℝ).extend
      (fun p => ballCutoff (0 : ℝ) 1 2 p.val) 0)
    (by intro i p; rw [one_mul]; rfl)
    (fun _ => ball (0 : ℝ) 1) (fun _ => ball_subset_ball (by norm_num))
    (by
      intro i p hp
      exact ballCutoff_eq_one_of_mem_closedBall (by norm_num) (by norm_num) (show p ∈ closedBall (0 : ℝ) 1 from
        le_of_lt (show dist p 0 < 1 from hp)))
    (ball (0 : ℝ) 1) (fun p hp => ⟨(), hp⟩)
  intro p hp
  obtain ⟨i, hi⟩ := hh.2.1 p hp
  exact hi

theorem point_cloud_coordinate_preservation (z : ball (0 : ℝ) 1) :
    (⊤ : Submodule ℝ ℝ).starProjection (0 : ℝ) = 0 ∧
      ((⊤ : Submodule ℝ ℝ).starProjection (z : ℝ) = 0 → ∀ ψ : ℝ,
        (⊤ : Submodule ℝ ℝ).starProjection ((z : ℝ) + ψ • (0 - z)) = 0) := by
  have hh := spectral_zero_coordinate_of_nearest_value_bound
    (⊤ : Submodule ℝ ℝ) ({()} : Finset Unit) (fun _ => ⊥) (fun _ => (0 : ℝ))
    (fun _ _ => (1 : ℝ)) 0 (⊥ : Submodule ℝ ℝ)
    (b := 1) (r := 1) (ε := 0) (by norm_num) (by norm_num) (by norm_num)
    (by intro y hy; simp) (by intro y hy i hi hw; exact bot_le)
    (by intro y hy i hi hw; exact Submodule.zero_mem _)
    (fun _ => ⟨0, by simp⟩) (by intro y; simp) z
  exact hh

theorem smaller_original_packet_block_vanishes :
    let ζ : ball (1 : ℝ) ((1 / 4 : ℝ) * 1) → ℝ := fun _ => 1
    (Subtype.val : ball (1 : ℝ) ((1 / 4 : ℝ) * 1) → ℝ).extend ζ 0 2 = 0 := by
  have hh := original_small_packet_block_zero (ρ := id) LipschitzWith.id
    (2 : ℝ) 1 2 (Da := 1 / 4) (Di := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (mem_ball_self (by norm_num)) (by norm_num) (fun _ => 1) (1 : ℝ)
  exact hh.1

end GC.MetricGeometry.CloudContinuationExamples
