import DifferentialGeometry.Geometry.Metric.RetainedMarkerLocality
import DifferentialGeometry.Analysis.NormedSpace.ScaleVanishing
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open GC.MetricGeometry Set

noncomputable section

namespace MarkerApplications

private def ρ (b : Bool) : ℝ := if b then 3 / 4 else 5 / 4
private def marker (i : Bool) (_x : ℝ) : ℝ := if i then 0 else 1
private def R (i : Bool) : ℝ := if i then 1 / 100 else 1
private theorem support : ∀ i p, 0 < marker i 0 →
    3 * R i / 4 ≤ ρ p ∧ ρ p ≤ 5 * R i / 4 := by
  intro i p
  cases i <;> cases p <;> norm_num [marker, R, ρ]

example : (3 / 5 : ℝ) * ρ false ≤ ρ true ∧ ρ true ≤ (5 / 3 : ℝ) * ρ false := by
  apply nearby_scale_comparison_of_retained_markers (fun _ : Bool => (0 : ℝ)) ρ marker R
    (fun i => by cases i <;> norm_num [R]) (fun _ => (LipschitzWith.const _).weaken (by norm_num))
    (fun _ => ⟨false, rfl⟩) support (σ := 1 / 640) (L := 128)
    (by norm_num) (by norm_num) (by norm_num) false true
  norm_num [ρ]

example : R true < R false / 2 := by
  apply small_radius_lt_half_reference_of_contributing_support
    (fun _ : Bool => (0 : ℝ)) ρ marker R
    (fun i => by cases i <;> norm_num [R]) (fun _ => (LipschitzWith.const _).weaken (by norm_num))
    (fun _ => ⟨false, rfl⟩) support (b := 1) (σ := 1 / 640)
    (by norm_num) (by norm_num) (by norm_num) false true true false rfl rfl
    ?_ false true rfl (by norm_num [R, ρ])
  exact ⟨0, by norm_num [Metric.mem_closedBall, ρ], by norm_num [Metric.mem_ball, ρ]⟩

example : ∀ z ∈ segment ℝ (0 : ℝ) (1 / 512), |z| ≤ 1 / 32 := by
  have hh := (ContinuousLinearMap.id ℝ ℝ).norm_on_segment_le_of_vanishing_at_small_scale
    (by simp) (x := 0) (y := 1 / 512) (by simp) (ρ := 1) (R := 1)
    (c := 16) (e := 1 / 512) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at hh ⊢
  exact hh

end MarkerApplications
