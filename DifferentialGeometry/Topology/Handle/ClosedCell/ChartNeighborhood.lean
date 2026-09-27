import DifferentialGeometry.Topology.Handle.ClosedCell.InteriorCoordinates
import Mathlib.Analysis.Normed.Module.Basic

noncomputable section

open Manifold Set
open scoped Manifold

namespace DifferentialGeometry.Topology.Handle

private local instance (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m

theorem closedCell_extChartAt_target_eq_ball {m : ℕ}
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1) :
    (extChartAt (𝓡∂ (m + 1)) α).target =
      Metric.ball (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0) 1 := by
  ext y
  simpa only [closedCellShiftSucc_eq_add, neg_one_smul, sub_eq_add_neg,
    Metric.mem_ball, dist_eq_norm] using
      mem_closedCell_extChartAt_target_iff_of_norm_lt_one α hα y

theorem affine_image_closedCell_extChartAt_target
    {m : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] F)
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1)
    (c : EuclideanSpace ℝ (Fin (m + 1))) {r : ℝ} (hr : 0 < r) :
    (fun y : F => e c - r • e (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0) + r • y) ''
        (e '' interior (extChartAt (𝓡∂ (m + 1)) α).target) =
      e '' Metric.ball c r := by
  rw [closedCell_extChartAt_target_eq_ball α hα, Metric.isOpen_ball.interior_eq]
  let v₀ := EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨c + r • (x - v₀), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos hr]
      have hx' : ‖x - v₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm, v₀] using hx
      simpa only [mul_one] using mul_lt_mul_of_pos_left hx' hr
    · simp only [map_add, map_smul, map_sub, smul_sub]
      abel
  · rintro ⟨x, hx, rfl⟩
    refine ⟨e (v₀ + r⁻¹ • (x - c)), ⟨v₀ + r⁻¹ • (x - c), ?_, rfl⟩, ?_⟩
    · change v₀ + r⁻¹ • (x - c) ∈ Metric.ball v₀ 1
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      have hx' : ‖x - c‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
      calc
        r⁻¹ * ‖x - c‖ < r⁻¹ * r := mul_lt_mul_of_pos_left hx' (inv_pos.mpr hr)
        _ = 1 := inv_mul_cancel₀ hr.ne'
    · simp only [map_add, map_smul, map_sub, smul_add, smul_smul,
        mul_inv_cancel₀ hr.ne', one_smul, v₀]
      abel

end DifferentialGeometry.Topology.Handle
