import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp



noncomputable section

open NormedSpace
open scoped NNReal

namespace DifferentialGeometry.Analysis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]



theorem normalize_dist_le {a : ℝ} (ha : 0 < a) {x y : V}
    (hx : a ≤ ‖x‖) (hy : a ≤ ‖y‖) :
    dist (normalize x) (normalize y) ≤ (2 / a) * dist x y := by
  have hxpos : 0 < ‖x‖ := ha.trans_le hx
  have hypos : 0 < ‖y‖ := ha.trans_le hy
  have hy0 : y ≠ 0 := norm_pos_iff.mp hypos
  have heq : normalize x - normalize y =
      ‖x‖⁻¹ • ((x - y) + (‖y‖ - ‖x‖) • normalize y) := by
    rw [smul_add, smul_sub, sub_smul, norm_smul_normalize, smul_sub,
      smul_smul, inv_mul_cancel₀ hxpos.ne', one_smul]
    simp only [NormedSpace.normalize]
    module
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hxpos, dist_eq_norm]
  have hb : ‖(x - y) + (‖y‖ - ‖x‖) • normalize y‖ ≤ 2 * ‖x - y‖ := by
    calc
      _ ≤ ‖x - y‖ + ‖(‖y‖ - ‖x‖) • normalize y‖ := norm_add_le _ _
      _ = ‖x - y‖ + |‖y‖ - ‖x‖| := by
        rw [norm_smul, Real.norm_eq_abs, norm_normalize hy0, mul_one]
      _ ≤ 2 * ‖x - y‖ := by
        have h := abs_norm_sub_norm_le y x
        rw [norm_sub_rev y x] at h
        linarith
  calc
    _ ≤ ‖x‖⁻¹ * (2 * ‖x - y‖) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hxpos.le)
    _ ≤ a⁻¹ * (2 * ‖x - y‖) :=
      mul_le_mul_of_nonneg_right (inv_anti₀ ha hx) (by positivity)
    _ = _ := by ring

end DifferentialGeometry.Analysis
