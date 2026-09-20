import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology NNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem tendsto_comparisonAngle_zero_of_bounded_cross_distance
    {q : ℝ≥0 → ℝ} (hnonneg : ∀ s, 0 ≤ q s) {D : ℝ}
    (hbound : ∀ s, q s ≤ D) :
    Tendsto (fun s : ℝ≥0 => comparisonAngle s s (q s)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun s : ℝ≥0 => (s : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (NNReal.tendsto_coe_atTop.mpr tendsto_id)
  have hu : Tendsto (fun s : ℝ≥0 => D / (s : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hinv
  have hq : Tendsto (fun s : ℝ≥0 => q s / (s : ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun s => div_nonneg (hnonneg s) s.coe_nonneg)
      (fun s => div_le_div_of_nonneg_right (hbound s) s.coe_nonneg) hu
  have hlim := tendsto_comparisonAngle (a0 := (1 : ℝ)) (b0 := (1 : ℝ))
    tendsto_const_nhds tendsto_const_nhds hq zero_lt_one zero_lt_one
  have hz : comparisonAngle 1 1 0 = 0 := by
    simpa only [sub_self, abs_zero] using comparisonAngle_abs_sub zero_lt_one zero_lt_one
  rw [hz] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with s hs
  have hp : (0 : ℝ) < s := hs
  simpa only [inv_mul_cancel₀ hp.ne', ← div_eq_mul_inv, mul_comm] using
    comparisonAngle_scale s s (q s) (inv_pos.mpr hp)

end DifferentialGeometry.Geometry.Comparison.Toponogov
