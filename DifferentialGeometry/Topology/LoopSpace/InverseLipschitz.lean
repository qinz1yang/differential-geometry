import DifferentialGeometry.Topology.LoopSpace.CircleMetric
import Mathlib.Topology.MetricSpace.Antilipschitz

noncomputable section

open Set
open scoped NNReal ENNReal

namespace DifferentialGeometry.Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] in
theorem abs_sub_le_mul_norm_sub_of_antilipschitz_loop
    {Γ : loopCircle → F} {L : ℝ≥0} (hΓ : AntilipschitzWith L Γ)
    {a b : ℝ} (hab : |a - b| ≤ 1 / 2) :
    |a - b| ≤ (L : ℝ) * ‖Γ (a : loopCircle) - Γ (b : loopCircle)‖ := by
  have hnorm : ‖((a - b : ℝ) : loopCircle)‖ = |a - b| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr (by simpa using hab)
  have h := hΓ.le_mul_dist (a : loopCircle) (b : loopCircle)
  simpa only [dist_eq_norm, ← AddCircle.coe_sub, hnorm] using h

omit [NormedSpace ℝ F] in
theorem sub_le_two_mul_norm_sub_of_antilipschitz_loop
    {Γ : loopCircle → F} {L : ℝ≥0} (hΓ : AntilipschitzWith L Γ)
    {a b : ℝ} (hab : a ≤ b) (hshort : b - a ≤ 2 / 3) :
    b - a ≤ 2 * (L : ℝ) * ‖Γ (b : loopCircle) - Γ (a : loopCircle)‖ := by
  have hcircle : b - a ≤ 2 * dist (b : loopCircle) (a : loopCircle) := by
    rw [dist_eq_norm, ← AddCircle.coe_sub]
    by_cases hhalf : b - a ≤ 1 / 2
    · have hnorm : ‖((b - a : ℝ) : loopCircle)‖ = b - a := by
        rw [(AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr]
        · exact abs_of_nonneg (sub_nonneg.mpr hab)
        · simpa only [abs_one, abs_of_nonneg (sub_nonneg.mpr hab)] using hhalf
      rw [hnorm]
      linarith
    · have hnorm : ‖((b - a - 1 : ℝ) : loopCircle)‖ = |b - a - 1| :=
        (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr (by
          rw [abs_one, abs_le]
          constructor <;> linarith)
      have hcoe : ((b - a - 1 : ℝ) : loopCircle) = ((b - a : ℝ) : loopCircle) := by
        rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
      rw [hcoe] at hnorm
      rw [hnorm, abs_of_nonpos (by linarith : b - a - 1 ≤ 0)]
      linarith
  exact hcircle.trans (by
    have h := mul_le_mul_of_nonneg_left
      (hΓ.le_mul_dist (b : loopCircle) (a : loopCircle)) (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [dist_eq_norm, mul_assoc] using h)

end DifferentialGeometry.Topology

theorem AntilipschitzWith.lipschitzWith_of_comp
    {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]
    {f : Y → Z} {g : X → Y} {K L : ℝ≥0} (hf : AntilipschitzWith K f)
    (hg : LipschitzWith L (f ∘ g)) : LipschitzWith (K * L) g := by
  intro x y
  apply (hf (g x) (g y)).trans
  calc
    (K : ℝ≥0∞) * edist (f (g x)) (f (g y)) ≤
        (K : ℝ≥0∞) * ((L : ℝ≥0∞) * edist x y) := by
      gcongr
      exact hg x y
    _ = (↑(K * L) : ℝ≥0∞) * edist x y := by
      simp only [ENNReal.coe_mul, mul_assoc]

end
