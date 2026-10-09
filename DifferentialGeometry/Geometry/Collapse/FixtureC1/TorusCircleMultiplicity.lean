import DifferentialGeometry.Geometry.Collapse.RescaledLimits.ModifiedScale
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Count

/-!
# The numerical constant of the circle multiplicity (S-FIXTURE-C1b, F1, G3 file 2)

`CircleFamily.multiplicity` bounds the support multiplicity by
`V(6·10⁶ + 2/3) / V(1/3)` with `V = modelVolume (-(1/(2·10⁶))²) 3`. This file proves the elementary
two-sided bound `ω₃ r³ ≤ V(r) ≤ ω₃ r³ e^{2 q r}` (lower bound from `sn_q(t) ≥ t`, upper bound from
`ModifiedScale`) and the consequence `401² ≤ V(6·10⁶ + 2/3)/V(1/3)`: the number of nodes of the
`R`-spaced planar net within `200 R` of a point (`torCentres_ncard_le_FXC1`) is below the constant.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Collapse

/-- **Lower volume bound**: `ω₃ R³ ≤ V_{-q²}(R)` in dimension three. -/
theorem euclid_le_modelVolume_neg_sq_three_FXC1 {q R : ℝ} (hq : 0 ≤ q) (hR : 0 ≤ R) :
    euclideanUnitBallVolume 3 * R ^ 3 ≤ modelVolume (-(q ^ 2)) 3 R := by
  rw [modelVolume_neg_sq q 3 R hq, hyperbolicRadialVolume]
  have hc := euclideanUnitBallVolume_pos 3
  have hint : ∫ t in (0 : ℝ)..R, t ^ 2 ≤
      ∫ t in (0 : ℝ)..R, hyperbolicDensity q (3 - 1) t := by
    apply intervalIntegral.integral_mono_on hR
    · exact (continuous_pow 2).intervalIntegrable 0 R
    · exact ((hyperbolicSn_continuous q).pow _).intervalIntegrable 0 R
    · intro t ht
      have h := hyperbolicSn_ge_self hq ht.1
      exact pow_le_pow_left₀ ht.1 h 2
  rw [integral_pow] at hint
  calc euclideanUnitBallVolume 3 * R ^ 3
      = ((3 : ℕ) : ℝ) * euclideanUnitBallVolume 3 * ((R ^ (2 + 1) - 0 ^ (2 + 1)) / (2 + 1)) := by
        push_cast
        ring
    _ ≤ ((3 : ℕ) : ℝ) * euclideanUnitBallVolume 3 *
          ∫ t in (0 : ℝ)..R, hyperbolicDensity q (3 - 1) t :=
        mul_le_mul_of_nonneg_left hint (by positivity)

/-- **The circle multiplicity constant is at least `401²`.** -/
theorem circle_multiplicity_const_ge_FXC1 :
    (401 * 401 : ℝ) ≤ modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
      modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3) := by
  have hq : (0 : ℝ) ≤ 1 / 2000000 := by norm_num
  have hω := euclideanUnitBallVolume_pos 3
  have hlow := euclid_le_modelVolume_neg_sq_three_FXC1 hq (R := 3 * 2000000 + 2 / 3) (by norm_num)
  have hup := modelVolume_neg_sq_three_le hq (R := 1 / 3) (by norm_num)
  have hexp : Real.exp (2 * (1 / 2000000) * (1 / 3)) < 2 :=
    lt_of_le_of_lt (Real.exp_le_exp.mpr (by norm_num)) exp_half_lt_two
  have hpos : 0 < modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3) :=
    lt_of_lt_of_le (by positivity) (euclid_le_modelVolume_neg_sq_three_FXC1 hq (R := 1 / 3)
      (by norm_num))
  rw [le_div_iff₀ hpos]
  have h1 : modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3) ≤
      euclideanUnitBallVolume 3 * (1 / 3) ^ 3 * 2 :=
    hup.trans (mul_le_mul_of_nonneg_left hexp.le (by positivity))
  calc (401 * 401 : ℝ) * modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)
      ≤ (401 * 401) * (euclideanUnitBallVolume 3 * (1 / 3) ^ 3 * 2) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ euclideanUnitBallVolume 3 * (3 * 2000000 + 2 / 3) ^ 3 := by
        have : (401 * 401 : ℝ) * ((1 / 3) ^ 3 * 2) ≤ (3 * 2000000 + 2 / 3) ^ 3 := by norm_num
        nlinarith
    _ ≤ _ := hlow

end DifferentialGeometry.Geometry.Collapse
