import DifferentialGeometry.Topology.LoopSpace.CircleMetric
import DifferentialGeometry.Analysis.Calculus.Retraction.Normalization



noncomputable section

open NormedSpace Set
open scoped NNReal

namespace DifferentialGeometry.Topology


def radialDirection (z : ℂ) : Circle :=
  if h : z = 0 then 1 else
    ⟨NormedSpace.normalize z, by
      exact mem_sphere_zero_iff_norm.mpr (norm_normalize h)⟩

theorem radialDirection_coe {z : ℂ} (hz : z ≠ 0) :
    (radialDirection z : ℂ) = NormedSpace.normalize z := by
  unfold radialDirection
  erw [dif_neg hz]

theorem radialDirection_reconstruct (z : ℂ) : ‖z‖ • (radialDirection z : ℂ) = z := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [radialDirection_coe hz]
    exact norm_smul_normalize z

theorem radialDirection_unit (z : Circle) : radialDirection (z : ℂ) = z := by
  apply Subtype.ext
  rw [radialDirection_coe z.coe_ne_zero, normalize_eq_self_of_norm_eq_one z.norm_coe]

theorem radialDirection_pos_smul {r : ℝ} (hr : 0 < r) (z : Circle) :
    radialDirection (r • (z : ℂ)) = z := by
  have hz : r • (z : ℂ) ≠ 0 := smul_ne_zero hr.ne' z.coe_ne_zero
  apply Subtype.ext
  rw [radialDirection_coe hz, normalize_smul_of_pos hr,
    normalize_eq_self_of_norm_eq_one z.norm_coe]


def polarAnnulusCoordinates (z : ℂ) : ℝ × loopCircle :=
  (2 * ‖z‖ - 1, (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (radialDirection z))

theorem polarAnnulusCoordinates_outer (θ : loopCircle) :
    polarAnnulusCoordinates (AddCircle.toCircle θ : ℂ) = (1, θ) := by
  unfold polarAnnulusCoordinates
  rw [Circle.norm_coe, radialDirection_unit, ← AddCircle.homeomorphCircle_apply one_ne_zero]
  norm_num

theorem polarAnnulusCoordinates_inner (θ : loopCircle) :
    polarAnnulusCoordinates ((1 / 2 : ℝ) • (AddCircle.toCircle θ : ℂ)) = (0, θ) := by
  unfold polarAnnulusCoordinates
  rw [norm_smul, Real.norm_eq_abs, Circle.norm_coe,
    radialDirection_pos_smul (by norm_num : (0 : ℝ) < 1 / 2),
    ← AddCircle.homeomorphCircle_apply one_ne_zero]
  simp



theorem polarAnnulusCoordinates_lipschitz :
    LipschitzOnWith 4 polarAnnulusCoordinates {z : ℂ | 1 / 2 ≤ ‖z‖} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hz)
  have hw0 : w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hw)
  have hd : dist (radialDirection z) (radialDirection w) ≤ 4 * dist z w := by
    change dist (radialDirection z : ℂ) (radialDirection w : ℂ) ≤ _
    rw [radialDirection_coe hz0, radialDirection_coe hw0]
    convert DifferentialGeometry.Analysis.normalize_dist_le (by norm_num : (0 : ℝ) < 1 / 2) hz hw using 1
    norm_num
  have ha := circle_parameter_lipschitz.dist_le_mul (radialDirection z) (radialDirection w)
  have ht : dist (2 * ‖z‖ - 1) (2 * ‖w‖ - 1) ≤ 4 * dist z w := by
    rw [Real.dist_eq, sub_sub_sub_cancel_right, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := abs_norm_sub_norm_le z w
    rw [← dist_eq_norm] at h
    nlinarith [dist_nonneg (x := z) (y := w)]
  change max (dist (2 * ‖z‖ - 1) (2 * ‖w‖ - 1)) _ ≤ (4 : ℝ) * dist z w
  apply max_le ht
  simpa only [NNReal.coe_one, one_mul, polarAnnulusCoordinates] using! ha.trans (by simpa using hd)

end DifferentialGeometry.Topology
