import DifferentialGeometry.Geometry.Comparison.ModelAngle
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.HyperbolicEstimates

set_option autoImplicit false

open Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem abs_sub_add_cos_comparisonAngleNegCurvature_one_le
    {a A r t c : ℝ} (ha : 0 < a) (har : a ≤ r) (hrA : r ≤ A)
    (ht : 0 < t) (ht1 : t ≤ 1) (hta : t ≤ a / 2)
    (hlower : |r - t| ≤ c) (hupper : c ≤ r + t) :
    |c - r + t * cos (comparisonAngleNegCurvature 1 r t c)| ≤
      (4 * cosh (A + 1) / sinh a) * t ^ 2 := by
  have hr : 0 < r := ha.trans_le har
  have hA : 0 < A := hr.trans_le hrA
  have hsar : sinh a ≤ sinh r := sinh_le_sinh.mpr har
  have hsa : 0 < sinh a := sinh_pos_iff.mpr ha
  have hsr : 0 < sinh r := sinh_pos_iff.mpr hr
  have hst : 0 < sinh t := sinh_pos_iff.mpr ht
  have hct : |c - r| ≤ t := by
    apply abs_le.mpr
    have := (le_abs_self (r - t)).trans hlower
    constructor <;> linarith
  have hrem := abs_cosh_sub_linear_le (by linarith : 0 ≤ r - t)
    (show r + t ≤ A + 1 by linarith) hct
  have hcr : cosh r ≤ cosh (A + 1) := cosh_le_cosh.mpr
    (by rw [abs_of_pos hr, abs_of_pos (by linarith : 0 < A + 1)]; linarith)
  have hsrl : sinh r ≤ cosh (A + 1) := (sinh_lt_cosh r).le.trans hcr
  let θ := comparisonAngleNegCurvature 1 r t c
  have hcos : cos θ = (cosh r * cosh t - cosh c) / (sinh r * sinh t) := by
    simpa [θ] using cos_comparisonAngleNegCurvature_of_pos (by norm_num : (0 : ℝ) < 1)
      hr ht hlower hupper
  have hlaw : cosh c = cosh r * cosh t - sinh r * sinh t * cos θ := by
    have := (eq_div_iff (mul_pos hsr hst).ne').mp hcos
    nlinarith
  have hterm1 : |cosh r * (cosh t - 1)| ≤ cosh (A + 1) * t ^ 2 := by
    rw [abs_mul, abs_of_pos (cosh_pos r), abs_of_nonneg (sub_nonneg.mpr (one_le_cosh t))]
    exact (mul_le_mul_of_nonneg_left (cosh_sub_one_le_sq ht.le ht1) (cosh_pos r).le).trans
      (mul_le_mul_of_nonneg_right hcr (sq_nonneg t))
  have hterm2 : |sinh r * (sinh t - t) * cos θ| ≤ cosh (A + 1) * t ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos hsr]
    have h := mul_le_mul_of_nonneg_left (sinh_sub_self_le_sq ht.le ht1) hsr.le
    calc
      sinh r * |sinh t - t| * |cos θ| ≤ sinh r * |sinh t - t| :=
        mul_le_of_le_one_right (mul_nonneg hsr.le (abs_nonneg _)) (abs_cos_le_one θ)
      _ ≤ sinh r * t ^ 2 := h
      _ ≤ cosh (A + 1) * t ^ 2 := mul_le_mul_of_nonneg_right hsrl (sq_nonneg t)
  have hid : sinh r * (c - r + t * cos θ) =
      -(cosh c - cosh r - (c - r) * sinh r) + cosh r * (cosh t - 1) -
        sinh r * (sinh t - t) * cos θ := by rw [hlaw]; ring
  have hbudget : sinh r * |c - r + t * cos θ| ≤ 3 * cosh (A + 1) * t ^ 2 := by
    rw [← abs_of_pos hsr, ← abs_mul, hid]
    have h := abs_sub (-(cosh c - cosh r - (c - r) * sinh r) + cosh r * (cosh t - 1))
      (sinh r * (sinh t - t) * cos θ)
    have h' := abs_add_le (-(cosh c - cosh r - (c - r) * sinh r)) (cosh r * (cosh t - 1))
    rw [abs_neg] at h'
    linarith
  change |c - r + t * cos θ| ≤ _
  rw [div_mul_eq_mul_div, le_div_iff₀ hsa]
  have hmono := mul_le_mul_of_nonneg_right hsar (abs_nonneg (c - r + t * cos θ))
  nlinarith [mul_nonneg (cosh_pos (A + 1)).le (sq_nonneg t)]

theorem abs_dist_sub_add_cos_comparisonAngleNegCurvature_one_le
    {X : Type*} [MetricSpace X] (x y z : X) {a A : ℝ}
    (ha : 0 < a) (har : a ≤ dist x z) (hrA : dist x z ≤ A)
    (ht : 0 < dist x y) (ht1 : dist x y ≤ 1) (hta : dist x y ≤ a / 2) :
    |dist y z - dist x z + dist x y *
        cos (comparisonAngleNegCurvature 1 (dist x z) (dist x y) (dist y z))| ≤
      (4 * cosh (A + 1) / sinh a) * (dist x y) ^ 2 := by
  apply abs_sub_add_cos_comparisonAngleNegCurvature_one_le ha har hrA ht ht1 hta
  · apply abs_sub_le_iff.mpr
    constructor
    · linarith [dist_triangle x y z]
    · have := dist_triangle x z y
      rw [dist_comm z y] at this
      linarith
  · have := dist_triangle y x z
    rw [dist_comm y x] at this
    linarith

end DifferentialGeometry.Geometry.Comparison.Toponogov
