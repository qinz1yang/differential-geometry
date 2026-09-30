import DifferentialGeometry.Geometry.Metric.ConeDistance
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

open Set Real

namespace Metric

private noncomputable def coneTrianglePoint (r θ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![r * cos θ, r * sin θ]

private theorem coneTrianglePoint_dist (r s θ φ : ℝ) :
    dist (coneTrianglePoint r θ) (coneTrianglePoint s φ) =
      sqrt (r ^ 2 + s ^ 2 - 2 * r * s * cos (θ - φ)) := by
  have hs : dist (coneTrianglePoint r θ) (coneTrianglePoint s φ) ^ 2 =
      r ^ 2 + s ^ 2 - 2 * r * s * cos (θ - φ) := by
    rw [EuclideanSpace.dist_sq_eq]
    norm_num only [coneTrianglePoint, Fin.sum_univ_two, PiLp.toLp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq, sq_abs]
    rw [cos_sub]
    linear_combination r ^ 2 * sin_sq_add_cos_sq θ + s ^ 2 * sin_sq_add_cos_sq φ
  rw [← hs, sqrt_sq_eq_abs, abs_of_nonneg dist_nonneg]

theorem coneDistance_triangle {Y : Type*} [PseudoMetricSpace Y]
    {x y z : ℝ × Y} (hx : 0 ≤ x.1) (hy : 0 ≤ y.1) (hz : 0 ≤ z.1) :
    coneDistance x z ≤ coneDistance x y + coneDistance y z := by
  let a := min Real.pi (dist x.2 y.2)
  let b := min Real.pi (dist y.2 z.2)
  let c := min Real.pi (dist x.2 z.2)
  have ha : a ∈ Icc (0 : ℝ) Real.pi := ⟨le_min pi_pos.le dist_nonneg, min_le_left _ _⟩
  have hb : b ∈ Icc (0 : ℝ) Real.pi := ⟨le_min pi_pos.le dist_nonneg, min_le_left _ _⟩
  have hc : c ∈ Icc (0 : ℝ) Real.pi := ⟨le_min pi_pos.le dist_nonneg, min_le_left _ _⟩
  have hcab : c ≤ a + b := by
    by_cases hxy : dist x.2 y.2 ≤ Real.pi
    · by_cases hyz : dist y.2 z.2 ≤ Real.pi
      · dsimp only [a, b, c]
        rw [min_eq_right hxy, min_eq_right hyz]
        exact (min_le_right _ _).trans (dist_triangle _ _ _)
      · have hbpi : b = Real.pi := min_eq_left (le_of_not_ge hyz)
        rw [hbpi]
        linarith [hc.2, ha.1]
    · have hapi : a = Real.pi := min_eq_left (le_of_not_ge hxy)
      rw [hapi]
      linarith [hc.2, hb.1]
  let d := min Real.pi (a + b)
  have hd : d ∈ Icc (0 : ℝ) Real.pi :=
    ⟨le_min pi_pos.le (add_nonneg ha.1 hb.1), min_le_left _ _⟩
  have hcd : c ≤ d := le_min hc.2 hcab
  have had : a ≤ d := le_min ha.2 (le_add_of_nonneg_right hb.1)
  have hdab : d - a ≤ b := by have h := min_le_right Real.pi (a + b); dsimp only [d]; linarith
  have hleft : coneDistance x z ≤ dist (coneTrianglePoint x.1 0) (coneTrianglePoint z.1 d) := by
    rw [coneTrianglePoint_dist]
    simp only [zero_sub, cos_neg]
    unfold coneDistance
    apply sqrt_le_sqrt
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left
      (cos_le_cos_of_nonneg_of_le_pi hc.1 hd.2 hcd) (by positivity)) _
  have hfirst : dist (coneTrianglePoint x.1 0) (coneTrianglePoint y.1 a) = coneDistance x y := by
    rw [coneTrianglePoint_dist]
    simp only [zero_sub, cos_neg]
    rfl
  have hlast : dist (coneTrianglePoint y.1 a) (coneTrianglePoint z.1 d) ≤ coneDistance y z := by
    rw [coneTrianglePoint_dist]
    rw [show a - d = -(d - a) by ring, cos_neg]
    unfold coneDistance
    apply sqrt_le_sqrt
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left
      (cos_le_cos_of_nonneg_of_le_pi (sub_nonneg.mpr had) hb.2 hdab) (by positivity)) _
  exact hleft.trans ((dist_triangle _ (coneTrianglePoint y.1 a) _).trans
    (by rw [hfirst]; exact add_le_add le_rfl hlast))

end Metric
