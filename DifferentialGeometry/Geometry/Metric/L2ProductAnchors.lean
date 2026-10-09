import DifferentialGeometry.Geometry.Metric.L2Product
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace GC.MetricGeometry

private theorem square_root_defect_bound {A u r B : ℝ}
    (hu : 0 < u) (hA : 0 ≤ A) (hr : 0 ≤ r) (hB : r ≤ B)
    (hAsq : A ^ 2 = u ^ 2 + r ^ 2) :
    0 ≤ A - u ∧ A - u ≤ B ^ 2 / (2 * u) := by
  have huA : u ≤ A := by nlinarith [sq_nonneg r]
  refine ⟨by linarith, ?_⟩
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (A - u), sq_le_sq₀ hr (hr.trans hB) |>.mpr hB]

theorem product_positive_anchor_value_bound {Y : Type*} [MetricSpace Y]
    (y₀ : Y) (x : WithLp 2 (ℝ × Y)) {B s : ℝ}
    (hs : B < s)
    (hx : dist x (WithLp.toLp 2 (0, y₀)) ≤ B) :
    |s - dist x (WithLp.toLp 2 (s, y₀)) - x.fst| ≤ B ^ 2 / (2 * (s - B)) := by
  have ht := (WithLp.dist_fst_le x (WithLp.toLp 2 (0, y₀))).trans hx
  have hr := (WithLp.dist_snd_le x (WithLp.toLp 2 (0, y₀))).trans hx
  change dist x.fst 0 ≤ B at ht
  change dist x.snd y₀ ≤ B at hr
  simp only [Real.dist_eq, sub_zero] at ht
  have hts : 0 < s - x.fst := by linarith [(abs_le.mp ht).2]
  have hsq := WithLp.prod_dist_sq_eq_add_sq x (WithLp.toLp 2 (s, y₀))
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq, sq_abs] at hsq
  have hsq' : dist x (WithLp.toLp 2 (s, y₀)) ^ 2 =
      (s - x.fst) ^ 2 + dist x.snd y₀ ^ 2 := by nlinarith
  obtain ⟨hlo, hup⟩ := square_root_defect_bound hts dist_nonneg dist_nonneg hr hsq'
  have heq : |s - dist x (WithLp.toLp 2 (s, y₀)) - x.fst| =
      dist x (WithLp.toLp 2 (s, y₀)) - (s - x.fst) := by
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [heq]
  apply hup.trans
  exact div_le_div_of_nonneg_left (sq_nonneg B) (by positivity)
    (by linarith [(abs_le.mp ht).2])

end GC.MetricGeometry
