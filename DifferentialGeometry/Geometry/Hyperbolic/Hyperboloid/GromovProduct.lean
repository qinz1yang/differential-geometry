import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Boost
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Klein
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Proper
import Mathlib.Topology.MetricSpace.GromovProduct

noncomputable section

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def kernel (x y : Hyperboloid E) : ℝ :=
  1 - inner ℝ (kleinHomeomorph x : E) (kleinHomeomorph y : E)

private theorem kernel_eq (x y : Hyperboloid E) :
    kernel x y = Real.cosh (dist x y) / (x.time * y.time) := by
  rw [cosh_dist]
  simp only [kernel, kleinHomeomorph_apply_coe, real_inner_smul_left, real_inner_smul_right]
  field_simp [x.time_pos.ne', y.time_pos.ne']

private theorem one_sub_inner_le (a b c : E) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hc : ‖c‖ ≤ 1) :
    1 - inner ℝ a c ≤ 2 * ((1 - inner ℝ a b) + (1 - inner ℝ b c)) := by
  have h : 0 ≤ inner ℝ (a - (2 : ℝ) • b + c) (a - (2 : ℝ) • b + c) :=
    real_inner_self_nonneg
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm b a,
    real_inner_comm c a, real_inner_comm c b, real_inner_self_eq_norm_sq] at h
  norm_num only [norm_smul, Real.norm_eq_abs] at h
  rw [real_inner_comm a b, real_inner_comm a c, real_inner_comm b c] at h
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg c]

private theorem kernel_triangle (x y z : Hyperboloid E) :
    kernel x z ≤ 2 * (kernel x y + kernel y z) := by
  have hn (p : Hyperboloid E) : ‖(kleinHomeomorph p : E)‖ ≤ 1 := by
    exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using
      (kleinHomeomorph p).property)
  exact one_sub_inner_le _ _ _ (hn x) (hn y) (hn z)

private theorem cosh_le_exp {r : ℝ} (hr : 0 ≤ r) : Real.cosh r ≤ Real.exp r := by
  have hs := Real.sinh_nonneg_iff.mpr hr
  linarith [Real.cosh_add_sinh r]

private theorem exp_le_two_cosh (r : ℝ) : Real.exp r ≤ 2 * Real.cosh r := by
  rw [Real.cosh_eq]
  linarith [Real.exp_pos (-r)]

private def expProduct (x y : Hyperboloid E) : ℝ :=
  Real.exp (-2 * Metric.gromovProduct origin x y)

private theorem expProduct_eq (x y : Hyperboloid E) :
    expProduct x y = Real.exp (dist x y - dist origin x - dist origin y) := by
  unfold expProduct
  congr 1
  rw [Metric.gromovProduct_eq]
  ring

private theorem expProduct_eq_div (x y : Hyperboloid E) :
    expProduct x y = Real.exp (dist x y) /
      (Real.exp (dist origin x) * Real.exp (dist origin y)) := by
  rw [expProduct_eq, Real.exp_sub, Real.exp_sub, div_div]

private theorem time_le_exp (x : Hyperboloid E) : x.time ≤ Real.exp (dist origin x) := by
  rw [← cosh_dist_origin]
  exact cosh_le_exp dist_nonneg

private theorem exp_le_two_time (x : Hyperboloid E) : Real.exp (dist origin x) ≤ 2 * x.time := by
  rw [← cosh_dist_origin]
  exact exp_le_two_cosh _

private theorem expProduct_le_two_kernel (x y : Hyperboloid E) :
    expProduct x y ≤ 2 * kernel x y := by
  rw [expProduct_eq_div, kernel_eq, ← mul_div_assoc]
  apply div_le_div₀ (by positivity) (exp_le_two_cosh _) (mul_pos x.time_pos y.time_pos)
  exact mul_le_mul (time_le_exp x) (time_le_exp y) y.time_pos.le (Real.exp_pos _).le

private theorem kernel_le_four_expProduct (x y : Hyperboloid E) :
    kernel x y ≤ 4 * expProduct x y := by
  rw [kernel_eq, expProduct_eq_div, ← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos x.time_pos y.time_pos)
    (mul_pos (Real.exp_pos _) (Real.exp_pos _))).mpr
  have hd : Real.exp (dist origin x) * Real.exp (dist origin y) ≤
      4 * (x.time * y.time) := by
    have h := mul_le_mul (exp_le_two_time x) (exp_le_two_time y)
      (Real.exp_pos _).le (mul_nonneg (by norm_num) x.time_pos.le)
    nlinarith
  calc
    Real.cosh (dist x y) * (Real.exp (dist origin x) * Real.exp (dist origin y)) ≤
        Real.cosh (dist x y) * (4 * (x.time * y.time)) :=
      mul_le_mul_of_nonneg_left hd (Real.cosh_pos _).le
    _ = 4 * Real.cosh (dist x y) * (x.time * y.time) := by ring
    _ ≤ 4 * Real.exp (dist x y) * (x.time * y.time) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (cosh_le_exp dist_nonneg) (by norm_num))
        (mul_pos x.time_pos y.time_pos).le

private theorem expProduct_triangle (x y z : Hyperboloid E) :
    expProduct x z ≤ 32 * max (expProduct x y) (expProduct y z) := by
  have h := expProduct_le_two_kernel x z
  have hk := kernel_triangle x y z
  have hxy := kernel_le_four_expProduct x y
  have hyz := kernel_le_four_expProduct y z
  have hx := le_max_left (expProduct x y) (expProduct y z)
  have hy := le_max_right (expProduct x y) (expProduct y z)
  linarith

private theorem four_point_origin (x y z : Hyperboloid E) :
    dist origin y + dist x z ≤
      max (dist origin x + dist y z) (dist origin z + dist x y) + Real.log 32 := by
  have he := expProduct_triangle x y z
  rcases le_total (expProduct x y) (expProduct y z) with h | h
  · rw [max_eq_right h] at he
    have hl : dist x z - dist origin x - dist origin z ≤
        dist y z - dist origin y - dist origin z + Real.log 32 := by
      apply Real.exp_le_exp.mp
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 32)]
      rw [mul_comm]
      simpa only [expProduct_eq] using he
    have hm := le_max_left (dist origin x + dist y z) (dist origin z + dist x y)
    linarith
  · rw [max_eq_left h] at he
    have hl : dist x z - dist origin x - dist origin z ≤
        dist x y - dist origin x - dist origin y + Real.log 32 := by
      apply Real.exp_le_exp.mp
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 32)]
      rw [mul_comm]
      simpa only [expProduct_eq] using he
    have hm := le_max_right (dist origin x + dist y z) (dist origin z + dist x y)
    linarith

theorem four_point_inequality (w x y z : Hyperboloid E) :
    dist w y + dist x z ≤
      max (dist w x + dist y z) (dist w z + dist x y) + Real.log 32 := by
  let f := (boost w).symm
  have hw : f w = origin := by
    simpa only [boost_origin] using (boost w).symm_apply_apply origin
  have h := four_point_origin (f x) (f y) (f z)
  simpa only [← hw, IsometryEquiv.dist_eq] using h

end DifferentialGeometry.Hyperboloid
