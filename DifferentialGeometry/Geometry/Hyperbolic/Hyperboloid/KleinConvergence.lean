import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Klein
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Metric

noncomputable section

open scoped Topology

namespace DifferentialGeometry.Hyperboloid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem inv_time_sq (x : Hyperboloid E) :
    x.time⁻¹ ^ 2 = 1 - ‖(kleinHomeomorph x : E)‖ ^ 2 := by
  rw [kleinHomeomorph_apply_coe, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr x.time_pos)]
  field_simp [x.time_pos.ne']
  nlinarith [x.time_sq]

theorem norm_kleinHomeomorph_sub_sq_le (x y : Hyperboloid E) {C : ℝ}
    (hxy : dist x y ≤ C) :
    ‖(kleinHomeomorph x : E) - (kleinHomeomorph y : E)‖ ^ 2 ≤
      2 * Real.cosh C * x.time⁻¹ := by
  have hx : ‖(kleinHomeomorph x : E)‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using (kleinHomeomorph x).property
  have hy : ‖(kleinHomeomorph y : E)‖ < 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using (kleinHomeomorph y).property
  have hi : 1 - inner ℝ (kleinHomeomorph x : E) (kleinHomeomorph y : E) =
      Real.cosh (dist x y) * x.time⁻¹ * y.time⁻¹ := by
    rw [kleinHomeomorph_apply_coe, kleinHomeomorph_apply_coe,
      real_inner_smul_left, real_inner_smul_right, cosh_dist]
    field_simp [x.time_pos.ne', y.time_pos.ne']
  have hd : Real.cosh (dist x y) ≤ Real.cosh C := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg dist_nonneg, abs_of_nonneg (dist_nonneg.trans hxy)] using hxy
  have ht : 1 ≤ y.time := by
    nlinarith [y.time_sq, sq_nonneg ‖y.space‖, y.time_pos]
  have htinv : y.time⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) ht)
  calc
    ‖(kleinHomeomorph x : E) - (kleinHomeomorph y : E)‖ ^ 2 ≤
        2 * Real.cosh (dist x y) * x.time⁻¹ * y.time⁻¹ := by
      rw [norm_sub_sq_real]
      nlinarith [norm_nonneg (kleinHomeomorph x : E),
        norm_nonneg (kleinHomeomorph y : E)]
    _ ≤ 2 * Real.cosh C * x.time⁻¹ * y.time⁻¹ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num))
          (inv_nonneg.mpr x.time_pos.le)) (inv_nonneg.mpr y.time_pos.le)
    _ ≤ 2 * Real.cosh C * x.time⁻¹ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left htinv
        (mul_nonneg (mul_nonneg (by norm_num) (Real.cosh_pos C).le)
          (inv_nonneg.mpr x.time_pos.le))

theorem tendsto_kleinHomeomorph_of_dist_bounded {α : Type*} {l : Filter α}
    {x y : α → Hyperboloid E} {ξ : Metric.sphere (0 : E) 1} {C : ℝ}
    (hxy : ∀ᶠ i in l, dist (x i) (y i) ≤ C)
    (hx : Filter.Tendsto (fun i => (kleinHomeomorph (x i) : E)) l (𝓝 (ξ : E))) :
    Filter.Tendsto (fun i => (kleinHomeomorph (y i) : E)) l (𝓝 (ξ : E)) := by
  have hξ : ‖(ξ : E)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ξ.property
  have hinvsq : Filter.Tendsto (fun i => (x i).time⁻¹ ^ 2) l (𝓝 0) := by
    simpa only [inv_time_sq, hξ, one_pow, sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (hx.norm.pow 2)
  have hinv : Filter.Tendsto (fun i => (x i).time⁻¹) l (𝓝 0) := by
    simpa only [Real.sqrt_sq (inv_nonneg.mpr (time_pos _).le), Real.sqrt_zero] using hinvsq.sqrt
  have hsq : Filter.Tendsto
      (fun i => ‖(kleinHomeomorph (x i) : E) - (kleinHomeomorph (y i) : E)‖ ^ 2)
      l (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun i => sq_nonneg _)
      (hxy.mono fun i hi => norm_kleinHomeomorph_sub_sq_le (x i) (y i) hi)
    simpa only [mul_zero] using hinv.const_mul (2 * Real.cosh C)
  have hsub : Filter.Tendsto
      (fun i => (kleinHomeomorph (x i) : E) - (kleinHomeomorph (y i) : E)) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt
  simpa only [sub_sub_cancel, sub_zero] using hx.sub hsub

end DifferentialGeometry.Hyperboloid
