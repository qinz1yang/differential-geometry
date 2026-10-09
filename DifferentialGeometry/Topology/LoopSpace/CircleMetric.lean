import DifferentialGeometry.Topology.LoopSpace.Lipschitz
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds







noncomputable section

open scoped NNReal

namespace DifferentialGeometry.Topology


theorem toCircle_chord_sub (x y : loopCircle) :
    ‖(AddCircle.toCircle (x - y) : ℂ) - 1‖ =
      ‖(AddCircle.toCircle x : ℂ) - (AddCircle.toCircle y : ℂ)‖ := by
  erw [sub_eq_add_neg x y, AddCircle.toCircle_add, AddCircle.toCircle_neg,
    Circle.coe_mul, Circle.coe_inv]
  have hy := (AddCircle.toCircle y).coe_ne_zero
  have heq : (AddCircle.toCircle x : ℂ) * (AddCircle.toCircle y : ℂ)⁻¹ - 1 =
      ((AddCircle.toCircle x : ℂ) - (AddCircle.toCircle y : ℂ)) *
        (AddCircle.toCircle y : ℂ)⁻¹ := by
    rw [sub_mul, mul_inv_cancel₀ hy]
  rw [heq, norm_mul, norm_inv, Circle.norm_coe, inv_one, mul_one]


theorem loopCircle_exists_minimal_lift (θ : loopCircle) :
    ∃ t : ℝ, (t : loopCircle) = θ ∧ |t| = ‖θ‖ := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective θ
  refine ⟨x - round x, ?_, ?_⟩
  · have hi : ((round x : ℝ) : loopCircle) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨round x, by simp⟩
    rw [AddCircle.coe_sub, hi, sub_zero]
  · simp only [AddCircle.norm_eq, inv_one, one_mul, mul_one]


theorem loopCircle_chord_le (θ : loopCircle) :
    ‖(AddCircle.toCircle θ : ℂ) - 1‖ ≤ (2 * Real.pi) * ‖θ‖ := by
  obtain ⟨t, ht, hnorm⟩ := loopCircle_exists_minimal_lift θ
  rw [← ht, AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one,
    mul_comm _ Complex.I]
  calc
    _ ≤ ‖2 * Real.pi * t‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = _ := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi),
        hnorm, ht]



theorem circle_boundary_lipschitz :
    LipschitzWith ⟨2 * Real.pi, by positivity⟩ (fun θ : loopCircle => (AddCircle.toCircle θ : ℂ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← toCircle_chord_sub]
  exact loopCircle_chord_le (x - y)


theorem four_mul_loopCircle_norm_le_chord (θ : loopCircle) :
    4 * ‖θ‖ ≤ ‖(AddCircle.toCircle θ : ℂ) - 1‖ := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective θ
  let t : ℝ := x - round x
  have hi : ((round x : ℝ) : loopCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨round x, by simp⟩
  have ht : (t : loopCircle) = (x : loopCircle) := by
    simp only [t, AddCircle.coe_sub, hi, sub_zero]
  have hnorm : ‖(x : loopCircle)‖ = |t| := by
    simp only [AddCircle.norm_eq, inv_one, one_mul, mul_one, t]
  have hhalf : |t| ≤ 1 / 2 := by
    simpa only [hnorm, abs_one] using AddCircle.norm_le_half_period (1 : ℝ) (x := (x : loopCircle)) one_ne_zero
  have hs := Real.mul_abs_le_abs_sin (x := Real.pi * t) (by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos])
  have hlinear : 2 * |t| ≤ |Real.sin (Real.pi * t)| := by
    convert hs using 1
    rw [abs_mul, abs_of_pos Real.pi_pos]
    field_simp
  rw [hnorm, ← ht, AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one]
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : 2 * Real.pi * t / 2 = Real.pi * t := by ring
  rw [heq, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith



theorem circle_parameter_lipschitz :
    LipschitzWith 1 (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let h := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hb := four_mul_loopCircle_norm_le_chord (h.symm x - h.symm y)
  rw [toCircle_chord_sub] at hb
  have hx : AddCircle.toCircle (h.symm x) = x := by
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact h.apply_symm_apply x
  have hy : AddCircle.toCircle (h.symm y) = y := by
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact h.apply_symm_apply y
  rw [hx, hy] at hb
  rw [dist_eq_norm, NNReal.coe_one]
  have hd : dist x y = ‖(x : ℂ) - (y : ℂ)‖ := dist_eq_norm (x : ℂ) (y : ℂ)
  rw [hd]
  nlinarith [norm_nonneg (h.symm x - h.symm y)]

end DifferentialGeometry.Topology
