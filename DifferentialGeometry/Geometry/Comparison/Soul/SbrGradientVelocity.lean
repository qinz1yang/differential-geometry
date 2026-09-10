import DifferentialGeometry.Geometry.Comparison.Soul.SbrGradientAlgebra

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {D : E → ℝ} {G V U : E}

theorem superadditive_normalized_gradient_spec
    (hsmul : ∀ (a : ℝ), 0 ≤ a → ∀ v : E, D (a • v) = a * D v)
    (hcal : D G = ‖G‖ ^ 2) (hG : G ≠ 0) :
    D ((‖G‖ ^ 2)⁻¹ • G) = 1 ∧ ‖(‖G‖ ^ 2)⁻¹ • G‖ = ‖G‖⁻¹ := by
  have hnorm : 0 < ‖G‖ := norm_pos_iff.mpr hG
  have hsq : ‖G‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm.ne'
  constructor
  · rw [hsmul _ (inv_nonneg.mpr (sq_nonneg _)) G, hcal, inv_mul_cancel₀ hsq]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hnorm))]
    field_simp [hnorm.ne']

theorem eq_normalized_gradient_of_calibration_and_norm_le
    (hsupport : ∀ v : E, D v ≤ inner ℝ G v) (hG : G ≠ 0)
    (hvalue : D V = 1) (hbound : ‖V‖ ≤ ‖G‖⁻¹) :
    V = (‖G‖ ^ 2)⁻¹ • G := by
  have hpos : 0 < ‖G‖ := norm_pos_iff.mpr hG
  have hne : ‖G‖ ≠ 0 := hpos.ne'
  have hlower : 1 ≤ inner ℝ G V := by simpa only [hvalue] using hsupport V
  have hmul : ‖G‖ * ‖V‖ ≤ 1 := by
    simpa only [mul_inv_cancel₀ hne] using
      mul_le_mul_of_nonneg_left hbound (norm_nonneg G)
  have hprod : ‖G‖ * ‖V‖ = 1 :=
    le_antisymm hmul (hlower.trans (real_inner_le_norm G V))
  have hvnorm : ‖V‖ = ‖G‖⁻¹ := by
    apply (mul_left_cancel₀ hne)
    rw [hprod, mul_inv_cancel₀ hne]
  have hinner : inner ℝ G V = ‖G‖ * ‖V‖ :=
    le_antisymm (real_inner_le_norm G V) (hprod.le.trans hlower)
  have heq := ((inner_eq_norm_mul_iff_div (𝕜 := ℝ) hG).mp hinner).symm
  rw [hvnorm] at heq
  have hcoeff : ‖G‖⁻¹ / ‖G‖ = (‖G‖ ^ 2)⁻¹ := by
    simp only [div_eq_mul_inv, pow_two, mul_inv_rev]
  simpa only [RCLike.ofReal_real_eq_id, id_eq, hcoeff] using heq

theorem superadditive_gradient_eq_of_unit_value
    (hsupport : ∀ v : E, D v ≤ inner ℝ G v)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ‖G‖ ≤ L)
    (hunit : ‖U‖ = 1) (hvalue : D U = L) :
    G = L • U := by
  have hlower : L ≤ inner ℝ G U := by simpa only [hvalue] using hsupport U
  have hsq : ‖G‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (norm_nonneg G) hbound 2
  have hsub : ‖G - L • U‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL,
      hunit, mul_one, real_inner_smul_right]
    nlinarith [mul_le_mul_of_nonneg_left hlower hL]
  have hnorm : ‖G - L • U‖ = 0 := by nlinarith [norm_nonneg (G - L • U)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end DifferentialGeometry.Geometry.Topology
