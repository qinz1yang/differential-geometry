import DifferentialGeometry.Analysis.Calculus.Derivative.ClippedReciprocal

set_option autoImplicit false
noncomputable section
open Set
open scoped NNReal

namespace DifferentialGeometry.Analysis.ODE

theorem le_of_initial_bound_of_quadratic_deriv_bound
    {r r' : ℝ → ℝ} {a b q A B t : ℝ} {C : ℝ≥0}
    (hA : 0 < A) (hB : 0 < B) (hqA : q ≤ A)
    (hc : ContinuousOn r (Icc a b))
    (hd : ∀ s ∈ Ioo a b, q < r s → HasDerivAt r (r' s) s)
    (hb : ∀ s ∈ Ioo a b, q < r s → |r' s| ≤ C * r s ^ 2)
    (hinit : r a ≤ A) (ht : t ∈ Icc a b)
    (htime : C * (t - a) ≤ A⁻¹ - B⁻¹) : r t ≤ B := by
  have hlip := DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound_Icc
    hA hc (fun s hs hAs => hd s hs (hqA.trans_lt hAs))
    (fun s hs hAs => hb s hs (hqA.trans_lt hAs))
  have hrec := hlip.dist_le_mul t ht a ⟨le_rfl, ht.1.trans ht.2⟩
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1),
    max_eq_left hinit] at hrec
  have hlow : B⁻¹ ≤ (max A (r t))⁻¹ := by
    linarith [le_abs_self (A⁻¹ - (max A (r t))⁻¹), abs_sub_comm ((max A (r t))⁻¹) A⁻¹]
  exact (le_max_right _ _).trans
    ((inv_le_inv₀ hB (hA.trans_le (le_max_left _ _))).mp hlow)

theorem le_two_mul_of_initial_bound_of_quadratic_deriv_bound
    {r r' : ℝ → ℝ} {a b q A t : ℝ} {C : ℝ≥0}
    (hA : 0 < A) (hqA : q ≤ A) (hc : ContinuousOn r (Icc a b))
    (hd : ∀ s ∈ Ioo a b, q < r s → HasDerivAt r (r' s) s)
    (hb : ∀ s ∈ Ioo a b, q < r s → |r' s| ≤ C * r s ^ 2)
    (hinit : r a ≤ A) (ht : t ∈ Icc a b)
    (htime : 2 * C * A * (t - a) ≤ 1) : r t ≤ 2 * A := by
  apply le_of_initial_bound_of_quadratic_deriv_bound hA (by positivity) hqA hc hd hb hinit ht
  have hbound : C * (t - a) ≤ (2*A)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have heq : A⁻¹ - (2*A)⁻¹ = (2*A)⁻¹ := by field_simp; ring
  rwa [heq]

end DifferentialGeometry.Analysis.ODE
