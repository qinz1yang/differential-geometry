import DifferentialGeometry.Analysis.Calculus.BilinearBounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Algebra.Support

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem weighted_affine_cutoff_derivative_bounds (L : E →L[ℝ] H) (b : H)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) {M C L₁ L₂ : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hvalue : ∀ x, |φ x| ≤ M)
    (hfirst : ∀ x, ‖fderiv ℝ φ x‖ ≤ L₁)
    (hsecond : ∀ x, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ L₂)
    (hsupport : ∀ x ∈ tsupport φ, ‖L x + b‖ ≤ C) (x : E) :
    let F : E → H := fun y => φ y • (L y + b)
    ‖fderiv ℝ F x‖ ≤ M * ‖L‖ + L₁ * C ∧
      ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ 2 * L₁ * ‖L‖ + L₂ * C := by
  let F : E → H := fun y => φ y • (L y + b)
  change ‖fderiv ℝ F x‖ ≤ _ ∧ ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ _
  by_cases hx : x ∈ tsupport φ
  · let B : ℝ →L[ℝ] H →L[ℝ] H := ContinuousLinearMap.lsmul ℝ ℝ
    have hB : ‖B‖ ≤ 1 := ContinuousLinearMap.opNorm_lsmul_le
    have hdiff := hφ.differentiable (by norm_num)
    have hDdiff : Differentiable ℝ (fderiv ℝ φ) :=
      ((contDiff_succ_iff_fderiv (n := 1)).mp hφ).2.2.differentiable (by norm_num)
    have ha (y : E) : HasFDerivAt (fun z => L z + b) L y := L.hasFDerivAt.add_const b
    have heq : fderiv ℝ (fun z => L z + b) = fun _ => L := funext fun y => (ha y).fderiv
    have hd : DifferentiableAt ℝ (fderiv ℝ (fun z => L z + b)) x := by
      rw [heq]
      exact differentiableAt_const L
    have hh₁ := B.norm_fderiv_bilinear_le (hdiff x) (ha x).differentiableAt
    have hh₂ := B.norm_second_fderiv_bilinear_le hdiff (fun y => (ha y).differentiableAt)
      (hDdiff x) hd
    simp only [heq, fderiv_const_apply, norm_zero, mul_zero, zero_add] at hh₁ hh₂
    have hb₁ := mul_le_mul_of_nonneg_right hB
      (show 0 ≤ |φ x| * ‖L‖ + ‖fderiv ℝ φ x‖ * ‖L x + b‖ by positivity)
    have hb₂ := mul_le_mul_of_nonneg_right hB
      (show 0 ≤ 2 * ‖fderiv ℝ φ x‖ * ‖L‖ +
        ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖L x + b‖ by positivity)
    have hv := mul_le_mul_of_nonneg_right (hvalue x) (norm_nonneg L)
    have h1 := mul_le_mul (hfirst x) (hsupport x hx) (norm_nonneg _) hL₁
    have h2 := mul_le_mul (hsecond x) (hsupport x hx) (norm_nonneg _) hL₂
    have h3 := mul_le_mul_of_nonneg_right (hfirst x) (norm_nonneg L)
    change ‖fderiv ℝ F x‖ ≤ _ at hh₁
    change ‖fderiv ℝ (fderiv ℝ F) x‖ ≤ _ at hh₂
    rw [Real.norm_eq_abs] at hh₁
    constructor <;> nlinarith
  · have hn : x ∉ tsupport F := fun h => hx (tsupport_smul_subset_left φ (fun y => L y + b) h)
    have hDn : x ∉ tsupport (fderiv ℝ F) := fun h => hn (tsupport_fderiv_subset ℝ h)
    rw [fderiv_of_notMem_tsupport ℝ hn, fderiv_of_notMem_tsupport ℝ hDn, norm_zero]
    constructor
    · exact add_nonneg (mul_nonneg hM (norm_nonneg L)) (mul_nonneg hL₁ hC)
    · simpa only [norm_zero] using add_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL₁) (norm_nonneg L)) (mul_nonneg hL₂ hC)

end DifferentialGeometry.Analysis
