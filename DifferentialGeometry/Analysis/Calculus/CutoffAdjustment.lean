import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem cutoff_adjustment_value_derivative_le {f : E → H} {ψ : H → ℝ} {v : H → H} {x : E}
    (hf : DifferentiableAt ℝ f x) (hψ : DifferentiableAt ℝ ψ (f x))
    (hv : DifferentiableAt ℝ v (f x)) {a b L c ρ : ℝ}
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hρ : 0 < ρ)
    (hcutoff : 0 ≤ ψ (f x) ∧ ψ (f x) ≤ 1)
    (hvalue : ‖v (f x)‖ ≤ a * ρ) (hcutoffDeriv : ‖fderiv ℝ ψ (f x)‖ ≤ b / ρ)
    (hfirst : ‖fderiv ℝ f x‖ ≤ L)
    (hcomposite : ‖(fderiv ℝ v (f x)).comp (fderiv ℝ f x)‖ ≤ c) :
    let g : E → H := fun y => f y + ψ (f y) • v (f y)
    ‖g x - f x‖ ≤ a * ρ ∧ ‖fderiv ℝ g x - fderiv ℝ f x‖ ≤ a * b * L + c := by
  have hψf := hψ.hasFDerivAt.comp x hf.hasFDerivAt
  have hvf := hv.hasFDerivAt.comp x hf.hasFDerivAt
  have hg := hf.hasFDerivAt.add (hψf.smul hvf)
  dsimp
  constructor
  · rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hcutoff.1]
    have hh := mul_le_mul_of_nonneg_right hcutoff.2 (norm_nonneg (v (f x)))
    nlinarith
  · change ‖fderiv ℝ (f + (ψ ∘ f) • (v ∘ f)) x - fderiv ℝ f x‖ ≤ _
    rw [hg.fderiv, add_sub_cancel_left]
    apply (norm_add_le _ _).trans
    have h1 : ‖ψ (f x) • (fderiv ℝ v (f x)).comp (fderiv ℝ f x)‖ ≤ c := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcutoff.1]
      exact (mul_le_mul hcutoff.2 hcomposite (norm_nonneg _) (by norm_num)).trans_eq (one_mul c)
    have h2 : ‖((fderiv ℝ ψ (f x)).comp (fderiv ℝ f x)).smulRight (v (f x))‖ ≤ a * b * L := by
      rw [ContinuousLinearMap.norm_smulRight_apply]
      have hcf : ‖(fderiv ℝ ψ (f x)).comp (fderiv ℝ f x)‖ ≤ (b / ρ) * L :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul hcutoffDeriv hfirst (norm_nonneg _) (div_nonneg hb hρ.le))
      calc
        _ ≤ ((b / ρ) * L) * (a * ρ) :=
          mul_le_mul hcf hvalue (norm_nonneg _) (mul_nonneg (div_nonneg hb hρ.le) hL)
        _ = _ := by field_simp
    simpa only [Function.comp_apply, add_comm] using add_le_add h1 h2

theorem projected_cutoff_adjustment_value_derivative_le {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → H} {ψ : H → ℝ} {P : F → F} {x : E}
    (Q : H →L[ℝ] F) (J : F →L[ℝ] H) (A : F →L[ℝ] F)
    (hQ : ‖Q‖ ≤ 1) (hJ : ‖J‖ ≤ 1)
    (hf : DifferentiableAt ℝ f x) (hψ : DifferentiableAt ℝ ψ (f x))
    (hP : DifferentiableAt ℝ P (Q (f x))) {a b L d e ρ : ℝ}
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hd : 0 ≤ d) (hρ : 0 < ρ)
    (hcutoff : 0 ≤ ψ (f x) ∧ ψ (f x) ≤ 1)
    (hvalue : ‖P (Q (f x)) - Q (f x)‖ ≤ a * ρ)
    (hcutoffDeriv : ‖fderiv ℝ ψ (f x)‖ ≤ b / ρ)
    (hfirst : ‖fderiv ℝ f x‖ ≤ L)
    (hcomparison : ‖fderiv ℝ P (Q (f x)) - A‖ ≤ d)
    (hnormal : ‖(ContinuousLinearMap.id ℝ F - A).comp (Q.comp (fderiv ℝ f x))‖ ≤ e) :
    let g : E → H := fun y => f y + ψ (f y) • J (P (Q (f y)) - Q (f y))
    ‖g x - f x‖ ≤ a * ρ ∧ ‖fderiv ℝ g x - fderiv ℝ f x‖ ≤ a * b * L + d * L + e := by
  let v : H → H := fun z => J (P (Q z) - Q z)
  have hv : HasFDerivAt v
      (J.comp ((fderiv ℝ P (Q (f x))).comp Q - Q)) (f x) :=
    J.hasFDerivAt.comp (f x) ((hP.hasFDerivAt.comp (f x) Q.hasFDerivAt).sub Q.hasFDerivAt)
  have hval : ‖v (f x)‖ ≤ a * ρ := by
    exact ((J.le_opNorm _).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))).trans
      (by simpa only [one_mul] using hvalue)
  let U := Q.comp (fderiv ℝ f x)
  let D := fderiv ℝ P (Q (f x))
  have hU : ‖U‖ ≤ L := ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul hQ hfirst (norm_nonneg _) (by norm_num))).trans_eq (one_mul _)
  have hsplit : (D - ContinuousLinearMap.id ℝ F).comp U =
      (D - A).comp U - (ContinuousLinearMap.id ℝ F - A).comp U := by
    ext z
    simp only [ContinuousLinearMap.comp_apply, sub_apply]
    abel
  have hinner : ‖(D - ContinuousLinearMap.id ℝ F).comp U‖ ≤ d * L + e := by
    rw [hsplit]
    apply (norm_sub_le _ _).trans
    apply add_le_add _ hnormal
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hcomparison hU (norm_nonneg _) hd)
  have heq : (J.comp (D.comp Q - Q)).comp (fderiv ℝ f x) =
      J.comp ((D - ContinuousLinearMap.id ℝ F).comp U) := by
    ext z
    simp [U]
  have hcomp : ‖(fderiv ℝ v (f x)).comp (fderiv ℝ f x)‖ ≤ d * L + e := by
    rw [hv.fderiv, heq]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))).trans
        (by simpa only [one_mul] using hinner)
  have hh := cutoff_adjustment_value_derivative_le hf hψ hv.differentiableAt hb hL hρ
    hcutoff hval hcutoffDeriv hfirst hcomp
  simpa only [v, add_assoc] using hh

theorem projected_cutoff_adjustment_cumulative_le {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f f₀ : E → H} {ψ : H → ℝ} {P : F → F} {x : E}
    (Q : H →L[ℝ] F) (J : F →L[ℝ] H) (A : F →L[ℝ] F)
    (hQ : ‖Q‖ ≤ 1) (hJ : ‖J‖ ≤ 1) (hA : ‖ContinuousLinearMap.id ℝ F - A‖ ≤ 1)
    (hf : DifferentiableAt ℝ f x) (hψ : DifferentiableAt ℝ ψ (f x))
    (hP : DifferentiableAt ℝ P (Q (f x))) {a b L d ν ρ E₀ H₀ : ℝ}
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hd : 0 ≤ d) (hH : 0 ≤ H₀) (hρ : 0 < ρ)
    (hcutoff : 0 ≤ ψ (f x) ∧ ψ (f x) ≤ 1)
    (hvalue : ‖P (Q (f x)) - Q (f x)‖ ≤ a * ρ)
    (hcutoffDeriv : ‖fderiv ℝ ψ (f x)‖ ≤ b / ρ)
    (hfirst : ‖fderiv ℝ f₀ x‖ ≤ L)
    (hcomparison : ‖fderiv ℝ P (Q (f x)) - A‖ ≤ d)
    (hnormal : ‖(ContinuousLinearMap.id ℝ F - A).comp (Q.comp (fderiv ℝ f₀ x))‖ ≤ ν)
    (hpriorValue : ‖f x - f₀ x‖ ≤ E₀ * ρ)
    (hpriorDeriv : ‖fderiv ℝ f x - fderiv ℝ f₀ x‖ ≤ H₀) :
    let g : E → H := fun y => f y + ψ (f y) • J (P (Q (f y)) - Q (f y))
    ‖g x - f₀ x‖ ≤ (E₀ + a) * ρ ∧
      ‖fderiv ℝ g x - fderiv ℝ f₀ x‖ ≤
        a * b * (L + H₀) + d * (L + H₀) + ν + 2 * H₀ := by
  have hDf : ‖fderiv ℝ f x‖ ≤ L + H₀ := by
    have hh := norm_sub_le (fderiv ℝ f x - fderiv ℝ f₀ x) (-(fderiv ℝ f₀ x))
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hh
    linarith
  let N := (ContinuousLinearMap.id ℝ F - A).comp Q
  have hN : ‖N‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hA hQ (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  have hn : ‖N.comp (fderiv ℝ f x)‖ ≤ ν + H₀ := by
    have heq : N.comp (fderiv ℝ f x) =
        N.comp (fderiv ℝ f₀ x) + N.comp (fderiv ℝ f x - fderiv ℝ f₀ x) := by
      rw [ContinuousLinearMap.comp_sub]
      abel
    rw [heq]
    apply (norm_add_le _ _).trans
    apply add_le_add _
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul hN hpriorDeriv (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)))
    simpa only [N, ContinuousLinearMap.comp_assoc] using hnormal
  have hh := projected_cutoff_adjustment_value_derivative_le Q J A hQ hJ hf hψ hP
    hb (add_nonneg hL hH) hd hρ hcutoff hvalue hcutoffDeriv hDf hcomparison
    (by simpa only [N, ContinuousLinearMap.comp_assoc] using hn)
  let g : E → H := fun y => f y + ψ (f y) • J (P (Q (f y)) - Q (f y))
  change ‖g x - f₀ x‖ ≤ _ ∧ ‖fderiv ℝ g x - fderiv ℝ f₀ x‖ ≤ _
  have h1 := norm_sub_le (g x - f x) (f₀ x - f x)
  have h2 := norm_sub_le (fderiv ℝ g x - fderiv ℝ f x)
    (fderiv ℝ f₀ x - fderiv ℝ f x)
  rw [sub_sub_sub_cancel_right, norm_sub_rev (f₀ x) (f x)] at h1
  rw [sub_sub_sub_cancel_right, norm_sub_rev (fderiv ℝ f₀ x) (fderiv ℝ f x)] at h2
  constructor <;> nlinarith [hh.1, hh.2]

end DifferentialGeometry.Analysis
