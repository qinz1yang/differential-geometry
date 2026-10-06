import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

private theorem hasDerivAt_angular_monomial (c : ℂ) (n : ℕ) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => (c * (Complex.exp ((t : ℂ) * Complex.I)) ^ n).re)
      ((c * (Complex.exp ((θ : ℂ) * Complex.I)) ^ n * (n : ℂ) * Complex.I).re) θ := by
  have hd := ((((hasDerivAt_id θ).ofReal_comp.mul_const Complex.I).const_mul
    (n : ℂ)).cexp.const_mul c)
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ hd
  simpa only [Function.comp_def, id_eq, Complex.ofReal_one, one_mul, Complex.reCLM_apply,
    Complex.exp_nat_mul, mul_assoc] using hreal

/-- A nonzero complex monomial has only simple angular zeros, and finitely many
on one closed period interval. -/
theorem finite_simple_zeros_real_monomial_on_circle
    {c : ℂ} (hc : c ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    Set.Finite {θ : ℝ | θ ∈ Icc 0 (2 * Real.pi) ∧
      (c * (Complex.exp ((θ : ℂ) * Complex.I)) ^ n).re = 0} ∧
    ∀ θ : ℝ, (c * (Complex.exp ((θ : ℂ) * Complex.I)) ^ n).re = 0 →
      deriv (fun t : ℝ => (c * (Complex.exp ((t : ℂ) * Complex.I)) ^ n).re) θ ≠ 0 := by
  let h : ℝ → ℝ := fun θ => (c * (Complex.exp ((θ : ℂ) * Complex.I)) ^ n).re
  have hn0 : n ≠ 0 := (lt_of_lt_of_le (by decide : 0 < 2) hn).ne'
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hsimple (θ : ℝ) (hz : h θ = 0) : deriv h θ ≠ 0 := by
    intro hd
    rw [(hasDerivAt_angular_monomial c n θ).deriv] at hd
    have himmul :
        -((c * (Complex.exp ((θ : ℂ) * Complex.I)) ^ n).im * (n : ℝ)) = 0 := by
      simpa only [Complex.mul_I_re, Complex.mul_im, Complex.natCast_re,
        Complex.natCast_im, mul_zero, zero_add] using hd
    have him : (c * (Complex.exp ((θ : ℂ) * Complex.I)) ^ n).im = 0 :=
      (mul_eq_zero.mp (neg_eq_zero.mp himmul)).resolve_right hnR
    have hw : c * (Complex.exp ((θ : ℂ) * Complex.I)) ^ n = 0 :=
      Complex.ext hz him
    exact (mul_ne_zero hc (pow_ne_zero n (Complex.exp_ne_zero _))) hw
  have han : AnalyticOnNhd ℝ h univ := by
    intro θ _
    have hcomplex : AnalyticAt ℂ
        (fun z : ℂ => c * (Complex.exp (z * Complex.I)) ^ n) (θ : ℂ) :=
      analyticAt_const.mul ((analyticAt_id.mul analyticAt_const).cexp'.pow n)
    have hreal : AnalyticAt ℝ
        (fun z : ℂ => c * (Complex.exp (z * Complex.I)) ^ n) (θ : ℂ) :=
      hcomplex.restrictScalars
    exact (Complex.reCLM.analyticAt _).comp
      (hreal.comp (Complex.ofRealCLM.analyticAt θ))
  have hfinite : Set.Finite {θ : ℝ | θ ∈ Icc 0 (2 * Real.pi) ∧ h θ = 0} := by
    rcases han.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with
      hzero | hdiscrete
    · have heq : h = fun _ => 0 := funext fun θ => hzero (mem_univ θ)
      have hcontra := hsimple 0 (congrFun heq 0)
      rw [heq, deriv_const] at hcontra
      exact False.elim (hcontra rfl)
    · have hwithin : {θ : ℝ | h θ ≠ 0} ∈ codiscreteWithin (Icc 0 (2 * Real.pi)) :=
        Filter.codiscreteWithin_mono (subset_univ _) hdiscrete
      apply ((isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi))).finite_sdiff_of_mem_codiscreteWithin
        hwithin).subset
      rintro θ ⟨hθ, hzero⟩
      exact ⟨hθ, fun hne => hne hzero⟩
  exact ⟨hfinite, hsimple⟩

end DifferentialGeometry.Analysis
