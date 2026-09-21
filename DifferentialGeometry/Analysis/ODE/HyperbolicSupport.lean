import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis.ODE

private theorem second_deriv_nonneg_of_isLocalMin {f : ℝ → ℝ} {x : ℝ}
    (hmin : IsLocalMin f x) (hc : ContinuousAt f x) : 0 ≤ deriv (deriv f) x := by
  by_contra h
  have hneg : deriv (deriv f) x < 0 := lt_of_not_ge h
  have hmax : IsLocalMax f x := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hmax, hmin] with y h1 h2
    exact le_antisymm h1 h2
  have hzero : deriv (deriv f) x = 0 := by
    simpa only [deriv_const', deriv_const] using heq.deriv.deriv_eq
  exact (ne_of_lt hneg) hzero

theorem le_of_second_deriv_upper_support {f h : ℝ → ℝ} {a b c : ℝ}
    (hc : 0 < c) (hf : ContinuousOn f (Icc a b))
    (hh : ContDiffOn ℝ 2 h (Icc a b)) (hha : h a ≤ f a) (hhb : h b ≤ f b)
    (hode : ∀ x ∈ Ioo a b, deriv (deriv h) x = c * h x)
    (hsupport : ∀ x ∈ Ioo a b, ∀ ε : ℝ, 0 < ε → ∃ ψ : ℝ → ℝ,
      ContDiffAt ℝ 2 ψ x ∧ ψ x = f x ∧
        (∀ᶠ y in 𝓝 x, f y ≤ ψ y) ∧ deriv (deriv ψ) x ≤ c * f x + ε) :
    ∀ x ∈ Icc a b, h x ≤ f x := by
  intro x hx
  by_contra hbad
  have hgap : f x - h x < 0 := sub_neg.mpr (lt_of_not_ge hbad)
  let G : ℝ → ℝ := fun t => f t - h t
  have hGD : ContinuousOn G (Icc a b) := hf.sub hh.continuousOn
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨x, hx⟩ hGD
  have hGm : G m < 0 := lt_of_le_of_lt (hmin hx) hgap
  have ham : a < m := by
    refine lt_of_le_of_ne hm.1 ?_
    intro heq
    rw [← heq] at hGm
    dsimp only [G] at hGm
    linarith
  have hmb : m < b := by
    refine lt_of_le_of_ne hm.2 ?_
    intro heq
    rw [heq] at hGm
    dsimp only [G] at hGm
    linarith
  let ε : ℝ := -(c * G m) / 2
  have hε : 0 < ε := by dsimp only [ε]; nlinarith [mul_neg_of_pos_of_neg hc hGm]
  obtain ⟨ψ, hψC, hcontact, habove, hsecond⟩ := hsupport m ⟨ham, hmb⟩ ε hε
  let φ : ℝ → ℝ := fun t => ψ t - h t
  have hminloc : IsLocalMin G m := hmin.isLocalMin (Icc_mem_nhds ham hmb)
  have hφmin : IsLocalMin φ m := by
    filter_upwards [hminloc, habove] with t ht hle
    dsimp only [φ, G] at *
    rw [hcontact]
    linarith
  have hhC : ContDiffAt ℝ 2 h m := (hh m hm).contDiffAt (Icc_mem_nhds ham hmb)
  have hhDiff : ∀ᶠ t in 𝓝 m, DifferentiableAt ℝ h t :=
    (hhC.eventually (by norm_num)).mono fun _ h => h.differentiableAt (by norm_num)
  have hψDiff : ∀ᶠ t in 𝓝 m, DifferentiableAt ℝ ψ t :=
    (hψC.eventually (by norm_num)).mono fun _ h => h.differentiableAt (by norm_num)
  have hφ_deriv : deriv φ =ᶠ[𝓝 m] fun t => deriv ψ t - deriv h t := by
    filter_upwards [hψDiff, hhDiff] with t ht hht
    exact deriv_sub ht hht
  have hψSecond : DifferentiableAt ℝ (deriv ψ) m :=
    (hψC.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hhSecond : DifferentiableAt ℝ (deriv h) m :=
    (hhC.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hφ_second : deriv (deriv φ) m = deriv (deriv ψ) m - c * h m := by
    rw [hφ_deriv.deriv_eq]
    simpa only [Pi.sub_apply, hode m ⟨ham, hmb⟩] using! (hψSecond.hasDerivAt.sub hhSecond.hasDerivAt).deriv
  have hnonneg := second_deriv_nonneg_of_isLocalMin hφmin
    (hψC.continuousAt.sub hhC.continuousAt)
  rw [hφ_second] at hnonneg
  dsimp only [ε, G] at hsecond hGm
  nlinarith [mul_neg_of_pos_of_neg hc hGm]

private theorem hyperbolic_linear_combination_second_deriv (k u v x : ℝ) :
    deriv (deriv (fun t => Real.cosh (k * t) * u + Real.sinh (k * t) * v)) x =
      k ^ 2 * (Real.cosh (k * x) * u + Real.sinh (k * x) * v) := by
  have hd (t : ℝ) : HasDerivAt
      (fun t => Real.cosh (k * t) * u + Real.sinh (k * t) * v)
      (Real.sinh (k * t) * k * u + Real.cosh (k * t) * k * v) t := by
    simpa only [mul_one] using!
      ((((hasDerivAt_id t).const_mul k).cosh).mul_const u).add
        ((((hasDerivAt_id t).const_mul k).sinh).mul_const v)
  have hd_eq : deriv (fun t => Real.cosh (k * t) * u + Real.sinh (k * t) * v) =
      fun t => Real.sinh (k * t) * k * u + Real.cosh (k * t) * k * v :=
    funext fun t => (hd t).deriv
  rw [hd_eq]
  have hdd := (((((hasDerivAt_id x).const_mul k).sinh).mul_const k).mul_const u).add
    (((((hasDerivAt_id x).const_mul k).cosh).mul_const k).mul_const v)
  convert! hdd.deriv using 1
  simp only [mul_one, id_eq]
  ring

theorem hyperbolic_chord_le_of_second_deriv_upper_support {f : ℝ → ℝ} {k A : ℝ}
    (hk : 0 < k) (hA : 0 < A) (hf : ContinuousOn f (Icc 0 A))
    (hsupport : ∀ x ∈ Ioo 0 A, ∀ ε : ℝ, 0 < ε → ∃ ψ : ℝ → ℝ,
      ContDiffAt ℝ 2 ψ x ∧ ψ x = f x ∧
        (∀ᶠ y in 𝓝 x, f y ≤ ψ y) ∧ deriv (deriv ψ) x ≤ k ^ 2 * f x + ε)
    {a : ℝ} (ha : a ∈ Icc 0 A) :
    Real.cosh (k * a) * f 0 + Real.sinh (k * a) / Real.sinh (k * A) *
      (f A - Real.cosh (k * A) * f 0) ≤ f a := by
  let v := (f A - Real.cosh (k * A) * f 0) / Real.sinh (k * A)
  have hsinh : Real.sinh (k * A) ≠ 0 :=
    ne_of_gt (Real.sinh_pos_iff.mpr (mul_pos hk hA))
  have h := le_of_second_deriv_upper_support (f := f)
    (h := fun t => Real.cosh (k * t) * f 0 + Real.sinh (k * t) * v)
    (sq_pos_of_pos hk) hf (by fun_prop) (by simp) (by
      dsimp only [v]
      field_simp
      ring_nf
      exact le_refl _)
    (fun x _ => hyperbolic_linear_combination_second_deriv k (f 0) v x)
    hsupport a ha
  convert h using 1
  dsimp only [v]
  ring

theorem hyperbolic_quotient_mono_of_second_deriv_upper_support
    {f : ℝ → ℝ} {k A a : ℝ}
    (hk : 0 < k) (hA : 0 < A) (hf : ContinuousOn f (Icc 0 A))
    (hsupport : ∀ x ∈ Ioo 0 A, ∀ ε : ℝ, 0 < ε → ∃ ψ : ℝ → ℝ,
      ContDiffAt ℝ 2 ψ x ∧ ψ x = f x ∧
        (∀ᶠ y in 𝓝 x, f y ≤ ψ y) ∧ deriv (deriv ψ) x ≤ k ^ 2 * f x + ε)
    (ha : 0 < a) (haA : a ≤ A) :
    (Real.cosh (k * a) * f 0 - f a) / Real.sinh (k * a) ≤
      (Real.cosh (k * A) * f 0 - f A) / Real.sinh (k * A) := by
  have h := hyperbolic_chord_le_of_second_deriv_upper_support hk hA hf hsupport ⟨ha.le, haA⟩
  have hsa : 0 < Real.sinh (k * a) := Real.sinh_pos_iff.mpr (mul_pos hk ha)
  have hsA : 0 < Real.sinh (k * A) := Real.sinh_pos_iff.mpr (mul_pos hk hA)
  rw [div_le_div_iff₀ hsa hsA]
  have hmul := mul_le_mul_of_nonneg_right h hsA.le
  field_simp at hmul
  nlinarith

end DifferentialGeometry.Analysis.ODE
