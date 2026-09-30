import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.ODE

open Set

theorem le_of_local_hyperbolic_midpoint {f g : ℝ → ℝ} {a b k : ℝ}
    (hk : 0 < k) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (ha : g a ≤ f a) (hb : g b ≤ f b)
    (hlocal : ∀ t ∈ Ioo a b, f t < g t → ∃ h : ℝ, 0 < h ∧
      t - h ∈ Icc a b ∧ t + h ∈ Icc a b ∧
      f (t - h) + f (t + h) ≤ 2 * Real.cosh (k * h) * f t ∧
      g (t - h) + g (t + h) = 2 * Real.cosh (k * h) * g t) :
    ∀ t ∈ Icc a b, g t ≤ f t := by
  intro t ht
  by_contra hn
  let u : ℝ → ℝ := fun x => f x - g x
  obtain ⟨x, hx, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨t, ht⟩ (hf.sub hg)
  have hneg : u x < 0 := lt_of_le_of_lt (hmin ht) (sub_neg.mpr (lt_of_not_ge hn))
  have hax : a < x := by
    refine lt_of_le_of_ne hx.1 ?_
    intro he
    rw [← he] at hneg
    exact (not_lt_of_ge (sub_nonneg.mpr ha)) hneg
  have hxb : x < b := by
    refine lt_of_le_of_ne hx.2 ?_
    intro he
    rw [he] at hneg
    exact (not_lt_of_ge (sub_nonneg.mpr hb)) hneg
  obtain ⟨h, hh, hl, hr, hfm, hgm⟩ := hlocal x ⟨hax, hxb⟩ (sub_neg.mp hneg)
  have hleft := hmin hl
  have hright := hmin hr
  change f x - g x ≤ f (x - h) - g (x - h) at hleft
  change f x - g x ≤ f (x + h) - g (x + h) at hright
  have hc : 1 < Real.cosh (k * h) := Real.one_lt_cosh.mpr (mul_pos hk hh).ne'
  have hprod : (Real.cosh (k * h) - 1) * u x < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hc) hneg
  dsimp only [u] at hneg hprod
  nlinarith

noncomputable def hyperbolicInterpolate (k A u v t : ℝ) : ℝ :=
  (Real.sinh (k * (A - t)) * u + Real.sinh (k * t) * v) / Real.sinh (k * A)

theorem continuous_hyperbolicInterpolate (k A u v : ℝ) :
    Continuous (hyperbolicInterpolate k A u v) := by
  unfold hyperbolicInterpolate
  fun_prop

theorem hyperbolicInterpolate_zero {k A : ℝ} (hk : 0 < k) (hA : 0 < A) (u v : ℝ) :
    hyperbolicInterpolate k A u v 0 = u := by
  simp [hyperbolicInterpolate, (Real.sinh_pos_iff.mpr (mul_pos hk hA)).ne']

theorem hyperbolicInterpolate_right {k A : ℝ} (hk : 0 < k) (hA : 0 < A) (u v : ℝ) :
    hyperbolicInterpolate k A u v A = v := by
  simp [hyperbolicInterpolate, (Real.sinh_pos_iff.mpr (mul_pos hk hA)).ne']

theorem hyperbolicInterpolate_midpoint (k A u v t h : ℝ) :
    hyperbolicInterpolate k A u v (t - h) + hyperbolicInterpolate k A u v (t + h) =
      2 * Real.cosh (k * h) * hyperbolicInterpolate k A u v t := by
  have hm : k * (A - (t - h)) = k * (A - t) + k * h := by ring
  have hp : k * (A - (t + h)) = k * (A - t) - k * h := by ring
  simp only [hyperbolicInterpolate, hm, hp, mul_sub, mul_add, Real.sinh_add, Real.sinh_sub]
  ring

theorem hyperbolicInterpolate_le_max {k A u v t : ℝ} (hk : 0 ≤ k)
    (hA : 0 < A) (hmax : 0 ≤ max u v) (ht : t ∈ Icc 0 A) :
    hyperbolicInterpolate k A u v t ≤ max u v := by
  by_cases hk0 : k = 0
  · simpa [hk0, hyperbolicInterpolate] using hmax
  have hk' : 0 < k := lt_of_le_of_ne hk (Ne.symm hk0)
  have hden : 0 < Real.sinh (k * A) := Real.sinh_pos_iff.mpr (mul_pos hk' hA)
  have hx : 0 ≤ Real.sinh (k * (A - t)) := Real.sinh_nonneg_iff.mpr (mul_nonneg hk (sub_nonneg.mpr ht.2))
  have hy : 0 ≤ Real.sinh (k * t) := Real.sinh_nonneg_iff.mpr (mul_nonneg hk ht.1)
  have heq : k * A = k * (A - t) + k * t := by ring
  have hsum : Real.sinh (k * (A - t)) + Real.sinh (k * t) ≤ Real.sinh (k * A) := by
    rw [heq, Real.sinh_add]
    nlinarith [mul_nonneg hx (sub_nonneg.mpr (Real.one_le_cosh (k * t))),
      mul_nonneg hy (sub_nonneg.mpr (Real.one_le_cosh (k * (A - t))))]
  unfold hyperbolicInterpolate
  apply (div_le_iff₀ hden).mpr
  have h1 := mul_le_mul_of_nonneg_left (le_max_left u v) hx
  have h2 := mul_le_mul_of_nonneg_left (le_max_right u v) hy
  have h3 := mul_le_mul_of_nonneg_right hsum hmax
  nlinarith

theorem hyperbolicInterpolate_le_of_local_midpoint {f : ℝ → ℝ} {k A : ℝ}
    (hk : 0 < k) (hA : 0 < A) (hf : ContinuousOn f (Icc 0 A))
    (hlocal : ∀ t ∈ Ioo 0 A, f t < hyperbolicInterpolate k A (f 0) (f A) t →
      ∃ h : ℝ, 0 < h ∧ t - h ∈ Icc 0 A ∧ t + h ∈ Icc 0 A ∧
        f (t - h) + f (t + h) ≤ 2 * Real.cosh (k * h) * f t) :
    ∀ t ∈ Icc 0 A, hyperbolicInterpolate k A (f 0) (f A) t ≤ f t := by
  apply le_of_local_hyperbolic_midpoint hk hf
    (continuous_hyperbolicInterpolate k A (f 0) (f A)).continuousOn
    (by rw [hyperbolicInterpolate_zero hk hA])
    (by rw [hyperbolicInterpolate_right hk hA])
  intro t ht hbad
  obtain ⟨h, hh, hl, hr, hmid⟩ := hlocal t ht hbad
  exact ⟨h, hh, hl, hr, hmid, hyperbolicInterpolate_midpoint k A (f 0) (f A) t h⟩

theorem hyperbolicInterpolate_eq_cosh {k A : ℝ} (hk : 0 < k) (hA : 0 < A)
    (u v t : ℝ) :
    hyperbolicInterpolate k A u v t = Real.cosh (k * t) * u +
      Real.sinh (k * t) / Real.sinh (k * A) * (v - Real.cosh (k * A) * u) := by
  have hden : Real.sinh (k * A) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos hk hA)).ne'
  unfold hyperbolicInterpolate
  rw [mul_sub, Real.sinh_sub]
  field_simp
  ring

theorem hyperbolic_quotient_le_of_interpolate_le {f : ℝ → ℝ} {k A t : ℝ}
    (hk : 0 < k) (hA : 0 < A) (ht : 0 < t)
    (h : hyperbolicInterpolate k A (f 0) (f A) t ≤ f t) :
    (Real.cosh (k * t) * f 0 - f t) / Real.sinh (k * t) ≤
      (Real.cosh (k * A) * f 0 - f A) / Real.sinh (k * A) := by
  rw [hyperbolicInterpolate_eq_cosh hk hA] at h
  have hst : 0 < Real.sinh (k * t) := Real.sinh_pos_iff.mpr (mul_pos hk ht)
  have hsA : 0 < Real.sinh (k * A) := Real.sinh_pos_iff.mpr (mul_pos hk hA)
  rw [div_le_div_iff₀ hst hsA]
  have hmul := mul_le_mul_of_nonneg_right h hsA.le
  field_simp at hmul
  nlinarith

end DifferentialGeometry.Analysis.ODE
