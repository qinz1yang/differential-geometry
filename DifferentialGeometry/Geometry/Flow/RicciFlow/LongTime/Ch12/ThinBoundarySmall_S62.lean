import Mathlib

set_option autoImplicit false

/-!
# CH12-S62 (G3 piece): smallness of the nearly-cuspidal size `max δ (√(1+δ) · e^{-L/2} D)`

Pure real analysis: if the accuracy `a` is small and the level `L ≥ a⁻¹/2` (the `hlev` input of the
`hNCB` binder), then `max a (√(1+a) · (e^{-L/2} · Dm)) ≤ w`.
-/

namespace GC.LongTime.Ch12

theorem exp_neg_le_S62 {a L : ℝ} (ha : 0 < a) (hL : a⁻¹ / 2 ≤ L) :
    Real.exp (-L / 2) ≤ 4 * a := by
  set x := a⁻¹ / 4 with hx
  have hx0 : 0 < x := by positivity
  have h1 : Real.exp (-L / 2) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by rw [hx]; linarith)
  have h2 : Real.exp (-x) ≤ x⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hx0 (by linarith [Real.add_one_le_exp x])
  have h3 : x⁻¹ = 4 * a := by rw [hx]; field_simp
  linarith

theorem small_size_S62 {Dm : ℝ} (hDm : 0 ≤ Dm) {w : ℝ} (hw : 0 < w) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a L : ℝ, 0 < a → a < ε → a⁻¹ / 2 ≤ L →
      max a (Real.sqrt (1 + a) * (Real.exp (-L / 2) * Dm)) ≤ w := by
  refine ⟨min (min 1 w) (w / (12 * (Dm + 1))), lt_min (lt_min one_pos hw) (by positivity),
    fun a L ha haε hL => ?_⟩
  have ha1 : a < 1 := lt_of_lt_of_le haε ((min_le_left _ _).trans (min_le_left _ _))
  have haw : a < w := lt_of_lt_of_le haε ((min_le_left _ _).trans (min_le_right _ _))
  have ha3 : a < w / (12 * (Dm + 1)) := lt_of_lt_of_le haε (min_le_right _ _)
  have ha4 : a * (12 * (Dm + 1)) < w := by
    rwa [lt_div_iff₀ (by positivity)] at ha3
  refine max_le haw.le ?_
  have hs : Real.sqrt (1 + a) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hE := exp_neg_le_S62 ha hL
  have h1 : Real.sqrt (1 + a) * (Real.exp (-L / 2) * Dm) ≤ 2 * ((4 * a) * Dm) :=
    mul_le_mul hs (mul_le_mul_of_nonneg_right hE hDm) (by positivity) (by norm_num)
  nlinarith [mul_nonneg ha.le hDm]

end GC.LongTime.Ch12
