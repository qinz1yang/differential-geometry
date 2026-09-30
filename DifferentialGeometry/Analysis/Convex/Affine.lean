import DifferentialGeometry.Analysis.Convex.Concavity
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open Set

theorem ConcaveOn.eq_of_nonneg_univ {f : ℝ → ℝ} (hf : ConcaveOn ℝ univ f)
    (hn : ∀ t, 0 ≤ f t) (x y : ℝ) : f x = f y := by
  exact DifferentialGeometry.eq_of_concaveOn_univ_of_bddBelow hf
    ⟨0, by rintro _ ⟨t, rfl⟩; exact hn t⟩ x y

theorem ConcaveOn.eq_affine_of_add_neg_nonneg {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ univ f) (hn : ∀ t, 0 ≤ f t + f (-t)) (t : ℝ) :
    f t = f 0 + t * (f 1 - f 0) := by
  have hg : ConcaveOn ℝ univ (fun x => f x + f (-x)) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have h₁ := hf.2 hx hy ha hb hab
    have h₂ := hf.2 (mem_univ (-x)) (mem_univ (-y)) ha hb hab
    simp only [smul_eq_mul] at *
    have heq : a * -x + b * -y = -(a * x + b * y) := by ring
    rw [heq] at h₂
    linarith
  have hsum (x : ℝ) : f x + f (-x) = 2 * f 0 := by
    simpa only [neg_zero, two_mul] using hg.eq_of_nonneg_univ hn x 0
  have heq (x y a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
      f (a * x + b * y) = a * f x + b * f y := by
    have h₁ := hf.2 (mem_univ x) (mem_univ y) ha hb hab
    have h₂ := hf.2 (mem_univ (-x)) (mem_univ (-y)) ha hb hab
    simp only [smul_eq_mul] at *
    have harg : a * -x + b * -y = -(a * x + b * y) := by ring
    rw [harg] at h₂
    have hneg (z : ℝ) : f (-z) = 2 * f 0 - f z := by linarith [hsum z]
    rw [hneg, hneg, hneg] at h₂
    nlinarith [congrArg (fun z : ℝ => z * (2 * f 0)) hab]
  have hpos (u : ℝ) (hu : 0 ≤ u) : f u = f 0 + u * (f 1 - f 0) := by
    by_cases hu1 : u ≤ 1
    · have h := heq 0 1 (1 - u) u (by linarith) hu (by ring)
      simp only [mul_zero, mul_one, zero_add] at h
      linarith
    · have hup : 0 < u := by linarith
      have h := heq 0 u (1 - 1 / u) (1 / u)
        (sub_nonneg.mpr ((div_le_one hup).2 (le_of_not_ge hu1)))
        (by positivity) (by ring)
      have harg : (1 - 1 / u) * 0 + 1 / u * u = 1 := by field_simp; ring
      rw [harg] at h
      have hmul := congrArg (fun v : ℝ => v * u) h
      field_simp at hmul
      nlinarith
  by_cases ht : 0 ≤ t
  · exact hpos t ht
  · have h := hpos (-t) (by linarith)
    linarith [hsum t]
