import Mathlib.Analysis.Convex.Strong
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring


namespace DifferentialGeometry.Analysis

open Set

theorem concaveOn_sub_norm_sq_of_concaveOn_affine_segments
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} {f : E → ℝ} {D : ℝ} (hK : Convex ℝ K)
    (hline : ∀ x ∈ K, ∀ y ∈ K, ConcaveOn ℝ (Icc (0 : ℝ) 1)
      (fun r => f (x + r • (y - x)) - (D * ‖y - x‖ ^ 2) / 2 * r ^ 2)) :
    ConcaveOn ℝ K (fun x => f x - D / 2 * ‖x‖ ^ 2) := by
  have hstrong : StrongConcaveOn K (-D) f := by
    refine ⟨hK, ?_⟩
    intro x hx y hy a b ha hb hab
    have hzero : x + (0 : ℝ) • (y - x) = x := by simp
    have hone : x + (1 : ℝ) • (y - x) = y := by module
    have harg : x + b • (y - x) = a • x + b • y := by
      rw [show a = 1 - b from eq_sub_of_add_eq hab]
      module
    have hjensen : a * f x + b * (f y - (D * ‖y - x‖ ^ 2) / 2) ≤
        f (a • x + b • y) - (D * ‖y - x‖ ^ 2) / 2 * b ^ 2 := by
      have h := (hline x hx y hy).2
        (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
        (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩) ha hb hab
      simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_pow (by decide : 2 ≠ 0),
        one_pow, hzero, hone, harg, sub_zero] using h
    change a * f x + b * f y + a * b * ((-D) / 2 * ‖x - y‖ ^ 2) ≤ _
    rw [norm_sub_rev x y]
    calc
      _ = (a * f x + b * (f y - (D * ‖y - x‖ ^ 2) / 2)) +
          (D * ‖y - x‖ ^ 2) / 2 * b ^ 2 := by
        rw [show a = 1 - b from eq_sub_of_add_eq hab]
        ring
      _ ≤ _ := le_sub_iff_add_le.mp hjensen
  exact (strongConcaveOn_iff_convex.mp hstrong).congr fun x _ => by ring

end DifferentialGeometry.Analysis
