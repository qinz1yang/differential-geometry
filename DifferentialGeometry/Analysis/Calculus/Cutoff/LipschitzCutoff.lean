import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
open Set Metric
open scoped NNReal

namespace Poincare.Analysis

variable {E F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem lipschitzWith_cutoff_smul
    {ψ : E → ℝ} {f : E → F} {B c r : ℝ≥0}
    (hψ : LipschitzWith B ψ) (hψnorm : ∀ x, ‖ψ x‖ ≤ 1)
    (hψout : ∀ x, x ∉ closedBall 0 r → ψ x = 0)
    (hf : LipschitzOnWith c f (closedBall 0 r)) (hf0 : f 0 = 0) :
    LipschitzWith (c * (1 + B * r)) (fun x ↦ ψ x • f x) := by
  have hfbound (x : E) (hx : x ∈ closedBall 0 r) : ‖f x‖ ≤ c * r := by
    have h := hf.norm_sub_le hx (show (0 : E) ∈ closedBall 0 r by simp)
    rw [hf0, sub_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) c.coe_nonneg)
  have hin (x y : E) (hx : x ∈ closedBall 0 r) (hy : y ∈ closedBall 0 r) :
      ‖ψ x • f x - ψ y • f y‖ ≤ (c * (1 + B * r) : ℝ≥0) * ‖x - y‖ := by
    have he : ψ x • f x - ψ y • f y = ψ x • (f x - f y) + (ψ x - ψ y) • f y := by
      simp only [smul_sub, sub_smul]
      abel
    rw [he]
    calc
      ‖ψ x • (f x - f y) + (ψ x - ψ y) • f y‖ ≤
          ‖ψ x‖ * ‖f x - f y‖ + ‖ψ x - ψ y‖ * ‖f y‖ := by
        simpa only [norm_smul] using norm_add_le (ψ x • (f x - f y)) ((ψ x - ψ y) • f y)
      _ ≤ 1 * (c * ‖x - y‖) + (B * ‖x - y‖) * (c * r) := by
        gcongr
        · exact hψnorm x
        · exact hf.norm_sub_le hx hy
        · exact hψ.norm_sub_le x y
        · exact hfbound y hy
      _ = _ := by push_cast; ring
  have hout (x y : E) (hx : x ∈ closedBall 0 r) (hy : y ∉ closedBall 0 r) :
      ‖ψ x • f x - ψ y • f y‖ ≤ (c * (1 + B * r) : ℝ≥0) * ‖x - y‖ := by
    have hp := hψ.norm_sub_le x y
    rw [hψout y hy, sub_zero] at hp
    rw [hψout y hy, zero_smul, sub_zero, norm_smul]
    calc
      ‖ψ x‖ * ‖f x‖ ≤ (B * ‖x - y‖) * (c * r) :=
        mul_le_mul hp (hfbound x hx) (norm_nonneg _) (mul_nonneg B.coe_nonneg (norm_nonneg _))
      _ ≤ (c * (1 + B * r) : ℝ≥0) * ‖x - y‖ := by
        push_cast
        nlinarith [mul_nonneg c.coe_nonneg (norm_nonneg (x - y))]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  by_cases hx : x ∈ closedBall 0 r
  · by_cases hy : y ∈ closedBall 0 r
    · exact hin x y hx hy
    · exact hout x y hx hy
  · by_cases hy : y ∈ closedBall 0 r
    · simpa only [norm_sub_rev] using hout y x hy hx
    · simp only [hψout x hx, hψout y hy, zero_smul, sub_self, norm_zero]
      positivity

end Poincare.Analysis
