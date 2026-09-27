import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
noncomputable section

open Set

namespace DifferentialGeometry.Analysis

theorem affine_bound_backward_closed (u : ℝ → ℝ) {c b α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β)
    (hc : ContinuousOn u (Icc c b)) (hb : 0 ≤ u b)
    (hd : ∀ s ∈ Ioo c b, ∃ d, HasDerivAt u d s ∧ -(α * u s + β) ≤ d)
    (t : ℝ) (ht : t ∈ Icc c b) :
    u t ≤ Real.exp (α * (b - c)) * (u b + β / α) := by
  let F := fun s => Real.exp (α * s) * (u s + β / α)
  have hFc : ContinuousOn F (Icc c b) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      (hc.add continuousOn_const)
  have hFd (s : ℝ) (hs : s ∈ Ioo c b) : ∃ d, HasDerivAt F d s ∧ 0 ≤ d := by
    obtain ⟨d, hd, hb⟩ := hd s hs
    refine ⟨Real.exp (α * s) * α * (u s + β / α) + Real.exp (α * s) * d, ?_, ?_⟩
    · have hh := (((hasDerivAt_id s).const_mul α).exp.mul (hd.add_const (β / α)))
      convert hh using 1 <;> first | rfl | simp only [mul_one, id_eq]
    · have heq : Real.exp (α * s) * α * (u s + β / α) + Real.exp (α * s) * d =
          Real.exp (α * s) * (d + α * u s + β) := by
        field_simp
        ring
      rw [heq]
      exact mul_nonneg (Real.exp_pos _).le (by linarith)
  have hmono : MonotoneOn F (Icc c b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc c b) hFc
    · intro s hs
      obtain ⟨d, hd, _⟩ := hFd s (by simpa only [interior_Icc] using hs)
      exact hd.differentiableAt.differentiableWithinAt
    · intro s hs
      obtain ⟨d, hd, hb⟩ := hFd s (by simpa only [interior_Icc] using hs)
      simpa only [hd.deriv] using hb
  have hh := hmono ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2
  have hmul := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-α * t)).le
  have he : Real.exp (-α * t) * F t = u t + β / α := by
    dsimp only [F]
    rw [← mul_assoc, ← Real.exp_add]
    simp only [neg_mul, neg_add_cancel, Real.exp_zero, one_mul]
  rw [he] at hmul
  have hFb : Real.exp (-α * t) * F b =
      Real.exp (α * (b - t)) * (u b + β / α) := by
    dsimp only [F]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hFb] at hmul
  have hb0 : 0 ≤ β / α := div_nonneg hβ hα.le
  exact (by linarith : u t ≤ Real.exp (α * (b - t)) * (u b + β / α)).trans
    (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_left ht.1 b) hα.le))
      (add_nonneg hb hb0))

end DifferentialGeometry.Analysis
