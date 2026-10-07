import Mathlib.Analysis.Calculus.MeanValue

/-!
# CH12-O26 L2: one-step interpolation (C⁰ small + C² bounded ⇒ C¹ small)

On a closed ball `closedBall x t` (`t > 0`), if `‖g‖ ≤ S` and `‖g''‖ ≤ M` then
`‖g' x‖ ≤ 2 S / t + t M`.  Building block of the single-model core `L1` of `[FROZEN] CH12-O26`
(route: bounded `C^{k+1}` from the chart connection identity + small `C⁰` ⇒ small `C^k`, by
iterating this step on `D^{j-1}(Ψ̃ - id)`); also usable for S57's W-B2 interpolation.
-/

set_option autoImplicit false

open Metric Set

namespace GC.LongTime.Ch12

/-- **One-step interpolation.**  First-order Taylor with the mean-value bound on a closed ball. -/
theorem norm_fderiv_le_interp_O26 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : E → F} {g' : E → E →L[ℝ] F}
    {g'' : E → E →L[ℝ] E →L[ℝ] F} {x : E} {t S M : ℝ} (ht : 0 < t)
    (hg : ∀ y ∈ closedBall x t, HasFDerivWithinAt g (g' y) (closedBall x t) y)
    (hg' : ∀ y ∈ closedBall x t, HasFDerivWithinAt g' (g'' y) (closedBall x t) y)
    (hS : ∀ y ∈ closedBall x t, ‖g y‖ ≤ S) (hM : ∀ y ∈ closedBall x t, ‖g'' y‖ ≤ M) :
    ‖g' x‖ ≤ 2 * S / t + t * M := by
  have hx : x ∈ closedBall x t := mem_closedBall_self ht.le
  have hconv : Convex ℝ (closedBall x t) := convex_closedBall x t
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hx)
  -- `‖g' y - g' x‖ ≤ M t` on the ball
  have hd : ∀ y ∈ closedBall x t, ‖g' y - g' x‖ ≤ M * t := fun y hy =>
    (hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hg' hM hx hy).trans
      (mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hy) hM0)
  -- φ y := g y - g' x y has derivative g' y - g' x
  have hφ : ∀ y ∈ closedBall x t, HasFDerivWithinAt (fun z => g z - g' x z) (g' y - g' x)
      (closedBall x t) y := fun y hy => (hg y hy).sub (g' x).hasFDerivWithinAt
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hx)
  refine ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg (div_nonneg (by linarith) ht.le) (mul_nonneg ht.le hM0)) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  set w : E := (t / ‖v‖) • v with hw
  have hwn : ‖w‖ = t := by
    rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ht hvpos), div_mul_cancel₀ _ hvpos.ne']
  have hy : x + w ∈ closedBall x t := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hwn]
  have hmv := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hφ hd hx hy
  rw [add_sub_cancel_left, hwn, map_add] at hmv
  have hgw : ‖g' x w‖ ≤ 2 * S + M * t * t := by
    have h1 : g' x w = (g (x + w) - g x) - (g (x + w) - (g' x x + g' x w) - (g x - g' x x)) := by
      abel
    rw [h1]
    refine (norm_sub_le _ _).trans ?_
    have h2 := norm_sub_le (g (x + w)) (g x)
    linarith [hS _ hy, hS x hx]
  have hgv : g' x w = (t / ‖v‖) • g' x v := by rw [hw, map_smul]
  rw [hgv, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ht hvpos)] at hgw
  have key : ‖g' x v‖ ≤ (2 * S + M * t * t) * ‖v‖ / t := by
    rw [le_div_iff₀ ht]
    have h3 : t / ‖v‖ * ‖g' x v‖ * ‖v‖ = ‖g' x v‖ * t := by field_simp
    have := mul_le_mul_of_nonneg_right hgw hvpos.le
    rw [h3] at this
    exact this
  calc ‖g' x v‖ ≤ (2 * S + M * t * t) * ‖v‖ / t := key
    _ = (2 * S / t + t * M) * ‖v‖ := by field_simp

end GC.LongTime.Ch12
