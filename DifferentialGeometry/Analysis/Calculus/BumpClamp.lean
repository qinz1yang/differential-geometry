import Mathlib.Analysis.Calculus.BumpFunction.Basic

set_option autoImplicit false

/-!
# Radial clamps from smooth bump functions

A bump centered at the origin gives a globally smooth radial clamp.  It is the
identity on the bump's inner closed ball and sends the whole space into its
outer open ball.
-/

namespace ContDiffBump

open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [HasContDiffBump E]

/-- The radial clamp associated to a smooth bump centered at the origin. -/
noncomputable def radial (b : ContDiffBump (0 : E)) (x : E) : E :=
  b x • x

/-- A radial bump clamp is smooth. -/
theorem radial_contDiff (b : ContDiffBump (0 : E)) :
    ContDiff Real (∞ : WithTop ℕ∞) b.radial := by
  exact b.contDiff.smul contDiff_id

/-- A radial bump clamp maps the whole space into the bump's outer open ball. -/
theorem radial_mapsTo (b : ContDiffBump (0 : E)) :
    MapsTo b.radial Set.univ (Metric.ball 0 b.rOut) := by
  intro x _hx
  by_cases hbx : b x = 0
  · rw [radial, hbx, zero_smul, Metric.mem_ball, dist_self]
    exact b.rOut_pos
  · have hxout : x ∈ Metric.ball (0 : E) b.rOut := by
      rw [← b.support_eq]
      exact hbx
    rw [Metric.mem_ball, dist_zero_right] at hxout ⊢
    rw [radial, norm_smul, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
    calc
      b x * ‖x‖ ≤ 1 * ‖x‖ :=
        mul_le_mul_of_nonneg_right b.le_one (norm_nonneg x)
      _ = ‖x‖ := one_mul _
      _ < b.rOut := hxout

/-- A radial bump clamp is the identity on the bump's inner closed ball. -/
theorem radial_eq_self (b : ContDiffBump (0 : E)) {x : E}
    (hx : x ∈ Metric.closedBall 0 b.rIn) : b.radial x = x := by
  rw [radial, b.one_of_mem_closedBall hx, one_smul]

end ContDiffBump
