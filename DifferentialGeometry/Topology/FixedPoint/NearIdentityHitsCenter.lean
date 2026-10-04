import DifferentialGeometry.Topology.FixedPoint.Brouwer

/-!
# A continuous map within `r` of the identity on a closed ball hits its center (CGP07)

Blueprint 207B, CGP07 (`thm:fibration-marked-base-one-sheet`, B:4176–4247), existence step: for
`H(u) = u_i(f_j(s_i(u)))/R_i` on the closed ball of radius `1/100` about `a`, cumulative value control
gives `|H(u) - u| < 1/100`; the continuous map `u ↦ a + u - H(u)` carries that closed ball into itself,
and Brouwer's fixed-point theorem gives `H(u) = a`. This is the only foundational input; it is the
tree's `exists_fixedPoint_closedBall_of_continuous` (finite-dimensional inner product spaces), so the
one- and two-dimensional bases are covered by the same statement.
-/

set_option autoImplicit false
open Metric

namespace DifferentialGeometry.Topology.FixedPoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- CGP07: a map that is continuous on `closedBall a r` and moves every point by at most `r`
takes the value `a` somewhere in that ball. -/
theorem exists_eq_center_of_norm_sub_le (H : E → E) {a : E} {r : ℝ} (hr : 0 ≤ r)
    (hc : ContinuousOn H (closedBall a r)) (hnear : ∀ u ∈ closedBall a r, ‖H u - u‖ ≤ r) :
    ∃ u ∈ closedBall a r, H u = a := by
  rcases hr.lt_or_eq with hr0 | hr0
  · let c : E → E := fun w => a + r • w
    have hcmaps : Set.MapsTo c (closedBall 0 1) (closedBall a r) := by
      intro w hw
      rw [mem_closedBall, dist_zero_right] at hw
      rw [mem_closedBall, dist_eq_norm]
      simp only [c, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
      nlinarith [norm_nonneg w]
    let K : E → E := fun w => r⁻¹ • (c w - H (c w))
    have hcc : Continuous c := continuous_const.add (continuous_const.smul continuous_id)
    have hK : ContinuousOn K (closedBall 0 1) :=
      continuousOn_const.smul (hcc.continuousOn.sub (hc.comp hcc.continuousOn hcmaps))
    have hKmaps : ∀ w ∈ closedBall (0 : E) 1, K w ∈ closedBall (0 : E) 1 := by
      intro w hw
      rw [mem_closedBall, dist_zero_right]
      have h := hnear (c w) (hcmaps hw)
      simp only [K, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr0]
      rw [norm_sub_rev] at h
      calc r⁻¹ * ‖c w - H (c w)‖ ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left h (by positivity)
        _ = 1 := inv_mul_cancel₀ hr0.ne'
    let f : closedBall (0 : E) 1 → closedBall (0 : E) 1 := fun w => ⟨K w, hKmaps w w.property⟩
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      exact (continuousOn_iff_continuous_domRestrict.mp hK)
    obtain ⟨w, hw⟩ := exists_fixedPoint_closedBall_of_continuous f hf
    have hw' : K w = w := congrArg Subtype.val hw
    refine ⟨c w, hcmaps w.property, ?_⟩
    have h1 : c w - H (c w) = r • (w : E) := by
      have h := congrArg (fun v => r • v) hw'
      simpa only [K, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul] using h
    have h2 : c w - H (c w) = c w - a := by
      rw [h1]
      simp [c]
    exact sub_right_injective h2
  · subst hr0
    refine ⟨a, mem_closedBall_self le_rfl, ?_⟩
    have h := hnear a (mem_closedBall_self le_rfl)
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

end DifferentialGeometry.Topology.FixedPoint
