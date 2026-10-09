import DifferentialGeometry.Geometry.Metric.Approximation.RayConeAtInfinity

/-!
# The cone at infinity is complete and proper

The producer (F) `exists_cone_at_infinity_of_fourPointComparison_zero` exports `ProperSpace C`;
`CompleteSpace C` follows (`complete_of_proper`) but is not stated there. The LC21 package and the
MC24 interface of LC75 consume both, and a positive scale threshold. This corollary states them
(review of the wave-3 sheets and of the Tits-cone design: "`exists_tits_cone_package` must give
`CompleteSpace C`, `ProperSpace C`").
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u

/-- (F) with `CompleteSpace C`, `ProperSpace C` and a positive threshold `R₀`: a proper space with
segments and nonnegative four-point comparison has a complete, proper AC82 cone at infinity, fixed
before `ε`, with Kleiner–Lott `ε`-maps from every blow-down `(R⁻¹ Y, q)`, `R ≥ R₀(ε) > 0`. -/
theorem exists_complete_proper_cone_at_infinity_of_fourPointComparison_zero
    {Y : Type u} [mY : MetricSpace Y] [ProperSpace Y]
    (hcomp : fourPointComparison 0 (univ : Set Y))
    (hsegments : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
      f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (q : Y) :
    ∃ (C : Type u) (mC : MetricSpace C) (o : C), Nonempty (@RadialConeData C mC o) ∧
      @CompleteSpace C mC.toUniformSpace ∧ @ProperSpace C mC.toPseudoMetricSpace ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox Y C (mY.rescale R⁻¹ (inv_pos.mpr hR)) mC q o ε) := by
  obtain ⟨C, mC, o, hH, hP, hK⟩ := exists_cone_at_infinity_of_fourPointComparison_zero hcomp hsegments q
  refine ⟨C, mC, o, hH, @complete_of_proper C mC.toPseudoMetricSpace hP, hP, fun ε hε hε1 => ?_⟩
  obtain ⟨R₀, hR₀⟩ := hK ε hε hε1
  exact ⟨max R₀ 1, lt_max_of_lt_right one_pos,
    fun R hR hle => hR₀ R hR ((le_max_left _ _).trans hle)⟩

end GC.MetricGeometry
