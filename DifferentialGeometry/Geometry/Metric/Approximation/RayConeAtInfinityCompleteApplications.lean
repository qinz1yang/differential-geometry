import DifferentialGeometry.Geometry.Metric.Approximation.RayConeAtInfinityComplete
import DifferentialGeometry.Geometry.Metric.Approximation.RayConeAtInfinityApplications

/-!
# Consumer: the complete proper cone at infinity of a Euclidean space

`exists_complete_proper_cone_at_infinity_of_innerProductSpace`: every finite-dimensional real inner
product space has a complete, proper AC82 cone at infinity with Kleiner–Lott maps from all
blow-downs above a positive threshold.
-/

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry

open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u

/-- The complete-and-proper form of (F) for a finite-dimensional real inner product space. -/
theorem exists_complete_proper_cone_at_infinity_of_innerProductSpace {V : Type u}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] (q : V) :
    ∃ (C : Type u) (mC : MetricSpace C) (o : C), Nonempty (@RadialConeData C mC o) ∧
      @CompleteSpace C mC.toUniformSpace ∧ @ProperSpace C mC.toPseudoMetricSpace ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox V C ((inferInstance : MetricSpace V).rescale R⁻¹
          (inv_pos.mpr hR)) mC q o ε) :=
  exists_complete_proper_cone_at_infinity_of_fourPointComparison_zero
    fourPointComparison_zero_of_innerProductSpace exists_affine_segment q

end GC.MetricGeometry
