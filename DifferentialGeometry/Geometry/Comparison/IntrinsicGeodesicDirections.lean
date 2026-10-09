import DifferentialGeometry.Geometry.Comparison.IntrinsicLocalComparison
import DifferentialGeometry.Geometry.Comparison.LocalGeodesicDirections

set_option autoImplicit false

open Set Metric Topology

namespace Metric

open DifferentialGeometry.Geometry.Comparison.Toponogov

theorem hasAnglesAt_of_intrinsic_ball_local_comparison
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (p : X) {L κ : ℝ} (hL : 0 < L) (hκ : 0 ≤ κ)
    (hlocal : ∀ z : ball p L, ∃ Ω : Set (ball p L),
      @IsOpen (ball p L)
        (intrinsicBallMetricSpace hcurves p hL).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison (ball p L)
        (intrinsicBallMetricSpace hcurves p hL) κ Ω ∧ z ∈ Ω)
    {z : X} (hz : z ∈ ball p L) : HasAnglesAt z := by
  obtain ⟨Ω, hΩ, hc, hzΩ⟩ :=
    (exists_local_fourPointComparison_intrinsicBall_iff hcurves p hL ⟨z, hz⟩).mp
      (hlocal ⟨z, hz⟩)
  exact hasAnglesAt_of_local_fourPointComparison hκ hΩ hc hzΩ

end Metric
