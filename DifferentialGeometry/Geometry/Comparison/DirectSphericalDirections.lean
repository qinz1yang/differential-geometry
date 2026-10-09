import DifferentialGeometry.Geometry.Comparison.TangentComparison
import DifferentialGeometry.Geometry.Comparison.ConeSphericalComparison

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem spherical_direction_comparison_of_local_fourPointComparison
    {X : Type*} [MetricSpace X] {q : X} {κ : ℝ} (hκ : 0 ≤ κ) {Ω : Set X}
    (hΩ : IsOpen Ω) (hcomp : fourPointComparison κ Ω) (hq : q ∈ Ω) :
    letI : HasAnglesAt q := hasAnglesAt_of_local_fourPointComparison hκ hΩ hcomp hq
    ∀ ξ : SpaceOfDirections q,
      fourPointSphericalComparison (ball ξ (Real.pi / 4)) := by
  let : HasAnglesAt q := hasAnglesAt_of_local_fourPointComparison hκ hΩ hcomp hq
  have hcone := tangentCone_fourPointComparison_zero_of_local_fourPointComparison hκ hΩ hcomp hq
  exact fun ξ => fourPointSphericalComparison_ball_of_cone_comparison hcone ξ

end DifferentialGeometry.Geometry.Comparison.Toponogov
