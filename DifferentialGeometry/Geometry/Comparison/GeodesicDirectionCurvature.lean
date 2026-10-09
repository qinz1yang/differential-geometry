import DifferentialGeometry.Geometry.Metric.SpaceOfDirections
import DifferentialGeometry.Geometry.Comparison.GermCurvatureIndependence

set_option autoImplicit false

open Set Filter Topology

namespace Metric.GeodesicRepresentative

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] {p : X} [HasAnglesAt p]

theorem tendsto_comparisonAngleNegCurvature_dist_direction
    (σ τ : GeodesicRepresentative p) {κ : ℝ} (hκ : 0 ≤ κ) :
    Tendsto (fun z : ℝ × ℝ => comparisonAngleNegCurvature κ z.1 z.2
      (dist (σ.path z.1) (τ.path z.2)))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (dist σ.direction τ.direction)) := by
  have hdiff := tendsto_comparisonAngleNegCurvature_sub_curvature_zero_of_radial
    hκ σ.length_pos τ.length_pos p σ.path τ.path
    (fun _ ht => σ.dist_base_path ⟨ht.1.le, ht.2⟩)
    (fun _ ht => τ.dist_base_path ⟨ht.1.le, ht.2⟩)
  simpa only [sub_add_cancel, zero_add] using hdiff.add
    (σ.tendsto_comparisonAngle_dist_direction τ)

end Metric.GeodesicRepresentative
