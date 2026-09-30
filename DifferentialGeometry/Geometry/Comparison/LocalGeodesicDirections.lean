import DifferentialGeometry.Geometry.Metric.SpaceOfDirections
import DifferentialGeometry.Geometry.Comparison.GermCurvatureIndependence

set_option autoImplicit false

open Set Filter Topology Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace Metric

variable {X : Type*} [MetricSpace X] {p : X}

theorem hasAnglesAt_of_local_fourPointComparison {κ : ℝ} (hκ : 0 ≤ κ) {Ω : Set X}
    (hΩ : IsOpen Ω) (hcomp : fourPointComparison κ Ω) (hp : p ∈ Ω) : HasAnglesAt p := by
  refine ⟨fun σ τ => ?_⟩
  have h := tendsto_germComparisonAngle_of_local_fourPointComparison hκ
    σ.length_pos τ.length_pos hΩ hcomp hp
    (fun _ ht => σ.dist_base_path ⟨ht.1.le, ht.2⟩)
    (fun _ ht => τ.dist_base_path ⟨ht.1.le, ht.2⟩)
    (fun _ hs _ ht => σ.dist_path ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩)
    (fun _ hs _ ht => τ.dist_path ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩)
  have hzero := tendsto_curvature_zero_comparisonAngle_of_tendsto hκ σ.length_pos τ.length_pos
    p σ.path τ.path
    (fun _ ht => σ.dist_base_path ⟨ht.1.le, ht.2⟩)
    (fun _ ht => τ.dist_base_path ⟨ht.1.le, ht.2⟩) h
  simpa only [GeodesicRepresentative.angle, germComparisonAngle_eq_of_tendsto hzero] using hzero

theorem GeodesicRepresentative.tendsto_comparisonAngle_dist_direction_of_local_fourPointComparison
    [HasAnglesAt p] {κ : ℝ} (hκ : 0 ≤ κ) {Ω : Set X}
    (hΩ : IsOpen Ω) (hcomp : fourPointComparison κ Ω) (hp : p ∈ Ω)
    (σ τ : GeodesicRepresentative p) :
    Tendsto (fun z : ℝ × ℝ => comparisonAngleNegCurvature κ z.1 z.2
      (dist (σ.path z.1) (τ.path z.2)))
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (dist σ.direction τ.direction)) := by
  have h := tendsto_germComparisonAngle_of_local_fourPointComparison hκ
    σ.length_pos τ.length_pos hΩ hcomp hp
    (fun _ ht => σ.dist_base_path ⟨ht.1.le, ht.2⟩)
    (fun _ ht => τ.dist_base_path ⟨ht.1.le, ht.2⟩)
    (fun _ hs _ ht => σ.dist_path ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩)
    (fun _ hs _ ht => τ.dist_path ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩)
  have heq := germComparisonAngle_eq_curvature_zero_of_tendsto hκ σ.length_pos τ.length_pos
    p σ.path τ.path
    (fun _ ht => σ.dist_base_path ⟨ht.1.le, ht.2⟩)
    (fun _ ht => τ.dist_base_path ⟨ht.1.le, ht.2⟩) h
  rwa [heq, ← GeodesicRepresentative.angle, ← σ.dist_direction τ] at h

end Metric
