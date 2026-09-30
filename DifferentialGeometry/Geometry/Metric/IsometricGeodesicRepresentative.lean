import DifferentialGeometry.Geometry.Comparison.GeodesicAngle

set_option autoImplicit false

open Set Filter Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {p : X}

def GeodesicRepresentative.map (σ : GeodesicRepresentative p)
    (f : X → Y) (hf : Isometry f) : GeodesicRepresentative (f p) where
  length := σ.length
  length_pos := σ.length_pos
  curve := f ∘ σ.curve
  isometry := hf.comp σ.isometry
  start := congrArg f σ.start

theorem GeodesicRepresentative.map_path (σ : GeodesicRepresentative p)
    (f : X → Y) (hf : Isometry f) (t : ℝ) : (σ.map f hf).path t = f (σ.path t) := rfl

theorem GeodesicRepresentative.angle_map (σ τ : GeodesicRepresentative p)
    (f : X → Y) (hf : Isometry f) : (σ.map f hf).angle (τ.map f hf) = σ.angle τ := by
  unfold GeodesicRepresentative.angle germComparisonAngle
  simp only [GeodesicRepresentative.map_path, hf.dist_eq]

theorem hasAnglesAt_of_isometry (f : X → Y) (hf : Isometry f)
    [HasAnglesAt (f p)] : HasAnglesAt p := by
  refine ⟨fun σ τ => ?_⟩
  simpa only [GeodesicRepresentative.map_path, hf.dist_eq, GeodesicRepresentative.angle_map]
    using HasAnglesAt.tendsto_angle (σ.map f hf) (τ.map f hf)

theorem GeodesicRepresentative.isometry_map (f : X → Y) (hf : Isometry f)
    [HasAnglesAt p] [HasAnglesAt (f p)] :
    Isometry (fun σ : GeodesicRepresentative p => σ.map f hf) := by
  apply Isometry.of_dist_eq
  intro σ τ
  exact σ.angle_map τ f hf

end Metric
