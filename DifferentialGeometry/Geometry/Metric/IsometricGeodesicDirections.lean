import DifferentialGeometry.Geometry.Metric.SpaceOfDirections
import DifferentialGeometry.Geometry.Metric.IsometricGeodesicRepresentative

set_option autoImplicit false

noncomputable section

open UniformSpace (Completion)

namespace Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {p : X}
variable (f : X → Y) (hf : Isometry f) [HasAnglesAt p] [HasAnglesAt (f p)]

def GeodesicDirections.map : GeodesicDirections p → GeodesicDirections (f p) :=
  SeparationQuotient.map (fun σ : GeodesicRepresentative p => σ.map f hf)

theorem GeodesicDirections.map_geodesicDirection (σ : GeodesicRepresentative p) :
    map f hf σ.geodesicDirection = (σ.map f hf).geodesicDirection :=
  SeparationQuotient.map_mk (GeodesicRepresentative.isometry_map f hf).uniformContinuous σ

theorem GeodesicDirections.isometry_map :
    Isometry (map f hf : GeodesicDirections p → GeodesicDirections (f p)) := by
  apply Isometry.of_dist_eq
  intro a b
  obtain ⟨σ, rfl⟩ := SeparationQuotient.surjective_mk a
  obtain ⟨τ, rfl⟩ := SeparationQuotient.surjective_mk b
  change dist (map f hf σ.geodesicDirection) (map f hf τ.geodesicDirection) =
    dist σ.geodesicDirection τ.geodesicDirection
  rw [map_geodesicDirection, map_geodesicDirection,
    GeodesicRepresentative.dist_geodesicDirection,
    GeodesicRepresentative.dist_geodesicDirection,
    GeodesicRepresentative.angle_map]

def SpaceOfDirections.map : SpaceOfDirections p → SpaceOfDirections (f p) :=
  Completion.map (GeodesicDirections.map f hf)

theorem SpaceOfDirections.map_toDirection (v : GeodesicDirections p) :
    map f hf v.toDirection = (GeodesicDirections.map f hf v).toDirection :=
  Completion.map_coe (GeodesicDirections.isometry_map f hf).uniformContinuous v

theorem SpaceOfDirections.isometry_map :
    Isometry (map f hf : SpaceOfDirections p → SpaceOfDirections (f p)) :=
  (GeodesicDirections.isometry_map f hf).completion_map

theorem SpaceOfDirections.map_direction (σ : GeodesicRepresentative p) :
    map f hf σ.direction = (σ.map f hf).direction := by
  change map f hf σ.geodesicDirection.toDirection =
    (σ.map f hf).geodesicDirection.toDirection
  rw [map_toDirection, GeodesicDirections.map_geodesicDirection]

end Metric
