import DifferentialGeometry.Geometry.Metric.IsometricGeodesicDirections
import DifferentialGeometry.Geometry.Metric.OpenGeodesicRepresentative

set_option autoImplicit false

noncomputable section

open Set Metric

namespace Metric.SpaceOfDirections

variable {X : Type*} [MetricSpace X] {U : Set X}

theorem surjective_map_subtype_val (hU : IsOpen U) (p : U) [HasAnglesAt (p : X)] :
    letI : HasAnglesAt p := hasAnglesAt_of_isometry (Subtype.val : U → X) isometry_subtype_coe
    Function.Surjective (map (Subtype.val : U → X) isometry_subtype_coe :
      SpaceOfDirections p → SpaceOfDirections (p : X)) := by
  let : HasAnglesAt p := hasAnglesAt_of_isometry (Subtype.val : U → X) isometry_subtype_coe
  let f : SpaceOfDirections p → SpaceOfDirections (p : X) :=
    map (Subtype.val : U → X) isometry_subtype_coe
  have hf : Isometry f := isometry_map _ _
  have hclosed : IsClosed (range f) := hf.isClosedEmbedding.isClosed_range
  have hrep : range (GeodesicRepresentative.direction :
      GeodesicRepresentative (p : X) → SpaceOfDirections (p : X)) ⊆ range f := by
    rintro _ ⟨σ, rfl⟩
    obtain ⟨r, hr, hle, τ, hτ⟩ := σ.exists_lift_shorten hU p
    refine ⟨τ.direction, ?_⟩
    change map (Subtype.val : U → X) isometry_subtype_coe τ.direction = σ.direction
    rw [map_direction, hτ, GeodesicRepresentative.direction_shorten]
  have hd : DenseRange (GeodesicRepresentative.direction :
      GeodesicRepresentative (p : X) → SpaceOfDirections (p : X)) :=
    Metric.denseRange_iff.mpr fun v _ hε => v.exists_representative_dist_lt hε
  intro v
  exact hclosed.closure_subset_iff.mpr hrep (hd v)

def openIsometryEquiv (hU : IsOpen U) (p : U) [HasAnglesAt (p : X)] :
    letI : HasAnglesAt p := hasAnglesAt_of_isometry (Subtype.val : U → X) isometry_subtype_coe
    SpaceOfDirections p ≃ᵢ SpaceOfDirections (p : X) := by
  let : HasAnglesAt p := hasAnglesAt_of_isometry (Subtype.val : U → X) isometry_subtype_coe
  exact
    { toEquiv := Equiv.ofBijective (map (Subtype.val : U → X) isometry_subtype_coe)
        ⟨(isometry_map _ _).injective, surjective_map_subtype_val hU p⟩
      isometry_toFun := isometry_map _ _ }

theorem openIsometryEquiv_apply (hU : IsOpen U) (p : U) [HasAnglesAt (p : X)] :
    letI : HasAnglesAt p := hasAnglesAt_of_isometry (Subtype.val : U → X) isometry_subtype_coe
    ∀ v : SpaceOfDirections p,
      openIsometryEquiv hU p v = map (Subtype.val : U → X) isometry_subtype_coe v := by
  intro
  rfl

theorem openIsometryEquiv_direction (hU : IsOpen U) (p : U) [HasAnglesAt (p : X)]
    (τ : GeodesicRepresentative p) :
    letI : HasAnglesAt p := hasAnglesAt_of_isometry (Subtype.val : U → X) isometry_subtype_coe
    openIsometryEquiv hU p τ.direction =
      (τ.map (Subtype.val : U → X) isometry_subtype_coe).direction := by
  let : HasAnglesAt p := hasAnglesAt_of_isometry (Subtype.val : U → X) isometry_subtype_coe
  exact map_direction _ _ τ

end Metric.SpaceOfDirections
