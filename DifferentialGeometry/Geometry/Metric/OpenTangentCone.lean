import DifferentialGeometry.Geometry.Metric.TangentCone
import DifferentialGeometry.Geometry.Metric.OpenDirections
import DifferentialGeometry.Geometry.Metric.EuclideanConeIsometry

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped NNReal

namespace Metric.TangentCone

variable {X : Type*} [MetricSpace X] {U : Set X}

def openIsometryEquiv (hU : IsOpen U) (p : U) [HasAnglesAt (p : X)] :
    letI : HasAnglesAt p := hasAnglesAt_of_isometry (Subtype.val : U → X) isometry_subtype_coe
    TangentCone p ≃ᵢ TangentCone (p : X) := by
  let : HasAnglesAt p := hasAnglesAt_of_isometry (Subtype.val : U → X) isometry_subtype_coe
  exact EuclideanCone.congr (SpaceOfDirections.openIsometryEquiv hU p)

@[simp] theorem openIsometryEquiv_tip (hU : IsOpen U) (p : U) [HasAnglesAt (p : X)] :
    letI : HasAnglesAt p := hasAnglesAt_of_isometry (Subtype.val : U → X) isometry_subtype_coe
    openIsometryEquiv hU p EuclideanCone.tip = EuclideanCone.tip := by
  rfl

theorem openIsometryEquiv_tangentVector (hU : IsOpen U) (p : U)
    [HasAnglesAt (p : X)] (τ : GeodesicRepresentative p) (r : ℝ≥0) :
    letI : HasAnglesAt p := hasAnglesAt_of_isometry (Subtype.val : U → X) isometry_subtype_coe
    openIsometryEquiv hU p (τ.tangentVector r) =
      (τ.map (Subtype.val : U → X) isometry_subtype_coe).tangentVector r := by
  let : HasAnglesAt p := hasAnglesAt_of_isometry (Subtype.val : U → X) isometry_subtype_coe
  change EuclideanCone.map (SpaceOfDirections.openIsometryEquiv hU p)
    (EuclideanCone.mk r τ.direction) = _
  rw [EuclideanCone.map_mk, SpaceOfDirections.openIsometryEquiv_direction]
  rfl

theorem openIsometryEquiv_dilate (hU : IsOpen U) (p : U) [HasAnglesAt (p : X)] :
    letI : HasAnglesAt p := hasAnglesAt_of_isometry (Subtype.val : U → X) isometry_subtype_coe
    ∀ (c : ℝ≥0) (v : TangentCone p),
      openIsometryEquiv hU p (EuclideanCone.dilate c v) =
        EuclideanCone.dilate c (openIsometryEquiv hU p v) := by
  intro c v
  exact EuclideanCone.map_dilate _ c v

end Metric.TangentCone
