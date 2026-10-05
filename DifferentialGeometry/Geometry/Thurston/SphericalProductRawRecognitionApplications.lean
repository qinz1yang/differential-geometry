import DifferentialGeometry.Geometry.Thurston.SphericalProductRawRecognition
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CircleFibrationUniverseLift
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawConnectedSumConsumers
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.NormalizeTerminalSplit

/-!
The unit translation quotient feeds a fixed connected sum, and the lens fibration keeps its map.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff

namespace GC.GraphManifold

universe u

theorem nonempty_rawConnectedSum_of_unitCylinderPresentation
    (Q : ConnectedClosedOrientedManifold.{u} 3)
    (pr : GC.Geometry.SphericalProduct.CylinderQuotientPresentation
      (Subgroup.zpowers ((1 : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ]
        EuclideanSpace ℝ (Fin 3)), AffineIsometryEquiv.vaddConst ℝ (1 : ℝ))) Q.Carrier) :
    Nonempty (RawGraphPresentation (NoCuts.carrier
      (connectedSum Q sphereTwoTimesCircleLift.ulift.{0, u}))) := by
  obtain ⟨G⟩ := nonempty_rawGraphPresentation_of_cyclicCylinderPresentation Q 1 1
    (by exact LinearMap.det_id) one_ne_zero pr
  exact rawGraphPresentation_connectedSum Q sphereTwoTimesCircleLift.ulift.{0, u}
    G sphereTwoTimesCircleUliftRawGraphPresentation

private noncomputable abbrev antipodalLensRaw :=
  lensSpaceRawGraphPresentation 2 1 isCoprime_one_right

private abbrev antipodalLensFirst : Fin antipodalLensRaw.components.count :=
  ⟨0, antipodalLensRaw.components.count_pos⟩

theorem antipodalLensFibration_lift_projection
    (x : RawUniverseLift.openLift.{u} antipodalLensRaw.cutCarrier
      (antipodalLensRaw.components.piece antipodalLensFirst)) :
    (RawUniverseLift.fibration antipodalLensRaw.cutCarrier
      (antipodalLensRaw.components.piece antipodalLensFirst)
      (antipodalLensRaw.fibration antipodalLensFirst)).projection x =
        ULift.up ((antipodalLensRaw.fibration antipodalLensFirst).projection
          (RawUniverseLift.openDown antipodalLensRaw.cutCarrier
            (antipodalLensRaw.components.piece antipodalLensFirst) x)) := rfl

end GC.GraphManifold
