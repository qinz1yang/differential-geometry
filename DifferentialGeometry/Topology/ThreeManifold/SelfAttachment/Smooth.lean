import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.LocalMaps
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Connected
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Defs

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
universe u

structure SmoothSelfAttachment {M : ConnectedClosedOrientedManifold.{u} 3}
    (c d : OrientedBallChart M.toClosedOrientedManifold)
    (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
    (a : BoundaryAttachment) where
  [charts : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph)]
  [smooth : IsManifold (𝓡 3) ∞ (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph)]
  orientation : ManifoldOrientation (𝓡 3) (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) 3
  core_localDiffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
    (SelfAttachment.coreInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
  band_localDiffeomorph : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
    (SelfAttachment.bandInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph)
  lower_localDiffeomorph : ∀ z, IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
    (SelfAttachment.lowerCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph) (SelfAttachment.collarZero z)
  upper_localDiffeomorph : ∀ z, IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
    (SelfAttachment.upperCollar c.toBallChart d.toBallChart hcd a.val.toHomeomorph) (SelfAttachment.collarZero z)
  core_preserves_orientation : ∀ x, Orientation.map (Fin 3)
    (core_localDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (M.orientation.orientation x.val) = orientation.orientation
        (SelfAttachment.coreInteriorInclusion c.toBallChart d.toBallChart hcd a.val.toHomeomorph x)

namespace SmoothSelfAttachment

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  {c d : OrientedBallChart M.toClosedOrientedManifold}
  {hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2)}
  {a : BoundaryAttachment}

def toConnectedClosedOrientedManifold (s : SmoothSelfAttachment c d hcd a) : ConnectedClosedOrientedManifold.{u} 3 where
  Carrier := SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph
  topology := inferInstance
  charts := s.charts
  smooth := s.smooth
  hausdorff := inferInstance
  compact := inferInstance
  connected := SelfAttachment.connectedSpace_quotient c d hcd a.val.toHomeomorph
  orientation := s.orientation

end SmoothSelfAttachment
end DifferentialGeometry.Topology
