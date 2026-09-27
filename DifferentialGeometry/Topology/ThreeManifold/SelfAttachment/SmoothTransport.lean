import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Smooth
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.CoreOrientationTransport
import DifferentialGeometry.Topology.Manifold.ClosedOrientedPullback

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u v
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
  (c d : OrientedBallChart M.toClosedOrientedManifold) (c' d' : OrientedBallChart N.toClosedOrientedManifold)
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (hcd' : Disjoint (c'.chart '' Metric.closedBall 0 2) (d'.chart '' Metric.closedBall 0 2))
  (a : BoundaryAttachment) (F : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold N.toClosedOrientedManifold)
  (hc : ∀ x ∈ Metric.closedBall (0 : E3) 2, F.val (c.chart x) = c'.chart x)
  (hd : ∀ x ∈ Metric.closedBall (0 : E3) 2, F.val (d.chart x) = d'.chart x)
  (s : SmoothSelfAttachment c' d' hcd' a)

def SmoothSelfAttachment.pullback : SmoothSelfAttachment c d hcd a := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c'.toBallChart d'.toBallChart hcd' a.val.toHomeomorph) := s.charts
  let _ : IsManifold (𝓡 3) ∞ (SelfAttachment.Quotient c'.toBallChart d'.toBallChart hcd' a.val.toHomeomorph) := s.smooth
  let H := SelfAttachment.homeomorphOfChartTransport c.toBallChart d.toBallChart c'.toBallChart d'.toBallChart
    hcd hcd' F.val.toHomeomorph hc hd a.val.toHomeomorph
  let Q := s.toConnectedClosedOrientedManifold.pullback H
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := Q.charts
  let _ : IsManifold (𝓡 3) ∞ (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd a.val.toHomeomorph) := Q.smooth
  let hlocal := SelfAttachment.local_maps_of_chart_transport c.toBallChart d.toBallChart
    c'.toBallChart d'.toBallChart F.val hc hd hcd hcd' a.val.toHomeomorph
    s.core_localDiffeomorph s.band_localDiffeomorph s.lower_localDiffeomorph s.upper_localDiffeomorph
  let hcore := hlocal.1
  let hband := hlocal.2.1
  let hlower := hlocal.2.2.1
  let hupper := hlocal.2.2.2
  refine {
    charts := Q.charts
    smooth := Q.smooth
    orientation := Q.orientation
    core_localDiffeomorph := hcore
    band_localDiffeomorph := hband
    lower_localDiffeomorph := hlower
    upper_localDiffeomorph := hupper
    core_preserves_orientation := ?_ }
  exact SelfAttachment.core_orientation_of_chart_transport c.toBallChart d.toBallChart c'.toBallChart d'.toBallChart
    F.val hc hd hcd hcd' a.val.toHomeomorph M.orientation N.orientation F.property s.orientation
    s.core_localDiffeomorph s.core_preserves_orientation Q.orientation
    (s.toConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph H).property hcore

def SmoothSelfAttachment.pullbackEquiv : ClosedOrientedManifold.OrientedDiffeomorph
    (SmoothSelfAttachment.pullback c d c' d' hcd hcd' a F hc hd s).toConnectedClosedOrientedManifold.toClosedOrientedManifold
    s.toConnectedClosedOrientedManifold.toClosedOrientedManifold := by
  let E := s.toConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph
    (SelfAttachment.homeomorphOfChartTransport c.toBallChart d.toBallChart c'.toBallChart d'.toBallChart
      hcd hcd' F.val.toHomeomorph hc hd a.val.toHomeomorph)
  exact ⟨E.val, E.property⟩

end DifferentialGeometry.Topology
