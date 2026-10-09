import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedTransport
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ChoiceIndependence
import DifferentialGeometry.Topology.Manifold.OrientedBallChartMap

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Topology

universe u v u' v'

theorem nonempty_orientedDiffeomorph_connectedSum_of_orientedDiffeomorph
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    {M' : ConnectedClosedOrientedManifold.{u'} 3} {N' : ConnectedClosedOrientedManifold.{v'} 3}
    (F : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
        M'.toClosedOrientedManifold)
    (G : ClosedOrientedManifold.OrientedDiffeomorph N.toClosedOrientedManifold
        N'.toClosedOrientedManifold) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (connectedSum M N).toClosedOrientedManifold (connectedSum M'
          N').toClosedOrientedManifold) := by
  let c := orientedBallChart M
  let d := orientedBallChart N
  obtain ⟨H⟩ := csTransport_diffeomorph_preservesOrientation c (c.map F) d (d.map G)
    boundaryAttachment F.val G.val (fun _ _ => rfl) (fun _ _ => rfl) F.property
  obtain ⟨K⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts
    (c.map F) (orientedBallChart M') (d.map G) (orientedBallChart N') boundaryAttachment
  exact ⟨H.trans K⟩

end DifferentialGeometry.Topology
