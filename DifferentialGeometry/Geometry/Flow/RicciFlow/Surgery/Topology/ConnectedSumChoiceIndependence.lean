import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ChoiceIndependenceAttachment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphereDiffeomorphismIsotopyConnected

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u v

theorem boundaryAttachmentIsotopic_smaleMunkresSphereIsotopy
    (a a' : BoundaryAttachment) : BoundaryAttachmentIsotopic a a' :=
  boundaryAttachmentIsotopic_of_smaleMunkres
    DifferentialGeometry.Topology.Manifold.smaleMunkresSphereIsotopy_holds a a'

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_of_collarExtension
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    (c c' : OrientedBallChart M.toClosedOrientedManifold)
    (d d' : OrientedBallChart N.toClosedOrientedManifold)
    (a a' : BoundaryAttachment)
    (hsmooth : boundaryAttachmentCollarExtensionOrientedDiffeomorphism M N c' d') :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum M N c' d' a').toConnectedClosedOrientedManifold.toClosedOrientedManifold) :=
  nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts_and_attachment c c' d d'
    (boundaryAttachmentIsotopic_smaleMunkresSphereIsotopy a a') hsmooth

end DifferentialGeometry.Topology
