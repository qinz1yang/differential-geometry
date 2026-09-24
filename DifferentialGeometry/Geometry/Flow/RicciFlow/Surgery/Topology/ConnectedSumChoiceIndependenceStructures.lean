import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ConnectedSumChoiceIndependence
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Construction

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u v

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_of_smoothConnectedSumDataUniqueness_and_collarExtension
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    (c c' : OrientedBallChart M.toClosedOrientedManifold)
    (d d' : OrientedBallChart N.toClosedOrientedManifold)
    (a a' : BoundaryAttachment)
    (h : SmoothConnectedSumDataUniqueness c d a)
    (h' : SmoothConnectedSumDataUniqueness c' d' a')
    (hsmooth : boundaryAttachmentCollarExtensionOrientedDiffeomorphism M N c' d')
    (s : SmoothConnectedSum c d a) (s' : SmoothConnectedSum c' d' a') :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
      s'.toConnectedClosedOrientedManifold.toClosedOrientedManifold) := by
  obtain ⟨f⟩ := h s (smoothConnectedSum M N c d a)
  obtain ⟨g⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_collarExtension
    c c' d d' a a' hsmooth
  obtain ⟨k⟩ := h' (smoothConnectedSum M N c' d' a') s'
  exact ⟨f.trans (g.trans k)⟩

theorem smoothConnectedSumDataUniqueness_of_connectedSum_choice_independent
    (h : ∀ {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}
      (c c' : OrientedBallChart M) (d d' : OrientedBallChart N)
      (a a' : BoundaryAttachment)
      (s : SmoothConnectedSum c d a) (s' : SmoothConnectedSum c' d' a'),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
        s'.toConnectedClosedOrientedManifold.toClosedOrientedManifold))
    {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M) (d : OrientedBallChart N) (a : BoundaryAttachment) :
    SmoothConnectedSumDataUniqueness c d a :=
  fun s s' => h c c d d a a s s'

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_of_connectedSum_choice_independent
    (h : ∀ {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}
      (c c' : OrientedBallChart M) (d d' : OrientedBallChart N)
      (a a' : BoundaryAttachment)
      (s : SmoothConnectedSum c d a) (s' : SmoothConnectedSum c' d' a'),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
        s'.toConnectedClosedOrientedManifold.toClosedOrientedManifold))
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    (c c' : OrientedBallChart M.toClosedOrientedManifold)
    (d d' : OrientedBallChart N.toClosedOrientedManifold) (a a' : BoundaryAttachment) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum M N c' d' a'
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold) :=
  h c c' d d' a a' (smoothConnectedSum M N c d a) (smoothConnectedSum M N c' d' a')

end DifferentialGeometry.Topology
