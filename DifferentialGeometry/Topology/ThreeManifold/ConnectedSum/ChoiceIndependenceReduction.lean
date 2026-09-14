import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ChoiceIndependenceAttachment
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereCollarExtension

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u v

def ConnectedSumAttachmentIndependence (M : ConnectedClosedOrientedManifold.{u} 3)
    (N : ConnectedClosedOrientedManifold.{v} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) : Prop :=
  ∀ a a' : BoundaryAttachment,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum M N c d a'
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold)

theorem collarExtensionOrientedDiffeomorphism_of_connectedSumAttachmentIndependence
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    {c : OrientedBallChart M.toClosedOrientedManifold}
    {d : OrientedBallChart N.toClosedOrientedManifold}
    (h : ConnectedSumAttachmentIndependence M N c d) :
    boundaryAttachmentCollarExtensionOrientedDiffeomorphism M N c d :=
  fun a a' _ => h a a'

theorem connectedSumAttachmentIndependence_of_collarExtensionOrientedDiffeomorphism
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    {c : OrientedBallChart M.toClosedOrientedManifold}
    {d : OrientedBallChart N.toClosedOrientedManifold}
    (hsm : SmaleMunkresSphereIsotopy)
    (h : boundaryAttachmentCollarExtensionOrientedDiffeomorphism M N c d) :
    ConnectedSumAttachmentIndependence M N c d :=
  fun a a' => h a a' (boundaryAttachmentCollarExtension_holds N d a a'
    (boundaryAttachmentIsotopic_of_smaleMunkres hsm a a'))

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_of_attachmentIndependence
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold)
    (h : ConnectedSumAttachmentIndependence M N c d)
    (c' : OrientedBallChart M.toClosedOrientedManifold)
    (d' : OrientedBallChart N.toClosedOrientedManifold)
    (a a' : BoundaryAttachment) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum M N c' d' a'
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold) := by
  obtain ⟨f⟩ := h a a'
  obtain ⟨g⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_leftChart c c' d a'
  obtain ⟨k⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_rightChart c' d d' a'
  exact ⟨f.trans (g.trans k)⟩

theorem connectedSum_choice_independent_of_dataUniqueness_and_attachmentIndependence
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    (c c' : OrientedBallChart M.toClosedOrientedManifold)
    (d d' : OrientedBallChart N.toClosedOrientedManifold) (a a' : BoundaryAttachment)
    (hdata : SmoothConnectedSumDataUniqueness c d a)
    (hdata' : SmoothConnectedSumDataUniqueness c' d' a')
    (hatt : ConnectedSumAttachmentIndependence M N c d)
    (s : SmoothConnectedSum c d a) (s' : SmoothConnectedSum c' d' a') :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
      s'.toConnectedClosedOrientedManifold.toClosedOrientedManifold) := by
  obtain ⟨f⟩ := hdata s (smoothConnectedSum M N c d a)
  obtain ⟨g⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_attachmentIndependence
    c d hatt c' d' a a'
  obtain ⟨k⟩ := hdata' (smoothConnectedSum M N c' d' a') s'
  exact ⟨f.trans (g.trans k)⟩

end DifferentialGeometry.Topology
