import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ChoiceIndependence
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereCollarExtension

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u v

def SmoothConnectedSumDataUniqueness {M : ClosedOrientedManifold.{u} 3}
    {N : ClosedOrientedManifold.{v} 3} (c : OrientedBallChart M)
    (d : OrientedBallChart N) (a : BoundaryAttachment) : Prop :=
  ∀ s s' : SmoothConnectedSum c d a,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
      s'.toConnectedClosedOrientedManifold.toClosedOrientedManifold)

theorem nonempty_orientedDiffeomorph_self_smoothConnectedSum
    {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M) (d : OrientedBallChart N) (a : BoundaryAttachment)
    (s : SmoothConnectedSum c d a) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
      s.toConnectedClosedOrientedManifold.toClosedOrientedManifold) :=
  ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts_and_attachment
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    (c c' : OrientedBallChart M.toClosedOrientedManifold)
    (d d' : OrientedBallChart N.toClosedOrientedManifold)
    {a a' : BoundaryAttachment} (hiso : BoundaryAttachmentIsotopic a a')
    (hsmooth : boundaryAttachmentCollarExtensionOrientedDiffeomorphism M N c' d') :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum M N c' d' a').toConnectedClosedOrientedManifold.toClosedOrientedManifold) := by
  obtain ⟨f⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts c c' d d' a
  obtain ⟨g⟩ := hsmooth a a' (boundaryAttachmentCollarExtension_holds N d' a a' hiso)
  exact ⟨f.trans g⟩

theorem connectedSum_choice_independent_of_smoothConnectedSumDataUniqueness
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    (c c' : OrientedBallChart M.toClosedOrientedManifold)
    (d d' : OrientedBallChart N.toClosedOrientedManifold)
    (a a' : BoundaryAttachment)
    (h : SmoothConnectedSumDataUniqueness c d a)
    (h' : SmoothConnectedSumDataUniqueness c' d' a')
    (hiso : BoundaryAttachmentIsotopic a a')
    (hsmooth : boundaryAttachmentCollarExtensionOrientedDiffeomorphism M N c' d')
    (s : SmoothConnectedSum c d a) (s' : SmoothConnectedSum c' d' a') :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
      s'.toConnectedClosedOrientedManifold.toClosedOrientedManifold) := by
  obtain ⟨f⟩ := h s (smoothConnectedSum M N c d a)
  obtain ⟨g⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts_and_attachment
    c c' d d' hiso hsmooth
  obtain ⟨k⟩ := h' (smoothConnectedSum M N c' d' a') s'
  exact ⟨f.trans (g.trans k)⟩

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_of_refl_collarExtension
    (M : ConnectedClosedOrientedManifold.{u} 3) (N : ConnectedClosedOrientedManifold.{v} 3)
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    BoundaryAttachmentCollarExtension N d a a ∧
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold
        (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold) :=
  ⟨boundaryAttachmentCollarExtension_refl N d a,
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold⟩⟩

end DifferentialGeometry.Topology
