import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BoundaryAttachmentIsotopy
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.ChoiceIndependence
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SphereCollarExtension

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u v

theorem smaleMunkresSphereIsotopy_of_forall_boundaryAttachmentIsotopic
    (h : ∀ a a' : BoundaryAttachment, BoundaryAttachmentIsotopic a a') :
    SmaleMunkresSphereIsotopy := by
  intro f hf
  let a' : BoundaryAttachment :=
    ⟨f.trans boundaryAttachment.1,
      Diffeomorph.preservesOrientation_trans hf boundaryAttachment.2⟩
  have hdisc : boundaryAttachmentDiscrepancy boundaryAttachment a' = f := by
    refine Diffeomorph.ext fun x => ?_
    rw [boundaryAttachmentDiscrepancy_apply]
    change boundaryAttachment.1.symm ((f.trans boundaryAttachment.1) x) = f x
    rw [Diffeomorph.coe_trans, Function.comp_apply, Diffeomorph.symm_apply_apply]
  rw [← hdisc]
  exact (boundaryAttachmentIsotopic_iff_sphereDiffeomorphIsotopicToIdentity_discrepancy
    boundaryAttachment a').mp (h boundaryAttachment a')

theorem smaleMunkresSphereIsotopy_iff_forall_boundaryAttachmentIsotopic :
    SmaleMunkresSphereIsotopy ↔
      ∀ a a' : BoundaryAttachment, BoundaryAttachmentIsotopic a a' :=
  ⟨fun h a a' => boundaryAttachmentIsotopic_of_smaleMunkres h a a',
    smaleMunkresSphereIsotopy_of_forall_boundaryAttachmentIsotopic⟩

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_of_choices
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    (c c' : OrientedBallChart M.toClosedOrientedManifold)
    (d d' : OrientedBallChart N.toClosedOrientedManifold) (a a' : BoundaryAttachment)
    (hsm : SmaleMunkresSphereIsotopy)
    (hsc : boundaryAttachmentCollarExtensionOrientedDiffeomorphism M N c d) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum M N c' d' a'
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold) := by
  obtain ⟨f⟩ :=
    nonempty_orientedDiffeomorph_smoothConnectedSum_of_boundaryAttachmentCollarExtension
      c d a a' (boundaryAttachmentIsotopic_of_smaleMunkres hsm a a') hsc
  obtain ⟨g⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_charts c c' d d a'
  obtain ⟨h⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_rightChart c' d d' a'
  exact ⟨f.trans (g.trans h)⟩

def SmoothConnectedSumRealizationsDiffeomorphic
    {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M) (d : OrientedBallChart N) (a : BoundaryAttachment) : Prop :=
  ∀ s s' : SmoothConnectedSum c d a,
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
      s'.toConnectedClosedOrientedManifold.toClosedOrientedManifold)

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_refl
    {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M) (d : OrientedBallChart N) (a : BoundaryAttachment)
    (s : SmoothConnectedSum c d a) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
      s.toConnectedClosedOrientedManifold.toClosedOrientedManifold) :=
  ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_of_realizationsDiffeomorphic
    {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}
    [hM : ConnectedSpace M.Carrier] [hN : ConnectedSpace N.Carrier]
    (c c' : OrientedBallChart M) (d d' : OrientedBallChart N) (a a' : BoundaryAttachment)
    (s : SmoothConnectedSum c d a) (s' : SmoothConnectedSum c' d' a')
    (hs : SmoothConnectedSumRealizationsDiffeomorphic c d a)
    (hs' : SmoothConnectedSumRealizationsDiffeomorphic c' d' a')
    (hsm : SmaleMunkresSphereIsotopy)
    (hsc : boundaryAttachmentCollarExtensionOrientedDiffeomorphism
      { M with connected := hM } { N with connected := hN } c d) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      s.toConnectedClosedOrientedManifold.toClosedOrientedManifold
      s'.toConnectedClosedOrientedManifold.toClosedOrientedManifold) := by
  obtain ⟨f⟩ := hs s (smoothConnectedSum { M with connected := hM }
    { N with connected := hN } c d a)
  obtain ⟨g⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_choices
    (M := { M with connected := hM }) (N := { N with connected := hN }) c c' d d' a a' hsm hsc
  obtain ⟨h⟩ := hs' (smoothConnectedSum { M with connected := hM }
    { N with connected := hN } c' d' a') s'
  exact ⟨f.trans (g.trans h)⟩

end DifferentialGeometry.Topology
