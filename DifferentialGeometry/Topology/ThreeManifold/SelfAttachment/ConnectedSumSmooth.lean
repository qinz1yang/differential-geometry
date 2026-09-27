import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.ConnectedSumOrientation
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Pullback

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u v
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

variable {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
  (m : OrientedBallChart M.toClosedOrientedManifold) (e c d : OrientedBallChart N.toClosedOrientedManifold)
  (a b : BoundaryAttachment)
  (hec : Disjoint (e.chart '' Metric.closedBall 0 2) (c.chart '' Metric.closedBall 0 2))
  (hed : Disjoint (e.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (c' d' : OrientedBallChart (smoothConnectedSum M N m e a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
  (hc' : ∀ x ∈ Metric.closedBall (0 : E3) 2, ∃ hx,
    c'.chart x = ConnectedSumQuotient.inr m.toBallChart e.toBallChart a.val.toHomeomorph ⟨c.chart x, hx⟩)
  (hd' : ∀ x ∈ Metric.closedBall (0 : E3) 2, ∃ hx,
    d'.chart x = ConnectedSumQuotient.inr m.toBallChart e.toBallChart a.val.toHomeomorph ⟨d.chart x, hx⟩)
  (hcd' : Disjoint (c'.chart '' Metric.closedBall 0 2) (d'.chart '' Metric.closedBall 0 2))
  (s : SmoothSelfAttachment c d hcd b)
  (e' : OrientedBallChart s.toConnectedClosedOrientedManifold.toClosedOrientedManifold)
  (he' : ∀ x ∈ Metric.closedBall (0 : E3) 2,
    ∃ hx : e.chart x ∈ (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ,
      e'.chart x = SelfAttachment.coreInclusion c.toBallChart d.toBallChart hcd b.val.toHomeomorph ⟨e.chart x, hx⟩)



def smoothSelfAttachmentConnectedSum : SmoothSelfAttachment c' d' hcd' b := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
  let t := smoothConnectedSum M s.toConnectedClosedOrientedManifold m e' a
  let T := t.toConnectedClosedOrientedManifold
  let _ := t.charts
  let _ := t.smooth
  let H : SelfAttachment.Quotient c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph ≃ₜ T.Carrier :=
    selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he'
  let Q := T.pullback H
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph) := Q.charts
  let _ : IsManifold (𝓡 3) ∞ (SelfAttachment.Quotient c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph) := Q.smooth
  let G := T.pullbackOrientedDiffeomorph H
  have hcore : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (SelfAttachment.coreInteriorInclusion c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph) :=
    isLocalDiffeomorph_pullback_of_comp H _
      (selfAttachmentConnectedSumHomeomorph_core_localDiffeomorph m e c d a b hec hed hcd c' d' hc' hd' hcd' s e' he')
  have hband : IsLocalDiffeomorph IC (𝓡 3) ∞
      (SelfAttachment.bandInteriorInclusion c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph) :=
    isLocalDiffeomorph_pullback_of_comp H _
      (selfAttachmentConnectedSumHomeomorph_band_localDiffeomorph m e c d a b hec hed hcd c' d' hc' hd' hcd' s e' he')
  have hlower : ∀ z, IsLocalDiffeomorphAt IC (𝓡 3) ∞
      (SelfAttachment.lowerCollar c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph) (SelfAttachment.collarZero z) :=
    fun z => isLocalDiffeomorphAt_pullback_of_comp H _ _
      (selfAttachmentConnectedSumHomeomorph_lower_localDiffeomorph m e c d a b hec hed hcd c' d' hc' hd' hcd' s e' he' z)
  have hupper : ∀ z, IsLocalDiffeomorphAt IC (𝓡 3) ∞
      (SelfAttachment.upperCollar c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph) (SelfAttachment.collarZero z) :=
    fun z => isLocalDiffeomorphAt_pullback_of_comp H _ _
      (selfAttachmentConnectedSumHomeomorph_upper_localDiffeomorph m e c d a b hec hed hcd c' d' hc' hd' hcd' s e' he' z)
  refine {
    charts := Q.charts
    smooth := Q.smooth
    orientation := Q.orientation
    core_localDiffeomorph := hcore
    band_localDiffeomorph := hband
    lower_localDiffeomorph := hlower
    upper_localDiffeomorph := hupper
    core_preserves_orientation := ?_ }
  let S := smoothConnectedSum M N m e a
  let _ : ChartedSpace E3 (ConnectedSumQuotient m.toBallChart e.toBallChart a.val.toHomeomorph) := S.charts
  let _ : IsManifold (𝓡 3) ∞ (ConnectedSumQuotient m.toBallChart e.toBallChart a.val.toHomeomorph) := S.smooth
  have hcomp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (H ∘ SelfAttachment.coreInteriorInclusion c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph) :=
    selfAttachmentConnectedSumHomeomorph_core_localDiffeomorph m e c d a b hec hed hcd c' d' hc' hd' hcd' s e' he'
  exact Manifold.local_orientation_of_comp
    (SelfAttachment.coreInteriorInclusion c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph) G.val
    (H ∘ SelfAttachment.coreInteriorInclusion c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph)
    hcore G.val.isLocalDiffeomorph hcomp rfl
    (S.orientation.restrictOpen (SelfAttachment.coreInterior c'.toBallChart d'.toBallChart))
    Q.orientation T.orientation G.property
    (selfAttachmentConnectedSumHomeomorph_core_orientation m e c d a b hec hed hcd c' d' hc' hd' hcd' s e' he')


def smoothSelfAttachmentConnectedSumEquiv : ClosedOrientedManifold.OrientedDiffeomorph
    (smoothSelfAttachmentConnectedSum m e c d a b hec hed hcd c' d' hc' hd' hcd' s e' he').toConnectedClosedOrientedManifold.toClosedOrientedManifold
    (smoothConnectedSum M s.toConnectedClosedOrientedManifold m e' a).toConnectedClosedOrientedManifold.toClosedOrientedManifold := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
  let T := (smoothConnectedSum M s.toConnectedClosedOrientedManifold m e' a).toConnectedClosedOrientedManifold
  let H : SelfAttachment.Quotient c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph ≃ₜ T.Carrier :=
    selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he'
  let E := T.pullbackOrientedDiffeomorph H
  exact ⟨E.val, E.property⟩

end DifferentialGeometry.Topology
