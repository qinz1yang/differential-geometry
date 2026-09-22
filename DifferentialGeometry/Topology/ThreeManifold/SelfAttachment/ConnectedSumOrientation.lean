import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.ConnectedSumLocalMaps
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OrientationComposition
import DifferentialGeometry.Topology.Manifold.ClosedOrientedPullback

set_option autoImplicit false
noncomputable section
open Set Function Filter
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


local instance sourceCharts : ChartedSpace E3 (ConnectedSumQuotient m.toBallChart e.toBallChart a.val.toHomeomorph) :=
  (smoothConnectedSum M N m e a).charts

local instance selfAttachmentSourceSmooth : IsManifold (𝓡 3) ∞ (ConnectedSumQuotient m.toBallChart e.toBallChart a.val.toHomeomorph) :=
  (smoothConnectedSum M N m e a).smooth

private def leftCoreMap (x : m.interior) : SelfAttachment.coreInterior c'.toBallChart d'.toBallChart :=
  ⟨ConnectedSumQuotient.interiorLeft m.toBallChart e.toBallChart a.val x, by
    rintro (hc | hd)
    · exact ConnectedSumQuotient.inl_not_mem_chart_closedBall m e c a c' hc' hec _ hc
    · exact ConnectedSumQuotient.inl_not_mem_chart_closedBall m e d a d' hd' hed _ hd⟩

private theorem leftCoreMap_isLocalDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (leftCoreMap m e c d a hec hed c' d' hc' hd') := by
  let S := smoothConnectedSum M N m e a
  let _ : ChartedSpace E3 (ConnectedSumQuotient m.toBallChart e.toBallChart a.val.toHomeomorph) := S.charts
  have hmap : ∀ x : m.interior, ConnectedSumQuotient.interiorLeft m.toBallChart e.toBallChart a.val x ∈
      SelfAttachment.coreInterior c'.toBallChart d'.toBallChart :=
    fun x => (leftCoreMap m e c d a hec hed c' d' hc' hd' x).property
  intro x
  have hf : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
      (ConnectedSumQuotient.interiorLeft m.toBallChart e.toBallChart a.val) x := S.interiorLeft_localDiffeomorph x
  exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
    (V := SelfAttachment.coreInterior c'.toBallChart d'.toBallChart) hmap hf

private theorem leftCoreMap_orientation :
    let hf := leftCoreMap_isLocalDiffeomorph m e c d a hec hed c' d' hc' hd'
    ∀ x, Orientation.map (Fin 3) (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (M.orientation.orientation x.val) = (smoothConnectedSum M N m e a).orientation.orientation
        (leftCoreMap m e c d a hec hed c' d' hc' hd' x).val := by
  let S := smoothConnectedSum M N m e a
  let _ : ChartedSpace E3 (ConnectedSumQuotient m.toBallChart e.toBallChart a.val.toHomeomorph) := S.charts
  let hf := leftCoreMap_isLocalDiffeomorph m e c d a hec hed c' d' hc' hd'
  dsimp only
  intro x
  have heq : (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv =
      (S.interiorLeft_localDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change mfderiv (𝓡 3) (𝓡 3) (leftCoreMap m e c d a hec hed c' d' hc' hd') x v =
      mfderiv (𝓡 3) (𝓡 3) (ConnectedSumQuotient.interiorLeft m.toBallChart e.toBallChart a.val) x v
    rw [← DifferentialGeometry.mfderiv_subtypeVal_comp]
    rfl
  rw [heq]
  exact S.interiorLeft_preserves_orientation x

theorem selfAttachmentConnectedSumHomeomorph_core_orientation :
    let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
    let t := smoothConnectedSum M s.toConnectedClosedOrientedManifold m e' a
    let _ := t.charts
    let _ := t.smooth
    let H : SelfAttachment.Quotient c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph ≃ₜ
        t.toConnectedClosedOrientedManifold.Carrier :=
      selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he'
    let hg := selfAttachmentConnectedSumHomeomorph_core_localDiffeomorph m e c d a b hec hed hcd c' d' hc' hd' hcd' s e' he'
    ∀ x, Orientation.map (Fin 3) (hg.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      ((smoothConnectedSum M N m e a).orientation.orientation x.val) =
        t.orientation.orientation (H (SelfAttachment.coreInteriorInclusion c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph x)) := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
  let S := smoothConnectedSum M N m e a
  let _ : ChartedSpace E3 (ConnectedSumQuotient m.toBallChart e.toBallChart a.val.toHomeomorph) := S.charts
  let t := smoothConnectedSum M s.toConnectedClosedOrientedManifold m e' a
  let _ := t.charts
  let _ := t.smooth
  let _ := SelfAttachment.coreInterior_connected (X := S.toConnectedClosedOrientedManifold) c' d' hcd'
  let H : SelfAttachment.Quotient c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph ≃ₜ
      t.toConnectedClosedOrientedManifold.Carrier :=
    selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he'
  let g := H ∘ SelfAttachment.coreInteriorInclusion c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph
  let hg : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ g :=
    selfAttachmentConnectedSumHomeomorph_core_localDiffeomorph m e c d a b hec hed hcd c' d' hc' hd' hcd' s e' he'
  let f := leftCoreMap m e c d a hec hed c' d' hc' hd'
  let hf := leftCoreMap_isLocalDiffeomorph m e c d a hec hed c' d' hc' hd'
  have heq : g ∘ f = ConnectedSumQuotient.interiorLeft m.toBallChart e'.toBallChart a.val := by
    funext x
    have h := selfAttachmentConnectedSumHomeomorph_first m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he'
      (m.toBallChart.interiorToPunctured x)
    exact h
  obtain ⟨x₀⟩ := ConnectedSumUnit.nonempty_chart_interior m
  have hp := Manifold.local_orientation_of_comp_eq_at f g
    (ConnectedSumQuotient.interiorLeft m.toBallChart e'.toBallChart a.val) hf hg t.interiorLeft_localDiffeomorph heq
    (M.orientation.restrictOpen m.interior)
    (S.orientation.restrictOpen (SelfAttachment.coreInterior c'.toBallChart d'.toBallChart))
    t.orientation x₀ (leftCoreMap_orientation m e c d a hec hed c' d' hc' hd' x₀)
    (t.interiorLeft_preserves_orientation x₀)
  have hi : Injective g := by
    intro x y h
    have hh := SelfAttachment.coreInclusion_injective c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph (H.injective h)
    exact Subtype.ext (congrArg (fun q : c'.toBallChart.DoublePunctured d'.toBallChart => q.val) hh)
  exact Manifold.localDiffeomorph_orientation_of_eq_at g hg hi
    (S.orientation.restrictOpen (SelfAttachment.coreInterior c'.toBallChart d'.toBallChart)) t.orientation (f x₀) hp

end DifferentialGeometry.Topology
