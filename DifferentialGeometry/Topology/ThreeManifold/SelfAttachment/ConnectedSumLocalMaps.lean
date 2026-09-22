import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.ConnectedSumCommutation
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.Smooth
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.InteriorComposition
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FactorBallPairMembership
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.LocalMaps
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.CoreExtension

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

include hec hed in
private theorem e_image_avoids_pair (x : E3) (hx : x ∈ Metric.closedBall (0 : E3) 2) :
    e.chart x ∉ c.chart '' Metric.closedBall 0 1 ∪ d.chart '' Metric.closedBall 0 1 := by
  rintro (hc | hd)
  · exact Set.disjoint_left.mp hec ⟨x, hx, rfl⟩
      (Set.image_mono (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)) hc)
  · exact Set.disjoint_left.mp hed ⟨x, hx, rfl⟩
      (Set.image_mono (Metric.closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2)) hd)

include hec hed he' in
private theorem lowerCollar_not_mem_retained_closedBall :
    let _ := s.charts
    ∀ p : SelfAttachment.CollarDomain,
      SelfAttachment.lowerCollar c.toBallChart d.toBallChart hcd b.val.toHomeomorph p ∉
        e'.chart '' Metric.closedBall 0 1 := by
  let _ := s.charts
  dsimp only
  intro p
  by_cases ht : p.2.val ≤ 0
  · rw [SelfAttachment.lowerCollar_of_nonpos c.toBallChart d.toBallChart hcd b.val.toHomeomorph p ht]
    intro h
    have hh := Set.ext_iff.mp (SelfAttachment.preimage_coreInclusion_retained_closedBall
      c.toBallChart d.toBallChart hcd b.val.toHomeomorph e.toBallChart e'.toBallChart he') _ |>.mp h
    obtain ⟨x, hx, heq⟩ := hh
    have hy : c.chart ((1 - p.2.val) • p.1.val) ∈ c.chart '' Metric.closedBall 0 2 :=
      ⟨_, by
        rw [Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial p.1 (by linarith)]
        linarith [p.2.property.1], rfl⟩
    exact Set.disjoint_left.mp hec ⟨x, Metric.closedBall_subset_closedBall (by norm_num) hx, rfl⟩
      (heq ▸ hy)
  · rw [SelfAttachment.lowerCollar_of_pos c.toBallChart d.toBallChart hcd b.val.toHomeomorph p (not_le.mp ht)]
    have h := SelfAttachment.preimage_bandInclusion_retained_closedBall c.toBallChart d.toBallChart hcd b.val.toHomeomorph
      e.toBallChart e'.toBallChart he' (e_image_avoids_pair e c d hec hed)
    intro hp
    exact (Set.ext_iff.mp h _).mp hp

include hec hed he' in
private theorem upperCollar_not_mem_retained_closedBall :
    let _ := s.charts
    ∀ p : SelfAttachment.CollarDomain,
      SelfAttachment.upperCollar c.toBallChart d.toBallChart hcd b.val.toHomeomorph p ∉
        e'.chart '' Metric.closedBall 0 1 := by
  let _ := s.charts
  dsimp only
  intro p
  by_cases ht : 0 ≤ p.2.val
  · rw [SelfAttachment.upperCollar_of_nonneg c.toBallChart d.toBallChart hcd b.val.toHomeomorph p ht]
    intro h
    have hh := Set.ext_iff.mp (SelfAttachment.preimage_coreInclusion_retained_closedBall
      c.toBallChart d.toBallChart hcd b.val.toHomeomorph e.toBallChart e'.toBallChart he') _ |>.mp h
    obtain ⟨x, hx, heq⟩ := hh
    have hy : d.chart ((1 + p.2.val) • (b.val p.1).val) ∈ d.chart '' Metric.closedBall 0 2 :=
      ⟨_, by
        rw [Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial (b.val p.1) (by linarith)]
        linarith [p.2.property.2], rfl⟩
    exact Set.disjoint_left.mp hed ⟨x, Metric.closedBall_subset_closedBall (by norm_num) hx, rfl⟩
      (heq ▸ hy)
  · rw [SelfAttachment.upperCollar_of_neg c.toBallChart d.toBallChart hcd b.val.toHomeomorph p (not_le.mp ht)]
    have h := SelfAttachment.preimage_bandInclusion_retained_closedBall c.toBallChart d.toBallChart hcd b.val.toHomeomorph
      e.toBallChart e'.toBallChart he' (e_image_avoids_pair e c d hec hed)
    intro hp
    exact (Set.ext_iff.mp h _).mp hp

theorem selfAttachmentConnectedSumHomeomorph_lower_localDiffeomorph :
    let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
    let t := smoothConnectedSum M s.toConnectedClosedOrientedManifold m e' a
    let _ := t.charts
    let H : SelfAttachment.Quotient c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph ≃ₜ
        t.toConnectedClosedOrientedManifold.Carrier :=
      selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he'
    ∀ z, IsLocalDiffeomorphAt IC (𝓡 3) ∞
      (H ∘ SelfAttachment.lowerCollar c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph)
      (SelfAttachment.collarZero z) := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
  let t := smoothConnectedSum M s.toConnectedClosedOrientedManifold m e' a
  let _ := t.charts
  dsimp only
  intro z
  let f := innerLowerCollarPunctured e c d hec hed hcd b.val.toHomeomorph e'.toBallChart he'
  have hf : IsLocalDiffeomorphAt IC (𝓡 3) ∞ (fun p => (f p).val) (SelfAttachment.collarZero z) := by
    have heq : (fun p => (f p).val) = SelfAttachment.lowerCollar c.toBallChart d.toBallChart hcd b.val.toHomeomorph :=
      funext (innerLowerCollarPunctured_val e c d hec hed hcd b.val.toHomeomorph e'.toBallChart he')
    rw [heq]
    exact s.lower_localDiffeomorph z
  have hx : (f (SelfAttachment.collarZero z)).val ∈ e'.interior := by
    rw [show (f (SelfAttachment.collarZero z)).val = _ from
      innerLowerCollarPunctured_val e c d hec hed hcd b.val.toHomeomorph e'.toBallChart he' _]
    exact lowerCollar_not_mem_retained_closedBall e c d b hec hed hcd s e' he' _
  have h := t.isLocalDiffeomorphAt_inr_comp f (SelfAttachment.collarZero z) hf hx
  apply IsLocalDiffeomorphAt.of_eventuallyEq _ h
  exact Filter.Eventually.of_forall
    (selfAttachmentConnectedSumHomeomorph_lowerCollar m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he')

theorem selfAttachmentConnectedSumHomeomorph_upper_localDiffeomorph :
    let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
    let t := smoothConnectedSum M s.toConnectedClosedOrientedManifold m e' a
    let _ := t.charts
    let H : SelfAttachment.Quotient c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph ≃ₜ
        t.toConnectedClosedOrientedManifold.Carrier :=
      selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he'
    ∀ z, IsLocalDiffeomorphAt IC (𝓡 3) ∞
      (H ∘ SelfAttachment.upperCollar c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph)
      (SelfAttachment.collarZero z) := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
  let t := smoothConnectedSum M s.toConnectedClosedOrientedManifold m e' a
  let _ := t.charts
  dsimp only
  intro z
  let f := innerUpperCollarPunctured e c d hec hed hcd b.val.toHomeomorph e'.toBallChart he'
  have hf : IsLocalDiffeomorphAt IC (𝓡 3) ∞ (fun p => (f p).val) (SelfAttachment.collarZero z) := by
    have heq : (fun p => (f p).val) = SelfAttachment.upperCollar c.toBallChart d.toBallChart hcd b.val.toHomeomorph :=
      funext (innerUpperCollarPunctured_val e c d hec hed hcd b.val.toHomeomorph e'.toBallChart he')
    rw [heq]
    exact s.upper_localDiffeomorph z
  have hx : (f (SelfAttachment.collarZero z)).val ∈ e'.interior := by
    rw [show (f (SelfAttachment.collarZero z)).val = _ from
      innerUpperCollarPunctured_val e c d hec hed hcd b.val.toHomeomorph e'.toBallChart he' _]
    exact upperCollar_not_mem_retained_closedBall e c d b hec hed hcd s e' he' _
  have h := t.isLocalDiffeomorphAt_inr_comp f (SelfAttachment.collarZero z) hf hx
  apply IsLocalDiffeomorphAt.of_eventuallyEq _ h
  exact Filter.Eventually.of_forall
    (selfAttachmentConnectedSumHomeomorph_upperCollar m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he')


theorem selfAttachmentConnectedSumHomeomorph_band_localDiffeomorph :
    let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
    let t := smoothConnectedSum M s.toConnectedClosedOrientedManifold m e' a
    let _ := t.charts
    let H : SelfAttachment.Quotient c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph ≃ₜ
        t.toConnectedClosedOrientedManifold.Carrier :=
      selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he'
    IsLocalDiffeomorph IC (𝓡 3) ∞
      (H ∘ SelfAttachment.bandInteriorInclusion c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph) := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
  let t := smoothConnectedSum M s.toConnectedClosedOrientedManifold m e' a
  let _ := t.charts
  dsimp only
  let f : SelfAttachment.bandInterior → e'.Punctured := fun p =>
    SelfAttachment.puncturedBallHomeomorph e.toBallChart c.toBallChart d.toBallChart hec hed hcd
      b.val.toHomeomorph e'.toBallChart he'
      (adjunctionCell SelfAttachment.boundaryInclusion
        (SelfAttachment.tripleAttachingMap e.toBallChart c.toBallChart d.toBallChart hec hed hcd b.val.toHomeomorph)
        (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩))
  have hf : (fun p => (f p).val) = SelfAttachment.bandInteriorInclusion c.toBallChart d.toBallChart hcd b.val.toHomeomorph := by
    funext p
    exact SelfAttachment.puncturedBallHomeomorph_cell e.toBallChart c.toBallChart d.toBallChart hec hed hcd
      b.val.toHomeomorph e'.toBallChart he' _
  intro p
  have hloc : IsLocalDiffeomorphAt IC (𝓡 3) ∞ (fun x => (f x).val) p := by
    rw [hf]
    exact s.band_localDiffeomorph p
  have hx : (f p).val ∈ e'.interior := by
    rw [show (f p).val = _ from congrFun hf p]
    have h := SelfAttachment.preimage_bandInclusion_retained_closedBall c.toBallChart d.toBallChart hcd b.val.toHomeomorph
      e.toBallChart e'.toBallChart he' (e_image_avoids_pair e c d hec hed)
    intro hp
    exact (Set.ext_iff.mp h _).mp hp
  have h := t.isLocalDiffeomorphAt_inr_comp f p hloc hx
  apply IsLocalDiffeomorphAt.of_eventuallyEq _ h
  exact Filter.Eventually.of_forall (fun q => selfAttachmentConnectedSumHomeomorph_band m e c d a hec hed hcd
    c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he' (q.val.1, ⟨q.val.2, q.property.2.1.le, q.property.2.2.le⟩))


private def commutationCoreExtension :
    (smoothConnectedSum M N m e a).toConnectedClosedOrientedManifold.Carrier →
      (smoothConnectedSum M s.toConnectedClosedOrientedManifold m e' a).toConnectedClosedOrientedManifold.Carrier := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
  exact selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he' ∘
    SelfAttachment.coreExtension c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph

private theorem commutationCoreExtension_left (x : m.interior) :
    commutationCoreExtension m e c d a b hec hed hcd c' d' hc' hd' hcd' s e' he'
      (ConnectedSumQuotient.interiorLeft m.toBallChart e.toBallChart a.val x) =
      ConnectedSumQuotient.interiorLeft m.toBallChart e'.toBallChart a.val x := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
  let y := ConnectedSumQuotient.puncturedPairHomeomorph m e c d a hec hed c' d' hc' hd'
    (adjunctionCell m.toBallChart.boundaryMap
      (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph)
      (m.toBallChart.interiorToPunctured x))
  have hy : y.val = ConnectedSumQuotient.interiorLeft m.toBallChart e.toBallChart a.val x :=
    ConnectedSumQuotient.puncturedPairHomeomorph_cell m e c d a hec hed c' d' hc' hd' _
  change (selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he')
    (SelfAttachment.coreExtension c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph _) = _
  rw [← hy, SelfAttachment.coreExtension_apply]
  exact selfAttachmentConnectedSumHomeomorph_first m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he' _

private theorem commutationCoreExtension_outerCollar (p : ConnectedSumQuotient.CollarDomain) :
    commutationCoreExtension m e c d a b hec hed hcd c' d' hc' hd' hcd' s e' he'
      (ConnectedSumQuotient.collarMap m.toBallChart e.toBallChart a.val p) =
      ConnectedSumQuotient.collarMap m.toBallChart e'.toBallChart a.val p := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
  let y := connectedSumCoreCollar m e c d a hec hed c' d' hc' hd' p
  have hy : y.val = ConnectedSumQuotient.collarMap m.toBallChart e.toBallChart a.val p :=
    connectedSumCoreCollar_val m e c d a hec hed c' d' hc' hd' p
  change (selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he')
    (SelfAttachment.coreExtension c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph _) = _
  rw [← hy, SelfAttachment.coreExtension_apply]
  exact selfAttachmentConnectedSumHomeomorph_outerCollar m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he' _

private def rightCoreDomain : TopologicalSpace.Opens e.interior :=
  ⟨{x : e.interior | x.val ∈ SelfAttachment.coreInterior c.toBallChart d.toBallChart},
    (SelfAttachment.coreInterior c.toBallChart d.toBallChart).isOpen.preimage continuous_subtype_val⟩

private def rightCoreToTriple (x : rightCoreDomain e c d) : e.toBallChart.TriplePunctured c.toBallChart d.toBallChart :=
  ⟨x.val.val, fun h => x.val.property (Set.image_mono Metric.ball_subset_closedBall h),
    fun h => x.property (Or.inl (Set.image_mono Metric.ball_subset_closedBall h)),
    fun h => x.property (Or.inr (Set.image_mono Metric.ball_subset_closedBall h))⟩

private def rightCoreToPunctured (x : rightCoreDomain e c d) : e'.Punctured := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
  exact SelfAttachment.puncturedBallHomeomorph e.toBallChart c.toBallChart d.toBallChart hec hed hcd b.val.toHomeomorph e'.toBallChart he'
    (adjunctionLower (i := SelfAttachment.boundaryInclusion)
      (SelfAttachment.tripleAttachingMap e.toBallChart c.toBallChart d.toBallChart hec hed hcd b.val.toHomeomorph)
      (rightCoreToTriple e c d x))

private theorem rightCoreToPunctured_val (x : rightCoreDomain e c d) :
    (rightCoreToPunctured e c d b hec hed hcd s e' he' x).val =
      SelfAttachment.coreInteriorInclusion c.toBallChart d.toBallChart hcd b.val.toHomeomorph
        ⟨x.val.val, x.property⟩ := rfl

private theorem commutationCoreExtension_right (x : rightCoreDomain e c d) :
    commutationCoreExtension m e c d a b hec hed hcd c' d' hc' hd' hcd' s e' he'
      (ConnectedSumQuotient.interiorRight m.toBallChart e.toBallChart a.val x.val) =
      ConnectedSumQuotient.inr m.toBallChart e'.toBallChart a.val.toHomeomorph
        (rightCoreToPunctured e c d b hec hed hcd s e' he' x) := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
  let y := ConnectedSumQuotient.puncturedPairHomeomorph m e c d a hec hed c' d' hc' hd'
    (adjunctionLower (i := m.toBallChart.boundaryMap)
      (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph) (rightCoreToTriple e c d x))
  have hy : y.val = ConnectedSumQuotient.interiorRight m.toBallChart e.toBallChart a.val x.val := rfl
  change (selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he')
    (SelfAttachment.coreExtension c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph _) = _
  rw [← hy, SelfAttachment.coreExtension_apply]
  exact selfAttachmentConnectedSumHomeomorph_commonCore m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he' _


private theorem rightCoreToPunctured_inr_localDiffeomorph :
    let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
    let t := smoothConnectedSum M s.toConnectedClosedOrientedManifold m e' a
    let _ := t.charts
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (fun x : rightCoreDomain e c d => ConnectedSumQuotient.inr m.toBallChart e'.toBallChart a.val.toHomeomorph
        (rightCoreToPunctured e c d b hec hed hcd s e' he' x)) := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
  let t := smoothConnectedSum M s.toConnectedClosedOrientedManifold m e' a
  let _ := t.charts
  dsimp only
  let g : rightCoreDomain e c d → SelfAttachment.coreInterior c.toBallChart d.toBallChart :=
    fun x => ⟨x.val.val, x.property⟩
  have hg : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ g := by
    have hval := DifferentialGeometry.isLocalDiffeomorph_comp
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := 𝓡 3) e.interior)
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := 𝓡 3) (rightCoreDomain e c d))
    intro x
    exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict (fun y => y.property) (hval x)
  let f := rightCoreToPunctured e c d b hec hed hcd s e' he'
  have hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x => (f x).val) := by
    have h := DifferentialGeometry.isLocalDiffeomorph_comp s.core_localDiffeomorph hg
    have heq : (fun x => (f x).val) = SelfAttachment.coreInteriorInclusion c.toBallChart d.toBallChart hcd b.val.toHomeomorph ∘ g :=
      funext (rightCoreToPunctured_val e c d b hec hed hcd s e' he')
    rw [heq]
    exact h
  intro x
  have hx : (f x).val ∈ e'.interior := by
    rw [show (f x).val = _ from rightCoreToPunctured_val e c d b hec hed hcd s e' he' x]
    intro h
    have h' := Set.ext_iff.mp (SelfAttachment.preimage_coreInclusion_retained_closedBall
      c.toBallChart d.toBallChart hcd b.val.toHomeomorph e.toBallChart e'.toBallChart he') _ |>.mp h
    exact x.val.property h'
  exact t.isLocalDiffeomorphAt_inr_comp f x (hf x) hx

theorem selfAttachmentConnectedSumHomeomorph_core_localDiffeomorph :
    let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
    let t := smoothConnectedSum M s.toConnectedClosedOrientedManifold m e' a
    let _ := t.charts
    let H : SelfAttachment.Quotient c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph ≃ₜ
        t.toConnectedClosedOrientedManifold.Carrier :=
      selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he'
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (H ∘ SelfAttachment.coreInteriorInclusion c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph) := by
  let _ : ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b.val.toHomeomorph) := s.charts
  let t := smoothConnectedSum M s.toConnectedClosedOrientedManifold m e' a
  let _ := t.charts
  dsimp only
  let S := smoothConnectedSum M N m e a
  let _ : ChartedSpace E3 (ConnectedSumQuotient m.toBallChart e.toBallChart a.val.toHomeomorph) := S.charts
  let f := commutationCoreExtension m e c d a b hec hed hcd c' d' hc' hd' hcd' s e' he'
  have hlocal : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (fun x : SelfAttachment.coreInterior c'.toBallChart d'.toBallChart => f x.val) := by
    apply S.isLocalDiffeomorph_restrict_of_comp f (SelfAttachment.coreInterior c'.toBallChart d'.toBallChart)
    · intro x _
      exact IsLocalDiffeomorphAt.of_eventuallyEq
        (Filter.Eventually.of_forall (commutationCoreExtension_left m e c d a b hec hed hcd c' d' hc' hd' hcd' s e' he'))
        (t.interiorLeft_localDiffeomorph x)
    · intro x hx
      have hxgood : x ∈ rightCoreDomain e c d :=
        (ConnectedSumQuotient.interiorRight_mem_pairCore_iff m e c d a c' d' hc' hd' x).mp hx
      let x' : rightCoreDomain e c d := ⟨x, hxgood⟩
      have hgf : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
          (fun y : rightCoreDomain e c d => f (ConnectedSumQuotient.interiorRight m.toBallChart e.toBallChart a.val y.val)) x' :=
        IsLocalDiffeomorphAt.of_eventuallyEq
          (Filter.Eventually.of_forall (commutationCoreExtension_right m e c d a b hec hed hcd c' d' hc' hd' hcd' s e' he'))
          (rightCoreToPunctured_inr_localDiffeomorph m e c d a b hec hed hcd s e' he' x')
      exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp
        (f := (Subtype.val : rightCoreDomain e c d → e.interior))
        (g := f ∘ ConnectedSumQuotient.interiorRight m.toBallChart e.toBallChart a.val) hgf
        (DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := 𝓡 3) (rightCoreDomain e c d) x')
    · intro p _
      exact IsLocalDiffeomorphAt.of_eventuallyEq
        (Filter.Eventually.of_forall (commutationCoreExtension_outerCollar m e c d a b hec hed hcd c' d' hc' hd' hcd' s e' he'))
        (t.collar_localDiffeomorph p)
  have heq : (fun x : SelfAttachment.coreInterior c'.toBallChart d'.toBallChart => f x.val) =
      selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he' ∘
        SelfAttachment.coreInteriorInclusion c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph := by
    funext x
    change (selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he')
      (SelfAttachment.coreExtension c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph x.val) = _
    exact congrArg (selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b.val.toHomeomorph e'.toBallChart he')
      (SelfAttachment.coreExtension_apply c'.toBallChart d'.toBallChart hcd' b.val.toHomeomorph
        (SelfAttachment.coreInteriorToCore c'.toBallChart d'.toBallChart x))
  rwa [heq] at hlocal


theorem SelfAttachment.coreInterior_connected
    {X : ConnectedClosedOrientedManifold 3}
    (u v : OrientedBallChart X.toClosedOrientedManifold)
    (huv : Disjoint (u.chart '' Metric.closedBall 0 2) (v.chart '' Metric.closedBall 0 2)) :
    ConnectedSpace (SelfAttachment.coreInterior u.toBallChart v.toBallChart) := by
  let B := u.doubleMarking v huv
  have h := B.isPathConnected_ambient.isConnected
  have heq : B.ambient = (SelfAttachment.coreInterior u.toBallChart v.toBallChart : Set X.Carrier) := by
    ext x
    simp only [B, BallMarking.ambient, BallMarking.closedBallImages, BallMarking.closedBallImage,
      OrientedBallChart.doubleMarking, mem_compl_iff, mem_iUnion, Bool.exists_bool, Bool.false_eq_true,
      ↓reduceIte, SelfAttachment.coreInterior, TopologicalSpace.Opens.coe_mk, mem_union]
  rw [heq] at h
  exact isConnected_iff_connectedSpace.mp h

end DifferentialGeometry.Topology
