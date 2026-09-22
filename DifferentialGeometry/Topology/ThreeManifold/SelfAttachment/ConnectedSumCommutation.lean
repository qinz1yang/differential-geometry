import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.PuncturedPair
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.PuncturedBall
import DifferentialGeometry.Topology.Attachment.Commutation
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.TriplePuncturedCollar

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u v
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1

variable {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
  (m : OrientedBallChart M.toClosedOrientedManifold) (e c d : OrientedBallChart N.toClosedOrientedManifold)
  (a : BoundaryAttachment)
  (hec : Disjoint (e.chart '' Metric.closedBall 0 2) (c.chart '' Metric.closedBall 0 2))
  (hed : Disjoint (e.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (c' d' : OrientedBallChart (smoothConnectedSum M N m e a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
  (hc' : ∀ x ∈ Metric.closedBall (0 : E3) 2, ∃ hx,
    c'.chart x = ConnectedSumQuotient.inr m.toBallChart e.toBallChart a.val.toHomeomorph ⟨c.chart x, hx⟩)
  (hd' : ∀ x ∈ Metric.closedBall (0 : E3) 2, ∃ hx,
    d'.chart x = ConnectedSumQuotient.inr m.toBallChart e.toBallChart a.val.toHomeomorph ⟨d.chart x, hx⟩)
  (hcd' : Disjoint (c'.chart '' Metric.closedBall 0 2) (d'.chart '' Metric.closedBall 0 2))
  (b : S2 ≃ₜ S2)
  [ChartedSpace E3 (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b)]
  (e' : BallChart 3 (𝓡 3) (SelfAttachment.Quotient c.toBallChart d.toBallChart hcd b))
  (he' : ∀ x ∈ Metric.closedBall (0 : E3) 2,
    ∃ hx : e.chart x ∈ (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ,
      e'.chart x = SelfAttachment.coreInclusion c.toBallChart d.toBallChart hcd b ⟨e.chart x, hx⟩)

private def selfAttachmentFlatSourceHomeomorph :
    AdjunctionSpace SelfAttachment.boundaryInclusion
      (adjunctionLower (i := m.toBallChart.boundaryMap)
        (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph) ∘
          SelfAttachment.tripleAttachingMap e.toBallChart c.toBallChart d.toBallChart hec hed hcd b) ≃ₜ
      SelfAttachment.Quotient c'.toBallChart d'.toBallChart hcd' b := by
  let H := ConnectedSumQuotient.puncturedPairHomeomorph m e c d a hec hed c' d' hc' hd'
  apply adjunctionSpaceHomeomorphOfHomeomorph SelfAttachment.boundaryInclusion _
    SelfAttachment.boundaryInclusion (SelfAttachment.attachingMap c'.toBallChart d'.toBallChart hcd' b)
    (Homeomorph.refl _) (Homeomorph.refl _) H (fun _ => rfl)
  rintro ⟨q, z⟩
  apply Subtype.ext
  cases q
  · change (H (adjunctionLower _ (e.toBallChart.tripleBoundarySecond c.toBallChart d.toBallChart hec hcd z))).val = c'.chart z
    rw [ConnectedSumQuotient.puncturedPairHomeomorph_lower]
    obtain ⟨hz, heq⟩ := hc' z (by rw [Metric.mem_closedBall, Metric.mem_sphere.mp z.property]; norm_num)
    exact heq.symm
  · change (H (adjunctionLower _ (e.toBallChart.tripleBoundaryThird c.toBallChart d.toBallChart hed hcd (b z)))).val = d'.chart (b z)
    rw [ConnectedSumQuotient.puncturedPairHomeomorph_lower]
    obtain ⟨hz, heq⟩ := hd' (b z) (by rw [Metric.mem_closedBall, Metric.mem_sphere.mp (b z).property]; norm_num)
    exact heq.symm

private def selfAttachmentFlatTargetHomeomorph :
    AdjunctionSpace m.toBallChart.boundaryMap
      (adjunctionLower (i := SelfAttachment.boundaryInclusion)
        (SelfAttachment.tripleAttachingMap e.toBallChart c.toBallChart d.toBallChart hec hed hcd b) ∘
          (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph)) ≃ₜ
      ConnectedSumQuotient m.toBallChart e' a.val.toHomeomorph := by
  let H := SelfAttachment.puncturedBallHomeomorph e.toBallChart c.toBallChart d.toBallChart
    hec hed hcd b e' he'
  apply adjunctionSpaceHomeomorphOfHomeomorph m.toBallChart.boundaryMap _ m.toBallChart.boundaryMap
    (e'.boundaryMap ∘ a.val.toHomeomorph) (Homeomorph.refl _) (Homeomorph.refl _) H (fun _ => rfl)
  intro z
  apply Subtype.ext
  rw [Homeomorph.refl_apply]
  change (H (adjunctionLower _ (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed (a.val z)))).val = e'.chart (a.val z)
  rw [SelfAttachment.puncturedBallHomeomorph_lower]
  obtain ⟨hz, heq⟩ := he' (a.val z) (by rw [Metric.mem_closedBall, Metric.mem_sphere.mp (a.val z).property]; norm_num)
  exact heq.symm

def selfAttachmentConnectedSumHomeomorph :
    SelfAttachment.Quotient c'.toBallChart d'.toBallChart hcd' b ≃ₜ
      ConnectedSumQuotient m.toBallChart e' a.val.toHomeomorph :=
  (selfAttachmentFlatSourceHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b).symm.trans
    ((adjunctionAttachmentsHomeomorphComm m.toBallChart.boundaryMap
      (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph)
      SelfAttachment.boundaryInclusion
      (SelfAttachment.tripleAttachingMap e.toBallChart c.toBallChart d.toBallChart hec hed hcd b)).trans
        (selfAttachmentFlatTargetHomeomorph m e c d a hec hed hcd b e' he'))


theorem selfAttachmentConnectedSumHomeomorph_band (p : SelfAttachment.Band (n := 3)) :
    selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b e' he'
      (SelfAttachment.bandInclusion c'.toBallChart d'.toBallChart hcd' b p) =
      ConnectedSumQuotient.inr m.toBallChart e' a.val.toHomeomorph
        (SelfAttachment.puncturedBallHomeomorph e.toBallChart c.toBallChart d.toBallChart
          hec hed hcd b e' he'
          (adjunctionCell SelfAttachment.boundaryInclusion
            (SelfAttachment.tripleAttachingMap e.toBallChart c.toBallChart d.toBallChart hec hed hcd b) p)) := rfl

theorem selfAttachmentConnectedSumHomeomorph_first (p : m.Punctured) :
    selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b e' he'
      (SelfAttachment.coreInclusion c'.toBallChart d'.toBallChart hcd' b
        (ConnectedSumQuotient.puncturedPairHomeomorph m e c d a hec hed c' d' hc' hd'
          (adjunctionCell m.toBallChart.boundaryMap
            (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph) p))) =
      ConnectedSumQuotient.inl m.toBallChart e' a.val.toHomeomorph p := by
  let φ := e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph
  let ψ := SelfAttachment.tripleAttachingMap e.toBallChart c.toBallChart d.toBallChart hec hed hcd b
  let H := selfAttachmentFlatSourceHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b
  have heq : SelfAttachment.coreInclusion c'.toBallChart d'.toBallChart hcd' b
      (ConnectedSumQuotient.puncturedPairHomeomorph m e c d a hec hed c' d' hc' hd'
        (adjunctionCell m.toBallChart.boundaryMap φ p)) =
      H (adjunctionLower (i := SelfAttachment.boundaryInclusion)
        (adjunctionLower (i := m.toBallChart.boundaryMap) φ ∘ ψ)
        (adjunctionCell m.toBallChart.boundaryMap φ p)) := rfl
  rw [heq]
  change (selfAttachmentFlatTargetHomeomorph m e c d a hec hed hcd b e' he')
    ((adjunctionAttachmentsHomeomorphComm m.toBallChart.boundaryMap φ SelfAttachment.boundaryInclusion ψ)
      (H.symm (H _))) = _
  rw [Homeomorph.symm_apply_apply, adjunctionAttachmentsHomeomorphComm_lower_cell]
  rfl

theorem selfAttachmentConnectedSumHomeomorph_commonCore
    (x : e.toBallChart.TriplePunctured c.toBallChart d.toBallChart) :
    selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b e' he'
      (SelfAttachment.coreInclusion c'.toBallChart d'.toBallChart hcd' b
        (ConnectedSumQuotient.puncturedPairHomeomorph m e c d a hec hed c' d' hc' hd'
          (adjunctionLower (i := m.toBallChart.boundaryMap)
            (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph) x))) =
      ConnectedSumQuotient.inr m.toBallChart e' a.val.toHomeomorph
        (SelfAttachment.puncturedBallHomeomorph e.toBallChart c.toBallChart d.toBallChart
          hec hed hcd b e' he'
          (adjunctionLower (i := SelfAttachment.boundaryInclusion)
            (SelfAttachment.tripleAttachingMap e.toBallChart c.toBallChart d.toBallChart hec hed hcd b) x)) := by
  let φ := e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph
  let ψ := SelfAttachment.tripleAttachingMap e.toBallChart c.toBallChart d.toBallChart hec hed hcd b
  let H := selfAttachmentFlatSourceHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b
  have heq : SelfAttachment.coreInclusion c'.toBallChart d'.toBallChart hcd' b
      (ConnectedSumQuotient.puncturedPairHomeomorph m e c d a hec hed c' d' hc' hd'
        (adjunctionLower (i := m.toBallChart.boundaryMap) φ x)) =
      H (adjunctionLower (i := SelfAttachment.boundaryInclusion)
        (adjunctionLower (i := m.toBallChart.boundaryMap) φ ∘ ψ)
        (adjunctionLower (i := m.toBallChart.boundaryMap) φ x)) := rfl
  rw [heq]
  change (selfAttachmentFlatTargetHomeomorph m e c d a hec hed hcd b e' he')
    ((adjunctionAttachmentsHomeomorphComm m.toBallChart.boundaryMap φ SelfAttachment.boundaryInclusion ψ)
      (H.symm (H _))) = _
  rw [Homeomorph.symm_apply_apply, adjunctionAttachmentsHomeomorphComm_lower_lower]
  rfl


def connectedSumCoreCollar (p : ConnectedSumQuotient.CollarDomain) : c'.toBallChart.DoublePunctured d'.toBallChart :=
  if ht : 0 ≤ p.2.val then
    ConnectedSumQuotient.puncturedPairHomeomorph m e c d a hec hed c' d' hc' hd'
      (adjunctionCell m.toBallChart.boundaryMap
        (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph)
        (m.toBallChart.radialMap p.1 (1 + p.2.val) (by constructor <;> linarith [p.2.property.2])))
  else
    ConnectedSumQuotient.puncturedPairHomeomorph m e c d a hec hed c' d' hc' hd'
      (adjunctionLower (i := m.toBallChart.boundaryMap)
        (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph)
        (e.toBallChart.tripleRadialFirst c.toBallChart d.toBallChart hec hed (a.val p.1)
          (1 - p.2.val) (by constructor <;> linarith [p.2.property.1])))

theorem connectedSumCoreCollar_val (p : ConnectedSumQuotient.CollarDomain) :
    (connectedSumCoreCollar m e c d a hec hed c' d' hc' hd' p).val =
      ConnectedSumQuotient.collarMap m.toBallChart e.toBallChart a.val p := by
  unfold connectedSumCoreCollar
  split_ifs with ht
  · rw [ConnectedSumQuotient.puncturedPairHomeomorph_cell,
      ConnectedSumQuotient.collarMap_of_nonneg m.toBallChart e.toBallChart a.val p ht]
  · rw [ConnectedSumQuotient.puncturedPairHomeomorph_lower,
      ConnectedSumQuotient.collarMap_of_neg m.toBallChart e.toBallChart a.val p (not_le.mp ht)]
    rfl

theorem selfAttachmentConnectedSumHomeomorph_outerCollar (p : ConnectedSumQuotient.CollarDomain) :
    selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b e' he'
      (SelfAttachment.coreInclusion c'.toBallChart d'.toBallChart hcd' b
        (connectedSumCoreCollar m e c d a hec hed c' d' hc' hd' p)) =
      ConnectedSumQuotient.collarMap m.toBallChart e' a.val p := by
  unfold connectedSumCoreCollar
  split_ifs with ht
  · rw [selfAttachmentConnectedSumHomeomorph_first,
      ConnectedSumQuotient.collarMap_of_nonneg m.toBallChart e' a.val p ht]
  · rw [selfAttachmentConnectedSumHomeomorph_commonCore,
      ConnectedSumQuotient.collarMap_of_neg m.toBallChart e' a.val p (not_le.mp ht)]
    apply congrArg (ConnectedSumQuotient.inr m.toBallChart e' a.val.toHomeomorph)
    apply Subtype.ext
    rw [SelfAttachment.puncturedBallHomeomorph_lower]
    obtain ⟨hx, hmap⟩ := he' ((1 - p.2.val) • (a.val p.1).val) (by
      rw [Metric.mem_closedBall, dist_zero_right,
        BallChart.norm_radial (a.val p.1) (by linarith)]
      linarith [p.2.property.1])
    exact hmap.symm


private def tripleRadialSecond (z : S2) (r : ℝ) (hr : r ∈ Icc 1 2) :
    e.toBallChart.TriplePunctured c.toBallChart d.toBallChart :=
  ⟨(c.toBallChart.firstRadialMap d.toBallChart hcd z r hr).val,
    fun h => (c.toBallChart.firstRadialMap e.toBallChart hec.symm z r hr).property (Or.inr h),
    (c.toBallChart.radialMap z r hr).property,
    fun h => (c.toBallChart.firstRadialMap d.toBallChart hcd z r hr).property (Or.inr h)⟩

private def tripleRadialThird (z : S2) (r : ℝ) (hr : r ∈ Icc 1 2) :
    e.toBallChart.TriplePunctured c.toBallChart d.toBallChart :=
  ⟨(c.toBallChart.secondRadialMap d.toBallChart hcd z r hr).val,
    fun h => (d.toBallChart.firstRadialMap e.toBallChart hed.symm z r hr).property (Or.inr h),
    fun h => (d.toBallChart.firstRadialMap c.toBallChart hcd.symm z r hr).property (Or.inr h),
    (d.toBallChart.radialMap z r hr).property⟩

private theorem puncturedPairHomeomorph_radialSecond (z : S2) (r : ℝ) (hr : r ∈ Icc 1 2) :
    ConnectedSumQuotient.puncturedPairHomeomorph m e c d a hec hed c' d' hc' hd'
      (adjunctionLower (i := m.toBallChart.boundaryMap)
        (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph)
        (tripleRadialSecond e c d hec hcd z r hr)) =
      c'.toBallChart.firstRadialMap d'.toBallChart hcd' z r hr := by
  apply Subtype.ext
  rw [ConnectedSumQuotient.puncturedPairHomeomorph_lower]
  obtain ⟨hz, hmap⟩ := hc' (r • z.val) (by
    rw [Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial z (by linarith [hr.1])]
    exact hr.2)
  exact hmap.symm

private theorem puncturedPairHomeomorph_radialThird (z : S2) (r : ℝ) (hr : r ∈ Icc 1 2) :
    ConnectedSumQuotient.puncturedPairHomeomorph m e c d a hec hed c' d' hc' hd'
      (adjunctionLower (i := m.toBallChart.boundaryMap)
        (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph)
        (tripleRadialThird e c d hed hcd z r hr)) =
      c'.toBallChart.secondRadialMap d'.toBallChart hcd' z r hr := by
  apply Subtype.ext
  rw [ConnectedSumQuotient.puncturedPairHomeomorph_lower]
  obtain ⟨hz, hmap⟩ := hd' (r • z.val) (by
    rw [Metric.mem_closedBall, dist_zero_right, BallChart.norm_radial z (by linarith [hr.1])]
    exact hr.2)
  exact hmap.symm

def innerLowerCollarPunctured (p : SelfAttachment.CollarDomain) : e'.Punctured :=
  if ht : p.2.val ≤ 0 then
    SelfAttachment.puncturedBallHomeomorph e.toBallChart c.toBallChart d.toBallChart hec hed hcd b e' he'
      (adjunctionLower (i := SelfAttachment.boundaryInclusion)
        (SelfAttachment.tripleAttachingMap e.toBallChart c.toBallChart d.toBallChart hec hed hcd b)
        (tripleRadialSecond e c d hec hcd p.1 (1 - p.2.val) (by constructor <;> linarith [p.2.property.1])))
  else
    SelfAttachment.puncturedBallHomeomorph e.toBallChart c.toBallChart d.toBallChart hec hed hcd b e' he'
      (adjunctionCell SelfAttachment.boundaryInclusion
        (SelfAttachment.tripleAttachingMap e.toBallChart c.toBallChart d.toBallChart hec hed hcd b)
        (p.1, ⟨p.2.val, (not_le.mp ht).le, by linarith [p.2.property.2]⟩))

theorem innerLowerCollarPunctured_val (p : SelfAttachment.CollarDomain) :
    (innerLowerCollarPunctured e c d hec hed hcd b e' he' p).val =
      SelfAttachment.lowerCollar c.toBallChart d.toBallChart hcd b p := by
  unfold innerLowerCollarPunctured
  split_ifs with ht
  · rw [SelfAttachment.puncturedBallHomeomorph_lower,
      SelfAttachment.lowerCollar_of_nonpos c.toBallChart d.toBallChart hcd b p ht]
    rfl
  · rw [SelfAttachment.puncturedBallHomeomorph_cell,
      SelfAttachment.lowerCollar_of_pos c.toBallChart d.toBallChart hcd b p (not_le.mp ht)]

theorem selfAttachmentConnectedSumHomeomorph_lowerCollar (p : SelfAttachment.CollarDomain) :
    selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b e' he'
      (SelfAttachment.lowerCollar c'.toBallChart d'.toBallChart hcd' b p) =
      ConnectedSumQuotient.inr m.toBallChart e' a.val.toHomeomorph
        (innerLowerCollarPunctured e c d hec hed hcd b e' he' p) := by
  by_cases ht : p.2.val ≤ 0
  · rw [SelfAttachment.lowerCollar_of_nonpos c'.toBallChart d'.toBallChart hcd' b p ht]
    erw [← puncturedPairHomeomorph_radialSecond m e c d a hec hed hcd c' d' hc' hd' hcd']
    rw [selfAttachmentConnectedSumHomeomorph_commonCore]
    rw [innerLowerCollarPunctured, dif_pos ht]
  · rw [SelfAttachment.lowerCollar_of_pos c'.toBallChart d'.toBallChart hcd' b p (not_le.mp ht),
      selfAttachmentConnectedSumHomeomorph_band, innerLowerCollarPunctured, dif_neg ht]


def innerUpperCollarPunctured (p : SelfAttachment.CollarDomain) : e'.Punctured :=
  if ht : 0 ≤ p.2.val then
    SelfAttachment.puncturedBallHomeomorph e.toBallChart c.toBallChart d.toBallChart hec hed hcd b e' he'
      (adjunctionLower (i := SelfAttachment.boundaryInclusion)
        (SelfAttachment.tripleAttachingMap e.toBallChart c.toBallChart d.toBallChart hec hed hcd b)
        (tripleRadialThird e c d hed hcd (b p.1) (1 + p.2.val) (by constructor <;> linarith [p.2.property.2])))
  else
    SelfAttachment.puncturedBallHomeomorph e.toBallChart c.toBallChart d.toBallChart hec hed hcd b e' he'
      (adjunctionCell SelfAttachment.boundaryInclusion
        (SelfAttachment.tripleAttachingMap e.toBallChart c.toBallChart d.toBallChart hec hed hcd b)
        (p.1, ⟨1 + p.2.val, by constructor <;> linarith [p.2.property.1]⟩))

theorem innerUpperCollarPunctured_val (p : SelfAttachment.CollarDomain) :
    (innerUpperCollarPunctured e c d hec hed hcd b e' he' p).val =
      SelfAttachment.upperCollar c.toBallChart d.toBallChart hcd b p := by
  unfold innerUpperCollarPunctured
  split_ifs with ht
  · rw [SelfAttachment.puncturedBallHomeomorph_lower,
      SelfAttachment.upperCollar_of_nonneg c.toBallChart d.toBallChart hcd b p ht]
    rfl
  · rw [SelfAttachment.puncturedBallHomeomorph_cell,
      SelfAttachment.upperCollar_of_neg c.toBallChart d.toBallChart hcd b p (not_le.mp ht)]

theorem selfAttachmentConnectedSumHomeomorph_upperCollar (p : SelfAttachment.CollarDomain) :
    selfAttachmentConnectedSumHomeomorph m e c d a hec hed hcd c' d' hc' hd' hcd' b e' he'
      (SelfAttachment.upperCollar c'.toBallChart d'.toBallChart hcd' b p) =
      ConnectedSumQuotient.inr m.toBallChart e' a.val.toHomeomorph
        (innerUpperCollarPunctured e c d hec hed hcd b e' he' p) := by
  by_cases ht : 0 ≤ p.2.val
  · rw [SelfAttachment.upperCollar_of_nonneg c'.toBallChart d'.toBallChart hcd' b p ht]
    erw [← puncturedPairHomeomorph_radialThird m e c d a hec hed hcd c' d' hc' hd' hcd']
    rw [selfAttachmentConnectedSumHomeomorph_commonCore]
    rw [innerUpperCollarPunctured, dif_pos ht]
  · rw [SelfAttachment.upperCollar_of_neg c'.toBallChart d'.toBallChart hcd' b p (not_le.mp ht),
      selfAttachmentConnectedSumHomeomorph_band, innerUpperCollarPunctured, dif_neg ht]

end DifferentialGeometry.Topology
