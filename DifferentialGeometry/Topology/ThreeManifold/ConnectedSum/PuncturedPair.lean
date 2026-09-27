import DifferentialGeometry.Topology.Attachment.Restriction
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.TriplePunctured
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FactorBallPair

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ConnectedSumQuotient

universe u v
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1

variable {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
  (m : OrientedBallChart M.toClosedOrientedManifold) (e c d : OrientedBallChart N.toClosedOrientedManifold)
  (a : BoundaryAttachment)
  (hec : Disjoint (e.chart '' Metric.closedBall 0 2) (c.chart '' Metric.closedBall 0 2))
  (hed : Disjoint (e.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (c' d' : OrientedBallChart (smoothConnectedSum M N m e a).toConnectedClosedOrientedManifold.toClosedOrientedManifold)
  (hc' : ∀ x ∈ Metric.closedBall (0 : E3) 2, ∃ hx,
    c'.chart x = inr m.toBallChart e.toBallChart a.val.toHomeomorph ⟨c.chart x, hx⟩)
  (hd' : ∀ x ∈ Metric.closedBall (0 : E3) 2, ∃ hx,
    d'.chart x = inr m.toBallChart e.toBallChart a.val.toHomeomorph ⟨d.chart x, hx⟩)

include hec hed in
private theorem boundary_mem_firstRestriction (z : S2) :
    e.boundaryMap (a.val z) ∈ e.toBallChart.firstRestriction c.toBallChart d.toBallChart := by
  rintro (h | h)
  · exact e.toBallChart.chart_sphere_not_mem_other_ball c.toBallChart hec (a.val z) h
  · exact e.toBallChart.chart_sphere_not_mem_other_ball d.toBallChart hed (a.val z) h

include hc' hd' in
private theorem retained_pair_holes :
    adjunctionLower (i := m.toBallChart.boundaryMap) (e.toBallChart.boundaryMap ∘ a.val.toHomeomorph) ''
      (e.toBallChart.firstRestriction c.toBallChart d.toBallChart)ᶜ =
        c'.chart '' Metric.ball 0 1 ∪ d'.chart '' Metric.ball 0 1 := by
  rw [chart_image_ball_eq_inr_image m e a c c' hc', chart_image_ball_eq_inr_image m e a d d' hd']
  erw [← Set.image_union]
  congr 1
  ext x
  simp only [BallChart.firstRestriction, mem_compl_iff, mem_ofPred_eq, not_not, mem_union]

def puncturedPairHomeomorph :
    AdjunctionSpace m.toBallChart.boundaryMap
      (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph) ≃ₜ
        c'.toBallChart.DoublePunctured d'.toBallChart := by
  let T := e.toBallChart.firstRestriction c.toBallChart d.toBallChart
  let φ := e.toBallChart.boundaryMap ∘ a.val.toHomeomorph
  let hT : IsClosed T := e.toBallChart.isClosed_firstRestriction c.toBallChart d.toBallChart
  let hφT : ∀ z, φ z ∈ T := boundary_mem_firstRestriction e c d a hec hed
  let H := adjunctionClosedRestrictionHomeomorph m.toBallChart.boundaryMap φ
    m.toBallChart.boundaryMap_injective (e.toBallChart.boundaryMap_injective.comp a.val.injective)
    m.toBallChart.continuous_boundaryMap (e.toBallChart.continuous_boundaryMap.comp a.val.continuous) T hT hφT
  let E := adjunctionSpaceHomeomorphOfHomeomorph
    m.toBallChart.boundaryMap (fun z => (⟨φ z, hφT z⟩ : T))
    m.toBallChart.boundaryMap
    (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph)
    (Homeomorph.refl _) (Homeomorph.refl _)
    (e.toBallChart.firstRestrictionHomeomorph c.toBallChart d.toBallChart)
    (fun _ => rfl) (fun _ => rfl)
  let C : {q : ConnectedSumQuotient m.toBallChart e.toBallChart a.val.toHomeomorph //
      q ∉ adjunctionLower (i := m.toBallChart.boundaryMap) φ '' Tᶜ} ≃ₜ
      c'.toBallChart.DoublePunctured d'.toBallChart := Homeomorph.setCongr (by
    rw [retained_pair_holes m e c d a c' d' hc' hd']
    rfl)
  exact (E.symm.trans H).trans C

theorem puncturedPairHomeomorph_cell (x : m.Punctured) :
    (puncturedPairHomeomorph m e c d a hec hed c' d' hc' hd'
      (adjunctionCell m.toBallChart.boundaryMap
        (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph) x)).val =
      inl m.toBallChart e.toBallChart a.val.toHomeomorph x := rfl

theorem puncturedPairHomeomorph_lower (x : e.toBallChart.TriplePunctured c.toBallChart d.toBallChart) :
    (puncturedPairHomeomorph m e c d a hec hed c' d' hc' hd'
      (adjunctionLower (i := m.toBallChart.boundaryMap)
        (e.toBallChart.tripleBoundaryFirst c.toBallChart d.toBallChart hec hed ∘ a.val.toHomeomorph) x)).val =
      inr m.toBallChart e.toBallChart a.val.toHomeomorph (e.toBallChart.tripleToFirst c.toBallChart d.toBallChart x) := rfl

end DifferentialGeometry.Topology.ConnectedSumQuotient
