import DifferentialGeometry.Topology.Attachment.Restriction
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.TriplePunctured
import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.RetainedBall

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SelfAttachment

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M] [CompactSpace M]
  (e c d : BallChart 3 (𝓡 3) M)
  (hec : Disjoint (e.chart '' Metric.closedBall 0 2) (c.chart '' Metric.closedBall 0 2))
  (hed : Disjoint (e.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (hcd : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : S2 ≃ₜ S2)

def tripleAttachingMap : Bool × S2 → e.TriplePunctured c d
  | (false, z) => e.tripleBoundarySecond c d hec hcd z
  | (true, z) => e.tripleBoundaryThird c d hed hcd (a z)

omit [T2Space M] [CompactSpace M] in
include hec hed in
private theorem attaching_mem_pairRestriction (q : Bool × S2) :
    attachingMap c d hcd a q ∈ e.pairRestriction c d := by
  rcases q with ⟨b, z⟩
  cases b
  · exact c.chart_sphere_not_mem_other_ball e hec.symm z
  · exact d.chart_sphere_not_mem_other_ball e hed.symm (a z)

variable [ChartedSpace E3 (Quotient c d hcd a)]
  (e' : BallChart 3 (𝓡 3) (Quotient c d hcd a))
  (he' : ∀ x ∈ Metric.closedBall (0 : E3) 2,
    ∃ hx : e.chart x ∈ (c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ,
      e'.chart x = coreInclusion c d hcd a ⟨e.chart x, hx⟩)

omit [T2Space M] [CompactSpace M] in
include he' in
private theorem retained_ball_hole :
    adjunctionLower (i := boundaryInclusion) (attachingMap c d hcd a) '' (e.pairRestriction c d)ᶜ =
      e'.chart '' Metric.ball 0 1 := by
  rw [retained_ball_eq_coreInclusion_image c d hcd a e e' he']
  congr 1
  ext x
  simp only [BallChart.pairRestriction, mem_compl_iff, mem_ofPred_eq, not_not]

def puncturedBallHomeomorph :
    AdjunctionSpace boundaryInclusion (tripleAttachingMap e c d hec hed hcd a) ≃ₜ e'.Punctured := by
  let T := e.pairRestriction c d
  let φ := attachingMap c d hcd a
  let hT : IsClosed T := e.isClosed_pairRestriction c d
  let hφT : ∀ q, φ q ∈ T := attaching_mem_pairRestriction e c d hec hed hcd a
  let H := adjunctionClosedRestrictionHomeomorph boundaryInclusion φ boundaryInclusion_injective
    (attachingMap_injective c d hcd a) continuous_boundaryInclusion (continuous_attachingMap c d hcd a)
    T hT hφT
  let E := adjunctionSpaceHomeomorphOfHomeomorph boundaryInclusion (fun q => (⟨φ q, hφT q⟩ : T))
    boundaryInclusion (tripleAttachingMap e c d hec hed hcd a)
    (Homeomorph.refl _) (Homeomorph.refl _) (e.pairRestrictionHomeomorph c d)
    (fun _ => rfl) (by rintro ⟨b, z⟩; cases b <;> rfl)
  let C : {q : Quotient c d hcd a // q ∉ adjunctionLower (i := boundaryInclusion) φ '' Tᶜ} ≃ₜ e'.Punctured :=
    Homeomorph.setCongr (by rw [retained_ball_hole e c d hcd a e' he'])
  exact (E.symm.trans H).trans C

theorem puncturedBallHomeomorph_cell (p : Band (n := 3)) :
    (puncturedBallHomeomorph e c d hec hed hcd a e' he'
      (adjunctionCell boundaryInclusion (tripleAttachingMap e c d hec hed hcd a) p)).val =
        bandInclusion c d hcd a p := rfl

theorem puncturedBallHomeomorph_lower (x : e.TriplePunctured c d) :
    (puncturedBallHomeomorph e c d hec hed hcd a e' he'
      (adjunctionLower (i := boundaryInclusion) (tripleAttachingMap e c d hec hed hcd a) x)).val =
        coreInclusion c d hcd a (e.tripleToPair c d x) := rfl

end DifferentialGeometry.Topology.SelfAttachment
