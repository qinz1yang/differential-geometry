import DifferentialGeometry.Topology.Manifold.BallChart.Defs
import DifferentialGeometry.Topology.Manifold.Attachment.AdjunctionSeparation

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

namespace BallChart

variable {n : ℕ} {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] (c d : BallChart n I M)

abbrev DoublePunctured :=
  ↥((c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ : Set M)

theorem isClosed_doublePunctured :
    IsClosed ((c.chart '' Metric.ball 0 1 ∪ d.chart '' Metric.ball 0 1)ᶜ : Set M) :=
  (c.isOpen_chart_image_ball.union d.isOpen_chart_image_ball).isClosed_compl

instance instCompactSpaceDoublePunctured [CompactSpace M] :
    CompactSpace (c.DoublePunctured d) :=
  isCompact_iff_compactSpace.mp (c.isClosed_doublePunctured d).isCompact

variable (hdisj : Disjoint (c.chart '' Metric.closedBall 0 2)
  (d.chart '' Metric.closedBall 0 2))

include hdisj in
theorem chart_sphere_not_mem_other_ball
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    c.chart z ∉ d.chart '' Metric.ball 0 1 := by
  intro hz
  exact Set.disjoint_left.mp hdisj
    ⟨z, by rw [Metric.mem_closedBall, Metric.mem_sphere.mp z.2]; norm_num, rfl⟩
    (Set.image_mono (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall
      (by norm_num : (1 : ℝ) ≤ 2))) hz)

def firstBoundaryMap (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    c.DoublePunctured d :=
  ⟨c.chart z, fun h => h.elim (c.boundaryMap z).property
    (c.chart_sphere_not_mem_other_ball d hdisj z)⟩

def secondBoundaryMap (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    c.DoublePunctured d :=
  ⟨d.chart z, fun h => h.elim (d.chart_sphere_not_mem_other_ball c hdisj.symm z)
    (d.boundaryMap z).property⟩

@[simp] theorem firstBoundaryMap_val
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (c.firstBoundaryMap d hdisj z).val = c.chart z := rfl

@[simp] theorem secondBoundaryMap_val
    (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (c.secondBoundaryMap d hdisj z).val = d.chart z := rfl

theorem firstBoundaryMap_injective : Injective (c.firstBoundaryMap d hdisj) := by
  intro z w h
  exact Subtype.ext (c.chart.toPartialEquiv.injOn (c.sphere_subset_source z.2)
    (c.sphere_subset_source w.2) (congrArg Subtype.val h))

theorem secondBoundaryMap_injective : Injective (c.secondBoundaryMap d hdisj) := by
  intro z w h
  exact Subtype.ext (d.chart.toPartialEquiv.injOn (d.sphere_subset_source z.2)
    (d.sphere_subset_source w.2) (congrArg Subtype.val h))

theorem firstBoundaryMap_ne_secondBoundaryMap
    (z w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    c.firstBoundaryMap d hdisj z ≠ c.secondBoundaryMap d hdisj w := by
  intro h
  have heq : c.chart z = d.chart w := congrArg Subtype.val h
  exact Set.disjoint_left.mp hdisj
    ⟨z, by rw [Metric.mem_closedBall, Metric.mem_sphere.mp z.2]; norm_num, rfl⟩
    ⟨w, by rw [Metric.mem_closedBall, Metric.mem_sphere.mp w.2]; norm_num, heq.symm⟩

theorem continuous_firstBoundaryMap : Continuous (c.firstBoundaryMap d hdisj) :=
  (c.chart.contMDiffOn_toFun.continuousOn.comp_continuous
    continuous_subtype_val (fun z => c.sphere_subset_source z.2)).subtype_mk _

theorem continuous_secondBoundaryMap : Continuous (c.secondBoundaryMap d hdisj) :=
  (d.chart.contMDiffOn_toFun.continuousOn.comp_continuous
    continuous_subtype_val (fun z => d.sphere_subset_source z.2)).subtype_mk _

end BallChart

namespace SelfAttachment

variable {n : ℕ}

abbrev Sphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
abbrev Band := Sphere (n := n) × Icc (0 : ℝ) 1

def boundaryInclusion : Bool × Sphere (n := n) → Band (n := n)
  | (false, z) => (z, ⟨0, by norm_num⟩)
  | (true, z) => (z, ⟨1, by norm_num⟩)

theorem boundaryInclusion_injective : Injective (boundaryInclusion (n := n)) := by
  rintro ⟨b, z⟩ ⟨e, w⟩ h
  cases b <;> cases e
  · exact Prod.ext rfl (congrArg Prod.fst h)
  · have ht := congrArg (fun q : Band (n := n) => q.2.val) h
    norm_num [boundaryInclusion] at ht
  · have ht := congrArg (fun q : Band (n := n) => q.2.val) h
    norm_num [boundaryInclusion] at ht
  · exact Prod.ext rfl (congrArg Prod.fst h)

theorem continuous_boundaryInclusion : Continuous (boundaryInclusion (n := n)) := by
  apply continuous_prod_of_discrete_left.mpr
  intro b
  cases b <;> exact continuous_id.prodMk continuous_const

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] (c d : BallChart n I M)
  (hdisj : Disjoint (c.chart '' Metric.closedBall 0 2) (d.chart '' Metric.closedBall 0 2))
  (a : Sphere (n := n) ≃ₜ Sphere (n := n))

def attachingMap : Bool × Sphere (n := n) → c.DoublePunctured d
  | (false, z) => c.firstBoundaryMap d hdisj z
  | (true, z) => c.secondBoundaryMap d hdisj (a z)

theorem attachingMap_injective : Injective (attachingMap c d hdisj a) := by
  rintro ⟨b, z⟩ ⟨e, w⟩ h
  cases b <;> cases e
  · exact Prod.ext rfl (c.firstBoundaryMap_injective d hdisj h)
  · exact False.elim (c.firstBoundaryMap_ne_secondBoundaryMap d hdisj z (a w) h)
  · exact False.elim (c.firstBoundaryMap_ne_secondBoundaryMap d hdisj w (a z) h.symm)
  · exact Prod.ext rfl (a.injective (c.secondBoundaryMap_injective d hdisj h))

theorem continuous_attachingMap : Continuous (attachingMap c d hdisj a) := by
  apply continuous_prod_of_discrete_left.mpr
  intro b
  cases b
  · exact c.continuous_firstBoundaryMap d hdisj
  · exact (c.continuous_secondBoundaryMap d hdisj).comp a.continuous

abbrev Quotient := AdjunctionSpace (boundaryInclusion (n := n)) (attachingMap c d hdisj a)

def coreInclusion : c.DoublePunctured d → Quotient c d hdisj a :=
  adjunctionLower (i := boundaryInclusion) (attachingMap c d hdisj a)

def bandInclusion : Band (n := n) → Quotient c d hdisj a :=
  adjunctionCell boundaryInclusion (attachingMap c d hdisj a)

theorem seam_eq (q : Bool × Sphere (n := n)) :
    bandInclusion c d hdisj a (boundaryInclusion q) =
      coreInclusion c d hdisj a (attachingMap c d hdisj a q) :=
  adjunction_coherence _ _ q

theorem continuous_coreInclusion : Continuous (coreInclusion c d hdisj a) :=
  continuous_adjunctionLower _ _

theorem continuous_bandInclusion : Continuous (bandInclusion c d hdisj a) :=
  continuous_adjunctionCell _ _

theorem coreInclusion_injective : Injective (coreInclusion c d hdisj a) :=
  Manifold.Attachment.adjunctionLower_injective _ _ boundaryInclusion_injective

theorem bandInclusion_injective : Injective (bandInclusion c d hdisj a) :=
  Manifold.Attachment.adjunctionCell_injective _ _ (attachingMap_injective c d hdisj a)

theorem bandInclusion_eq_coreInclusion_iff (q : Band (n := n)) (x : c.DoublePunctured d) :
    bandInclusion c d hdisj a q = coreInclusion c d hdisj a x ↔
      ∃ z, boundaryInclusion z = q ∧ attachingMap c d hdisj a z = x :=
  Manifold.Attachment.adjunctionCell_eq_lower_iff _ _ boundaryInclusion_injective q x

theorem inclusions_cover :
    range (bandInclusion c d hdisj a) ∪ range (coreInclusion c d hdisj a) = univ :=
  Manifold.Attachment.adjunction_inclusions_cover _ _

theorem inclusions_inter :
    range (bandInclusion c d hdisj a) ∩ range (coreInclusion c d hdisj a) =
      range (bandInclusion c d hdisj a ∘ boundaryInclusion) :=
  Manifold.Attachment.adjunction_inclusions_inter _ _ boundaryInclusion_injective

instance instT2Space [T2Space M] : T2Space (Quotient c d hdisj a) :=
  Manifold.Attachment.adjunction_t2Space _ _ boundaryInclusion_injective
    (attachingMap_injective c d hdisj a) continuous_boundaryInclusion
    (continuous_attachingMap c d hdisj a)

instance instCompactSpace [CompactSpace M] : CompactSpace (Quotient c d hdisj a) :=
  _root_.Quot.compactSpace

theorem isClosedEmbedding_coreInclusion [T2Space M] :
    _root_.Topology.IsClosedEmbedding (coreInclusion c d hdisj a) :=
  Manifold.Attachment.isClosedEmbedding_adjunctionLower _ _ boundaryInclusion_injective
    (attachingMap_injective c d hdisj a) continuous_boundaryInclusion
    (continuous_attachingMap c d hdisj a)

theorem isClosedEmbedding_bandInclusion [T2Space M] :
    _root_.Topology.IsClosedEmbedding (bandInclusion c d hdisj a) :=
  Manifold.Attachment.isClosedEmbedding_adjunctionCell _ _ boundaryInclusion_injective
    (attachingMap_injective c d hdisj a) continuous_boundaryInclusion
    (continuous_attachingMap c d hdisj a)

end SelfAttachment
end DifferentialGeometry.Topology
