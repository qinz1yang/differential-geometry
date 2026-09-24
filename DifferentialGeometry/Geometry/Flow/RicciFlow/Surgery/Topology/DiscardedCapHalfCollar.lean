import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapMaps
import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollarHalf

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

universe u

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)
  (b : E.trace.tubes.Boundary) (hb : E.trace.capDiscarded b)
  (c : DifferentialGeometry.Topology.SmoothTwoSidedCollar (𝓡 2) ThreeModel
    (fun s : Sphere 2 => E.trace.discardedCap b hb (sphereToThreeBall s)))
  (capSide : C({q : Sphere 2 × DifferentialGeometry.Topology.symmetricOpenInterval c.radius //
    q.2.val ≤ 0}, ThreeBall))

def discardedCapHalfCollar : C(Sphere 2 × Ico (0 : ℝ) c.radius, ThreeBall) :=
  capSide.comp ⟨c.negativeHalfHomeomorph, c.negativeHalfHomeomorph.continuous⟩

variable (hcap : ∀ q (hq : q.2.val ≤ 0),
  c.toFun q = E.trace.discardedCap b hb (capSide ⟨q, hq⟩))

include hcap

theorem discardedCap_comp_discardedCapHalfCollar :
    E.trace.discardedCap b hb ∘ E.discardedCapHalfCollar b hb c capSide =
      c.negativeHalfCollar := by
  funext p
  exact (hcap (c.negativeHalfHomeomorph p).val (c.negativeHalfHomeomorph p).property).symm

theorem discardedCapHalfCollar_isEmbedding :
    _root_.Topology.IsEmbedding (E.discardedCapHalfCollar b hb c capSide) := by
  apply (E.trace.discardedCap_isEmbedding b hb).of_comp_iff.mp
  rw [E.discardedCap_comp_discardedCapHalfCollar b hb c capSide hcap]
  exact c.negativeHalfCollar_isEmbedding

theorem discardedCapHalfCollar_contMDiff :
    letI := E.ballCharts
    letI := DifferentialGeometry.Topology.Manifold.halfClosedIntervalChartedSpace c.radius_pos
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ∞
      (E.discardedCapHalfCollar b hb c capSide) := by
  let := E.ballCharts
  let := DifferentialGeometry.Topology.Manifold.halfClosedIntervalChartedSpace c.radius_pos
  apply (ContMDiff.iff_comp_isImmersion (E.discardedCap_isSmoothEmbedding b hb).isImmersion).mpr
  refine ⟨(E.discardedCapHalfCollar b hb c capSide).continuous, ?_⟩
  rw [E.discardedCap_comp_discardedCapHalfCollar b hb c capSide hcap]
  exact c.negativeHalfCollar_contMDiff

@[simp] theorem discardedCapHalfCollar_zero (s : Sphere 2) :
    E.discardedCapHalfCollar b hb c capSide (s, ⟨0, le_rfl, c.radius_pos⟩) =
      sphereToThreeBall s := by
  apply (E.trace.discardedCap_isEmbedding b hb).injective
  have h := congrFun (E.discardedCap_comp_discardedCapHalfCollar b hb c capSide hcap)
    (s, ⟨0, le_rfl, c.radius_pos⟩)
  exact h.trans (c.negativeHalfCollar_zero s)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.SmoothCutCapTransition

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord

universe u

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)
  (b : (H.event i).transition.trace.tubes.Boundary)
  (hb : (H.event i).transition.trace.capDiscarded b)
  (c : DifferentialGeometry.Topology.SmoothTwoSidedCollar (𝓡 2) ThreeModel
    (fun s : Sphere 2 => (H.event i).transition.trace.discardedCap b hb (sphereToThreeBall s)))
  (hwidth : c.radius ≤ cuttingCollarWidth (G.delta b.1))
  (hcore : ∀ q (hq : 0 ≤ q.2.val), c.toFun q = G.discardedCoreCollar b hb
    ((H.event i).transition.trace.capping.attaching b q.1,
      ⟨q.2.val, hq, q.2.property.2.trans_le hwidth⟩))

include hcore

theorem discardedCollar_pos_not_mem_range_discardedCap
    (q : Sphere 2 × DifferentialGeometry.Topology.symmetricOpenInterval c.radius)
    (hq : 0 < q.2.val) :
    c.toFun q ∉ range ((H.event i).transition.trace.discardedCap b hb) := by
  intro hcap
  have hmem : c.toFun q ∈ range (H.event i).transition.trace.discardedCoreInclusion ∩
      range ((H.event i).transition.trace.discardedCap b hb) := by
    refine ⟨?_, hcap⟩
    rw [hcore q hq.le]
    exact mem_range_self _
  rw [(H.event i).transition.trace.discardedCoreInclusion_inter_discardedCap b hb] at hmem
  obtain ⟨y, hy⟩ := hmem
  have heq := c.isOpenEmbedding_toFun.injective ((c.toFun_zero y).trans hy)
  have ht : (0 : ℝ) = q.2.val := congrArg
    (fun p : Sphere 2 × DifferentialGeometry.Topology.symmetricOpenInterval c.radius =>
      p.2.val) heq
  exact (ne_of_gt hq) ht.symm

variable (capSide : C({q : Sphere 2 × DifferentialGeometry.Topology.symmetricOpenInterval c.radius //
    q.2.val ≤ 0}, ThreeBall))
  (hcap : ∀ q (hq : q.2.val ≤ 0), c.toFun q =
    (H.event i).transition.trace.discardedCap b hb (capSide ⟨q, hq⟩))

include hcap

theorem range_discardedCapHalfCollar :
    range ((H.event i).transition.discardedCapHalfCollar b hb c capSide) =
      (H.event i).transition.trace.discardedCap b hb ⁻¹'
        (c.neighborhood : Set (H.event i).discarded.Carrier) := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    have h := congrFun
      ((H.event i).transition.discardedCap_comp_discardedCapHalfCollar b hb c capSide hcap) p
    rw [Function.comp_apply] at h
    change (H.event i).transition.trace.discardedCap b hb
      ((H.event i).transition.discardedCapHalfCollar b hb c capSide p) ∈ c.neighborhood
    rw [h]
    exact (c.toDiffeomorph (c.negativeHalfHomeomorph p).val).property
  · intro hx
    let q := c.toDiffeomorph.symm ⟨(H.event i).transition.trace.discardedCap b hb x, hx⟩
    have hq : c.toFun q = (H.event i).transition.trace.discardedCap b hb x :=
      congrArg Subtype.val (c.toDiffeomorph.apply_symm_apply
        ⟨(H.event i).transition.trace.discardedCap b hb x, hx⟩)
    have hnonpos : q.2.val ≤ 0 := by
      by_contra h
      have hpos := lt_of_not_ge h
      exact G.discardedCollar_pos_not_mem_range_discardedCap b hb c hwidth hcore q hpos
        ⟨x, hq.symm⟩
    let p := c.negativeHalfHomeomorph.symm ⟨q, hnonpos⟩
    refine ⟨p, ?_⟩
    apply ((H.event i).transition.trace.discardedCap_isEmbedding b hb).injective
    have h := congrFun
      ((H.event i).transition.discardedCap_comp_discardedCapHalfCollar b hb c capSide hcap) p
    change (H.event i).transition.trace.discardedCap b hb
      ((H.event i).transition.discardedCapHalfCollar b hb c capSide p) =
        c.toFun (c.negativeHalfHomeomorph p).val at h
    rw [show c.negativeHalfHomeomorph p = ⟨q, hnonpos⟩ from
      c.negativeHalfHomeomorph.apply_symm_apply _] at h
    exact h.trans hq

theorem discardedCapHalfCollar_isOpenEmbedding :
    _root_.Topology.IsOpenEmbedding
      ((H.event i).transition.discardedCapHalfCollar b hb c capSide) := by
  refine ⟨(H.event i).transition.discardedCapHalfCollar_isEmbedding b hb c capSide hcap, ?_⟩
  rw [G.range_discardedCapHalfCollar b hb c hwidth hcore capSide hcap]
  exact c.neighborhood.isOpen.preimage
    ((H.event i).transition.trace.discardedCap b hb).continuous

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.GeometricCutoffRecord
