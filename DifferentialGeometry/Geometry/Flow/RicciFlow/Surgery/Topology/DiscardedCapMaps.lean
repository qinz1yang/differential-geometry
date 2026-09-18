import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedSideRelativeCollar
import DifferentialGeometry.Topology.Covering.ImmersionLift
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph

set_option autoImplicit false

noncomputable section

open Set Manifold
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace CutCapTopology

variable {M Q D N : Type*} [TopologicalSpace M] [TopologicalSpace Q]
  [TopologicalSpace D] [TopologicalSpace N] (E : CutCapTopology M Q D N)

def discardedCap (b : E.tubes.Boundary) (hb : E.capDiscarded b) : C(ThreeBall, D) where
  toFun := fun x => Classical.choose (hb x)
  continuous_toFun := by
    apply (_root_.Topology.IsEmbedding.inr (X := Q) (Y := D)).isInducing.continuous_iff.mpr
    exact (E.presentation.continuous.comp (E.capping.cap b).continuous).congr
      fun x => (Classical.choose_spec (hb x)).symm

@[simp] theorem inr_discardedCap (b : E.tubes.Boundary) (hb : E.capDiscarded b)
    (x : ThreeBall) :
    Sum.inr (E.discardedCap b hb x) = E.presentation (E.capping.cap b x) :=
  Classical.choose_spec (hb x)

theorem discardedCap_isEmbedding (b : E.tubes.Boundary) (hb : E.capDiscarded b) :
    _root_.Topology.IsEmbedding (E.discardedCap b hb) := by
  apply (_root_.Topology.IsEmbedding.inr (X := Q) (Y := D)).of_comp_iff.mp
  have heq : (Sum.inr : D → Q ⊕ D) ∘ E.discardedCap b hb =
      E.presentation ∘ E.capping.cap b := funext fun x => E.inr_discardedCap b hb x
  rw [heq]
  exact E.presentation.isEmbedding.comp (E.capping.capEmbedding b)

private theorem core_presentation_mem_range_inr (x : {x : E.tubes.core // x ∉ E.retainedCore}) :
    E.presentation (E.capping.coreInclusion x.1) ∈ range (Sum.inr : D → Q ⊕ D) := by
  cases h : E.presentation (E.capping.coreInclusion x.1) with
  | inl q => exact (x.2 ⟨q, h⟩).elim
  | inr d => exact ⟨d, rfl⟩

def discardedCoreInclusion : C({x : E.tubes.core // x ∉ E.retainedCore}, D) where
  toFun := fun x => Classical.choose (E.core_presentation_mem_range_inr x)
  continuous_toFun := by
    apply (_root_.Topology.IsEmbedding.inr (X := Q) (Y := D)).isInducing.continuous_iff.mpr
    exact (E.presentation.continuous.comp
      (E.capping.coreInclusion.continuous.comp continuous_subtype_val)).congr
        fun x => (Classical.choose_spec (E.core_presentation_mem_range_inr x)).symm

@[simp] theorem inr_discardedCoreInclusion (x : {x : E.tubes.core // x ∉ E.retainedCore}) :
    Sum.inr (E.discardedCoreInclusion x) = E.presentation (E.capping.coreInclusion x.1) :=
  Classical.choose_spec (E.core_presentation_mem_range_inr x)

theorem discardedCoreInclusion_isEmbedding :
    _root_.Topology.IsEmbedding E.discardedCoreInclusion := by
  apply (_root_.Topology.IsEmbedding.inr (X := Q) (Y := D)).of_comp_iff.mp
  have heq : (Sum.inr : D → Q ⊕ D) ∘ E.discardedCoreInclusion =
      E.presentation ∘ E.capping.coreInclusion ∘ Subtype.val :=
    funext fun x => E.inr_discardedCoreInclusion x
  rw [heq]
  exact E.presentation.isEmbedding.comp
    (E.capping.coreEmbedding.comp _root_.Topology.IsEmbedding.subtypeVal)

theorem discardedCap_boundary (b : E.tubes.Boundary) (hb : E.capDiscarded b)
    (y : Sphere 2) :
    E.discardedCap b hb (sphereToThreeBall y) =
      E.discardedCoreInclusion
        ⟨E.tubes.coreBoundarySphere b (E.capping.attaching b y),
          E.capDiscarded_coreBoundarySphere_not_mem_retainedCore b hb _⟩ := by
  apply Sum.inr_injective (α := Q)
  rw [E.inr_discardedCap, E.inr_discardedCoreInclusion, E.capping.boundary_eq]

theorem pairwise_disjoint_discardedCaps :
    Pairwise fun b c : {b : E.tubes.Boundary // E.capDiscarded b} =>
      Disjoint (range (E.discardedCap b.1 b.2)) (range (E.discardedCap c.1 c.2)) := by
  intro b c hbc
  apply disjoint_left.mpr
  rintro d ⟨x, rfl⟩ ⟨y, hy⟩
  apply disjoint_left.mp (E.capping.cap_disjoint (fun h => hbc (Subtype.ext h)))
    (mem_range_self x)
  refine ⟨y, E.presentation.injective ?_⟩
  rw [← E.inr_discardedCap b.1 b.2 x, ← E.inr_discardedCap c.1 c.2 y, hy]

theorem discardedCoreInclusion_inter_discardedCap (b : E.tubes.Boundary)
    (hb : E.capDiscarded b) :
    range E.discardedCoreInclusion ∩ range (E.discardedCap b hb) =
      range (fun y : Sphere 2 => E.discardedCap b hb (sphereToThreeBall y)) := by
  ext d
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, rfl⟩⟩
    have hxy : E.capping.coreInclusion x.1 = E.capping.cap b y := by
      apply E.presentation.injective
      rw [← E.inr_discardedCoreInclusion x, ← E.inr_discardedCap b hb y, hx]
    have hmem : E.capping.cap b y ∈
        range E.capping.coreInclusion ∩ range (E.capping.cap b) :=
      ⟨⟨x.1, hxy⟩, mem_range_self y⟩
    rw [E.capping.core_cap_intersection b] at hmem
    obtain ⟨z, hz⟩ := hmem
    refine ⟨(E.capping.attaching b).symm z, ?_⟩
    apply Sum.inr_injective (α := Q)
    rw [E.inr_discardedCap, E.inr_discardedCap, E.capping.boundary_eq,
      (E.capping.attaching b).apply_symm_apply]
    exact congrArg E.presentation hz
  · rintro ⟨y, rfl⟩
    exact ⟨⟨⟨E.tubes.coreBoundarySphere b (E.capping.attaching b y),
      E.capDiscarded_coreBoundarySphere_not_mem_retainedCore b hb _⟩,
      (E.discardedCap_boundary b hb y).symm⟩, mem_range_self _⟩

theorem discardedCoreInclusion_union_discardedCaps :
    range E.discardedCoreInclusion ∪
      (⋃ b : {b : E.tubes.Boundary // E.capDiscarded b}, range (E.discardedCap b.1 b.2)) =
      univ := by
  apply eq_univ_of_forall
  intro d
  have hmem : E.presentation.symm (Sum.inr d) ∈
      range E.capping.coreInclusion ∪ (⋃ b, range (E.capping.cap b)) := by
    rw [E.capping.exhaustive]
    exact mem_univ _
  rcases hmem with ⟨x, hx⟩ | hcap
  · have hxpres : E.presentation (E.capping.coreInclusion x) = Sum.inr d := by
      rw [hx, E.presentation.apply_symm_apply]
    have hxd : x ∉ E.retainedCore := by
      rintro ⟨q, hq⟩
      exact Sum.inr_ne_inl (hxpres.symm.trans hq)
    left
    refine ⟨⟨x, hxd⟩, ?_⟩
    apply Sum.inr_injective (α := Q)
    exact (E.inr_discardedCoreInclusion _).trans hxpres
  · obtain ⟨b, y, hy⟩ := mem_iUnion.mp hcap
    have hypres : E.presentation (E.capping.cap b y) = Sum.inr d := by
      rw [hy, E.presentation.apply_symm_apply]
    have hb : E.capDiscarded b := by
      rcases E.cap_retained_or_discarded b with hr | hd
      · obtain ⟨q, hq⟩ := hr y
        exact (Sum.inl_ne_inr (hq.trans hypres)).elim
      · exact hd
    right
    apply mem_iUnion.mpr
    refine ⟨⟨b, hb⟩, y, ?_⟩
    apply Sum.inr_injective (α := Q)
    exact (E.inr_discardedCap b hb y).trans hypres

end CutCapTopology

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

theorem discardedCap_contMDiff (b : E.trace.tubes.Boundary) (hb : E.trace.capDiscarded b) :
    let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
    ContMDiff (𝓡∂ 3) ThreeModel ∞ (E.trace.discardedCap b hb) := by
  let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  apply contMDiff_of_contMDiff_inr (N := Q.Carrier)
  have heq : (Sum.inr : D.Carrier → Q.Carrier ⊕ D.Carrier) ∘ E.trace.discardedCap b hb =
      E.presentation ∘ E.trace.capping.cap b := by
    funext x
    simp only [Function.comp_apply]
    rw [E.trace.inr_discardedCap, E.presentation_eq]
  rw [heq]
  exact E.presentation.contMDiff.comp (E.cap_smooth b).contMDiff

theorem discardedCap_isSmoothEmbedding (b : E.trace.tubes.Boundary)
    (hb : E.trace.capDiscarded b) :
    let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (E.trace.discardedCap b hb) := by
  let : ChartedSpace (EuclideanHalfSpace 3) ThreeBall := E.ballCharts
  have hinr : IsLocalDiffeomorph ThreeModel ThreeModel ∞
      (Sum.inr : D.Carrier → Q.Carrier ⊕ D.Carrier) := by
    apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
      ContMDiff.inr
    · intro x
      rw [mfderiv_sumInr]
      exact Function.injective_id
    · rfl
  apply DifferentialGeometry.Topology.isSmoothEmbedding_of_lift_through_localDiffeomorph hinr
    (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp
      (𝓡∂ 3) ThreeModel _ (E.cap_smooth b) E.presentation)
    (E.trace.discardedCap b hb).continuous
  intro x
  simp only [Function.comp_apply]
  rw [E.trace.inr_discardedCap, E.presentation_eq]

end SmoothCutCapTransition

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

def discardedCoreCollar (b : (H.event i).transition.trace.tubes.Boundary)
    (hb : (H.event i).transition.trace.capDiscarded b) :
    C(Sphere 2 × Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1)), (H.event i).discarded.Carrier) :=
  (H.event i).transition.trace.discardedCoreInclusion.comp
    ⟨fun q => ⟨G.coreCollar b q,
        G.coreCollar_not_mem_retainedCore_of_capDiscarded b hb sphereNorth q⟩,
      (G.coreCollar_isOpenEmbedding b).continuous.subtype_mk _⟩

@[simp] theorem inr_discardedCoreCollar
    (b : (H.event i).transition.trace.tubes.Boundary)
    (hb : (H.event i).transition.trace.capDiscarded b)
    (q : Sphere 2 × Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1))) :
    Sum.inr (G.discardedCoreCollar b hb q) =
      (H.event i).transition.trace.presentation
        ((H.event i).transition.trace.capping.coreInclusion (G.coreCollar b q)) :=
  (H.event i).transition.trace.inr_discardedCoreInclusion _

theorem discardedCoreCollar_isEmbedding
    (b : (H.event i).transition.trace.tubes.Boundary)
    (hb : (H.event i).transition.trace.capDiscarded b) :
    _root_.Topology.IsEmbedding (G.discardedCoreCollar b hb) :=
  (H.event i).transition.trace.discardedCoreInclusion_isEmbedding.comp
    (_root_.Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
      (G.coreCollar_isOpenEmbedding b).isEmbedding)

theorem discardedCap_eq_discardedCoreCollar_zero
    (b : (H.event i).transition.trace.tubes.Boundary)
    (hb : (H.event i).transition.trace.capDiscarded b) (y : Sphere 2) :
    (H.event i).transition.trace.discardedCap b hb (sphereToThreeBall y) =
      G.discardedCoreCollar b hb
        ((H.event i).transition.trace.capping.attaching b y,
          ⟨0, le_rfl, cuttingCollarWidth_pos (G.delta_pos b.1)⟩) := by
  apply Sum.inr_injective (α := (H.stage i.succ).Carrier)
  rw [(H.event i).transition.trace.inr_discardedCap, G.inr_discardedCoreCollar,
    G.coreCollar_zero, (H.event i).transition.trace.capping.boundary_eq]

theorem discardedCoreCollar_contMDiff
    (b : (H.event i).transition.trace.tubes.Boundary)
    (hb : (H.event i).transition.trace.capDiscarded b) :
    let : ChartedSpace (EuclideanHalfSpace 1)
        (Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1))) :=
      DifferentialGeometry.Topology.Manifold.halfClosedIntervalChartedSpace
        (cuttingCollarWidth_pos (G.delta_pos b.1))
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (G.discardedCoreCollar b hb) := by
  let : ChartedSpace (EuclideanHalfSpace 1)
      (Ico (0 : ℝ) (cuttingCollarWidth (G.delta b.1))) :=
    DifferentialGeometry.Topology.Manifold.halfClosedIntervalChartedSpace
      (cuttingCollarWidth_pos (G.delta_pos b.1))
  apply contMDiff_of_contMDiff_inr (N := (H.stage i.succ).Carrier)
  have heq : (Sum.inr : (H.event i).discarded.Carrier →
        (H.stage i.succ).Carrier ⊕ (H.event i).discarded.Carrier) ∘ G.discardedCoreCollar b hb =
      (H.event i).transition.presentation ∘
        (H.event i).transition.trace.capping.coreInclusion ∘ G.coreCollar b := by
    funext q
    simp only [Function.comp_apply]
    rw [G.inr_discardedCoreCollar, (H.event i).transition.presentation_eq]
  rw [heq]
  let : ChartedSpace (EuclideanHalfSpace 3) (H.event i).transition.trace.tubes.core :=
    (H.event i).transition.coreCharts
  exact (H.event i).transition.presentation.contMDiff.comp
    ((H.event i).transition.core_inclusion_smooth.contMDiff.comp (G.coreCollar_contMDiff b))

theorem pairwise_disjoint_discardedCoreCollars :
    Pairwise fun b c : {b : (H.event i).transition.trace.tubes.Boundary //
        (H.event i).transition.trace.capDiscarded b} =>
      Disjoint (range (G.discardedCoreCollar b.1 b.2))
        (range (G.discardedCoreCollar c.1 c.2)) := by
  intro b c hbc
  apply disjoint_left.mpr
  rintro d ⟨x, rfl⟩ ⟨y, hy⟩
  apply disjoint_left.mp (G.pairwise_disjoint_coreCollars
    (fun h => hbc (Subtype.ext h))) (mem_range_self x)
  refine ⟨y, (H.event i).transition.trace.capping.coreEmbedding.injective
    ((H.event i).transition.trace.presentation.injective ?_)⟩
  rw [← G.inr_discardedCoreCollar b.1 b.2 x,
    ← G.inr_discardedCoreCollar c.1 c.2 y, hy]

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
