import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DiscardedCapMaps

set_option autoImplicit false

noncomputable section

open Set Function

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology

variable {M Q D N Y : Type*} [TopologicalSpace M] [TopologicalSpace Q]
  [TopologicalSpace D] [TopologicalSpace N] [TopologicalSpace Y]
  (E : CutCapTopology M Q D N)

private abbrev DiscardedPieces :=
  {x : E.tubes.core // x ∉ E.retainedCore} ⊕
    (Σ _b : {b : E.tubes.Boundary // E.capDiscarded b}, ThreeBall)

private def discardedPieceMap : C(E.DiscardedPieces, D) :=
  ⟨Sum.elim E.discardedCoreInclusion (fun p => E.discardedCap p.1.1 p.1.2 p.2),
    E.discardedCoreInclusion.continuous.sumElim
      (continuous_sigma fun b => (E.discardedCap b.1 b.2).continuous)⟩

private theorem discardedPieceMap_surjective : Surjective E.discardedPieceMap := by
  intro d
  have hd : d ∈ range E.discardedCoreInclusion ∪
      (⋃ b : {b : E.tubes.Boundary // E.capDiscarded b}, range (E.discardedCap b.1 b.2)) := by
    rw [E.discardedCoreInclusion_union_discardedCaps]
    exact mem_univ d
  rcases hd with ⟨x, rfl⟩ | hd
  · exact ⟨Sum.inl x, rfl⟩
  · obtain ⟨b, x, rfl⟩ := mem_iUnion.mp hd
    exact ⟨Sum.inr ⟨b, x⟩, rfl⟩

private theorem discardedPieceMap_isQuotientMap [CompactSpace {x : E.tubes.core // x ∉ E.retainedCore}] [T2Space D] :
    _root_.Topology.IsQuotientMap E.discardedPieceMap := by
  exact E.discardedPieceMap.continuous.isClosedMap.isQuotientMap
    E.discardedPieceMap.continuous E.discardedPieceMap_surjective

theorem discarded_map_ext {Z : Type*} {f g : D → Z}
    (hCore : ∀ x, f (E.discardedCoreInclusion x) = g (E.discardedCoreInclusion x))
    (hCap : ∀ (b : {b : E.tubes.Boundary // E.capDiscarded b}) x,
      f (E.discardedCap b.1 b.2 x) = g (E.discardedCap b.1 b.2 x)) : f = g := by
  funext d
  obtain ⟨x, rfl⟩ := E.discardedPieceMap_surjective d
  rcases x with x | ⟨b, x⟩
  · exact hCore x
  · exact hCap b x

variable (fCore : C({x : E.tubes.core // x ∉ E.retainedCore}, Y))
  (fCap : (b : {b : E.tubes.Boundary // E.capDiscarded b}) → C(ThreeBall, Y))
  (hboundary : ∀ (b : {b : E.tubes.Boundary // E.capDiscarded b}) (y : Sphere 2),
    fCap b (sphereToThreeBall y) = fCore
      ⟨E.tubes.coreBoundarySphere b.1 (E.capping.attaching b.1 y),
        E.capDiscarded_coreBoundarySphere_not_mem_retainedCore b.1 b.2 _⟩)

private def discardedPieceFunction : C(E.DiscardedPieces, Y) :=
  ⟨Sum.elim fCore (fun p => fCap p.1 p.2),
    fCore.continuous.sumElim (continuous_sigma fun b => (fCap b).continuous)⟩

include hboundary

private theorem discardedCore_cap_compatible
    (x : {x : E.tubes.core // x ∉ E.retainedCore})
    (b : {b : E.tubes.Boundary // E.capDiscarded b}) (y : ThreeBall)
    (hxy : E.discardedCoreInclusion x = E.discardedCap b.1 b.2 y) :
    fCore x = fCap b y := by
  have hmem : E.discardedCap b.1 b.2 y ∈
      range E.discardedCoreInclusion ∩ range (E.discardedCap b.1 b.2) :=
    ⟨⟨x, hxy⟩, mem_range_self y⟩
  rw [E.discardedCoreInclusion_inter_discardedCap b.1 b.2] at hmem
  obtain ⟨z, hz⟩ := hmem
  have hy : sphereToThreeBall z = y := (E.discardedCap_isEmbedding b.1 b.2).injective hz
  subst y
  have hx : x = ⟨E.tubes.coreBoundarySphere b.1 (E.capping.attaching b.1 z),
      E.capDiscarded_coreBoundarySphere_not_mem_retainedCore b.1 b.2 _⟩ :=
    E.discardedCoreInclusion_isEmbedding.injective
      (hxy.trans (E.discardedCap_boundary b.1 b.2 z))
  rw [hx]
  exact (hboundary b z).symm

private theorem discardedPieceFunction_factorsThrough :
    FactorsThrough (E.discardedPieceFunction fCore fCap) E.discardedPieceMap := by
  rintro (x | ⟨b, x⟩) (y | ⟨c, y⟩) hxy
  · exact congrArg fCore (E.discardedCoreInclusion_isEmbedding.injective hxy)
  · exact E.discardedCore_cap_compatible fCore fCap hboundary x c y hxy
  · exact (E.discardedCore_cap_compatible fCore fCap hboundary y b x hxy.symm).symm
  · by_cases hbc : b = c
    · subst c
      exact congrArg (fCap b) ((E.discardedCap_isEmbedding b.1 b.2).injective hxy)
    · exact (disjoint_left.mp (E.pairwise_disjoint_discardedCaps hbc)
        (mem_range_self x) ⟨y, hxy.symm⟩).elim

def discardedDesc [CompactSpace {x : E.tubes.core // x ∉ E.retainedCore}] [T2Space D] : C(D, Y) :=
  E.discardedPieceMap_isQuotientMap.lift (E.discardedPieceFunction fCore fCap)
    (E.discardedPieceFunction_factorsThrough fCore fCap hboundary)

@[simp] theorem discardedDesc_core [CompactSpace {x : E.tubes.core // x ∉ E.retainedCore}] [T2Space D]
    (x : {x : E.tubes.core // x ∉ E.retainedCore}) :
    E.discardedDesc fCore fCap hboundary (E.discardedCoreInclusion x) = fCore x :=
  congrArg (fun f : C(E.DiscardedPieces, Y) => f (Sum.inl x))
    (E.discardedPieceMap_isQuotientMap.lift_comp (E.discardedPieceFunction fCore fCap)
      (E.discardedPieceFunction_factorsThrough fCore fCap hboundary))

@[simp] theorem discardedDesc_cap [CompactSpace {x : E.tubes.core // x ∉ E.retainedCore}] [T2Space D]
    (b : {b : E.tubes.Boundary // E.capDiscarded b}) (x : ThreeBall) :
    E.discardedDesc fCore fCap hboundary (E.discardedCap b.1 b.2 x) = fCap b x :=
  congrArg (fun f : C(E.DiscardedPieces, Y) => f (Sum.inr ⟨b, x⟩))
    (E.discardedPieceMap_isQuotientMap.lift_comp (E.discardedPieceFunction fCore fCap)
      (E.discardedPieceFunction_factorsThrough fCore fCap hboundary))

theorem discardedDesc_unique [CompactSpace {x : E.tubes.core // x ∉ E.retainedCore}] [T2Space D]
    (f : C(D, Y))
    (hCore : ∀ x, f (E.discardedCoreInclusion x) = fCore x)
    (hCap : ∀ b x, f (E.discardedCap b.1 b.2 x) = fCap b x) :
    f = E.discardedDesc fCore fCap hboundary := by
  apply DFunLike.ext'
  exact E.discarded_map_ext
    (fun x => (hCore x).trans (E.discardedDesc_core fCore fCap hboundary x).symm)
    (fun b x => (hCap b x).trans (E.discardedDesc_cap fCore fCap hboundary b x).symm)

theorem exists_unique_continuousMap_discarded_of_boundary_eq
    [CompactSpace {x : E.tubes.core // x ∉ E.retainedCore}] [T2Space D] :
    ∃! f : C(D, Y),
      (∀ x, f (E.discardedCoreInclusion x) = fCore x) ∧
      ∀ b x, f (E.discardedCap b.1 b.2 x) = fCap b x := by
  refine ⟨E.discardedDesc fCore fCap hboundary, ⟨?_, ?_⟩, ?_⟩
  · exact E.discardedDesc_core fCore fCap hboundary
  · exact E.discardedDesc_cap fCore fCap hboundary
  · intro f hf
    exact E.discardedDesc_unique fCore fCap hboundary f hf.1 hf.2

theorem exists_unique_continuousMap_discarded_of_compact_core
    [CompactSpace E.tubes.core] [T2Space D] :
    ∃! f : C(D, Y),
      (∀ x, f (E.discardedCoreInclusion x) = fCore x) ∧
      ∀ b x, f (E.discardedCap b.1 b.2 x) = fCap b x := by
  let : CompactSpace {x : E.tubes.core // x ∉ E.retainedCore} :=
    isCompact_iff_compactSpace.mp E.isClopen_retainedCore.isOpen.isClosed_compl.isCompact
  exact E.exists_unique_continuousMap_discarded_of_boundary_eq fCore fCap hboundary

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology
