import DifferentialGeometry.Topology.Manifold.DisjointUnion
import DifferentialGeometry.Topology.ThreeManifold.MarkedBallTubeProducer
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundarySource

noncomputable section

open Bundle Manifold Set Topology TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u

private theorem disjoint_sigmaMk_image_of_ne {ι : Type u} {M : ι → Type u} {i i' : ι}
    (h : i ≠ i') (A : Set (M i)) (B : Set (M i')) :
    Disjoint (Sigma.mk i '' A) (Sigma.mk i' '' B) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, -, rfl⟩ ⟨b, -, hb⟩
  exact h (congrArg Sigma.fst hb).symm

private theorem disjoint_sigmaMk_image {ι : Type u} {M : ι → Type u} {i : ι}
    {A B : Set (M i)} (h : Disjoint A B) :
    Disjoint (Sigma.mk i '' A) (Sigma.mk i '' B) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
  exact Set.disjoint_left.mp h ha ((sigma_mk_injective hba).symm ▸ hb)

private theorem disjoint_sigmaMk_image_of_eq {ι : Type u} {M : ι → Type u} {i i' : ι}
    (h : i = i') {A : Set (M i)} {B : Set (M i')} (hd : Disjoint A (h ▸ B)) :
    Disjoint (Sigma.mk i '' A) (Sigma.mk i' '' B) := by
  cases h
  exact disjoint_sigmaMk_image hd

private theorem connectedComponents_mk_sigmaMk_eq_iff {ι : Type u} {M : ι → Type u}
    [∀ i, TopologicalSpace (M i)] [∀ i, PreconnectedSpace (M i)]
    {i i' : ι} (y : M i) (y' : M i') :
    ConnectedComponents.mk (⟨i, y⟩ : Σ j, M j) = ConnectedComponents.mk (⟨i', y'⟩ : Σ j, M j) ↔
      i = i' := by
  constructor
  · intro h
    have hmem : (⟨i', y'⟩ : Σ j, M j) ∈ connectedComponent (⟨i, y⟩ : Σ j, M j) :=
      (ConnectedComponents.coe_eq_coe').mp h.symm
    have hsub := isPreconnected_connectedComponent.subset_isClopen isClopen_range_sigmaMk
      ⟨⟨i, y⟩, mem_connectedComponent, ⟨y, rfl⟩⟩
    obtain ⟨z, hz⟩ := hsub hmem
    exact (Sigma.mk.inj_iff.mp hz).1
  · rintro rfl
    rw [ConnectedComponents.coe_eq_coe']
    exact (isPreconnected_univ.image _
        continuous_sigmaMk.continuousOn).subset_connectedComponent ⟨y', trivial, rfl⟩
      ⟨y, trivial, rfl⟩

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

local instance localClosedCellCharted : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
local instance localClosedCellIsManifold : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

abbrev vertexSum : ClosedOrientedManifold.{u} 3 :=
  closedOrientedUnion fun v => (G.vertexManifold v).toClosedOrientedManifold

theorem vertexSum_carrier :
    (vertexSum G).Carrier = (Σ v, (G.vertexManifold v).Carrier) := rfl

theorem vertexSum_orientation (v : G.Vertex) (y : (G.vertexManifold v).Carrier) :
    (vertexSum G).orientation.orientation (⟨v, y⟩ : Σ w, (G.vertexManifold w).Carrier) =
      (G.vertexManifold v).orientation.orientation y := rfl

def flagMarkedBall (e : G.Edge) : MarkedBall (vertexSum G) where
  ball x := (⟨G.endpoint e false, (G.flag e false).ball x⟩ : (vertexSum G).Carrier)
  ball_embedding :=
    IsSmoothEmbedding.comp_of_smoothBoundary
      (isSmoothEmbedding_sigmaMk
        (M := fun v => (G.vertexManifold v).Carrier)
        (I := 𝓡 3) (n := ∞) (G.endpoint e false))
      (G.flag e false).ball_embedding
  collar := Sigma.mk (G.endpoint e false) '' (G.flag e false).collar
  collar_isOpen :=
    (IsOpenEmbedding.sigmaMk (i := G.endpoint e false)).isOpenMap _ (G.flag e false).collar_isOpen
  ball_subset_collar := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(G.flag e false).ball x,
      (G.flag e false).ball_subset_collar (mem_range_self x), rfl⟩
  collarBudget := (G.flag e false).collarBudget
  collarBudget_pos := (G.flag e false).collarBudget_pos

theorem flagMarkedBall_ball (e : G.Edge) (x : ClosedCell 3) :
    (flagMarkedBall G e).ball x =
      (⟨G.endpoint e false, (G.flag e false).ball x⟩ : (vertexSum G).Carrier) := rfl

theorem flagMarkedBall_collar (e : G.Edge) :
    (flagMarkedBall G e).collar =
      Sigma.mk (G.endpoint e false) '' (G.flag e false).collar := rfl

theorem flagMarkedBall_collar_disjoint (e e' : G.Edge) (h : e ≠ e') :
    Disjoint (flagMarkedBall G e).collar (flagMarkedBall G e').collar := by
  rw [flagMarkedBall_collar, flagMarkedBall_collar]
  by_cases hv : G.endpoint e false = G.endpoint e' false
  · refine disjoint_sigmaMk_image_of_eq hv ?_
    refine G.flag_collar_disjoint (G.endpoint e false) ⟨(e, false), rfl⟩ ⟨(e', false), hv.symm⟩ ?_
    intro heq
    exact h (Prod.mk.inj (Subtype.ext_iff.mp heq)).1
  · exact disjoint_sigmaMk_image_of_ne hv _ _

end MarkedManifoldGraph

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

open ClosedOrientedManifold

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

def initialPartialRealization : PartialRealization G ∅ where
  realization := vertexSum G
  vertexPiece v :=
    ⟨fun y => (⟨v, y.1⟩ : (vertexSum G).Carrier),
      continuous_sigmaMk.comp continuous_subtype_val⟩
  cylinderPiece e he := (Finset.notMem_empty e he).elim
  survivingFlag e _ := flagMarkedBall G e
  covers x := Or.inl ⟨x.1,
    ⟨x.2, by rw [removedBallSet_empty]; exact Set.notMem_empty x.2⟩, Sigma.eta x⟩
  survivingFlag_collar_disjoint e e' _ _ hne := flagMarkedBall_collar_disjoint G e e' hne

theorem componentCorrespondence_initialPartialRealization :
    (initialPartialRealization G).componentCorrespondence := by
  intro v v' y y'
  rw [show G.processedGraph ∅ = (⊥ : SimpleGraph G.Vertex) from Finset.sup_empty,
    SimpleGraph.reachable_bot]
  exact connectedComponents_mk_sigmaMk_eq_iff
    (M := fun w => (G.vertexManifold w).Carrier) y.1 y'.1

theorem cylinderComponentCovering_initialPartialRealization :
    (initialPartialRealization G).CylinderComponentCovering := by
  intro x
  exact ⟨x.1, ⟨x.2, by rw [removedBallSet_empty]; exact Set.notMem_empty x.2⟩,
    (congrArg ConnectedComponents.mk (Sigma.eta x)).symm⟩

end MarkedManifoldGraph

def HasSummandComponentDiffeomorph : Prop :=
  ∀ (ι : Type u) [Fintype ι] (M : ι → ClosedOrientedManifold.{u} 3) (i : ι)
    (y : (M i).Carrier),
    Nonempty (OrientedDiffeomorph
      ((closedOrientedUnion M).component
        (ConnectedComponents.mk (⟨i, y⟩ : (closedOrientedUnion M).Carrier))).toClosedOrientedManifold
      ((M i).component (ConnectedComponents.mk y)).toClosedOrientedManifold)

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

theorem hasBlockPresentation_initialPartialRealization (h : HasSummandComponentDiffeomorph.{u})
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    (initialPartialRealization G).HasBlockPresentation Z := by
  refine ⟨fun _ => 0, fun _ _ _ => rfl, fun v y => ?_⟩
  have hb : (finiteConnectedSum
      (G.vertexBlockList ∅ v ++ List.replicate 0 Z)).toClosedOrientedManifold =
      (G.vertexManifold v).toClosedOrientedManifold := by
    rw [vertexBlockList_empty, List.replicate_zero, List.append_nil, finiteConnectedSum_singleton]
  rw [hb]
  obtain ⟨e⟩ := h (G.Vertex) (fun w => (G.vertexManifold w).toClosedOrientedManifold) v y.1
  exact ⟨e.trans (ClosedOrientedManifold.componentOrientedDiffeomorph
    (G.vertexManifold v).toClosedOrientedManifold (ConnectedComponents.mk y.1))⟩

theorem isBlockInvariant_initialPartialRealization (h : HasSummandComponentDiffeomorph.{u})
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    (initialPartialRealization G).IsBlockInvariant Z :=
  ⟨componentCorrespondence_initialPartialRealization G,
    hasBlockPresentation_initialPartialRealization G h Z,
    cylinderComponentCovering_initialPartialRealization G⟩

theorem exists_initial_of_hasSummandComponentDiffeomorph (h : HasSummandComponentDiffeomorph.{u})
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    ∃ P : PartialRealization G ∅, P.IsBlockInvariant Z := by
  exact ⟨initialPartialRealization G, isBlockInvariant_initialPartialRealization G h Z⟩

end MarkedManifoldGraph

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

theorem hasBlockPresentation_of_blockStepLaw {Z : ConnectedClosedOrientedManifold.{u} 3}
    (h : BlockStepLaw G Z) :
    ∃ P : PartialRealization G ∅, P.HasBlockPresentation Z :=
  h.initial.imp fun _ hP => hP.2.1

theorem isBlockInvariant_iff_hasBlockPresentation {Z : ConnectedClosedOrientedManifold.{u} 3} :
    (initialPartialRealization G).IsBlockInvariant Z ↔
      (initialPartialRealization G).HasBlockPresentation Z :=
  ⟨fun h => h.2.1, fun h => ⟨componentCorrespondence_initialPartialRealization G, h,
    cylinderComponentCovering_initialPartialRealization G⟩⟩

theorem blockStepLaw_of_hasSummandComponentDiffeomorph (h : HasSummandComponentDiffeomorph.{u})
    {Z : ConnectedClosedOrientedManifold.{u} 3}
    (hstep : ∀ (S : Finset G.Edge) (P : PartialRealization G S) (e : G.Edge), e ∉ S →
      P.IsBlockInvariant Z → ∃ P' : PartialRealization G (insert e S), P'.IsBlockInvariant Z) :
    BlockStepLaw G Z :=
  ⟨exists_initial_of_hasSummandComponentDiffeomorph G h Z, hstep⟩

end MarkedManifoldGraph

namespace MarkedManifoldGraph

theorem exists_initial_oneVertex (N : ConnectedClosedOrientedManifold.{u} 3)
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    ∃ P : PartialRealization (oneVertex N) ∅, P.IsBlockInvariant Z :=
  (oneVertexBlockStepLaw N Z).initial

end MarkedManifoldGraph

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

namespace MarkedManifoldGraph

theorem exists_initial_of_hasSummandComponentDiffeomorph_twoVertex
    (h : HasSummandComponentDiffeomorph.{0}) (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold)
    (Z : ConnectedClosedOrientedManifold.{0} 3) :
    ∃ P : PartialRealization (twoVertex N B B') ∅, P.IsBlockInvariant Z :=
  exists_initial_of_hasSummandComponentDiffeomorph (twoVertex N B B') h Z

theorem initialPartialRealization_twoVertex_componentCorrespondence
    (N : ConnectedClosedOrientedManifold.{0} 3) (B B' : MarkedBall N.toClosedOrientedManifold) :
    (initialPartialRealization (twoVertex N B B')).componentCorrespondence :=
  componentCorrespondence_initialPartialRealization (twoVertex N B B')

theorem initialPartialRealization_twoVertex_cylinderComponentCovering
    (N : ConnectedClosedOrientedManifold.{0} 3) (B B' : MarkedBall N.toClosedOrientedManifold) :
    (initialPartialRealization (twoVertex N B B')).CylinderComponentCovering :=
  cylinderComponentCovering_initialPartialRealization (twoVertex N B B')

end MarkedManifoldGraph

end DifferentialGeometry.Topology
