import DifferentialGeometry.Topology.ThreeManifold.CutCapMarkedGraphBridge
import DifferentialGeometry.Topology.ThreeManifold.CutCapCutComponentPieceGluing

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem cutCapVertex_mem_cappedCutComponents (C : ConnectedComponents M.Carrier)
    (a : E.cutIndices C) (side : Bool) :
    E.cutCapVertex a.1 side ∈ E.cappedCutComponents C :=
  ⟨E.tubes.coreBoundarySphere (a.1, side) sphereBasePoint,
    E.mk_coreBoundarySphere_eq C a side sphereBasePoint, rfl⟩

theorem cappedFactor_cutCapVertex (C : ConnectedComponents M.Carrier)
    (a : E.cutIndices C) (side : Bool) :
    E.cappedFactor C ⟨E.cutCapVertex a.1 side,
        E.cutCapVertex_mem_cappedCutComponents C a side⟩ =
      (E.cutEndFactor C a side sphereBasePoint :
        ConnectedClosedOrientedManifold.{u} 3) :=
  (E.cappedFactor_eq_of_mem C _ (E.tubes.coreBoundarySphere (a.1, side) sphereBasePoint)
      rfl).trans (E.cutEndFactor_coe_eq_associatedFactor C a side sphereBasePoint).symm

theorem reachable_cutCapVertex (K : E.CutCapCollarFamily) (a : E.tubes.Index) :
    ((E.cutCapMarkedGraph K).processedGraph Finset.univ).Reachable
      (E.cutCapVertex a false) (E.cutCapVertex a true) := by
  classical
  have h := (E.cutCapMarkedGraph K).reachable_source_target_insert
    (Finset.univ : Finset (E.cutCapMarkedGraph K).Edge) (ULift.up a)
  have hle : (E.cutCapMarkedGraph K).processedGraph
      (insert (ULift.up a) (Finset.univ : Finset (E.cutCapMarkedGraph K).Edge)) ≤
      (E.cutCapMarkedGraph K).processedGraph Finset.univ :=
    MarkedManifoldGraph.processedGraph_mono _ (Finset.subset_univ _)
  exact h.mono hle

def cutCapBranchBlock_eq_cutComponentBranches (K : E.CutCapCollarFamily) : Prop :=
  ∀ (C : ConnectedComponents M.Carrier) (_ : E.cutIndices C ≠ ∅) (a : E.cutIndices C)
    (v : (E.cutCapMarkedGraph K).Vertex),
    (v ∈ ((E.cutCapMarkedGraph K).vertexBlock Finset.univ (E.cutCapVertex a.1 false) :
        Set (E.cutCapMarkedGraph K).Vertex)) ↔ v ∈ E.cappedCutComponents C

def cutCapBranchBlockList_eq_cutPieceSummands (K : E.CutCapCollarFamily) : Prop :=
  ∀ (C : ConnectedComponents M.Carrier) (_ : E.cutIndices C ≠ ∅) (a : E.cutIndices C),
    (E.cutCapMarkedGraph K).vertexBlockList Finset.univ (E.cutCapVertex a.1 false) =
      E.cappedCutPieceSummands C

theorem forall₂_vertexBlockList_cappedCutPieceFactors (K : E.CutCapCollarFamily)
    (h : E.cutCapBranchBlockList_eq_cutPieceSummands K)
    (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C ≠ ∅) (a : E.cutIndices C) :
    List.Forall₂ (fun (A B : ConnectedClosedOrientedManifold.{u} 3) =>
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph A.toClosedOrientedManifold
        B.toClosedOrientedManifold))
      ((E.cutCapMarkedGraph K).vertexBlockList Finset.univ (E.cutCapVertex a.1 false))
      (E.cappedCutPieceFactors C) := by
  rw [h C hC a]
  exact E.forall₂_cappedCutPieceSummands_cappedCutPieceFactors C

theorem card_vertexBlock_eq_card_cappedCutPieceFactorSet (K : E.CutCapCollarFamily)
    (hb : E.cutCapBranchBlock_eq_cutComponentBranches K)
    (hQ : ClosedOrientedManifold.componentSeparated Q)
    (hD : ClosedOrientedManifold.componentSeparated E.discarded)
    (hside : E.summandSidesSeparated) (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C ≠ ∅) (a : E.cutIndices C) :
    ((E.cutCapMarkedGraph K).vertexBlock Finset.univ (E.cutCapVertex a.1 false)).card =
      (E.cappedCutPieceFactorSet C).card := by
  have hinj := E.injective_cappedFactor_of_componentSeparated_of_sidesSeparated hQ hD hside C
  have hncard : (E.cappedCutComponents C).ncard = (E.associatedFactors C).ncard := by
    have heq := Nat.card_congr (Equiv.ofBijective
      (fun D : E.cappedCutComponents C =>
        (⟨E.cappedFactor C D, ⟨D.2.choose, D.2.choose_spec.1, rfl⟩⟩ :
          ↥(E.associatedFactors C)))
      ⟨fun D D' h => hinj (congrArg Subtype.val h),
        fun N => by
          obtain ⟨x, hxC, hxN⟩ := N.2
          exact ⟨⟨ConnectedComponents.mk (E.capping.coreInclusion x), x, hxC, rfl⟩,
            Subtype.ext ((E.cappedFactor_eq_of_mem C _ x rfl).trans hxN)⟩⟩)
    rwa [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at heq
  have hblock : ((E.cutCapMarkedGraph K).vertexBlock Finset.univ
      (E.cutCapVertex a.1 false)).card = (E.cappedCutComponents C).ncard := by
    have hset : ((E.cutCapMarkedGraph K).vertexBlock Finset.univ (E.cutCapVertex a.1 false) :
        Set (E.cutCapMarkedGraph K).Vertex) =
        fun v : (E.cutCapMarkedGraph K).Vertex => v ∈ E.cappedCutComponents C :=
      funext fun v => propext (hb C hC a v)
    rw [← Set.ncard_coe_finset]
    exact (congrArg Set.ncard hset).trans rfl
  rw [hblock, hncard, ← E.card_cappedCutPieceFactorSet C]

theorem exists_blockInvariant_of_isEmpty_edge (K : E.CutCapCollarFamily)
    (hEdge : IsEmpty (E.cutCapMarkedGraph K).Edge)
    (F : Finset (E.cutCapMarkedGraph K).Edge)
    (Z : ConnectedClosedOrientedManifold.{u} 3) :
    ∃ P : PartialRealization (E.cutCapMarkedGraph K) F, P.IsBlockInvariant Z := by
  have hF : F = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun e _ => (hEdge.false e).elim
  cases hF
  exact E.exists_cutCapEmptyRealization_blockInvariant K Z

noncomputable def cutCapGraphRealization_of_isEmpty_index (K : E.CutCapCollarFamily)
    (S : ConnectedClosedOrientedManifold.{u} 3) [IsEmpty E.tubes.Index] :
    E.CutCapGraphRealization K S := by
  have hEdge : IsEmpty (E.cutCapMarkedGraph K).Edge :=
    ⟨fun e => isEmptyElim (ULift.down e)⟩
  refine ⟨Classical.choose (E.exists_blockInvariant_of_isEmpty_edge K hEdge Finset.univ S),
    Classical.choose_spec (E.exists_blockInvariant_of_isEmpty_edge K hEdge Finset.univ S), ?_⟩
  intro C hC
  exact absurd (E.cutIndices_eq_empty_of_isEmpty_index C) hC

end SphericalCutCapTransition

end DifferentialGeometry.Topology
