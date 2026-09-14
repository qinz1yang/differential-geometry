import DifferentialGeometry.Topology.ThreeManifold.CutCapGluing
import DifferentialGeometry.Topology.ThreeManifold.CutCapGraphSumFrontier
import DifferentialGeometry.Topology.ThreeManifold.CutCapNoTubeReduction
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace SimpleGraph

theorem exists_spanningTree_edgeFinset {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (hconn : G.Connected) :
    ∃ T : Finset (Sym2 V), T ⊆ G.edgeFinset ∧ T.card + 1 = Fintype.card V := by
  classical
  obtain ⟨τ, hle, hτ⟩ := hconn.exists_isTree_le
  have hsub : τ.edgeSet ⊆ G.edgeSet := (SimpleGraph.edgeSet_subset_edgeSet).mpr hle
  have hfin : Fintype τ.edgeSet := ((Set.toFinite G.edgeSet).subset hsub).fintype
  have hcard := @SimpleGraph.IsTree.card_edgeFinset V τ _ hfin hτ
  refine ⟨τ.edgeFinset, ?_, ?_⟩
  · simpa using hsub
  · simpa using hcard

theorem card_sub_spanningTree_edgeFinset_add_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (T : Finset (Sym2 V)) (hsub : T ⊆ G.edgeFinset)
    (hcard : T.card + 1 = Fintype.card V) :
    G.edgeFinset.card - T.card + Fintype.card V = G.edgeFinset.card + 1 := by
  have hle : T.card ≤ G.edgeFinset.card := Finset.card_le_card hsub
  omega

theorem exists_spanningTree_edgeSubtype {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (hconn : G.Connected) :
    ∃ T : Finset G.edgeSet, T.card + 1 = Fintype.card V ∧
      T.card ≤ Fintype.card G.edgeSet := by
  classical
  obtain ⟨τ, hle, hτ⟩ := hconn.exists_isTree_le
  have hsub : τ.edgeSet ⊆ G.edgeSet := (SimpleGraph.edgeSet_subset_edgeSet).mpr hle
  have hfin : Fintype τ.edgeSet := ((Set.toFinite G.edgeSet).subset hsub).fintype
  have hcard := @SimpleGraph.IsTree.card_edgeFinset V τ _ hfin hτ
  have hcard' : Fintype.card τ.edgeSet + 1 = Fintype.card V := by
    rwa [← SimpleGraph.edgeFinset_card]
  have hle_card : Fintype.card τ.edgeSet ≤ Fintype.card G.edgeSet := by
    rw [← SimpleGraph.edgeFinset_card, ← SimpleGraph.edgeFinset_card]
    exact Finset.card_le_card (by simpa using hsub)
  refine ⟨Finset.univ.map ⟨fun e : τ.edgeSet => (⟨e.1, hsub e.2⟩ : G.edgeSet), ?_⟩,
    ?_, ?_⟩
  · intro a b h
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  · rw [Finset.card_map, Finset.card_univ]
    exact hcard'
  · rw [Finset.card_map, Finset.card_univ]
    exact hle_card

end SimpleGraph

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem exists_mem_cutIndices_of_mem_edgeSet (C : ConnectedComponents M.Carrier)
    {e : Sym2 ↥(E.associatedFactors C)} (he : e ∈ (E.cutIncidenceGraph C).edgeSet) :
    ∃ a : E.cutIndices C, E.cutEnds C a = e := by
  induction e using Sym2.ind with
  | _ A B =>
    rw [SimpleGraph.mem_edgeSet, cutIncidenceGraph, SimpleGraph.fromRel_adj] at he
    rcases he with ⟨-, ⟨a, ha⟩ | ⟨a, ha⟩⟩
    · exact ⟨a, ha⟩
    · exact ⟨a, ha.trans Sym2.eq_swap⟩

noncomputable def treeIndices (C : ConnectedComponents M.Carrier)
    (T : Finset (E.cutIncidenceGraph C).edgeSet) : Finset E.tubes.Index := by
  classical
  exact T.image fun e => (Classical.choose (E.exists_mem_cutIndices_of_mem_edgeSet C e.2)).1

theorem treeIndices_subset_cutIndices (C : ConnectedComponents M.Carrier)
    (T : Finset (E.cutIncidenceGraph C).edgeSet) :
    E.treeIndices C T ⊆ E.cutIndices C := by
  classical
  intro a ha
  obtain ⟨e, -, he⟩ := Finset.mem_image.mp ha
  rw [← he]
  exact (Classical.choose (E.exists_mem_cutIndices_of_mem_edgeSet C e.2)).2

theorem card_treeIndices (C : ConnectedComponents M.Carrier)
    (T : Finset (E.cutIncidenceGraph C).edgeSet) : (E.treeIndices C T).card = T.card := by
  classical
  rw [treeIndices, Finset.card_image_iff]
  intro e _ e' _ heq
  refine Subtype.ext ?_
  have h1 := Classical.choose_spec (E.exists_mem_cutIndices_of_mem_edgeSet C e.2)
  have h2 := Classical.choose_spec (E.exists_mem_cutIndices_of_mem_edgeSet C e'.2)
  have hsub : (Classical.choose (E.exists_mem_cutIndices_of_mem_edgeSet C e.2)) =
      Classical.choose (E.exists_mem_cutIndices_of_mem_edgeSet C e'.2) := Subtype.ext heq
  have hcongr := congrArg (E.cutEnds C) hsub
  rw [h1, h2] at hcongr
  exact hcongr

theorem incidenceCycleRank_eq_card_sub_of_card_add_one (C : ConnectedComponents M.Carrier)
    {T : Finset E.tubes.Index} (hsub : T ⊆ E.cutIndices C)
    (hcard : T.card + 1 = (E.associatedFactors C).ncard) :
    (E.cutIndices C).card - T.card = E.incidenceCycleRank C := by
  have h1 := Finset.card_le_card hsub
  have h2 := E.incidenceCycleRank_add_ncard_associatedFactors C
  omega

theorem incidenceCycleRank_eq_card_sub_treeIndices (C : ConnectedComponents M.Carrier)
    (T : Finset (E.cutIncidenceGraph C).edgeSet)
    (hcard : T.card + 1 = (E.associatedFactors C).ncard) :
    (E.cutIndices C).card - (E.treeIndices C T).card = E.incidenceCycleRank C :=
  E.incidenceCycleRank_eq_card_sub_of_card_add_one C
    (E.treeIndices_subset_cutIndices C T) (by rw [E.card_treeIndices C T]; exact hcard)

theorem exists_spanningTreeIndices (C : ConnectedComponents M.Carrier) :
    ∃ S : Finset E.tubes.Index, S ⊆ E.cutIndices C ∧
      S.card + 1 = (E.associatedFactors C).ncard ∧
      (E.cutIndices C).card - S.card = E.incidenceCycleRank C := by
  classical
  obtain hfinV : Fintype ↥(E.associatedFactors C) := (E.associatedFactors_finite C).fintype
  obtain hfinE : Fintype (E.cutIncidenceGraph C).edgeSet := (Set.toFinite _).fintype
  obtain ⟨T, hTcard⟩ := SimpleGraph.exists_spanningTree_edgeSubtype (E.cutIncidenceGraph C)
    (E.cutIncidenceGraph_connected C)
  refine ⟨E.treeIndices C T, E.treeIndices_subset_cutIndices C T, ?_, ?_⟩
  · rw [E.card_treeIndices C T]
    rw [← Set.fintypeCard_eq_ncard]
    exact hTcard.1
  · exact E.incidenceCycleRank_eq_card_sub_treeIndices C T
      (by rw [← Set.fintypeCard_eq_ncard]; exact hTcard.1)

def sphericalTreeGluing (S : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ (C : ConnectedComponents M.Carrier) (T : Finset E.tubes.Index), T ⊆ E.cutIndices C →
    T.card + 1 = (E.associatedFactors C).ncard →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (E.canonicalEnumeration C ++
          List.replicate ((E.cutIndices C).card - T.card) S)).toClosedOrientedManifold)

theorem sphericalTreeGluing_of_sphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3) (h : E.sphericalGraphSumRealization S) :
    E.sphericalTreeGluing S := by
  intro C T hsub hcard
  rw [E.incidenceCycleRank_eq_card_sub_of_card_add_one C hsub hcard]
  exact h C

theorem orientedDiffeomorph_finiteConnectedSum_canonicalEnumeration_of_cutIndices_eq_empty
    (hr : E.NoTubeRealization) (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold) := by
  obtain ⟨N, hN⟩ := E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C hC
  obtain ⟨K, hKlen, -, hdiff⟩ :=
    E.componentConnectedSumDecomposition_of_cutIndices_eq_empty hr C hC (E.canonicalEnumeration C)
      (E.completeEnumeration_canonicalEnumeration C)
  have hlenL : (E.canonicalEnumeration C).length = 1 := by
    rw [E.length_canonicalEnumeration C, hN, Set.ncard_singleton]
  have hK0 : K.length = 0 := by
    rw [Finset.card_eq_zero.mpr hC, hlenL] at hKlen
    omega
  obtain rfl : K = [] := List.eq_nil_of_length_eq_zero hK0
  simpa using hdiff

theorem sphericalGraphSumRealization_of_sphericalTreeGluing
    (S : ConnectedClosedOrientedManifold.{u} 3) (h : E.sphericalTreeGluing S) :
    E.sphericalGraphSumRealization S := by
  intro C
  by_cases hC : E.cutIndices C = ∅
  · have h2 := E.incidenceCycleRank_add_ncard_associatedFactors C
    obtain ⟨N, hN⟩ := E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C hC
    rw [hN, Set.ncard_singleton, Finset.card_eq_zero.mpr hC] at h2
    have hcyc : E.incidenceCycleRank C = 0 := by omega
    have hsub : (∅ : Finset E.tubes.Index) ⊆ E.cutIndices C := by rw [hC]
    have hcard : (∅ : Finset E.tubes.Index).card + 1 = (E.associatedFactors C).ncard := by
      rw [hN, Set.ncard_singleton]
      simp
    have hmem := h C ∅ hsub hcard
    simpa [hcyc, Finset.card_eq_zero.mpr hC] using hmem
  · obtain ⟨T, hTsub, hTcard, -⟩ := E.exists_spanningTreeIndices C
    have hmem := h C T hTsub hTcard
    rwa [E.incidenceCycleRank_eq_card_sub_of_card_add_one C hTsub hTcard] at hmem

theorem sphericalTreeGluing_iff_sphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3) :
    E.sphericalTreeGluing S ↔ E.sphericalGraphSumRealization S :=
  ⟨E.sphericalGraphSumRealization_of_sphericalTreeGluing S,
    E.sphericalTreeGluing_of_sphericalGraphSumRealization S⟩

theorem graphSumRealization_of_sphericalTreeGluing
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (h : E.sphericalTreeGluing S) : E.graphSumRealization :=
  E.graphSumRealization_of_componentConnectedSumDecomposition
    (E.componentConnectedSumDecomposition_of_sphericalGraphSumRealization S hS
      (E.sphericalGraphSumRealization_of_sphericalTreeGluing S h))

theorem sphericalTreeGluing_of_noTubeRealization_of_forall_cutIndices_eq_empty
    (S : ConnectedClosedOrientedManifold.{u} 3) (hr : E.NoTubeRealization)
    (hC : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.sphericalTreeGluing S := by
  intro C T hsub hcard
  have hT : T = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr fun a ha => ?_
    have hmem := hsub ha
    rw [hC C] at hmem
    exact Finset.notMem_empty a hmem
  subst hT
  have h2 := E.incidenceCycleRank_add_ncard_associatedFactors C
  obtain ⟨N, hN⟩ := E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C (hC C)
  rw [hN, Set.ncard_singleton, Finset.card_eq_zero.mpr (hC C)] at h2
  have hcyc : E.incidenceCycleRank C = 0 := by omega
  simpa [hcyc, Finset.card_eq_zero.mpr (hC C)] using
    E.orientedDiffeomorph_finiteConnectedSum_canonicalEnumeration_of_cutIndices_eq_empty
      hr C (hC C)

theorem sphericalTreeGluing_of_isEmpty_index [IsEmpty E.tubes.Index]
    (hr : E.NoTubeRealization) (S : ConnectedClosedOrientedManifold.{u} 3)
    (hS : isSphereTwoTimesCircleFactor S) : E.sphericalTreeGluing S :=
  E.sphericalTreeGluing_of_sphericalGraphSumRealization S
    (E.sphericalGraphSumRealization_of_isEmpty_index hr S hS)

theorem incidenceCycleRank_ne_card_of_one_lt_ncard_associatedFactors
    (C : ConnectedComponents M.Carrier) (h : 1 < (E.associatedFactors C).ncard) :
    E.incidenceCycleRank C ≠ (E.cutIndices C).card := by
  have h1 := E.incidenceCycleRank_add_ncard_associatedFactors C
  have h2 := E.ncard_associatedFactors_le_card_cutIndices_add_one C
  omega

theorem incidenceCycleRank_eq_zero_or_eq_one_of_card_cutIndices_eq_one
    (C : ConnectedComponents M.Carrier) (hcard : (E.cutIndices C).card = 1) :
    E.incidenceCycleRank C = 0 ∨ E.incidenceCycleRank C = 1 := by
  have h1 := E.incidenceCycleRank_add_ncard_associatedFactors C
  have h2 := E.ncard_associatedFactors_le_card_cutIndices_add_one C
  have h3 : 1 ≤ (E.associatedFactors C).ncard :=
    Set.ncard_pos (E.associatedFactors_finite C) |>.mpr (E.associatedFactors_nonempty C)
  omega

theorem exists_isTree_le_cutIncidenceGraph (C : ConnectedComponents M.Carrier) :
    ∃ τ : SimpleGraph ↥(E.associatedFactors C), τ ≤ E.cutIncidenceGraph C ∧ τ.IsTree :=
  (E.cutIncidenceGraph_connected C).exists_isTree_le

theorem length_canonicalEnumeration_eq_one_of_cutIndices_eq_empty
    (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅) :
    (E.canonicalEnumeration C).length = 1 := by
  obtain ⟨N, hN⟩ := E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C hC
  rw [E.length_canonicalEnumeration C, hN, Set.ncard_singleton]

end SphericalCutCapTransition

end DifferentialGeometry.Topology
