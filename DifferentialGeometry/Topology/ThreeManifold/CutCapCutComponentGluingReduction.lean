import DifferentialGeometry.Topology.ThreeManifold.CutCapIncidenceSpanningTree
import DifferentialGeometry.Topology.ThreeManifold.CutCapLocalReconstructionReduction
import DifferentialGeometry.Topology.ThreeManifold.CutCapSphericalSummandCompletionReduction

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def cutComponentSingleTubeGluing : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), (E.cutIndices C).card = 1 →
    ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
      (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold)

theorem cutComponentSingleTubeGluing_of_cutComponentGluing (h : E.cutComponentGluing) :
    E.cutComponentSingleTubeGluing := by
  intro C hcard
  refine (E.cutComponentGluing_iff_cutComponentCanonicalGluing.mp h) C ?_
  rintro h0
  rw [h0] at hcard
  simp at hcard

theorem cutComponentGluing_of_cutComponentSingleTubeGluing_of_card_cutIndices_eq_one
    (hcard : ∀ C : ConnectedComponents M.Carrier,
      E.cutIndices C ≠ ∅ → (E.cutIndices C).card = 1)
    (h : E.cutComponentSingleTubeGluing) : E.cutComponentGluing := by
  intro C hC L hL
  obtain ⟨K, hKfac, hdiff⟩ := h C (hcard C hC)
  have hp := (E.completeEnumeration_perm hL
    (E.completeEnumeration_canonicalEnumeration C)).append_right K
  obtain ⟨σ⟩ := finiteConnectedSum_perm hp
  exact ⟨K, hKfac, hdiff.map fun ρ => ρ.trans σ.symm⟩

theorem cutComponentGluing_of_cutComponentSingleTubeGluing_of_subsingleton_index
    [Subsingleton E.tubes.Index] (h : E.cutComponentSingleTubeGluing) :
    E.cutComponentGluing :=
  E.cutComponentGluing_of_cutComponentSingleTubeGluing_of_card_cutIndices_eq_one
    (fun _ hC => le_antisymm
      (Finset.card_le_one.mpr fun a _ b _ => Subsingleton.elim a b)
      (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hC))) h

theorem cutComponentGluing_iff_cutComponentSingleTubeGluing_of_subsingleton_index
    [Subsingleton E.tubes.Index] :
    E.cutComponentGluing ↔ E.cutComponentSingleTubeGluing :=
  ⟨E.cutComponentSingleTubeGluing_of_cutComponentGluing,
    E.cutComponentGluing_of_cutComponentSingleTubeGluing_of_subsingleton_index⟩

theorem cutEndFactor_ne_of_ncard_associatedFactors_eq_two_of_card_cutIndices_eq_one
    (C : ConnectedComponents M.Carrier) (a : E.cutIndices C)
    (hcard : (E.cutIndices C).card = 1) (h2 : (E.associatedFactors C).ncard = 2) :
    E.cutEndFactor C a false sphereBasePoint ≠
      E.cutEndFactor C a true sphereBasePoint := by
  intro hEq
  classical
  have hfinV : Fintype ↥(E.associatedFactors C) := (E.associatedFactors_finite C).fintype
  have hfinE : (E.cutIncidenceGraph C).edgeSet.Finite := Set.toFinite _
  have hpos : 0 < (E.cutIncidenceGraph C).edgeSet.ncard := by
    have h := (E.cutIncidenceGraph_connected C).card_vert_le_card_edgeSet_add_one
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, h2] at h
    omega
  obtain ⟨e, he⟩ := (Set.ncard_pos hfinE).mp hpos
  obtain ⟨a', ha'⟩ := E.exists_mem_cutIndices_of_mem_edgeSet C he
  have haa : a' = a := Subtype.ext
    (Finset.card_le_one.mp (le_of_eq hcard) a' a'.2 a a.2)
  rw [← ha'] at he
  rw [haa] at he
  have hadj : (E.cutIncidenceGraph C).Adj
      (E.cutEndFactor C a false sphereBasePoint)
      (E.cutEndFactor C a true sphereBasePoint) :=
    (SimpleGraph.mem_edgeSet _).mp he
  exact SimpleGraph.irrefl (E.cutIncidenceGraph C) (hEq ▸ hadj)

theorem cutEndFactor_eq_iff_ncard_associatedFactors_eq_one_of_card_cutIndices_eq_one
    (C : ConnectedComponents M.Carrier) (a : E.cutIndices C)
    (hcard : (E.cutIndices C).card = 1) :
    E.cutEndFactor C a false sphereBasePoint =
        E.cutEndFactor C a true sphereBasePoint ↔
      (E.associatedFactors C).ncard = 1 := by
  constructor
  · intro hEq
    rcases E.ncard_associatedFactors_eq_one_or_two_of_card_cutIndices_eq_one C hcard with h1 | h2
    · exact h1
    · exact absurd hEq
        (E.cutEndFactor_ne_of_ncard_associatedFactors_eq_two_of_card_cutIndices_eq_one
          C a hcard h2)
  · intro h1
    obtain ⟨N, hN⟩ := Set.ncard_eq_one.mp h1
    have hf : (E.cutEndFactor C a false sphereBasePoint :
        ConnectedClosedOrientedManifold.{u} 3) = N :=
      Set.mem_singleton_iff.mp (Set.mem_of_subset_of_mem hN.le
        (E.cutEndFactor C a false sphereBasePoint).2)
    have ht : (E.cutEndFactor C a true sphereBasePoint :
        ConnectedClosedOrientedManifold.{u} 3) = N :=
      Set.mem_singleton_iff.mp (Set.mem_of_subset_of_mem hN.le
        (E.cutEndFactor C a true sphereBasePoint).2)
    exact Subtype.ext (hf.trans ht.symm)

theorem cutEndFactor_ne_iff_ncard_associatedFactors_eq_two_of_card_cutIndices_eq_one
    (C : ConnectedComponents M.Carrier) (a : E.cutIndices C)
    (hcard : (E.cutIndices C).card = 1) :
    E.cutEndFactor C a false sphereBasePoint ≠
        E.cutEndFactor C a true sphereBasePoint ↔
      (E.associatedFactors C).ncard = 2 := by
  constructor
  · intro hne
    rcases E.ncard_associatedFactors_eq_one_or_two_of_card_cutIndices_eq_one C hcard with h1 | h2
    · exact absurd
        ((E.cutEndFactor_eq_iff_ncard_associatedFactors_eq_one_of_card_cutIndices_eq_one
          C a hcard).mpr h1) hne
    · exact h2
  · intro h2 hEq
    have h1 := (E.cutEndFactor_eq_iff_ncard_associatedFactors_eq_one_of_card_cutIndices_eq_one
      C a hcard).mp hEq
    omega

theorem incidenceCycleRank_eq_one_iff_cutEndFactor_eq_of_card_cutIndices_eq_one
    (C : ConnectedComponents M.Carrier) (a : E.cutIndices C)
    (hcard : (E.cutIndices C).card = 1) :
    E.incidenceCycleRank C = 1 ↔
      E.cutEndFactor C a false sphereBasePoint =
        E.cutEndFactor C a true sphereBasePoint := by
  rw [E.cutEndFactor_eq_iff_ncard_associatedFactors_eq_one_of_card_cutIndices_eq_one C a hcard]
  have h := E.incidenceCycleRank_add_ncard_associatedFactors C
  constructor <;> intro h1 <;> omega

theorem incidenceCycleRank_eq_zero_iff_cutEndFactor_ne_of_card_cutIndices_eq_one
    (C : ConnectedComponents M.Carrier) (a : E.cutIndices C)
    (hcard : (E.cutIndices C).card = 1) :
    E.incidenceCycleRank C = 0 ↔
      E.cutEndFactor C a false sphereBasePoint ≠
        E.cutEndFactor C a true sphereBasePoint := by
  rw [E.cutEndFactor_ne_iff_ncard_associatedFactors_eq_two_of_card_cutIndices_eq_one C a hcard]
  have h := E.incidenceCycleRank_add_ncard_associatedFactors C
  constructor <;> intro h1 <;> omega

theorem cutSphericalGraphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (hglue : E.cutComponentGluing) (hcount : E.cutCapSummandCountDetermined) :
    E.cutSphericalGraphSumRealization S := by
  intro C hC
  obtain ⟨b, hb⟩ := (E.cutComponentCanonicalGluing_iff_sphericalSummandCompletion S hS).mp
    (E.cutComponentGluing_iff_cutComponentCanonicalGluing.mp hglue) C hC
  have huniq := (E.cutCapSummandCanonicalCount_iff_sphericalSummandExponentDetermined S hS).mp
    (E.cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount.mp hcount)
  rw [huniq C b hb] at hb
  exact hb

theorem cutSphericalGraphSumRealization_singleTube_dichotomy
    (S : ConnectedClosedOrientedManifold.{u} 3) (h : E.cutSphericalGraphSumRealization S)
    (C : ConnectedComponents M.Carrier) (hcard : (E.cutIndices C).card = 1) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (E.canonicalEnumeration C ++ [S])).toClosedOrientedManifold) ∨
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (M.component C).toClosedOrientedManifold
        (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold) := by
  have hC : E.cutIndices C ≠ ∅ := by
    rintro h0
    rw [h0] at hcard
    simp at hcard
  have hb := h C hC
  rcases E.incidenceCycleRank_eq_zero_or_eq_one_of_card_cutIndices_eq_one C hcard with h0 | h1
  · right
    rw [h0] at hb
    simpa using hb
  · left
    rw [h1] at hb
    simpa using hb

theorem exists_cutIndices_card_eq_one_of_subsingleton_index
    [Subsingleton E.tubes.Index] (h : Nonempty E.tubes.Index) :
    ∃ C : ConnectedComponents M.Carrier, (E.cutIndices C).card = 1 := by
  obtain ⟨C, hC⟩ := E.exists_cutIndices_ne_empty_of_nonempty_index h
  exact ⟨C, le_antisymm
    (Finset.card_le_one.mpr fun a _ b _ => Subsingleton.elim a b)
    (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hC))⟩

theorem cutComponentSingleTubeGluing_of_forall_cutIndices_eq_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.cutComponentSingleTubeGluing := by
  intro C hcard
  rw [h C] at hcard
  simp at hcard

theorem cutComponentGluing_and_cutComponentSingleTubeGluing_of_isEmpty_index
    [IsEmpty E.tubes.Index] :
    E.cutComponentGluing ∧ E.cutComponentSingleTubeGluing :=
  ⟨E.cutComponentGluing_of_forall_cutIndices_eq_empty
      fun C => E.cutIndices_eq_empty_of_isEmpty_index C,
    E.cutComponentSingleTubeGluing_of_forall_cutIndices_eq_empty
      fun C => E.cutIndices_eq_empty_of_isEmpty_index C⟩

end SphericalCutCapTransition

end DifferentialGeometry.Topology
