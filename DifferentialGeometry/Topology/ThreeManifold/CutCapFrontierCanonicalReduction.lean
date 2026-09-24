import DifferentialGeometry.Topology.ThreeManifold.CutCapGraphSumFrontier
import DifferentialGeometry.Topology.ThreeManifold.CutCapGluingPresentation

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

private theorem forall₂_replicate_of_forall_mem_of_isSphereTwoTimesCircleFactor
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S) :
    ∀ {K : List (ConnectedClosedOrientedManifold.{u} 3)},
      (∀ F ∈ K, isSphereTwoTimesCircleFactor F) →
      List.Forall₂ (fun (A B : ConnectedClosedOrientedManifold.{u} 3) =>
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          A.toClosedOrientedManifold B.toClosedOrientedManifold)) K
        (List.replicate K.length S)
  | [], _ => by simp
  | a :: t, h => by
    simp only [List.length_cons, List.replicate_succ]
    exact List.Forall₂.cons
      (nonempty_orientedDiffeomorph_of_isSphereTwoTimesCircleFactor (h a (by simp)) hS)
      (forall₂_replicate_of_forall_mem_of_isSphereTwoTimesCircleFactor hS
        fun F hF => h F (by simp [hF]))

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def cutComponentCanonicalGluing : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
    ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
      (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold)

def cutCapSummandCanonicalCount : Prop :=
  ∀ (C : ConnectedComponents M.Carrier) (K : List (ConnectedClosedOrientedManifold.{u} 3)),
    (∀ F ∈ K, isSphereTwoTimesCircleFactor F) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold) →
    K.length = E.incidenceCycleRank C

def sphericalSummandExponentUnique (S : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ (C : ConnectedComponents M.Carrier) (b b' : ℕ),
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate b S)).toClosedOrientedManifold) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate b' S)).toClosedOrientedManifold) →
    b = b'

def cutCapCanonicalFrontiers : Prop :=
  E.cutComponentCanonicalGluing ∧ E.cutCapSummandCanonicalCount

theorem cutComponentGluing_iff_cutComponentCanonicalGluing :
    E.cutComponentGluing ↔ E.cutComponentCanonicalGluing := by
  constructor
  · intro h C hC
    exact h C hC (E.canonicalEnumeration C) (E.completeEnumeration_canonicalEnumeration C)
  · intro h C hC L hL
    obtain ⟨K, hKfac, hdiff⟩ := h C hC
    have hp := (E.completeEnumeration_perm hL
      (E.completeEnumeration_canonicalEnumeration C)).append_right K
    obtain ⟨σ⟩ := finiteConnectedSum_perm hp
    exact ⟨K, hKfac, hdiff.map fun ρ => ρ.trans σ.symm⟩

theorem cutComponentCanonicalGluing_of_forall_cutIndices_eq_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.cutComponentCanonicalGluing :=
  fun C hC => absurd (h C) hC

theorem cutComponentCanonicalGluing_of_componentConnectedSumDecomposition
    (h : E.componentConnectedSumDecomposition) : E.cutComponentCanonicalGluing :=
  E.cutComponentGluing_iff_cutComponentCanonicalGluing.mp
    (E.cutComponentGluing_of_cutComponentRealization
      (E.cutComponentRealization_of_componentConnectedSumDecomposition h))

theorem cutComponentCanonicalGluing_of_sphericalGraphSumRealization
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S)
    (h : E.sphericalGraphSumRealization S) : E.cutComponentCanonicalGluing := by
  intro C _
  refine ⟨List.replicate (E.incidenceCycleRank C) S, fun F hF => ?_, h C⟩
  obtain ⟨-, rfl⟩ := List.mem_replicate.mp hF
  exact hS

theorem cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount :
    E.cutCapSummandCountDetermined ↔ E.cutCapSummandCanonicalCount := by
  constructor
  · intro h C K hKfac hdiff
    rw [incidenceCycleRank, ← E.length_canonicalEnumeration C]
    exact h C (E.canonicalEnumeration C) K
      (E.completeEnumeration_canonicalEnumeration C) hKfac hdiff
  · intro h C L K hL hKfac hdiff
    have hp := (E.completeEnumeration_perm hL
      (E.completeEnumeration_canonicalEnumeration C)).append_right K
    obtain ⟨σ⟩ := finiteConnectedSum_perm hp
    rw [h C K hKfac (hdiff.map fun ρ => ρ.trans σ), incidenceCycleRank,
      E.ncard_associatedFactors_eq_length hL]

theorem noTubeRealization_iff_canonicalEnumeration :
    E.NoTubeRealization ↔
      ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅ →
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold) := by
  constructor
  · intro hr C hC
    obtain ⟨N, hN⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty
      (E.completeEnumeration_canonicalEnumeration C) hC
    obtain ⟨N', hN'⟩ := E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C hC
    have hmem : N ∈ E.associatedFactors C :=
      (E.completeEnumeration_canonicalEnumeration C).2.1 N (hN ▸ List.mem_singleton.mpr rfl)
    rw [hN'] at hmem
    have hNN : N = N' := Set.mem_singleton_iff.mp hmem
    have hres := hr C N' hC hN'
    rw [← hNN] at hres
    simpa [hN] using hres
  · intro h C N hC hN
    obtain ⟨N', hN'⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty
      (E.completeEnumeration_canonicalEnumeration C) hC
    have hmem : N' ∈ E.associatedFactors C :=
      (E.completeEnumeration_canonicalEnumeration C).2.1 N' (hN' ▸ List.mem_singleton.mpr rfl)
    rw [hN] at hmem
    have hN'N : N' = N := Set.mem_singleton_iff.mp hmem
    have hres := h C hC
    rw [hN', hN'N] at hres
    simpa using hres

theorem cutComponentRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount
    (hglue : E.cutComponentCanonicalGluing) (hcount : E.cutCapSummandCanonicalCount) :
    E.cutComponentRealization :=
  E.cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (E.cutComponentGluing_iff_cutComponentCanonicalGluing.mpr hglue)
    (E.cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount.mpr hcount)

theorem cutComponentRealization_of_cutCapCanonicalFrontiers
    (h : E.cutCapCanonicalFrontiers) : E.cutComponentRealization :=
  E.cutComponentRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount h.1 h.2

theorem componentConnectedSumDecomposition_of_noTubeRealization_of_cutCapCanonicalFrontiers
    (hr : E.NoTubeRealization) (h : E.cutCapCanonicalFrontiers) :
    E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization.mpr
    ⟨hr, E.cutComponentRealization_of_cutCapCanonicalFrontiers h⟩

theorem sphericalSummandExponentUnique_of_cutCapSummandCountDetermined
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S)
    (h : E.cutCapSummandCountDetermined) : E.sphericalSummandExponentUnique S := by
  intro C b b' hb hb'
  have hfac : ∀ b : ℕ, ∀ F ∈ List.replicate b S, isSphereTwoTimesCircleFactor F := by
    intro b F hF
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp hF
    exact hS
  have h1 := h C (E.canonicalEnumeration C) (List.replicate b S)
    (E.completeEnumeration_canonicalEnumeration C) (hfac b) hb
  have h2 := h C (E.canonicalEnumeration C) (List.replicate b' S)
    (E.completeEnumeration_canonicalEnumeration C) (hfac b') hb'
  rw [List.length_replicate] at h1 h2
  omega

theorem cutCapSummandCountDetermined_of_sphericalGraphSumRealization_of_sphericalSummandExponentUnique
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S)
    (hex : E.sphericalGraphSumRealization S) (huniq : E.sphericalSummandExponentUnique S) :
    E.cutCapSummandCountDetermined := by
  refine E.cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount.mpr ?_
  intro C K hKfac hdiff
  obtain ⟨σ⟩ := finiteConnectedSum_congr_of_connectedSumLaws
    (connectedSumLaws_of_associative connectedSumAssociative_holds)
    (List.rel_append (List.forall₂_same.mpr fun A _ =>
      ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩)
      (forall₂_replicate_of_forall_mem_of_isSphereTwoTimesCircleFactor hS hKfac))
  exact huniq C K.length (E.incidenceCycleRank C) (hdiff.map fun ρ => ρ.trans σ) (hex C)

theorem cutCapCanonicalFrontiers_of_sphericalGraphSumRealization_of_sphericalSummandExponentUnique
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S)
    (hex : E.sphericalGraphSumRealization S) (huniq : E.sphericalSummandExponentUnique S) :
    E.cutCapCanonicalFrontiers :=
  ⟨E.cutComponentCanonicalGluing_of_sphericalGraphSumRealization hS hex,
    E.cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount.mp
      (E.cutCapSummandCountDetermined_of_sphericalGraphSumRealization_of_sphericalSummandExponentUnique
        hS hex huniq)⟩

theorem componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount
    (hr : E.NoTubeRealization) (hglue : E.cutComponentCanonicalGluing)
    (hcount : E.cutCapSummandCanonicalCount) : E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    hr (E.cutComponentGluing_iff_cutComponentCanonicalGluing.mpr hglue)
    (E.cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount.mpr hcount)

theorem exists_cutIndices_eq_empty_and_cutIncidenceGraph_connected [IsEmpty E.tubes.Index]
    (C : ConnectedComponents M.Carrier) :
    E.cutIndices C = ∅ ∧ (E.cutIncidenceGraph C).Connected :=
  ⟨E.cutIndices_eq_empty_of_isEmpty_index C, E.cutIncidenceGraph_connected C⟩

theorem not_forall_cutIndices_ne_empty_of_isEmpty_index [IsEmpty E.tubes.Index] :
    ¬ ∀ C : ConnectedComponents M.Carrier, E.cutIndices C ≠ ∅ :=
  fun h => h (ConnectedComponents.mk (Classical.choice E.source_nonempty))
    (E.cutIndices_eq_empty_of_isEmpty_index _)

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem cutComponentRealization_of_cutCapCanonicalFrontiers
    (h : ∀ i : Fin T.eventCount, (T.transition i).cutCapCanonicalFrontiers) :
    ∀ i : Fin T.eventCount, (T.transition i).cutComponentRealization :=
  fun i => by
    let E := T.transition i
    exact E.cutComponentRealization_of_cutCapCanonicalFrontiers (h i)

theorem componentConnectedSumDecomposition_of_noTubeRealization_of_cutCapCanonicalFrontiers
    (hr : ∀ i : Fin T.eventCount, (T.transition i).NoTubeRealization)
    (h : ∀ i : Fin T.eventCount, (T.transition i).cutCapCanonicalFrontiers) :
    ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition :=
  fun i => by
    let E := T.transition i
    exact E.componentConnectedSumDecomposition_of_noTubeRealization_of_cutCapCanonicalFrontiers
      (hr i) (h i)

theorem componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentCanonicalGluing_of_cutCapSummandCanonicalCount
    (hr : ∀ i : Fin T.eventCount, (T.transition i).NoTubeRealization)
    (hglue : ∀ i : Fin T.eventCount, (T.transition i).cutComponentCanonicalGluing)
    (hcount : ∀ i : Fin T.eventCount, (T.transition i).cutCapSummandCanonicalCount) :
    ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition :=
  T.componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    hr
    (fun i => (T.transition i).cutComponentGluing_iff_cutComponentCanonicalGluing.mpr (hglue i))
    (fun i =>
      (T.transition i).cutCapSummandCountDetermined_iff_cutCapSummandCanonicalCount.mpr (hcount i))

end FiniteCutCapTrace

end DifferentialGeometry.Topology
