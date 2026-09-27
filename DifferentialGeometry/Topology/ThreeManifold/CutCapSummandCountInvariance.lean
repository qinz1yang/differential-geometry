import DifferentialGeometry.Topology.ThreeManifold.CutCapGluingPresentation
import DifferentialGeometry.Topology.ThreeManifold.CutCapGraphSumFrontier
import DifferentialGeometry.Topology.ThreeManifold.CutCapIncidenceCycleRank
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedLaws
import DifferentialGeometry.Topology.ThreeManifold.SphereTwoTimesCircleLift

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem finiteConnectedSum_append_standardThreeSphereLift_orientedDiffeomorph
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ [standardThreeSphereLift.{u}])).toClosedOrientedManifold
      (finiteConnectedSum L).toClosedOrientedManifold) := by
  obtain ⟨e⟩ := finiteConnectedSum_append_of_connectedSumLaws
    (connectedSumLaws_of_associative connectedSumAssociative_holds) L
    [standardThreeSphereLift.{u}]
  obtain ⟨e'⟩ := (sphereUnitLaws_holds.{u}).2 (finiteConnectedSum L)
  exact ⟨e.trans e'⟩

theorem not_forall_length_eq_of_orientedDiffeomorph_finiteConnectedSum :
    ¬ (∀ (L L' : List (ConnectedClosedOrientedManifold.{u} 3)),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum L).toClosedOrientedManifold
        (finiteConnectedSum L').toClosedOrientedManifold) → L.length = L'.length) := by
  intro h
  have hnil : ([] : List (ConnectedClosedOrientedManifold.{u} 3)).length
      = [standardThreeSphereLift.{u}].length :=
    h [] [standardThreeSphereLift.{u}]
      ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩
  simp only [List.length_nil, List.length_singleton] at hnil
  exact absurd hnil (by decide)

theorem not_forall_append_length_eq_of_orientedDiffeomorph_finiteConnectedSum :
    ¬ (∀ (L K K' : List (ConnectedClosedOrientedManifold.{u} 3)),
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
        (finiteConnectedSum (L ++ K')).toClosedOrientedManifold) → K.length = K'.length) := by
  intro h
  have hnil : [standardThreeSphereLift.{u}].length
      = ([] : List (ConnectedClosedOrientedManifold.{u} 3)).length :=
    h [] [standardThreeSphereLift.{u}] []
      (by
        simpa using
          finiteConnectedSum_append_standardThreeSphereLift_orientedDiffeomorph
            ([] : List (ConnectedClosedOrientedManifold.{u} 3)))
  simp only [List.length_nil, List.length_singleton] at hnil
  exact absurd hnil (by decide)

def finiteConnectedSumSummandCountUnique
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) : Prop :=
  ∀ (K K' : List (ConnectedClosedOrientedManifold.{u} 3)),
    (∀ F ∈ K, isSphereTwoTimesCircleFactor F) →
    (∀ F ∈ K', isSphereTwoTimesCircleFactor F) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
      (finiteConnectedSum (L ++ K')).toClosedOrientedManifold) →
    K.length = K'.length

theorem finiteConnectedSumSummandCountUnique_self
    {L K : List (ConnectedClosedOrientedManifold.{u} 3)} :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold) :=
  ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩

theorem exists_sphericalFactor_hypothesis_witness :
    ∃ K : List (ConnectedClosedOrientedManifold.{0} 3),
      (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧ K.length = 1 ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (finiteConnectedSum ([] ++ K)).toClosedOrientedManifold
          (finiteConnectedSum ([] ++ K)).toClosedOrientedManifold) :=
  ⟨[sphereTwoTimesCircleLift], by
    refine ⟨?_, List.length_singleton, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩
    intro F hF
    rw [List.mem_singleton] at hF
    subst hF
    exact isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift⟩

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem cutCapSummandCountDetermined_of_graphSumRealization_of_summandCountUnique
    (h : E.graphSumRealization)
    (huniq : ∀ L : List (ConnectedClosedOrientedManifold.{u} 3),
      finiteConnectedSumSummandCountUnique L) :
    E.cutCapSummandCountDetermined := by
  intro C L K hL hKfac hdiff
  obtain ⟨K₀, hK₀len, hK₀fac, hdiff₀⟩ := h C
  obtain ⟨σ⟩ := finiteConnectedSum_perm
    ((E.completeEnumeration_perm hL (E.completeEnumeration_canonicalEnumeration C)).append_right K)
  have hcomp : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++ K₀)).toClosedOrientedManifold) :=
    (hdiff.map fun ρ => ρ.trans σ).map fun ρ => ρ.symm.trans hdiff₀.some
  have hlen := huniq (E.canonicalEnumeration C) K K₀ hKfac hK₀fac hcomp
  rw [hlen, hK₀len, incidenceCycleRank, E.ncard_associatedFactors_eq_length hL]

theorem eq_of_finiteConnectedSumSummandCountUnique_of_canonicalEnumeration_replicate
    (huniq : ∀ L : List (ConnectedClosedOrientedManifold.{u} 3),
      finiteConnectedSumSummandCountUnique L)
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S)
    (C : ConnectedComponents M.Carrier) {b b' : ℕ}
    (hb : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate b S)).toClosedOrientedManifold))
    (hb' : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate b' S)).toClosedOrientedManifold)) :
    b = b' := by
  have hfac : ∀ b : ℕ, ∀ F ∈ List.replicate b S, isSphereTwoTimesCircleFactor F := by
    intro b F hF
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp hF
    exact hS
  have hcomp : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate b S)).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate b' S)).toClosedOrientedManifold) :=
    hb.map fun ρ => ρ.symm.trans hb'.some
  have hlen := huniq (E.canonicalEnumeration C) (List.replicate b S) (List.replicate b' S)
    (hfac b) (hfac b') hcomp
  rwa [List.length_replicate, List.length_replicate] at hlen

theorem cutCapSummandCountDetermined_of_sphericalGraphSumRealization_of_summandCountUnique
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S)
    (hex : E.sphericalGraphSumRealization S)
    (huniq : ∀ L : List (ConnectedClosedOrientedManifold.{u} 3),
      finiteConnectedSumSummandCountUnique L) :
    E.cutCapSummandCountDetermined := by
  intro C L K hL hKfac hdiff
  obtain ⟨σ⟩ := finiteConnectedSum_perm
    ((E.completeEnumeration_perm hL (E.completeEnumeration_canonicalEnumeration C)).append_right K)
  have hfac : ∀ F ∈ List.replicate (E.incidenceCycleRank C) S,
      isSphereTwoTimesCircleFactor F := by
    intro F hF
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp hF
    exact hS
  have hcomp : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate (E.incidenceCycleRank C) S)).toClosedOrientedManifold) :=
    (hdiff.map fun ρ => ρ.trans σ).map fun ρ => ρ.symm.trans (hex C).some
  have hlen := huniq (E.canonicalEnumeration C) K
    (List.replicate (E.incidenceCycleRank C) S) hKfac hfac hcomp
  rw [List.length_replicate] at hlen
  rw [hlen, incidenceCycleRank, E.ncard_associatedFactors_eq_length hL]

theorem length_eq_incidenceCycleRank_of_completeEnumeration_of_cutIndices_eq_empty
    {C : ConnectedComponents M.Carrier}
    {L : List (ConnectedClosedOrientedManifold.{u} 3)} (hL : E.CompleteEnumeration C L)
    (hC : E.cutIndices C = ∅) :
    (0 : ℕ) = (E.cutIndices C).card + 1 - L.length := by
  obtain ⟨N, hN⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty hL hC
  rw [hC, hN]
  simp

end SphericalCutCapTransition

end DifferentialGeometry.Topology
