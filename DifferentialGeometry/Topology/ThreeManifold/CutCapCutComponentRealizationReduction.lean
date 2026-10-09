import DifferentialGeometry.Topology.ThreeManifold.CutCapLocalReconstructionReduction
import DifferentialGeometry.Topology.ThreeManifold.CutCapSphericalExponentReduction
import DifferentialGeometry.Topology.ThreeManifold.CutCapSummandCountInvariance
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscarded

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

theorem finiteConnectedSumSummandCountUnique_of_perm
    {L L' : List (ConnectedClosedOrientedManifold.{u} 3)} (hp : L.Perm L')
    (h : finiteConnectedSumSummandCountUnique L) :
    finiteConnectedSumSummandCountUnique L' := by
  intro K K' hKfac hK'fac hdiff
  obtain ⟨σ⟩ := finiteConnectedSum_perm (hp.append_right K)
  obtain ⟨τ⟩ := finiteConnectedSum_perm (hp.symm.append_right K')
  exact h K K' hKfac hK'fac ⟨σ.trans (hdiff.some.trans τ)⟩

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

private theorem forall₂_replicate_orientedDiffeomorph
    {S S' : ConnectedClosedOrientedManifold.{u} 3}
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      S.toClosedOrientedManifold S'.toClosedOrientedManifold)) (n : ℕ) :
    List.Forall₂ (fun (A B : ConnectedClosedOrientedManifold.{u} 3) =>
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        A.toClosedOrientedManifold B.toClosedOrientedManifold))
      (List.replicate n S') (List.replicate n S) := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [List.replicate_succ]
      exact List.Forall₂.cons (h.map fun ρ => ρ.symm) ih

theorem sphericalSummandExponentUnique_of_orientedDiffeomorph
    {S S' : ConnectedClosedOrientedManifold.{u} 3}
    (hSS' : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      S.toClosedOrientedManifold S'.toClosedOrientedManifold))
    (h : E.sphericalSummandExponentUnique S) : E.sphericalSummandExponentUnique S' := by
  intro C b b' hb hb'
  have hrep : ∀ n : ℕ, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate n S')).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate n S)).toClosedOrientedManifold) :=
    fun n => finiteConnectedSum_congr_of_connectedSumLaws
      (connectedSumLaws_of_associative connectedSumAssociative_holds)
      (List.rel_append (List.forall₂_same.mpr fun A _ =>
        ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩)
        (forall₂_replicate_orientedDiffeomorph hSS' n))
  exact h C b b' (hb.map fun ρ => ρ.trans (hrep b).some)
    (hb'.map fun ρ => ρ.trans (hrep b').some)

theorem cutCapSummandCountDetermined_of_graphSumRealization_of_canonicalSummandCountUnique
    (h : E.graphSumRealization)
    (huniq : ∀ C : ConnectedComponents M.Carrier,
      finiteConnectedSumSummandCountUnique (E.canonicalEnumeration C)) :
    E.cutCapSummandCountDetermined := by
  intro C L K hL hKfac hdiff
  obtain ⟨K₀, hK₀len, hK₀fac, hdiff₀⟩ := h C
  obtain ⟨σ⟩ := finiteConnectedSum_perm
    ((E.completeEnumeration_perm hL (E.completeEnumeration_canonicalEnumeration C)).append_right K)
  have hcomp : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++ K₀)).toClosedOrientedManifold) :=
    (hdiff.map fun ρ => ρ.trans σ).map fun ρ => ρ.symm.trans hdiff₀.some
  have hlen := huniq C K K₀ hKfac hK₀fac hcomp
  rw [hlen, hK₀len, incidenceCycleRank, E.ncard_associatedFactors_eq_length hL]

def cutCapSummandAbsorptionFree : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C = ∅ →
    ∀ K : List (ConnectedClosedOrientedManifold.{u} 3),
      (∀ F ∈ K, isSphereTwoTimesCircleFactor F) →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold
        (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold) →
      K = []

theorem cutCapSummandAbsorptionFree_of_summandCountUnique
    (huniq : ∀ C : ConnectedComponents M.Carrier,
      finiteConnectedSumSummandCountUnique (E.canonicalEnumeration C)) :
    E.cutCapSummandAbsorptionFree := by
  intro C _ K hKfac hρ
  have hρ' : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++ [])).toClosedOrientedManifold) := by
    rw [List.append_nil]
    exact hρ
  have hlen := huniq C K [] hKfac (by simp) hρ'
  rw [List.length_nil] at hlen
  exact List.length_eq_zero_iff.mp hlen

private theorem length_eq_card_add_one_sub_length_of_cutIndices_eq_empty
    (hr : E.NoTubeRealization) (habs : E.cutCapSummandAbsorptionFree)
    {C : ConnectedComponents M.Carrier} (hC : E.cutIndices C = ∅)
    {L K : List (ConnectedClosedOrientedManifold.{u} 3)} (hL : E.CompleteEnumeration C L)
    (hKfac : ∀ F ∈ K, isSphereTwoTimesCircleFactor F)
    (hdiff : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)) :
    K.length = (E.cutIndices C).card + 1 - L.length := by
  obtain ⟨N, hN⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty hL hC
  obtain ⟨N₀, hN₀⟩ := E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C hC
  obtain ⟨N₁, hN₁⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty
    (E.completeEnumeration_canonicalEnumeration C) hC
  have hNmem : N ∈ E.associatedFactors C := hL.2.1 N (hN ▸ List.mem_singleton.mpr rfl)
  rw [hN₀] at hNmem
  have hN₁mem : N₁ ∈ E.associatedFactors C :=
    (E.completeEnumeration_canonicalEnumeration C).2.1 N₁ (hN₁ ▸ List.mem_singleton.mpr rfl)
  rw [hN₀] at hN₁mem
  have hNN₁ : N = N₁ :=
    (Set.mem_singleton_iff.mp hNmem).trans (Set.mem_singleton_iff.mp hN₁mem).symm
  subst hNN₁
  rw [hN] at hdiff
  obtain ⟨ρ₀⟩ := E.noTubeRealization_iff_canonicalEnumeration.mp hr C hC
  rw [hN₁] at ρ₀
  have hgoal : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (E.canonicalEnumeration C ++ K)).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold) := by
    rw [hN₁]
    exact hdiff.map fun ρ => ρ.symm.trans ρ₀
  have hK : K = [] := habs C hC K hKfac hgoal
  rw [hK, hC, hN]
  simp

theorem cutCapSummandCountDetermined_iff_cutCapSummandAbsorptionFree_of_forall_cutIndices_eq_empty
    (hr : E.NoTubeRealization) (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.cutCapSummandCountDetermined ↔ E.cutCapSummandAbsorptionFree := by
  constructor
  · intro hcount C hC K hKfac hρ
    obtain ⟨ρ₀⟩ := E.noTubeRealization_iff_canonicalEnumeration.mp hr C hC
    obtain ⟨N, hN⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty
      (E.completeEnumeration_canonicalEnumeration C) hC
    have hlen := hcount C (E.canonicalEnumeration C) K
      (E.completeEnumeration_canonicalEnumeration C) hKfac ⟨ρ₀.trans hρ.some.symm⟩
    rw [hN, hC] at hlen
    exact List.length_eq_zero_iff.mp (by simpa using hlen)
  · intro habs C L K hL hKfac hdiff
    exact E.length_eq_card_add_one_sub_length_of_cutIndices_eq_empty hr habs (h C)
      hL hKfac hdiff

theorem cutCapSummandCountDetermined_of_componentConnectedSumDecomposition_of_summandCountUnique
    (h : E.componentConnectedSumDecomposition)
    (huniq : ∀ C : ConnectedComponents M.Carrier,
      finiteConnectedSumSummandCountUnique (E.canonicalEnumeration C)) :
    E.cutCapSummandCountDetermined :=
  E.cutCapSummandCountDetermined_of_graphSumRealization_of_canonicalSummandCountUnique
    (E.graphSumRealization_of_componentConnectedSumDecomposition h) huniq

def cutCapSummandCountOfStandardFactors : Prop :=
  ∀ (C : ConnectedComponents M.Carrier)
    (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
    E.CompleteEnumeration C L →
    (∀ F ∈ K, isStandardFactor F) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold) →
    K.length = (E.cutIndices C).card + 1 - L.length

theorem not_cutCapSummandCountOfStandardFactors_of_noTubeRealization
    (hr : E.NoTubeRealization) (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅) :
    ¬ E.cutCapSummandCountOfStandardFactors := by
  intro h
  obtain ⟨ρ₀⟩ := E.noTubeRealization_iff_canonicalEnumeration.mp hr C hC
  obtain ⟨σ⟩ := finiteConnectedSum_append_standardThreeSphereLift (E.canonicalEnumeration C)
  have hfac : ∀ F ∈ [standardThreeSphereLift.{u}], isStandardFactor F := by
    intro F hF
    rw [List.mem_singleton] at hF
    exact hF ▸ isStandardFactor_standardThreeSphereLift
  have hlen := h C (E.canonicalEnumeration C) [standardThreeSphereLift.{u}]
    (E.completeEnumeration_canonicalEnumeration C) hfac ⟨ρ₀.trans σ.symm⟩
  obtain ⟨N, hN⟩ := E.eq_singleton_of_completeEnumeration_of_cutIndices_eq_empty
    (E.completeEnumeration_canonicalEnumeration C) hC
  rw [hN, hC] at hlen
  simp at hlen

theorem componentConnectedSumDecomposition_iff_noTubeRealization_of_forall_cutIndices_eq_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.componentConnectedSumDecomposition ↔ E.NoTubeRealization :=
  ⟨E.noTubeRealization_of_componentConnectedSumDecomposition, fun hr =>
    E.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization.mpr
      ⟨hr, E.cutComponentRealization_of_forall_cutIndices_eq_empty h⟩⟩

theorem localReconstruction_iff_noTubeRealization_of_forall_cutIndices_eq_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.localReconstruction ↔ E.NoTubeRealization :=
  E.localReconstruction_iff_componentConnectedSumDecomposition.trans
    (E.componentConnectedSumDecomposition_iff_noTubeRealization_of_forall_cutIndices_eq_empty h)

theorem cutComponentRealization_and_cutComponentGluing_of_forall_cutIndices_eq_empty
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.cutComponentRealization ∧ E.cutComponentGluing :=
  ⟨E.cutComponentRealization_of_forall_cutIndices_eq_empty h,
    E.cutComponentGluing_of_forall_cutIndices_eq_empty h⟩

end SphericalCutCapTransition

end DifferentialGeometry.Topology
