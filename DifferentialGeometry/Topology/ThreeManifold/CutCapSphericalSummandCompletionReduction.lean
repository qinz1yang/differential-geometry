import DifferentialGeometry.Topology.ThreeManifold.CutCapGraphSumLocalization
import DifferentialGeometry.Topology.ThreeManifold.CutCapSphericalExponentReduction

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

private theorem forall₂_replicate_of_forall_mem_isSphereTwoTimesCircleFactor
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
      (forall₂_replicate_of_forall_mem_isSphereTwoTimesCircleFactor hS
        fun F hF => h F (by simp [hF]))

private theorem exists_orientedDiffeomorph_finiteConnectedSum_replicate
    {L K : List (ConnectedClosedOrientedManifold.{u} 3)}
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S)
    (hKfac : ∀ F ∈ K, isSphereTwoTimesCircleFactor F) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold
      (finiteConnectedSum (L ++ List.replicate K.length S)).toClosedOrientedManifold) :=
  finiteConnectedSum_congr_of_connectedSumLaws
    (connectedSumLaws_of_associative connectedSumAssociative_holds)
    (List.rel_append (List.forall₂_same.mpr fun _ _ =>
      ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩)
      (forall₂_replicate_of_forall_mem_isSphereTwoTimesCircleFactor hS hKfac))

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def cutSphericalGraphSumRealization (S : ConnectedClosedOrientedManifold.{u} 3) : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate (E.incidenceCycleRank C) S)).toClosedOrientedManifold)

theorem cutSphericalGraphSumRealization_of_sphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : E.sphericalGraphSumRealization S) : E.cutSphericalGraphSumRealization S :=
  fun C _ => h C

theorem cutSphericalGraphSumRealization_of_cutGraphSumFrontier
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : E.cutGraphSumFrontier S) : E.cutSphericalGraphSumRealization S :=
  fun C hC => by
    obtain ⟨b, hb⟩ := h.1 C hC
    rw [← h.2 C b hb]
    exact hb

theorem sphericalSummandCompletion_of_cutSphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : E.cutSphericalGraphSumRealization S) : E.sphericalSummandCompletion S :=
  fun C hC => ⟨E.incidenceCycleRank C, h C hC⟩

theorem
    cutGraphSumFrontier_iff_cutSphericalGraphSumRealization_and_sphericalSummandExponentDetermined
    (S : ConnectedClosedOrientedManifold.{u} 3) :
    E.cutGraphSumFrontier S ↔
      E.cutSphericalGraphSumRealization S ∧ E.sphericalSummandExponentDetermined S :=
  ⟨fun h => ⟨E.cutSphericalGraphSumRealization_of_cutGraphSumFrontier S h, h.2⟩,
    fun h => ⟨E.sphericalSummandCompletion_of_cutSphericalGraphSumRealization S h.1, h.2⟩⟩

theorem cutSphericalGraphSumRealization_of_forall_cutIndices_eq_empty
    (S : ConnectedClosedOrientedManifold.{u} 3)
    (h : ∀ C : ConnectedComponents M.Carrier, E.cutIndices C = ∅) :
    E.cutSphericalGraphSumRealization S :=
  fun C hC => absurd (h C) hC

theorem cutSphericalGraphSumRealization_of_isEmpty_index [IsEmpty E.tubes.Index]
    (S : ConnectedClosedOrientedManifold.{u} 3) : E.cutSphericalGraphSumRealization S :=
  E.cutSphericalGraphSumRealization_of_forall_cutIndices_eq_empty S
    fun C => E.cutIndices_eq_empty_of_isEmpty_index C

theorem sphericalGraphSumRealization_of_noTubeRealization_of_cutSphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3) (hr : E.NoTubeRealization)
    (h : E.cutSphericalGraphSumRealization S) : E.sphericalGraphSumRealization S := by
  intro C
  by_cases hC : E.cutIndices C = ∅
  · obtain ⟨ρ⟩ := (E.noTubeRealization_iff_canonicalEnumeration.mp hr) C hC
    rw [E.incidenceCycleRank_eq_zero_of_cutIndices_eq_empty C hC]
    exact ⟨by simpa using ρ⟩
  · exact h C hC

theorem sphericalGraphSumRealization_iff_noTubeRealization_and_cutSphericalGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3) :
    E.sphericalGraphSumRealization S ↔
      E.NoTubeRealization ∧ E.cutSphericalGraphSumRealization S :=
  ⟨fun h => ⟨E.noTubeRealization_of_sphericalGraphSumRealization S h,
      E.cutSphericalGraphSumRealization_of_sphericalGraphSumRealization S h⟩,
    fun h => E.sphericalGraphSumRealization_of_noTubeRealization_of_cutSphericalGraphSumRealization
      S h.1 h.2⟩

theorem cutSphericalGraphSumRealization_iff_cutGraphSumRealization
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S) :
    E.cutSphericalGraphSumRealization S ↔ E.cutGraphSumRealization := by
  constructor
  · intro h C hC
    exact ⟨List.replicate (E.incidenceCycleRank C) S, by simp,
      fun F hF => by
        obtain ⟨-, rfl⟩ := List.mem_replicate.mp hF
        exact hS,
      h C hC⟩
  · intro h C hC
    obtain ⟨K, hKlen, hKfac, hdiff⟩ := h C hC
    obtain ⟨σ⟩ := exists_orientedDiffeomorph_finiteConnectedSum_replicate
      (L := E.canonicalEnumeration C) hS hKfac
    rw [hKlen] at σ
    exact hdiff.map fun ρ => ρ.trans σ

theorem exists_orientedDiffeomorph_finiteConnectedSum_replicate_standardThreeSphereLift
    (C : ConnectedComponents M.Carrier)
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold)) :
    ∀ b : ℕ, Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate b standardThreeSphereLift.{u})).toClosedOrientedManifold) := by
  intro b
  induction b with
  | zero => simpa using h
  | succ b ih =>
    obtain ⟨ρ⟩ := ih
    obtain ⟨σ⟩ := finiteConnectedSum_append_standardThreeSphereLift
      (E.canonicalEnumeration C ++ List.replicate b standardThreeSphereLift.{u})
    rw [List.append_assoc] at σ
    rw [List.replicate_succ']
    exact ⟨ρ.trans σ.symm⟩

theorem not_sphericalSummandExponentDetermined_standardThreeSphereLift
    (C : ConnectedComponents M.Carrier)
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold)) :
    ¬ E.sphericalSummandExponentDetermined standardThreeSphereLift.{u} := by
  intro hdet
  have h0 := hdet C 0 (by simpa using h)
  have h1 := hdet C 1 (by
    simpa using
      E.exists_orientedDiffeomorph_finiteConnectedSum_replicate_standardThreeSphereLift C h 1)
  omega

theorem not_cutGraphSumFrontier_standardThreeSphereLift
    (C : ConnectedComponents M.Carrier)
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold)) :
    ¬ E.cutGraphSumFrontier standardThreeSphereLift.{u} :=
  fun hf => E.not_sphericalSummandExponentDetermined_standardThreeSphereLift C h hf.2

end SphericalCutCapTransition

end DifferentialGeometry.Topology
