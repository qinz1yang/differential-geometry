import DifferentialGeometry.Topology.ThreeManifold.CutCapFrontierCanonicalReduction
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.FiniteLawInstances

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set

namespace DifferentialGeometry.Topology

universe u

theorem finiteConnectedSum_append_standardThreeSphereLift
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (finiteConnectedSum (L ++ [standardThreeSphereLift.{u}])).toClosedOrientedManifold
      (finiteConnectedSum L).toClosedOrientedManifold) := by
  obtain ⟨e⟩ := finiteConnectedSum_append L [standardThreeSphereLift.{u}]
  obtain ⟨u⟩ := connectedSum_sphere_right (finiteConnectedSum L)
  exact ⟨e.trans u⟩

theorem finiteConnectedSum_additiveInvariant
    (ι : ConnectedClosedOrientedManifold.{u} 3 → ℕ)
    (hunit : ι standardThreeSphereLift.{u} = 0)
    (hadd : ∀ A B : ConnectedClosedOrientedManifold.{u} 3,
      ι (connectedSum A B) = ι A + ι B)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)) :
    ι (finiteConnectedSum L) = (L.map ι).sum := by
  induction L with
  | nil => simpa using hunit
  | cons M L ih =>
    match L, ih with
    | [], _ => simp
    | N :: L', ih =>
      rw [finiteConnectedSum_cons_cons, hadd, ih]
      simp [List.map_cons, List.sum_cons]

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem cutComponentRealization_of_sphericalGraphSumRealization
    {S : ConnectedClosedOrientedManifold.{u} 3} (hS : isSphereTwoTimesCircleFactor S)
    (h : E.sphericalGraphSumRealization S) : E.cutComponentRealization := by
  intro C _ L hL
  refine ⟨List.replicate (E.incidenceCycleRank C) S, ?_, ?_, ?_⟩
  · rw [List.length_replicate]
    have hlen := E.incidenceCycleRank_add_length_of_completeEnumeration hL
    omega
  · intro F hF
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp hF
    exact hS
  · obtain ⟨σ⟩ := finiteConnectedSum_perm
      ((E.completeEnumeration_perm hL (E.completeEnumeration_canonicalEnumeration C)).append_right
        (List.replicate (E.incidenceCycleRank C) S))
    exact (h C).map fun ρ => ρ.trans σ.symm

theorem sphericalSummandExponentUnique_of_additiveInvariant
    {S : ConnectedClosedOrientedManifold.{u} 3}
    (ι : ConnectedClosedOrientedManifold.{u} 3 → ℕ)
    (hinv : ∀ {A B : ConnectedClosedOrientedManifold.{u} 3},
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph A.toClosedOrientedManifold
        B.toClosedOrientedManifold) → ι A = ι B)
    (hunit : ι standardThreeSphereLift.{u} = 0)
    (hadd : ∀ A B : ConnectedClosedOrientedManifold.{u} 3,
      ι (connectedSum A B) = ι A + ι B)
    (hpos : 0 < ι S) : E.sphericalSummandExponentUnique S := by
  intro C b b' hb hb'
  have hbI : ι (M.component C) =
      ι (finiteConnectedSum (E.canonicalEnumeration C ++ List.replicate b S)) := hinv hb
  have hbI' : ι (M.component C) =
      ι (finiteConnectedSum (E.canonicalEnumeration C ++ List.replicate b' S)) := hinv hb'
  rw [finiteConnectedSum_additiveInvariant ι hunit hadd
      (E.canonicalEnumeration C ++ List.replicate b S)] at hbI
  rw [finiteConnectedSum_additiveInvariant ι hunit hadd
      (E.canonicalEnumeration C ++ List.replicate b' S)] at hbI'
  simp only [List.map_append, List.sum_append, List.map_replicate, List.sum_replicate,
    nsmul_eq_mul] at hbI hbI'
  have hmul : b * ι S = b' * ι S := Nat.add_left_cancel (hbI.symm.trans hbI')
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

theorem not_sphericalSummandExponentUnique_standardThreeSphereLift
    (C : ConnectedComponents M.Carrier)
    (h : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C)).toClosedOrientedManifold)) :
    ¬ E.sphericalSummandExponentUnique standardThreeSphereLift.{u} := by
  intro huniq
  obtain ⟨σ⟩ := finiteConnectedSum_append_standardThreeSphereLift (E.canonicalEnumeration C)
  have hb0 : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate 0 standardThreeSphereLift.{u})).toClosedOrientedManifold) := by
    simpa using h
  have hb1 : Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (E.canonicalEnumeration C ++
        List.replicate 1 standardThreeSphereLift.{u})).toClosedOrientedManifold) := by
    simpa using h.map fun ρ => ρ.trans σ.symm
  exact Nat.zero_ne_one (huniq C 0 1 hb0 hb1)

theorem not_sphericalSummandExponentUnique_standardThreeSphereLift_of_noTubeRealization
    (hr : E.NoTubeRealization) (C : ConnectedComponents M.Carrier)
    (hC : E.cutIndices C = ∅) :
    ¬ E.sphericalSummandExponentUnique standardThreeSphereLift.{u} :=
  E.not_sphericalSummandExponentUnique_standardThreeSphereLift C
    (E.noTubeRealization_iff_canonicalEnumeration.mp hr C hC)

theorem not_sphericalSummandExponentUnique_standardThreeSphereLift_of_isEmpty_index
    [IsEmpty E.tubes.Index] (hr : E.NoTubeRealization) :
    ¬ E.sphericalSummandExponentUnique standardThreeSphereLift.{u} :=
  E.not_sphericalSummandExponentUnique_standardThreeSphereLift_of_noTubeRealization hr
    (ConnectedComponents.mk (Classical.choice E.source_nonempty))
    (E.cutIndices_eq_empty_of_isEmpty_index _)

end SphericalCutCapTransition

end DifferentialGeometry.Topology
