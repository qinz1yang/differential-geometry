import DifferentialGeometry.Topology.ThreeManifold.CutCapGluing

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem completeEnumeration_perm {C : ConnectedComponents M.Carrier}
    {L L' : List (ConnectedClosedOrientedManifold.{u} 3)}
    (hL : E.CompleteEnumeration C L) (hL' : E.CompleteEnumeration C L') :
    L.Perm L' := by
  classical
  refine List.perm_of_nodup_nodup_toFinset_eq hL.1 hL'.1 ?_
  ext F
  simp only [List.mem_toFinset]
  exact ⟨fun h => hL'.2.2 F (hL.2.1 F h), fun h => hL.2.2 F (hL'.2.1 F h)⟩

def componentConnectedSumStandardDecomposition : Prop :=
  ∀ (C : ConnectedComponents M.Carrier)
    (L : List (ConnectedClosedOrientedManifold.{u} 3)),
    E.CompleteEnumeration C L →
      ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
        K.length = (E.cutIndices C).card + 1 - L.length ∧
        (∀ F ∈ K, isStandardFactor F) ∧
        Nonempty ((M.component C).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold.Carrier)

theorem componentConnectedSumStandardDecomposition_of_componentConnectedSumDecomposition
    (h : E.componentConnectedSumDecomposition) :
    E.componentConnectedSumStandardDecomposition := by
  intro C L hL
  obtain ⟨K, hKlen, hKfac, hdiff⟩ := h C L hL
  exact ⟨K, hKlen, fun F hF => isStandardFactor_of_isSphereTwoTimesCircleFactor (hKfac F hF),
    hdiff.map fun ρ => ρ.1⟩

theorem componentConnectedSumStandardDecomposition_of_singleEnumeration
    (hperm : ∀ {L L' : List (ConnectedClosedOrientedManifold.{u} 3)}, L.Perm L' →
      Nonempty ((finiteConnectedSum L).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
        (finiteConnectedSum L').toClosedOrientedManifold.Carrier))
    (hsingle : ∀ C : ConnectedComponents M.Carrier,
      ∃ L : List (ConnectedClosedOrientedManifold.{u} 3), E.CompleteEnumeration C L ∧
        ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
          K.length = (E.cutIndices C).card + 1 - L.length ∧
          (∀ F ∈ K, isStandardFactor F) ∧
          Nonempty ((M.component C).toClosedOrientedManifold.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
            (finiteConnectedSum (L ++ K)).toClosedOrientedManifold.Carrier)) :
    E.componentConnectedSumStandardDecomposition := by
  intro C L hL
  obtain ⟨L₀, hL₀, K, hKlen, hKfac, hρ⟩ := hsingle C
  have hp := E.completeEnumeration_perm hL hL₀
  refine ⟨K, ?_, hKfac, ?_⟩
  · rw [hp.length_eq]
    exact hKlen
  · obtain ⟨σ⟩ := hperm (hp.symm.append_right K)
    exact hρ.map fun ρ => ρ.trans σ

theorem componentConnectedSumDecomposition_of_singleEnumeration
    (hperm : ∀ {L L' : List (ConnectedClosedOrientedManifold.{u} 3)}, L.Perm L' →
      Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
        (finiteConnectedSum L).toClosedOrientedManifold
        (finiteConnectedSum L').toClosedOrientedManifold))
    (hsingle : ∀ C : ConnectedComponents M.Carrier,
      ∃ L : List (ConnectedClosedOrientedManifold.{u} 3), E.CompleteEnumeration C L ∧
        ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
          K.length = (E.cutIndices C).card + 1 - L.length ∧
          (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (M.component C).toClosedOrientedManifold
            (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)) :
    E.componentConnectedSumDecomposition := by
  intro C L hL
  obtain ⟨L₀, hL₀, K, hKlen, hKfac, hρ⟩ := hsingle C
  have hp := E.completeEnumeration_perm hL hL₀
  refine ⟨K, ?_, hKfac, ?_⟩
  · rw [hp.length_eq]
    exact hKlen
  · obtain ⟨σ⟩ := hperm (hp.symm.append_right K)
    exact hρ.map fun ρ => ρ.trans σ


end SphericalCutCapTransition


end DifferentialGeometry.Topology
