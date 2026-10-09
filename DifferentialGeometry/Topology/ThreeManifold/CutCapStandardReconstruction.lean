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

theorem componentwise_isPoincareStandard_of_standardDecomposition
    (h : E.componentConnectedSumStandardDecomposition)
    (hctrl : E.poincareControlled)
    (hnext : ∀ C : ConnectedComponents Q.Carrier, isPoincareStandard (Q.component C).Carrier)
    (hsum : poincareStandardSumClosed.{u}) :
    ∀ C : ConnectedComponents M.Carrier, isPoincareStandard (M.component C).Carrier := by
  intro C
  obtain ⟨L, hL⟩ := E.exists_completeEnumeration C
  obtain ⟨K, -, hKfac, ⟨ρ⟩⟩ := h C L hL
  refine isPoincareStandard_of_diffeomorph ρ (hsum (L ++ K) ?_)
  intro F hF
  rcases List.mem_append.mp hF with hF | hF
  · obtain ⟨x, -, rfl⟩ := hL.2.1 F hF
    rcases hx : E.presentation (E.capping.coreInclusion x) with q | d
    · rw [E.associatedFactor_eq_of_presentation_eq_inl x q hx]
      exact hnext (ConnectedComponents.mk q)
    · rw [E.associatedFactor_eq_of_presentation_eq_inr x d hx]
      exact hctrl (ConnectedComponents.mk d)
  · exact isPoincareStandard_of_standard_factor F (hKfac F hF)

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem componentwise_isPoincareStandard_of_standardDecomposition
    (h : ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumStandardDecomposition)
    (hctrl : T.poincareControlled) (hext : T.extinct) (hsum : poincareStandardSumClosed.{u}) :
    ∀ i : Fin (T.eventCount + 1), ∀ C : ConnectedComponents (T.stage i).Carrier,
      isPoincareStandard ((T.stage i).component C).Carrier := by
  have hbase : ∀ C : ConnectedComponents (T.stage (Fin.last T.eventCount)).Carrier,
      isPoincareStandard ((T.stage (Fin.last T.eventCount)).component C).Carrier := by
    have hEmpty : IsEmpty (ConnectedComponents (T.stage (Fin.last T.eventCount)).Carrier) :=
      ConnectedComponents.isEmpty_iff_isEmpty.mpr hext
    intro C
    exact hEmpty.elim C
  refine Fin.reverseInduction (motive := fun j => ∀ C : ConnectedComponents (T.stage j).Carrier,
    isPoincareStandard ((T.stage j).component C).Carrier) hbase ?_
  intro j ih
  exact (T.transition j).componentwise_isPoincareStandard_of_standardDecomposition
    (h j) (hctrl j) ih hsum

theorem isPoincareStandard_of_initialIdentification_of_standardDecomposition
    (h : ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumStandardDecomposition)
    (hctrl : T.poincareControlled) (hext : T.extinct) (hsum : poincareStandardSumClosed.{u})
    (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier]
    (Φ : T.InitialIdentification M) : isPoincareStandard M.Carrier := by
  have hcomp := T.componentwise_isPoincareStandard_of_standardDecomposition h hctrl hext hsum 0
  have : ConnectedSpace (T.stage 0).Carrier :=
    Φ.1.toHomeomorph.connectedSpace_iff.mp inferInstance
  let C : ConnectedComponents (T.stage 0).Carrier :=
    ConnectedComponents.mk (Φ.1 (Classical.choice inferInstance))
  exact isPoincareStandard_of_diffeomorph Φ.1
    ((T.stage 0).isPoincareStandard_of_component C (hcomp C))

end FiniteCutCapTrace

end DifferentialGeometry.Topology
