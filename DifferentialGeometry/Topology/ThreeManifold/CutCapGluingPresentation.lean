import DifferentialGeometry.Topology.ThreeManifold.CutCapNoTubeReduction

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

def cutComponentGluing : Prop :=
  ∀ (C : ConnectedComponents M.Carrier), E.cutIndices C ≠ ∅ →
    ∀ (L : List (ConnectedClosedOrientedManifold.{u} 3)), E.CompleteEnumeration C L →
      ∃ K : List (ConnectedClosedOrientedManifold.{u} 3),
        (∀ F ∈ K, isSphereTwoTimesCircleFactor F) ∧
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (finiteConnectedSum (L ++ K)).toClosedOrientedManifold)

def cutCapSummandCountDetermined : Prop :=
  ∀ (C : ConnectedComponents M.Carrier)
    (L K : List (ConnectedClosedOrientedManifold.{u} 3)),
    E.CompleteEnumeration C L →
    (∀ F ∈ K, isSphereTwoTimesCircleFactor F) →
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (M.component C).toClosedOrientedManifold
      (finiteConnectedSum (L ++ K)).toClosedOrientedManifold) →
    K.length = (E.cutIndices C).card + 1 - L.length

theorem cutComponentGluing_of_cutComponentRealization (h : E.cutComponentRealization) :
    E.cutComponentGluing := by
  intro C hC L hL
  obtain ⟨K, -, hKfac, hdiff⟩ := h C hC L hL
  exact ⟨K, hKfac, hdiff⟩

theorem cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hglue : E.cutComponentGluing) (hcount : E.cutCapSummandCountDetermined) :
    E.cutComponentRealization := by
  intro C hC L hL
  obtain ⟨K, hKfac, hdiff⟩ := hglue C hC L hL
  exact ⟨K, hcount C L K hL hKfac hdiff, hKfac, hdiff⟩

theorem componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hr : E.NoTubeRealization) (hglue : E.cutComponentGluing)
    (hcount : E.cutCapSummandCountDetermined) :
    E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization.mpr
    ⟨hr, E.cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
      hglue hcount⟩

theorem incidenceCycleRank_add_length_of_completeEnumeration
    {C : ConnectedComponents M.Carrier}
    {L : List (ConnectedClosedOrientedManifold.{u} 3)} (hL : E.CompleteEnumeration C L) :
    E.incidenceCycleRank C + L.length = (E.cutIndices C).card + 1 := by
  rw [← E.ncard_associatedFactors_eq_length hL]
  exact E.incidenceCycleRank_add_ncard_associatedFactors C

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hr : ∀ i : Fin T.eventCount, (T.transition i).NoTubeRealization)
    (hglue : ∀ i : Fin T.eventCount, (T.transition i).cutComponentGluing)
    (hcount : ∀ i : Fin T.eventCount, (T.transition i).cutCapSummandCountDetermined) :
    ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition :=
  fun i => (T.transition i).componentConnectedSumDecomposition_of_noTubeRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hr i) (hglue i) (hcount i)

end FiniteCutCapTrace

end DifferentialGeometry.Topology
