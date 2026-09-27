import DifferentialGeometry.Topology.ThreeManifold.CutCapNoTubeReduction

noncomputable section

open Set

namespace DifferentialGeometry.Topology

universe u

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem mk_eq_of_mem_componentSet_of_cutIndices_eq_empty
    (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    {x x' : E.tubes.core} (hx : ConnectedComponents.mk x.1 = C)
    (hx' : ConnectedComponents.mk x'.1 = C) :
    ConnectedComponents.mk x = ConnectedComponents.mk x' := by
  refine ConnectedComponents.coe_eq_coe'.mpr ?_
  have hsub := E.componentSet_subset_core_of_cutIndices_eq_empty C hC
  have hpre : IsPreconnected (ClosedOrientedManifold.componentSet M C) :=
    (ClosedOrientedManifold.isConnected_componentSet M C).isPreconnected
  have hmemx : (x : M.Carrier) ∈ ClosedOrientedManifold.componentSet M C :=
    (ClosedOrientedManifold.mem_componentSet M C _).mpr hx
  have hmemx' : (x' : M.Carrier) ∈ ClosedOrientedManifold.componentSet M C :=
    (ClosedOrientedManifold.mem_componentSet M C _).mpr hx'
  have hxin : (x : M.Carrier) ∈ connectedComponentIn E.tubes.core (x' : M.Carrier) :=
    hpre.subset_connectedComponentIn hmemx' hsub hmemx
  rw [connectedComponentIn_eq_image (F := E.tubes.core) x'.2] at hxin
  obtain ⟨z, hz, hzx⟩ := hxin
  have hzx' : z = x := Subtype.ext hzx
  rw [← hzx']
  exact hz

theorem mk_coreInclusion_eq_of_mem_componentSet_of_cutIndices_eq_empty
    (C : ConnectedComponents M.Carrier) (hC : E.cutIndices C = ∅)
    {x x' : E.tubes.core} (hx : ConnectedComponents.mk x.1 = C)
    (hx' : ConnectedComponents.mk x'.1 = C) :
    ConnectedComponents.mk (E.capping.coreInclusion x) =
      ConnectedComponents.mk (E.capping.coreInclusion x') := by
  rw [← Continuous.connectedComponentsMap_mk E.capping.coreInclusion.continuous x,
    ← Continuous.connectedComponentsMap_mk E.capping.coreInclusion.continuous x',
    E.mk_eq_of_mem_componentSet_of_cutIndices_eq_empty C hC hx hx']

theorem cutIndices_nonempty_of_preconnectedSpace [PreconnectedSpace M.Carrier]
    [Nonempty E.tubes.Index] (C : ConnectedComponents M.Carrier) :
    E.cutIndices C ≠ ∅ := by
  obtain ⟨a⟩ := ‹Nonempty E.tubes.Index›
  refine Finset.nonempty_iff_ne_empty.mp ⟨a, ?_⟩
  rw [E.mem_cutIndices_iff_exists_tube_mem_componentSet C a]
  exact ⟨(⟨EuclideanSpace.single 0 1, by simp⟩, ⟨0, by norm_num⟩),
    (ClosedOrientedManifold.componentSet_eq_univ_of_preconnectedSpace M C ▸ Set.mem_univ _)⟩

theorem noTubeRealization_of_preconnectedSpace [PreconnectedSpace M.Carrier]
    [Nonempty E.tubes.Index] : E.NoTubeRealization :=
  E.noTubeRealization_of_forall_cutIndices_ne_empty fun C =>
    E.cutIndices_nonempty_of_preconnectedSpace C

theorem componentConnectedSumDecomposition_iff_cutComponentRealization_of_preconnectedSpace
    [PreconnectedSpace M.Carrier] [Nonempty E.tubes.Index] :
    E.componentConnectedSumDecomposition ↔ E.cutComponentRealization :=
  E.componentConnectedSumDecomposition_iff_cutComponentRealization_of_cutIndices_ne_empty
    fun C => E.cutIndices_nonempty_of_preconnectedSpace C

theorem noTubeRealization_iff_forall_associatedFactor :
    E.NoTubeRealization ↔
      ∀ (C : ConnectedComponents M.Carrier) (x : E.tubes.core),
        ConnectedComponents.mk x.1 = C → E.cutIndices C = ∅ →
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (M.component C).toClosedOrientedManifold
            (E.associatedFactor x).toClosedOrientedManifold) := by
  constructor
  · intro hr C x hx hC
    obtain ⟨N, hN⟩ := E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C hC
    have hmem : E.associatedFactor x ∈ E.associatedFactors C := ⟨x, hx, rfl⟩
    rw [hN, Set.mem_singleton_iff] at hmem
    rw [hmem]
    exact hr C N hC hN
  · intro h C N hC hN
    obtain ⟨x, hx⟩ := E.exists_core_mem_componentSet C
    have hmem : E.associatedFactor x ∈ E.associatedFactors C := ⟨x, hx, rfl⟩
    rw [hN, Set.mem_singleton_iff] at hmem
    rw [← hmem]
    exact h C x hx hC

theorem forall_associatedFactor_of_componentConnectedSumDecomposition
    (h : E.componentConnectedSumDecomposition) :
    ∀ (C : ConnectedComponents M.Carrier) (x : E.tubes.core),
      ConnectedComponents.mk x.1 = C → E.cutIndices C = ∅ →
        Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
          (M.component C).toClosedOrientedManifold
          (E.associatedFactor x).toClosedOrientedManifold) :=
  E.noTubeRealization_iff_forall_associatedFactor.mp
    (E.noTubeRealization_of_componentConnectedSumDecomposition h)

theorem componentConnectedSumDecomposition_iff_forall_associatedFactor_and_cutComponentRealization :
    E.componentConnectedSumDecomposition ↔
      (∀ (C : ConnectedComponents M.Carrier) (x : E.tubes.core),
        ConnectedComponents.mk x.1 = C → E.cutIndices C = ∅ →
          Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
            (M.component C).toClosedOrientedManifold
            (E.associatedFactor x).toClosedOrientedManifold)) ∧
        E.cutComponentRealization := by
  rw [E.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization,
    E.noTubeRealization_iff_forall_associatedFactor]

theorem exists_cutIndices_eq_empty_and_associatedFactors_eq_singleton
    [IsEmpty E.tubes.Index] (C : ConnectedComponents M.Carrier) :
    E.cutIndices C = ∅ ∧ ∃ N : ConnectedClosedOrientedManifold.{u} 3,
      E.associatedFactors C = {N} :=
  ⟨E.cutIndices_eq_empty_of_isEmpty_index C,
    E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty C
      (E.cutIndices_eq_empty_of_isEmpty_index C)⟩

theorem exists_forall_associatedFactor_hypotheses [IsEmpty E.tubes.Index] :
    ∃ (C : ConnectedComponents M.Carrier) (x : E.tubes.core),
      ConnectedComponents.mk x.1 = C ∧ E.cutIndices C = ∅ ∧
        ∃ N : ConnectedClosedOrientedManifold.{u} 3, E.associatedFactors C = {N} := by
  obtain ⟨y⟩ := E.source_nonempty
  obtain ⟨x, hx⟩ := E.exists_core_mem_componentSet (ConnectedComponents.mk y)
  exact ⟨ConnectedComponents.mk y, x, hx, E.cutIndices_eq_empty_of_isEmpty_index _,
    E.exists_associatedFactors_eq_singleton_of_cutIndices_eq_empty _
      (E.cutIndices_eq_empty_of_isEmpty_index _)⟩

end SphericalCutCapTransition

end DifferentialGeometry.Topology
