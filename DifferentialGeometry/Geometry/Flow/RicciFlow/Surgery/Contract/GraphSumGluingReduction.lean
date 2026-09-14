import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.ExtinctionContractReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.EndgameCongruenceCutReduction
import DifferentialGeometry.Topology.ThreeManifold.CutCapGraphSumFrontier

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem sphericalGraphSumRealization_of_graphSumRealization
    {M Q : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    (E : DifferentialGeometry.Topology.SphericalCutCapTransition M Q)
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (h : E.graphSumRealization) : E.sphericalGraphSumRealization S :=
  (E.sphericalGraphSumRealization_iff_componentConnectedSumDecomposition S hS).mpr
    (E.componentConnectedSumDecomposition_of_graphSumRealization h)

private theorem graphSumRealization_of_sphericalGraphSumRealization
    {M Q : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    (E : DifferentialGeometry.Topology.SphericalCutCapTransition M Q)
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (h : E.sphericalGraphSumRealization S) : E.graphSumRealization :=
  E.graphSumRealization_of_componentConnectedSumDecomposition
    ((E.sphericalGraphSumRealization_iff_componentConnectedSumDecomposition S hS).mp h)

theorem componentSumInput_of_graphSumRealization
    (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
    (h : ∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).graphSumRealization) :
    ∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).componentConnectedSumDecomposition :=
  fun i =>
    (H.cutCapTrace.transition i).componentConnectedSumDecomposition_of_graphSumRealization (h i)

theorem componentSumInput_iff_graphSumRealization
    (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u}) :
    (∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).componentConnectedSumDecomposition) ↔
      ∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).graphSumRealization :=
  forall_congr' fun i =>
    ((H.cutCapTrace.transition i).graphSumRealization_iff_componentConnectedSumDecomposition).symm

theorem componentSumInput_of_noTubeRealization_of_cutGraphSumRealization
    (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
    (hr : ∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).NoTubeRealization)
    (h : ∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).cutGraphSumRealization) :
    ∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).componentConnectedSumDecomposition :=
  fun i => by
    let E := H.cutCapTrace.transition i
    exact E.componentConnectedSumDecomposition_of_graphSumRealization
      (E.graphSumRealization_iff_noTubeRealization_and_cutGraphSumRealization.mpr ⟨hr i, h i⟩)

theorem graphSumRealization_of_isEmpty_tubeIndex
    (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
    (hemp : ∀ i : Fin H.eventCount, IsEmpty (H.cutCapTrace.transition i).tubes.Index)
    (hr : ∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).NoTubeRealization) :
    ∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).graphSumRealization :=
  fun i =>
    @DifferentialGeometry.Topology.SphericalCutCapTransition.graphSumRealization_of_isEmpty_index
      _ _ (H.cutCapTrace.transition i) (hemp i) (hr i)

theorem nonempty_poincareExtinctionContracts_iff_graphSumRealization
    (DiscardedCutOpen : Type u → Prop) :
    Nonempty (PoincareExtinctionContracts DiscardedCutOpen) ↔
      relativeCollarUniqueness.{u} ∧ ballEmbeddingIsotopy.{u} ∧
        (∃ (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ),
          Nonempty (GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen)) ∧
        isCommonLocalRealization.{u} ∧
        (∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
          (i : Fin H.eventCount), (H.cutCapTrace.transition i).graphSumRealization) :=
  (nonempty_poincareExtinctionContracts_iff DiscardedCutOpen).trans
    ⟨fun h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun H i =>
        (H.cutCapTrace.transition i).graphSumRealization_of_componentConnectedSumDecomposition
          (h.2.2.2.2 H i)⟩,
      fun h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun H i =>
        (H.cutCapTrace.transition i).componentConnectedSumDecomposition_of_graphSumRealization
          (h.2.2.2.2 H i)⟩⟩

theorem nonempty_poincareExtinctionContracts_iff_sphericalGraphSumRealization
    (DiscardedCutOpen : Type u → Prop)
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S) :
    Nonempty (PoincareExtinctionContracts DiscardedCutOpen) ↔
      relativeCollarUniqueness.{u} ∧ ballEmbeddingIsotopy.{u} ∧
        (∃ (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ),
          Nonempty (GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen)) ∧
        isCommonLocalRealization.{u} ∧
        (∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
          (i : Fin H.eventCount), (H.cutCapTrace.transition i).sphericalGraphSumRealization S) :=
  (nonempty_poincareExtinctionContracts_iff_graphSumRealization DiscardedCutOpen).trans
    ⟨fun h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun H i =>
        sphericalGraphSumRealization_of_graphSumRealization
          (H.cutCapTrace.transition i) S hS (h.2.2.2.2 H i)⟩,
      fun h =>
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun H i =>
        graphSumRealization_of_sphericalGraphSumRealization
          (H.cutCapTrace.transition i) S hS (h.2.2.2.2 H i)⟩⟩

theorem nonempty_poincareExtinctionContracts_of_graphSumRealization
    (DiscardedCutOpen : Type u → Prop) (hr : relativeCollarUniqueness.{u})
    (hb : ballEmbeddingIsotopy.{u})
    (ht : ∃ (p : CutoffParameters) (τ ε d : ℝ) (k : ℕ),
      Nonempty (GlobalStepInputs.{u} p τ ε d k DiscardedCutOpen))
    (hm : isCommonLocalRealization.{u})
    (hs : ∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
      (i : Fin H.eventCount), (H.cutCapTrace.transition i).graphSumRealization) :
    Nonempty (PoincareExtinctionContracts DiscardedCutOpen) :=
  nonempty_poincareExtinctionContracts_of_geometricInput DiscardedCutOpen
    (geometricReconstructionBackground_of_relativeCollarUniqueness_ballEmbeddingIsotopy
      ⟨hr, hb⟩)
    ht hm (fun H i =>
      (H.cutCapTrace.transition i).componentConnectedSumDecomposition_of_graphSumRealization
        (hs H i))

theorem exists_diffeomorph_standardThreeSphere_of_graphSumRealization
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    {g : SmoothRiemannianMetric (𝓡 3) M.Carrier} (W : PoincareControlledExtinction M g)
    (h : ∀ i : Fin W.history.eventCount,
      (W.history.cutCapTrace.transition i).graphSumRealization)
    [ConnectedSpace M.Carrier] [SimplyConnectedSpace M.Carrier] :
    Nonempty (M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
      DifferentialGeometry.Topology.standardThreeSphereLift.{u}.Carrier) :=
  exists_diffeomorph_standardThreeSphere_of_poincareControlledExtinction W
    (fun i =>
      (W.history.cutCapTrace.transition i).componentConnectedSumDecomposition_of_graphSumRealization
        (h i))

theorem smoothPoincareConjecture_of_graphSumRealization
    (h : ∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
      (i : Fin H.eventCount), (H.cutCapTrace.transition i).graphSumRealization)
    (hext : ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g)) :
    smoothPoincareConjecture.{u} :=
  smoothPoincareConjecture_of_poincareControlledExtinction
    (fun H i =>
      (H.cutCapTrace.transition i).componentConnectedSumDecomposition_of_graphSumRealization
        (h H i)) hext

theorem smoothPoincareConjecture_of_sphericalGraphSumRealization
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (h : ∀ (H : DifferentialGeometry.PDE.RicciFlow.Surgery.FiniteSurgeryHistory.{u})
      (i : Fin H.eventCount), (H.cutCapTrace.transition i).sphericalGraphSumRealization S)
    (hext : ∀ (M : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
      [SimplyConnectedSpace M.Carrier]
      (g : SmoothRiemannianMetric (𝓡 3) M.Carrier),
      Nonempty (PoincareControlledExtinction M.toClosedOrientedManifold g)) :
    smoothPoincareConjecture.{u} :=
  smoothPoincareConjecture_of_graphSumRealization
    (fun H i =>
      graphSumRealization_of_sphericalGraphSumRealization
        (H.cutCapTrace.transition i) S hS (h H i)) hext

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
