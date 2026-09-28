import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.ExtinctionContractReduction
import DifferentialGeometry.Topology.ThreeManifold.CutCapGraphSumFrontier

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

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

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
