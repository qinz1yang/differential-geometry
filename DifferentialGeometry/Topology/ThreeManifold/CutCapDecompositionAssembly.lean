import DifferentialGeometry.Topology.ThreeManifold.CutCapIncidenceCycleRank
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardSumClosure

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem componentConnectedSumDecomposition_iff_localReconstruction :
    (∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition) ↔
      ∀ i : Fin T.eventCount, (T.transition i).localReconstruction :=
  forall_congr' fun i => ((T.transition i).localReconstruction_iff_componentConnectedSumDecomposition).symm

theorem componentwise_isPoincareStandard_of_componentConnectedSumDecomposition
    (h : ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition)
    (hctrl : T.poincareControlled) (hext : T.extinct) :
    ∀ i : Fin (T.eventCount + 1), ∀ C : ConnectedComponents (T.stage i).Carrier,
      isPoincareStandard ((T.stage i).component C).Carrier :=
  T.componentwise_isPoincareStandard_of_localReconstruction
    (fun i => ((T.transition i).localReconstruction_iff_componentConnectedSumDecomposition).mpr
      (h i)) hctrl hext

theorem isPoincareStandard_of_initialIdentification_of_componentConnectedSumDecomposition
    (h : ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition)
    (hctrl : T.poincareControlled) (hext : T.extinct)
    (M : ClosedOrientedManifold.{u} 3) [ConnectedSpace M.Carrier]
    (Φ : T.InitialIdentification M) : isPoincareStandard M.Carrier :=
  T.isPoincareStandard_of_initialIdentification_of_localReconstruction
    (fun i => ((T.transition i).localReconstruction_iff_componentConnectedSumDecomposition).mpr
      (h i)) hctrl hext M Φ

end FiniteCutCapTrace

end DifferentialGeometry.Topology
