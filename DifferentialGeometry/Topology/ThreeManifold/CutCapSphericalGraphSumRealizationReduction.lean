import DifferentialGeometry.Topology.ThreeManifold.CutCapCutComponentRealizationReduction
import DifferentialGeometry.Topology.ThreeManifold.CutCapEventSumRealizationAssembly
import DifferentialGeometry.Topology.ThreeManifold.CutCapIncidenceSpanningTree
import DifferentialGeometry.Topology.ThreeManifold.CutCapUncutCappingRealization

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

theorem componentConnectedSumDecomposition_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hglue : E.cutComponentGluing) (hcount : E.cutCapSummandCountDetermined) :
    E.componentConnectedSumDecomposition :=
  E.componentConnectedSumDecomposition_iff_noTubeRealization_and_cutComponentRealization.mpr
    ⟨E.noTubeRealization,
      E.cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined hglue hcount⟩

theorem graphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hglue : E.cutComponentGluing) (hcount : E.cutCapSummandCountDetermined) :
    E.graphSumRealization :=
  E.graphSumRealization_iff_cutComponentRealization.mpr
    (E.cutComponentRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined hglue hcount)

theorem localReconstruction_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hglue : E.cutComponentGluing) (hcount : E.cutCapSummandCountDetermined) :
    E.localReconstruction :=
  E.localReconstruction_of_incidenceGluing (fun C => E.cutIncidenceGraph_connected C)
    (E.componentConnectedSumDecomposition_of_cutComponentGluing_of_cutCapSummandCountDetermined
      hglue hcount)

theorem cutComponentGluing_and_cutCapSummandCountDetermined_of_componentConnectedSumDecomposition_of_summandCountUnique
    (h : E.componentConnectedSumDecomposition)
    (huniq : ∀ C : ConnectedComponents M.Carrier,
      finiteConnectedSumSummandCountUnique (E.canonicalEnumeration C)) :
    E.cutComponentGluing ∧ E.cutCapSummandCountDetermined :=
  ⟨E.cutComponentGluing_of_cutComponentRealization
      (E.cutComponentRealization_of_componentConnectedSumDecomposition h),
    E.cutCapSummandCountDetermined_of_componentConnectedSumDecomposition_of_summandCountUnique
      h huniq⟩

theorem cutComponentGluing_and_cutCapSummandCountDetermined_of_isEmpty_index_of_summandCountUnique
    [IsEmpty E.tubes.Index]
    (huniq : ∀ C : ConnectedComponents M.Carrier,
      finiteConnectedSumSummandCountUnique (E.canonicalEnumeration C)) :
    E.cutComponentGluing ∧ E.cutCapSummandCountDetermined :=
  ⟨E.cutComponentGluing_of_forall_cutIndices_eq_empty
      fun C => E.cutIndices_eq_empty_of_isEmpty_index C,
    (E.cutCapSummandCountDetermined_iff_cutCapSummandAbsorptionFree_of_forall_cutIndices_eq_empty
        E.noTubeRealization fun C => E.cutIndices_eq_empty_of_isEmpty_index C).mpr
      (E.cutCapSummandAbsorptionFree_of_summandCountUnique huniq)⟩

theorem sphericalGraphSumRealization_of_isEmpty_index_of_summandCountUnique
    [IsEmpty E.tubes.Index] (S : ConnectedClosedOrientedManifold.{u} 3)
    (hS : isSphereTwoTimesCircleFactor S)
    (huniq : ∀ C : ConnectedComponents M.Carrier,
      finiteConnectedSumSummandCountUnique (E.canonicalEnumeration C)) :
    E.sphericalGraphSumRealization S :=
  have hfrontier :=
    E.cutComponentGluing_and_cutCapSummandCountDetermined_of_isEmpty_index_of_summandCountUnique
      huniq
  E.sphericalGraphSumRealization_of_componentConnectedSumDecomposition S hS
    (E.componentConnectedSumDecomposition_of_cutComponentGluing_of_cutCapSummandCountDetermined
      hfrontier.1 hfrontier.2)

theorem sphericalGraphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (hglue : E.cutComponentGluing) (hcount : E.cutCapSummandCountDetermined) :
    E.sphericalGraphSumRealization S :=
  E.sphericalGraphSumRealization_of_componentConnectedSumDecomposition S hS
    (E.componentConnectedSumDecomposition_of_cutComponentGluing_of_cutCapSummandCountDetermined
      hglue hcount)

theorem sphericalTreeGluing_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (hglue : E.cutComponentGluing) (hcount : E.cutCapSummandCountDetermined) :
    E.sphericalTreeGluing S :=
  E.sphericalTreeGluing_of_sphericalGraphSumRealization S
    (E.sphericalGraphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
      S hS hglue hcount)

theorem sphericalGraphSumRealization_iff_cutComponentGluing_and_cutCapSummandCountDetermined_of_summandCountUnique
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (huniq : ∀ L : List (ConnectedClosedOrientedManifold.{u} 3),
      finiteConnectedSumSummandCountUnique L) :
    E.sphericalGraphSumRealization S ↔ E.cutComponentGluing ∧ E.cutCapSummandCountDetermined := by
  constructor
  · intro hex
    exact ⟨E.cutComponentGluing_iff_cutComponentCanonicalGluing.mpr
        (E.cutComponentCanonicalGluing_of_sphericalGraphSumRealization hS hex),
      E.cutCapSummandCountDetermined_of_sphericalGraphSumRealization_of_summandCountUnique
        hS hex huniq⟩
  · rintro ⟨hglue, hcount⟩
    exact E.sphericalGraphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
      S hS hglue hcount

theorem sphericalTreeGluing_iff_cutComponentGluing_and_cutCapSummandCountDetermined_of_summandCountUnique
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (huniq : ∀ L : List (ConnectedClosedOrientedManifold.{u} 3),
      finiteConnectedSumSummandCountUnique L) :
    E.sphericalTreeGluing S ↔ E.cutComponentGluing ∧ E.cutCapSummandCountDetermined :=
  (E.sphericalTreeGluing_iff_sphericalGraphSumRealization S).trans
    (E.sphericalGraphSumRealization_iff_cutComponentGluing_and_cutCapSummandCountDetermined_of_summandCountUnique
      S hS huniq)

end SphericalCutCapTransition

namespace FiniteCutCapTrace

variable (T : FiniteCutCapTrace.{u})

theorem componentConnectedSumDecomposition_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hglue : ∀ i : Fin T.eventCount, (T.transition i).cutComponentGluing)
    (hcount : ∀ i : Fin T.eventCount, (T.transition i).cutCapSummandCountDetermined) :
    ∀ i : Fin T.eventCount, (T.transition i).componentConnectedSumDecomposition :=
  fun i => (T.transition i).componentConnectedSumDecomposition_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (hglue i) (hcount i)

theorem sphericalGraphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (S : ConnectedClosedOrientedManifold.{u} 3) (hS : isSphereTwoTimesCircleFactor S)
    (hglue : ∀ i : Fin T.eventCount, (T.transition i).cutComponentGluing)
    (hcount : ∀ i : Fin T.eventCount, (T.transition i).cutCapSummandCountDetermined) :
    ∀ i : Fin T.eventCount, (T.transition i).sphericalGraphSumRealization S :=
  fun i => (T.transition i).sphericalGraphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    S hS (hglue i) (hcount i)

end FiniteCutCapTrace

end DifferentialGeometry.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery

universe u

open DifferentialGeometry.Topology (SphericalCutCapTransition)

theorem metricCutCapEvent_hsum_of_cutComponentGluing_of_cutCapSummandCountDetermined
    {M Q : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3} {a s : ℝ}
    (E : MetricCutCapEvent M Q a s)
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (hglue : E.transition.cutComponentGluing)
    (hcount : E.transition.cutCapSummandCountDetermined) :
    E.transition.sphericalGraphSumRealization S :=
  SphericalCutCapTransition.sphericalGraphSumRealization_of_cutComponentGluing_of_cutCapSummandCountDetermined
    E.transition S hS hglue hcount

theorem finiteSurgeryHistory_event_hsum_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (H : FiniteSurgeryHistory.{u})
    (S : DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.{u} 3)
    (hS : DifferentialGeometry.Topology.isSphereTwoTimesCircleFactor S)
    (hglue : ∀ i : Fin H.eventCount, (H.event i).transition.cutComponentGluing)
    (hcount : ∀ i : Fin H.eventCount, (H.event i).transition.cutCapSummandCountDetermined) :
    ∀ i : Fin H.eventCount, (H.cutCapTrace.transition i).sphericalGraphSumRealization S :=
  fun i => metricCutCapEvent_hsum_of_cutComponentGluing_of_cutCapSummandCountDetermined
    (H.event i) S hS (hglue i) (hcount i)

end DifferentialGeometry.PDE.RicciFlow.Surgery
